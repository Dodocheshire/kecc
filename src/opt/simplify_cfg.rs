use crate::asm::Register;
use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::*;
use crate::some_or;

use itertools::izip;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::Hash;
use std::io::empty;
use std::ops::Deref;
use std::task::Context;

pub type SimplifyCfg = FunctionPass<
    Repeat<(
        SimplifyCfgConstProp,
        (SimplifyCfgReach, (SimplifyCfgMerge, SimplifyCfgEmpty)),
    )>,
>;

/// Simplifies block exits by propagating constants.
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgConstProp {}

/// Retains only those blocks that are reachable from the init.
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgReach {}

/// Merges two blocks if a block is pointed to only by another
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgMerge {}

/// Removes empty blocks
#[derive(Default, Clone, Copy, Debug)]
pub struct SimplifyCfgEmpty {}

impl Optimize<FunctionDefinition> for SimplifyCfgConstProp {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        code.blocks
            .iter_mut()
            .map(|(_, block)| {
                if let Some(exit) = self.simplify_block_exit(&block.exit) {
                    block.exit = exit;
                    true
                } else {
                    false
                }
            })
            .fold(false, |l, r| l || r)
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgReach {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let graph = make_cfg(code);
        // do bfs on control flow graph to see which blocks cannot never be reached from bid_init

        let mut queue = Vec::new();
        let mut visited = HashSet::new();
        let _unused = visited.insert(code.bid_init);
        queue.push(code.bid_init);

        while let Some(bid) = queue.pop() {
            if let Some(args) = graph.get(&bid) {
                for arg in args {
                    let newly_inserted = visited.insert(arg.bid);
                    if newly_inserted {
                        queue.push(arg.bid);
                    }
                }
            }
        }

        let size_orig = code.blocks.len();
        code.blocks.retain(|bid, block| visited.contains(bid));

        code.blocks.len() < size_orig
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgMerge {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let mut result = false;
        // 可能要迭代多次
        loop {
            // 每次迭代开始重新计算一次control flow graph
            let graph = make_cfg(code);
            let pred = reverse_cfg(&graph);

            let mut changed = false;
            let keys: Vec<_> = code.blocks.keys().map(|k| *k).collect();

            for bid_from in keys {
                // 注意循环中会减少code.blocks中的block个数，但keys不变，所以code.blocks.get(&bid_from)不一定为Some
                let (bid_to, args_to) = {
                    let block_from = some_or!(code.blocks.get(&bid_from), continue);
                    let BlockExit::Jump { arg } = &block_from.exit else {
                        continue;
                    };
                    // 死循环block不能与自己合并
                    if bid_from == arg.bid {
                        continue;
                    }

                    // 用前驱图判断 arg.bid 只有一个前驱
                    let preds = some_or!(pred.get(&arg.bid), continue);
                    if preds.len() != 1 {
                        continue;
                    }
                    (arg.bid, arg.args.clone())
                    // 释放对code.blocks的immutable reference
                };

                // 开始merge
                let block_to = code.blocks.remove(&bid_to).unwrap();
                let block_from = code.blocks.get_mut(&bid_from).unwrap();
                let mut replaces = HashMap::new();

                // gathers phinode replacement information
                for (i, (a, p)) in izip!(&args_to, block_to.phinodes.iter()).enumerate() {
                    assert_eq!(&a.dtype(), p.deref());
                    let _unused = replaces.insert(RegisterId::arg(bid_to, i), a.clone());
                }
                // move instructions
                let len = block_from.instructions.len();
                for (i, inst) in block_to.instructions.into_iter().enumerate() {
                    let dtype = inst.dtype();
                    block_from.instructions.push(inst);
                    // 记录需要替换的temp register id
                    let from = RegisterId::temp(bid_to, i);
                    let to: Operand =
                        Operand::register(RegisterId::temp(bid_from, i + len), dtype.clone());
                    // b0(2条指令) -> b1 那么b1的第12条指令结果%b1:i12，合并到b0中变为%b0:i14
                    let _unused = replaces.insert(from, to);
                }
                // exit 替换
                block_from.exit = block_to.exit;
                let _ = code.walk(&mut |operand| replace_operands(operand, &replaces));

                changed = true;
                result = true;
            }
            // 如果本次迭代没有变化，不再进行迭代
            if !changed {
                break;
            }
        }
        result
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgEmpty {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let empty_blocks = code
            .blocks
            .iter()
            .filter(|(_, block)| block.phinodes.is_empty() && block.instructions.is_empty())
            .map(|(bid, block)| (*bid, block.clone()))
            .collect::<HashMap<_, _>>();
        code.blocks
            .iter_mut()
            .map(|(_, block)| self.simplify_block_exit(&mut block.exit, &empty_blocks))
            .fold(false, |l, r| l || r)
    }
}

impl SimplifyCfgConstProp {
    fn simplify_block_exit(&self, exit: &BlockExit) -> Option<BlockExit> {
        match exit {
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                if arg_then == arg_else {
                    return Some(BlockExit::Jump {
                        arg: arg_then.clone(),
                    });
                }
                if let Some(cst) = condition.get_constant() {
                    match cst {
                        Constant::Int { value: 0, .. } => {
                            return Some(BlockExit::Jump {
                                arg: arg_then.clone(),
                            });
                        }
                        Constant::Int { value: 1, .. } => {
                            return Some(BlockExit::Jump {
                                arg: arg_else.clone(),
                            });
                        }
                        _ => {}
                    }
                }
                None
            }
            BlockExit::Switch {
                value,
                default,
                cases,
            } => {
                if cases.iter().all(|(c, arg)| arg == default) {
                    return Some(BlockExit::Jump {
                        arg: default.clone(),
                    });
                }
                if let Some(v) = value.get_constant() {
                    let jump_arg = if let Some((_, arg)) = cases.iter().find(|(c, arg)| v == c) {
                        arg.clone()
                    } else {
                        default.clone()
                    };
                    return Some(BlockExit::Jump { arg: jump_arg });
                }
                None
            }
            _ => None,
        }
    }
}

impl SimplifyCfgEmpty {
    fn simplify_block_exit(
        &self,
        exit: &mut BlockExit,
        empty_blocks: &HashMap<BlockId, Block>,
    ) -> bool {
        match exit {
            BlockExit::Jump { arg } => {
                let block = some_or!(empty_blocks.get(&arg.bid), return false);
                *exit = block.exit.clone();
                true
            }
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                let changed1 = self.simplify_jump_arg(arg_then, empty_blocks);
                let changed2 = self.simplify_jump_arg(arg_else, empty_blocks);
                changed1 || changed2
            }
            BlockExit::Switch {
                value,
                default,
                cases,
            } => {
                let changed1 = self.simplify_jump_arg(default, empty_blocks);
                let changed2 = cases
                    .iter_mut()
                    .map(|(_, arg)| self.simplify_jump_arg(arg, empty_blocks))
                    .fold(false, |l, r| l || r);
                changed1 || changed2
            }
            BlockExit::Return { .. } | BlockExit::Unreachable => false,
        }
    }

    fn simplify_jump_arg(&self, arg: &mut JumpArg, empty_blocks: &HashMap<BlockId, Block>) -> bool {
        let block = some_or!(empty_blocks.get(&arg.bid), return false);
        // an empty block has no phinodes
        assert!(arg.args.is_empty());

        // 只能在next block的exit为jump时才能简化当前block的JumpArg
        if let BlockExit::Jump { arg: a } = &block.exit {
            *arg = a.clone();
            true
        } else {
            false
        }
    }
}
