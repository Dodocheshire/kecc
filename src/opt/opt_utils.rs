//! Utilities for implementing optimizations.
//!
//! You can freely add utilities commonly used in the implementation of multiple optimizations here.
use crate::ir::*;
use crate::opt::*;
use std::collections::{HashMap, HashSet};
use std::ops::DerefMut;

pub(crate) fn make_cfg(fdef: &FunctionDefinition) -> HashMap<BlockId, Vec<JumpArg>> {
    fdef.blocks
        .iter()
        .map(|(bid, block)| {
            let mut args = Vec::new();
            match &block.exit {
                BlockExit::Jump { arg } => {
                    args.push(arg.clone());
                }
                BlockExit::ConditionalJump {
                    condition,
                    arg_then,
                    arg_else,
                } => {
                    args.push(arg_else.clone());
                    args.push(arg_then.clone());
                }
                BlockExit::Switch {
                    value,
                    default,
                    cases,
                } => {
                    args.push(default.clone());
                    for (c, arg) in cases {
                        args.push(arg.clone());
                    }
                }
                _ => {}
            }
            (*bid, args)
        })
        .collect::<HashMap<_, _>>()
}

// 计算前驱control flow 图
pub(crate) fn reverse_cfg(
    cfg: &HashMap<BlockId, Vec<JumpArg>>,
) -> HashMap<BlockId, Vec<(BlockId, JumpArg)>> {
    let mut result = HashMap::new();
    for (bid, jumps) in cfg {
        for jump in jumps {
            result
                .entry(jump.bid)
                .or_insert_with(Vec::new)
                .push((*bid, jump.clone()));
        }
    }

    result
}

pub(crate) fn replace_operands(operand: &mut Operand, replaces: &HashMap<RegisterId, Operand>) {
    if let Operand::Register { rid, .. } = operand {
        if let Some(new_operand) = replaces.get(&rid) {
            *operand = new_operand.clone();
        }
    }
}

pub(crate) trait Walkable {
    fn walk<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Operand);
}

impl Walkable for FunctionDefinition {
    fn walk<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Operand),
    {
        for block in self.blocks.values_mut() {
            // iterate over all instructions
            for inst in &mut block.instructions {
                inst.deref_mut().walk(f);
            }
            // iterate block exit
            block.exit.walk(f);
        }
    }
}

impl Walkable for Instruction {
    fn walk<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Operand),
    {
        match self {
            Instruction::Nop => {}
            Instruction::Value { value } => f(value),
            Instruction::BinOp {
                op,
                lhs,
                rhs,
                dtype,
            } => {
                f(lhs);
                f(rhs);
            }
            Instruction::UnaryOp { op, operand, dtype } => {
                f(operand);
            }
            Instruction::Store { ptr, value } => {
                f(ptr);
                f(value);
            }
            Instruction::Load { ptr } => f(ptr),
            Instruction::Call {
                callee,
                args,
                return_type,
            } => {
                f(callee);
                for arg in args {
                    f(arg);
                }
            }
            Instruction::TypeCast {
                value,
                target_dtype,
            } => {
                f(value);
            }
            Instruction::GetElementPtr { ptr, offset, dtype } => {
                f(ptr);
                f(offset);
            }
        }
    }
}

impl Walkable for BlockExit {
    fn walk<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Operand),
    {
        match self {
            BlockExit::Jump { arg } => arg.walk(f),
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                f(condition);
                arg_then.walk(f);
                arg_else.walk(f);
            }
            BlockExit::Return { value } => f(value),
            BlockExit::Switch {
                value,
                default,
                cases,
            } => {
                f(value);
                default.walk(f);
                for (_, arg) in cases {
                    arg.walk(f);
                }
            }
            BlockExit::Unreachable => {}
        }
    }
}

impl Walkable for JumpArg {
    fn walk<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Operand),
    {
        for arg in &mut self.args {
            f(arg);
        }
    }
}
