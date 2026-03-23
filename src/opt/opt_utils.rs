//! Utilities for implementing optimizations.
//!
//! You can freely add utilities commonly used in the implementation of multiple optimizations here.
use crate::ir::*;
use crate::opt::*;
use crate::some_or;
use core::panic;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::ops::DerefMut;
use std::process::id;

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
        if let Some(new_operand) = replaces.get(rid) {
            *operand = new_operand.clone();
        }
    }
}

pub(crate) trait Walkable {
    fn walk<F>(&mut self, f: F)
    where
        F: FnMut(&mut Operand);
}

impl Walkable for FunctionDefinition {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand),
    {
        for block in self.blocks.values_mut() {
            // iterate over all instructions
            for inst in &mut block.instructions {
                inst.deref_mut().walk(&mut f);
            }
            // iterate block exit
            block.exit.walk(&mut f);
        }
    }
}

impl Walkable for Instruction {
    fn walk<F>(&mut self, mut f: F)
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
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand),
    {
        match self {
            BlockExit::Jump { arg } => arg.walk(&mut f),
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                f(condition);
                arg_then.walk(&mut f);
                arg_else.walk(&mut f);
            }
            BlockExit::Return { value } => f(value),
            BlockExit::Switch {
                value,
                default,
                cases,
            } => {
                f(value);
                default.walk(&mut f);
                for (_, arg) in cases {
                    arg.walk(&mut f);
                }
            }
            BlockExit::Unreachable => {}
        }
    }
}

impl Walkable for JumpArg {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand),
    {
        for arg in &mut self.args {
            f(arg);
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct Domtree {
    idoms: HashMap<BlockId, BlockId>,
    pub(crate) frontiers: HashMap<BlockId, Vec<BlockId>>,
    reverse_post_order: Vec<BlockId>,
}

impl Domtree {
    pub(crate) fn new(
        bid_init: BlockId,
        cfg: &HashMap<BlockId, Vec<JumpArg>>,
        reverse_cfg: &HashMap<BlockId, Vec<(BlockId, JumpArg)>>,
    ) -> Self {
        let mut reverse_post_order = traverse_postorder(bid_init, cfg);
        reverse_post_order.reverse();

        let inverse_reverse_post_order = reverse_post_order
            .iter()
            .enumerate()
            .map(|(i, bid)| (*bid, i))
            .collect();
        // println!("RPO: {:?}", reverse_post_order);
        // immediate dominator of each block
        let mut idoms = HashMap::<BlockId, BlockId>::new();
        // get idoms using iterative methods
        // 当idoms收敛时，结束迭代过程
        loop {
            let mut changed = false;

            // 根据拓扑排列顺序(虽然有环是不完全拓扑)遍历每个block
            for bid in &reverse_post_order {
                if *bid == bid_init {
                    continue;
                }

                let mut idom = None;
                // 遍历所有predecessor bid_prev, 更新idom为bid_prev p 与当前idom q的第一个共同祖先 c
                // `祖先`指 RPO偏序关系中较小节点，并且存在2条偏序链: c = idom(p1) = idom(idom(p2)) = ... = idom^*(p), c = idom(q1) = idom(idom(q2)) =...= idom^*(q)
                // 根据RPO性质可知, RPO(c) < RPO(p1) < ... < RPO(p), RPO(c) < RPO(q1) < ... < RPO(q).
                // `第一个`指的是这两条偏序链只在c处有交点(即第一个父亲交点)，对应的RPO值最大
                // 在更新bid的idom值时，要利用self.idoms中存储的各个bid_prev的idom值，这也是为什么我们需要从RPO值较小的节点开始更新idom
                for (bid_prev, _) in reverse_cfg.get(bid).unwrap() {
                    // 前驱节点的idom值计算过(这个判断是否有必要吗?)
                    if *bid_prev == bid_init || idoms.contains_key(bid_prev) {
                        idom = Some(intersect_idom(
                            idom,
                            *bid_prev,
                            &inverse_reverse_post_order,
                            &idoms,
                        ));
                    }
                }
                // 用idom更新idoms
                if let Some(idom) = idom {
                    let _unused = idoms
                        .entry(*bid)
                        .and_modify(|v| {
                            if *v != idom {
                                changed = true;
                                *v = idom;
                            }
                        })
                        .or_insert_with(|| {
                            changed = true;
                            idom
                        });
                }
            }
            if !changed {
                break;
            }
        }

        // 计算dominance frontier
        // DF(X) = {Y | X \notin dom(Y) /\ (exists Z \in pred(Y) s.t. X = {Z} U dom(Z))}
        // 注意dominate关系是在两个不同的block之间才有，不能说X \in dom(X), 但是如果X \in prev(X)且X不只1个prev，那么X \in DF(X)
        let mut frontiers = HashMap::new();
        for (bid, prevs) in reverse_cfg {
            // 如果唯一的predecessor被X dominate，那自己也一定被X dominate，所以自己一定不是dominance frontier
            // assume bid = Y
            if prevs.len() <= 1 {
                continue;
            }
            let idom = *some_or!(idoms.get(bid), continue);
            for (bid_prev, _) in prevs {
                // bid_prev = Z
                // (遍历)给定了Y与predecessor Z，反过来寻找满足上式DF(X) = ... 的X
                // 先遍历Z和Z的dominators，再判断是否满足 X \notin dom(Y)
                // runner = Z -> idom(Z) -> idom(idom(Z)) -> ...(runner iterates over Z U {dom(Z)})
                let mut runner = *bid_prev;
                // 当runner 能dominate Y时停止往dominance tree上级遍历
                while runner == *bid || !Self::dominates(&idoms, runner, *bid) {
                    // 此时的(X, Y)构成一组frontier有序对(X has a dominance frontier called Y)
                    frontiers.entry(runner).or_insert_with(Vec::new).push(*bid);
                    // println!("runner: {}, bid: {}, idom: {}", runner, bid, idom); // 打印X, Y, 和Y实际的immediate dominator(X应该不断向上靠近idom(Y),但是不会dominate Y)
                    runner = *idoms.get(&runner).unwrap(); // 不用担心是bid_init,因为runner = bid_init时一定退出循环了
                }
            }
        }

        Self {
            idoms,
            frontiers,
            reverse_post_order,
        }
    }

    pub(crate) fn idom(&self, bid: BlockId) -> Option<BlockId> {
        self.idoms.get(&bid).cloned()
    }

    pub(crate) fn frontiers(&self, bid: BlockId) -> Option<&Vec<BlockId>> {
        self.frontiers.get(&bid)
    }

    pub(crate) fn reverse_post_order(&self) -> Vec<BlockId> {
        self.reverse_post_order.clone()
    }

    pub(crate) fn walk<F>(&self, mut f: F)
    where
        F: FnMut(Option<BlockId>, BlockId),
    {
        for bid in &self.reverse_post_order {
            f(self.idoms.get(bid).cloned(), *bid);
        }
    }
}

impl Domtree {
    // whether lhs dominates rhs? -> lhs ?= idom^*(rhs)
    fn dominates(idoms: &HashMap<BlockId, BlockId>, lhs: BlockId, mut rhs: BlockId) -> bool {
        if rhs == lhs {
            panic!("dominance relation can only be judge when lhs != rhs");
        }
        while let Some(&idom) = idoms.get(&rhs) {
            rhs = idom;
            if rhs == lhs {
                return true;
            }
        }
        false
    }
}

fn traverse_postorder(bid_init: BlockId, cfg: &HashMap<BlockId, Vec<JumpArg>>) -> Vec<BlockId> {
    let mut post_order_config = PostOrderConfig {
        post_order: vec![],
        bid_visited: HashSet::from([bid_init]),
    };
    post_order_config.traverse(bid_init, cfg);
    post_order_config.post_order
}

struct PostOrderConfig {
    post_order: Vec<BlockId>,
    bid_visited: HashSet<BlockId>,
}

impl PostOrderConfig {
    fn traverse(&mut self, bid: BlockId, cfg: &HashMap<BlockId, Vec<JumpArg>>) {
        for arg in cfg.get(&bid).unwrap() {
            if self.bid_visited.insert(arg.bid) {
                self.traverse(arg.bid, cfg);
            }
        }
        self.post_order.push(bid);
    }
}

// 找第一个共同的父节点(通过不停取immediate dominator(减少RPO)向上遍历)
fn intersect_idom(
    lhs: Option<BlockId>,
    mut rhs: BlockId,
    inverse_reverse_post_order: &HashMap<BlockId, usize>, // block的RPO值
    idoms: &HashMap<BlockId, BlockId>,                    // 已经构建好的部分idom关系
) -> BlockId {
    let mut lhs = some_or!(lhs, return rhs);

    // lhs与rhs不断在dominator tree中向上遍历，直到双方相等
    loop {
        // 一定能退出，因为所有节点被bid_init支配
        if lhs == rhs {
            return lhs;
        }
        // 获取当前lhs, rhs的RPO值
        let lhs_index = inverse_reverse_post_order.get(&lhs).unwrap();
        let rhs_index = inverse_reverse_post_order.get(&rhs).unwrap();
        // RPO值大的往上爬一级
        match lhs_index.cmp(rhs_index) {
            Ordering::Less => {
                rhs = *idoms.get(&rhs).unwrap();
            }
            Ordering::Greater => {
                lhs = *idoms.get(&lhs).unwrap();
            }
            Ordering::Equal => panic!("intersect_dom: lhs == rhs cannot happen"),
        }
    }
}

// mark a(potentially) allocation as inpromotable
pub(crate) fn mark_inpromotable(inpromotable: &mut HashSet<usize>, value: &Operand) {
    let (rid, _) = some_or!(value.get_register(), return);
    let RegisterId::Local { aid } = rid else {
        return;
    };
    let _unused = inpromotable.insert(*aid);
}
