use core::ops::{Deref, DerefMut};
use std::collections::{BTreeMap, HashMap, HashSet};

use itertools::Itertools;

use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::opt_visualizer::*;
use crate::opt::*;
use crate::some_or;

pub type Mem2reg = FunctionPass<Mem2regInner>;

#[derive(Default, Clone, Copy, Debug)]
pub struct Mem2regInner {}

impl Optimize<FunctionDefinition> for Mem2regInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        // collects inpromotable local memory allocations and stores
        // A local allocation is promotable only if it is used only as the pointer of store/load inst
        let mut inpromotable = HashSet::new();
        // the blocks which have `Store` instructions of an allocation
        // aid -> Vec<BlockId>
        let mut stores = HashMap::<usize, HashSet<BlockId>>::new();

        for (bid, block) in &code.blocks {
            for instr in &block.instructions {
                match instr.deref() {
                    Instruction::Nop => {}
                    Instruction::BinOp { lhs, rhs, .. } => {
                        mark_inpromotable(&mut inpromotable, &lhs);
                        mark_inpromotable(&mut inpromotable, &rhs);
                    }
                    Instruction::UnaryOp { operand, .. } => {
                        mark_inpromotable(&mut inpromotable, &operand);
                    }
                    Instruction::Store { ptr, value } => {
                        mark_inpromotable(&mut inpromotable, &value);
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            // 注意stores里的一个allocation可能记录多个相同的bid
                            let _unused =
                                stores.entry(*aid).or_insert_with(HashSet::new).insert(*bid);
                        }
                    }
                    Instruction::Load { .. } => {}
                    Instruction::Call { callee, args, .. } => {
                        mark_inpromotable(&mut inpromotable, callee);
                        for arg in args {
                            mark_inpromotable(&mut inpromotable, arg);
                        }
                    }
                    Instruction::Value { value } => {
                        mark_inpromotable(&mut inpromotable, value);
                    }
                    // %p = gep %a, offset
                    // store x → %p
                    // 此时%a 被当作数组 / struct使用，会单独访问多个子位置，破坏了一个SSA变量的假设
                    Instruction::GetElementPtr { ptr, offset, dtype } => {
                        mark_inpromotable(&mut inpromotable, ptr);
                        mark_inpromotable(&mut inpromotable, offset);
                    }
                    Instruction::TypeCast { value, .. } => {
                        mark_inpromotable(&mut inpromotable, &value);
                    }
                }
            }
        }
        // if no local allocations are promotable, bail out
        if (0..code.allocations.len()).all(|i| inpromotable.contains(&i)) {
            return false;
        }

        println!("stores: {:?}", stores);
        println!("inpromotable: {:?}", inpromotable);

        // draws CFG, reverse CFG, and dominator tree(Domtree)
        let cfg = make_cfg(code);
        let reverse_cfg = reverse_cfg(&cfg);
        let domtree = Domtree::new(code.bid_init, &cfg, &reverse_cfg);

        // print debug information
        use std::fs;
        let func_name = "my_func";
        let _unused = fs::write("cfg.dot", OptVisualizer::cfg_to_dot(&cfg, func_name)).ok();
        let _unused = fs::write(
            "domtree.dot",
            OptVisualizer::domtree_to_dot(&domtree, func_name),
        )
        .ok();

        // `join block`: the block that will potentially be inserted with a phinode to prolong the lifetime of the value of var `aid`
        // calculates the join blocks with which a phinode may be inserted for each promotable locations:
        // Given allocation `aid` and all blocks `bid` that stores to `aid`, calculate DF(bids) U DF(DF(bids)) U ...
        let joins: HashMap<usize, HashSet<BlockId>> = stores
            .iter()
            .filter(|(aid, bids)| !inpromotable.contains(*aid))
            .map(|(aid, bids)| {
                (*aid, {
                    // DFS search start
                    let mut bid_stack: Vec<BlockId> = bids.iter().cloned().collect();
                    let mut visited = HashSet::new();
                    while let Some(bid) = bid_stack.pop() {
                        // get neighbors: DF(bid)
                        let bid_frontiers = some_or!(domtree.frontiers(bid), continue);
                        for bid_frontier in bid_frontiers {
                            if visited.insert(*bid_frontier) {
                                bid_stack.push(*bid_frontier);
                            }
                        }
                    }

                    visited
                })
            })
            .collect();

        println!("joins: {:?}", joins);

        // table for the nearest join block according to the dominator tree
        let mut join_table = JoinTable::new(&domtree, &joins);

        // replacement dictionary
        let mut replaces = HashMap::<RegisterId, OperandVar>::new();

        // Phinodes to be inserted. If `(aid, bid)` is in this set, then a phinode for `aid` should
        // be inserted at the beginning of `bid` 即记录哪些块确实需要插入Phi节点
        let mut phinode_indexes = HashSet::<(usize, BlockId)>::new();

        // values stored in local allcations at the end of each block. If `(aid, bid) |-> X`,
        // then the value stored in `aid`  at the end of `bid` is  `X`
        // 初始化每个变量的值为undef
        let mut end_values: HashMap<(usize, BlockId), OperandVar> = (0..code.allocations.len())
            .filter(|i| !inpromotable.contains(i))
            .map(|aid| {
                let dtype = code.allocations.get(aid).unwrap().deref().clone();
                (
                    (aid, code.bid_init),
                    OperandVar::Operand(Operand::constant(Constant::Undef { dtype })),
                )
            })
            .collect();

        // iterate in RPO order to calculate `end_values` and `replaces`
        let rpo = domtree.reverse_post_order();

        for bid in &rpo {
            let block = code.blocks.get(bid).unwrap();

            for (i, instr) in block.instructions.iter().enumerate() {
                match instr.deref() {
                    // 遇到一条store指令，更新end_values
                    Instruction::Store { ptr, value } => {
                        let (rid, _dtype) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if inpromotable.contains(aid) {
                                continue;
                            }
                            let _unused =
                                end_values.insert((*aid, *bid), OperandVar::Operand(value.clone()));
                        }
                    }
                    Instruction::Load { ptr } => {
                        let (rid, _dtype) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if inpromotable.contains(aid) {
                                continue;
                            }
                            let bid_join = join_table.lookup(*aid, *bid);
                            println!(
                                "in block {}, inst {}, the load instruction has bid_join: {}",
                                bid, i, bid_join
                            );
                            let mut runner = *bid;
                            // runner: bid -> idom(bid) -> idom(idom(bid)) -> ... -> bid_join
                            while runner != bid_join && !end_values.contains_key(&(*aid, runner)) {
                                runner = domtree.idom(runner).expect(
                                    "runner should have idom because it cannot be bid_init",
                                );
                            }

                            let var = end_values.entry((*aid, runner)).or_insert_with(|| {
                                // 此时说明bid_join没有store %aid的指令(且根据RPO的块访问顺序, runner路径上的block也没有对#aid进行store)，需要申请phinode延长变量#aid的lifetime
                                assert_eq!(runner, bid_join);
                                let _unused = phinode_indexes.insert((*aid, bid_join));
                                OperandVar::Phi((*aid, bid_join))
                            });
                            println!(
                                "in block {}, inst {}, the load result is replaced with: {}",
                                bid, i, var
                            );

                            let result = replaces.insert(RegisterId::temp(*bid, i), var.clone());
                            assert_eq!(result, None);
                            // 同步更新当前块结束时的最新值
                            let var = var.clone();
                            let _unused = end_values.insert((*aid, *bid), var);
                        }
                    }
                    _ => {}
                }
            }
        }

        println!(
            "the initial phinodes that should be inserted `phinode_indexes`: {:?}",
            phinode_indexes
        );

        // generate phinodes recursively
        println!("generating phinodes recursively...");

        let mut phinode_visited = phinode_indexes;
        let mut phinode_stack = phinode_visited.iter().cloned().collect::<Vec<_>>();
        let mut phinodes =
            BTreeMap::<(usize, BlockId), (Dtype, HashMap<BlockId, OperandVar>)>::new();
        println!("`initial phinode_stack` {:?}", phinode_stack);
        while let Some((aid, bid)) = phinode_stack.pop() {
            let mut cases = HashMap::new();
            // 一个phinode依赖多个predecessor的end value，可能要求新的phinode
            let prevs = some_or!(reverse_cfg.get(&bid), continue);
            for (bid_prev, _) in prevs {
                let bid_prev_join = join_table.lookup(aid, *bid_prev);

                println!(
                    "bid_prev: {}, bid: {}, bid_prev_join of aid#{} is {}",
                    bid_prev, bid, aid, bid_prev_join
                );

                let mut runner = *bid_prev;
                // runner: bid_prev -> idom(bid_prev) -> idom(idom(bid_prev)) -> ... -> bid_prev_join
                while runner != bid_prev_join && !end_values.contains_key(&(aid, runner)) {
                    runner = domtree
                        .idom(runner)
                        .expect("runner should have idom because it cannot be bid_init");
                }
                let var = end_values.entry((aid, runner)).or_insert_with(|| {
                    assert_eq!(runner, bid_prev_join);
                    if phinode_visited.insert((aid, bid_prev_join)) {
                        phinode_stack.push((aid, bid_prev_join));
                    }
                    OperandVar::Phi((aid, bid_prev_join))
                });

                println!(
                    "In bid_prev {}, phinode argument for aid#{} passed is {}",
                    bid_prev, aid, var
                );

                // phi(x1, x2, ..., x_n) bid有predecessor，传递参数为x_i(即下式的`var`)
                let _unused = cases.insert(*bid_prev, var.clone());
            }
            let _unused = phinodes.insert(
                (aid, bid),
                (code.allocations.get(aid).unwrap().deref().clone(), cases),
            );
        }

        println!("finally, these phinodes will be inserted: {:?}", phinodes);

        // the phinode indexes for promoted allocations in each block
        // phinode_indexes[(aid, bid)] = p -> bid块中为变量aid分配的phinode在第p个位置
        let mut phinode_indexes = HashMap::<(usize, BlockId), usize>::new();
        // insert phinodes
        println!("inserting phinodes...");
        for ((aid, bid), (dtype, _)) in &phinodes {
            let block = code.blocks.get_mut(bid).unwrap();
            let index = block.phinodes.len();
            let name = code.allocations.get(*aid).unwrap().name();
            block
                .phinodes
                .push(Named::new(name.cloned(), dtype.clone()));
            let _unused = phinode_indexes.insert((*aid, *bid), index);
        }

        // insert phinode arguments in BlockExit's JumpArg
        for ((aid, bid), (dtype, phinode_args)) in &phinodes {
            let index = *phinode_indexes.get(&(*aid, *bid)).unwrap();
            for (prev_bid, phinode_arg) in phinode_args {
                let block_prev = code.blocks.get_mut(prev_bid).unwrap();
                let phinode_arg = phinode_arg.lookup(dtype.clone(), &phinode_indexes);
                block_prev.exit.walk_jump_args(|jump_arg| {
                    if &jump_arg.bid == bid {
                        // 假如有3个predecessors要给phinode %bid:%index传参，要求此时这predecessor的blockexit中下一跳为bid的jumparg.args长度恰好为index
                        assert_eq!(jump_arg.args.len(), index);
                        jump_arg.args.push(phinode_arg.clone());
                    }
                });
            }
        }

        // replace values loaded from promotable locations
        code.walk(|op| {
            let (rid, dtype) = some_or!(op.get_register(), return);
            let operand_var = some_or!(replaces.get(rid), return);
            *op = operand_var.lookup(dtype.clone(), &phinode_indexes);
        });

        // replace load/store with nop instructions
        for block in code.blocks.values_mut() {
            for inst in block.instructions.iter_mut() {
                match inst.deref().deref() {
                    Instruction::Store { ptr, value } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if !inpromotable.contains(aid) {
                                *inst.deref_mut() = Instruction::Nop;
                            }
                        }
                    }
                    Instruction::Load { ptr } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if !inpromotable.contains(aid) {
                                *inst.deref_mut() = Instruction::Nop;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        true
    }
}

// inner: inner[(aid, bid)] represents the nearest(in dom tree's idom relation) block `bid_2` from `bid`
// where `joins` has value `(aid, bid_2)`(候选下含有表示变量`aid`的phinode的，离`bid`最近的block)
struct JoinTable<'s> {
    inner: HashMap<(usize, BlockId), BlockId>,
    domtree: &'s Domtree,
    joins: &'s HashMap<usize, HashSet<BlockId>>,
}

impl<'s> JoinTable<'s> {
    pub(crate) fn new(domtree: &'s Domtree, joins: &'s HashMap<usize, HashSet<BlockId>>) -> Self {
        Self {
            inner: HashMap::new(),
            domtree,
            joins,
        }
    }
    // 惰性计算self.inner, 在查询时更新
    // 寻找支配当前块 `bid` 的，且属于变量 `aid`的最近的迭代支配边界节点(join节点)
    pub(crate) fn lookup(&mut self, aid: usize, mut bid: BlockId) -> BlockId {
        let mut bids = Vec::new();
        let ret = loop {
            if let Some(ret) = self.inner.get(&(aid, bid)) {
                break *ret;
            }
            // bid 沿着domtree向上遍历时记录沿途的节点到bids中
            bids.push(bid);
            // 如果当前bid节点为`join`节点
            if self.joins.get(&aid).map_or(false, |v| v.contains(&bid)) {
                break bid;
            }
            bid = some_or!(self.domtree.idom(bid), break bid); // 到bid_init退出循环
        };
        // 将沿途节点的最近join节点记录下来
        // 如果这些节点没有最近的join block，那么使用bid_init作为默认值
        for bid in bids {
            let _unused = self.inner.insert((aid, bid), ret);
        }
        ret
    }
}

#[derive(Debug, Clone, PartialEq)]
enum OperandVar {
    Operand(Operand),
    Phi((usize, BlockId)), // 这个可以暂时不知道block中为变量aid 分配的是第几个phinode
}

impl OperandVar {
    pub(crate) fn lookup(
        &self,
        dtype: Dtype,
        phinode_indexes: &HashMap<(usize, BlockId), usize>,
    ) -> Operand {
        match self {
            OperandVar::Operand(op) => op.clone(),
            OperandVar::Phi((aid, bid)) => {
                let index = *phinode_indexes.get(&(*aid, *bid)).unwrap();
                Operand::register(RegisterId::arg(*bid, index), dtype)
            }
        }
    }
}

use std::fmt;

impl fmt::Display for OperandVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // 如果是已有的操作数，直接调用其原本的 Display 实现
            OperandVar::Operand(op) => write!(f, "{}", op),

            // 如果是待定的 Phi，显示为类似 PHI(%l0 @ b1) 的形式
            // %l{aid} 符合 RegisterId::Local 的表示习惯
            OperandVar::Phi((aid, bid)) => write!(f, "PHI(%{}:p?) for aid#{}", bid, aid),
        }
    }
}
