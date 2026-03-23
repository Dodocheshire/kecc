use crate::ir::*;
use crate::opt::opt_utils::Domtree;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

pub(crate) struct OptVisualizer;

impl OptVisualizer {
    /// 可视化标准的控制流图 (CFG)
    pub(crate) fn cfg_to_dot(cfg: &HashMap<BlockId, Vec<JumpArg>>, title: &str) -> String {
        let mut out = String::new();
        writeln!(out, "digraph CFG_{} {{", title).unwrap();
        writeln!(out, "  label=\"Control Flow Graph: {}\";", title).unwrap();
        writeln!(out, "  node [shape=circle, style=filled, color=lightblue];").unwrap();

        for (from, jumps) in cfg {
            for jump in jumps {
                writeln!(out, "  {} -> {};", from, jump.bid).unwrap();
            }
        }

        writeln!(out, "}}").unwrap();
        out
    }

    /// 可视化支配树 (Dominator Tree) 及其支配边界 (Dominance Frontiers)
    pub(crate) fn domtree_to_dot(domtree: &Domtree, title: &str) -> String {
        let mut out = String::new();
        writeln!(out, "digraph DomTree_{} {{", title).unwrap();
        writeln!(out, "  label=\"Dominator Tree & Frontiers: {}\";", title).unwrap();

        // 1. 绘制支配树的实线 (IDom 关系)
        writeln!(
            out,
            "  node [shape=ellipse, style=filled, color=lightgreen];"
        )
        .unwrap();
        // 我们利用 domtree 的 walk 方法或者遍历 idoms
        domtree.walk(|parent_opt, child| {
            if let Some(parent) = parent_opt {
                writeln!(
                    out,
                    "  {} -> {} [lhead=tree, label=\"idom\"];",
                    parent, child
                )
                .unwrap();
            }
        });

        // 2. 绘制支配边界 (Frontiers) 的虚线
        writeln!(out, "  edge [style=dashed, color=red, constraint=false];").unwrap();
        // 需要在 Domtree 定义中把 frontiers 改为 pub(crate)
        for (node, frontier_list) in &domtree.frontiers {
            for f_node in frontier_list {
                writeln!(out, "  {} -> {} [label=\"DF\"];", node, f_node).unwrap();
            }
        }

        writeln!(out, "}}").unwrap();
        out
    }
}
