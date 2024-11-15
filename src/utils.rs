use crate::avl_tree::AvlTree;
use std::collections::{HashMap, VecDeque};
use std::fmt::{Debug, Display};

use std::hash::Hash;

pub fn print_tree<K: Debug + Display + Hash + PartialOrd + Eq + Clone, V: Clone>(
    tree: &mut AvlTree<K, V>,
    place_holder: K,
) {
    // Works best if keys are between 10 and 99 because of formatting.
    let mut levels: HashMap<i32, HashMap<i32, K>> = HashMap::new();
    let mut queue: VecDeque<(K, i32, i32)> = VecDeque::new();
    if tree.root.is_none() {
        println!("Empty tree");
        return;
    }
    queue.push_back((tree.root.clone().unwrap(), 0, 0)); // root is at depth 0, position 0.

    while let Some((node_key, depth, pos)) = queue.pop_front() {
        let node = tree.get_node(&node_key).expect("Node should exist.");

        if !levels.contains_key(&depth) {
            levels.insert(depth, HashMap::new());
        }

        levels.get_mut(&depth).unwrap().insert(pos, node_key);
        // debug!("Node {} at depth {} and position {}", node_key, depth, pos); use this, when there is a loop in the tree -> infinite depth

        if let Some(left) = node.left_child.clone() {
            queue.push_back((left, depth + 1, pos * 2));
        }
        if let Some(right) = node.right_child.clone() {
            queue.push_back((right, depth + 1, pos * 2 + 1));
        }
    }

    let max_depth = levels.keys().max().unwrap().clone();
    let mut spacing = " ".to_string();
    let mut half_spacing = "".to_string();
    // Now we print the tree.
    let mut layers_string = Vec::new();
    for depth in 0..max_depth + 1 {
        let depth = max_depth - depth;
        let level = levels.get(&depth).unwrap();

        let mut node_keys: Vec<String> = Vec::new();
        let mut balance_factors: Vec<String> = Vec::new();
        let mut parents: Vec<String> = Vec::new();
        let mut nexts: Vec<String> = Vec::new();
        let mut prevs: Vec<String> = Vec::new();

        for pos in 0..=(i32::pow(2, depth as u32)) - 1 {
            if let Some(node_key) = level.get(&pos) {
                let node = tree.get_node(node_key).expect("Node should exist.");
                node_keys.push(format!("{}", node.key.to_string()));
                let balance_factor = match node.balance_factor {
                    2 => "+2",
                    1 => "+1",
                    0 => "+0",
                    -1 => "-1",
                    -2 => "-2",
                    _ => "??",
                };
                balance_factors.push(format!("{}", balance_factor));
                parents.push(format!(
                    "{}",
                    node.parent
                        .clone()
                        .unwrap_or(place_holder.clone())
                        .to_string()
                ));
                nexts.push(format!(
                    "{}",
                    node.next
                        .clone()
                        .unwrap_or(place_holder.clone())
                        .to_string()
                ));
                prevs.push(format!(
                    "{}",
                    node.prev
                        .clone()
                        .unwrap_or(place_holder.clone())
                        .to_string()
                ));
            } else {
                node_keys.push("--".to_string());
                parents.push("--".to_string());
                balance_factors.push("--".to_string());
                nexts.push("--".to_string());
                prevs.push("--".to_string());
            }
        }
        let spacing_front = match depth {
            _ if depth == max_depth => "".to_string(),
            _ => half_spacing.clone(),
        };

        layers_string.push(spacing_front.clone() + nexts.join(spacing.clone().as_str()).as_str());
        layers_string.push(spacing_front.clone() + prevs.join(spacing.clone().as_str()).as_str());
        layers_string.push(spacing_front.clone() + parents.join(spacing.clone().as_str()).as_str());
        layers_string
            .push(spacing_front.clone() + balance_factors.join(spacing.clone().as_str()).as_str());
        layers_string
            .push(spacing_front.clone() + node_keys.join(spacing.clone().as_str()).as_str());
        layers_string.push("".to_string());
        half_spacing = spacing.clone();
        spacing = spacing.clone() + spacing.clone().as_str() + "  ";
    }

    println!("Tree:");
    println!("Vertical node arangement: Node, Value Balance factor, Parent, prev, next");
    let _print_string = "\n".to_string()
        + layers_string
            .iter()
            .map(|s| s.as_str())
            .rev()
            .collect::<Vec<_>>()
            .join("\n")
            .as_str();
    println!("{}", _print_string);
    println!("depth: {}", max_depth);
}
