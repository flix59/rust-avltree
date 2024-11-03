use std::fmt::{Debug, Display};
use std::hash::Hash;

use crate::avl_tree::AvlTree;

// Check if tree is correctly balanced
pub fn check_health<K: Hash + PartialOrd + Eq + Clone + Debug + Display, V: Clone>(
    tree: &AvlTree<K, V>,
) {
    let root = tree.root.clone();
    check_health_recursive(tree, root.as_ref(), true);
}

fn check_health_recursive<K: Clone + Hash + PartialOrd + Eq + Debug + Display, V: Clone>(
    tree: &AvlTree<K, V>,
    key: Option<&K>,
    panic: bool,
) -> (i32, Option<K>) {
    if key.is_none() {
        return (0, None);
    }
    let key = key.unwrap();
    let node = tree
        .get_node(&key)
        .cloned()
        .expect("Node of subtree should exist.");
    let left = node.left_child.as_ref();
    let right = node.right_child.as_ref();
    let (height_left, parent_left) = check_health_recursive(tree, left, panic);
    let (height_right, parent_right) = check_health_recursive(tree, right, panic);
    assert_eq!(
        parent_left,
        node.left_child.as_ref().map(|_| node.key.clone()),
        "Parent of left child of node {} is not correct.",
        node.key
    );
    assert_eq!(
        parent_right,
        node.right_child.as_ref().map(|_| node.key.clone()),
        "Parent of right child of node {} is not correct.",
        node.key
    );
    let balance_factor = height_right - height_left;
    if balance_factor != node.balance_factor {
        panic!(
            "Balance factor of node {} is not correct. Should be {} but is {}",
            node.key, balance_factor, node.balance_factor
        );
    }
    if balance_factor.abs() > 1 {
        panic!("Balance factor is too high for node {}.", node.key);
    }
    (height_left.max(height_right) + 1, node.parent.clone())
}
