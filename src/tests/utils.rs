use std::i32;
use std::ops::RangeBounds;

use crate::tests::avl_tree_health::check_health;
use crate::AvlTree;
pub(crate) fn test_range(mut vector: Vec<i32>, to_delete: Vec<i32>) {
    println!("to_delete: {:?}", to_delete);
    println!("vector: {:?}", vector);
    let mut tree = AvlTree::new();
    // helper.instantiate_default(false);
    for i in vector.iter() {
        println!("inserting {:?}", i);
        tree.insert(*i, *i);
        check_health(&tree);
    }

    vector.sort();
    let mut expected_values: Vec<(i32, i32)> = to_key_values(&vector);
    assert_tree_contains(&tree, expected_values.clone());

    for i in to_delete.iter().rev() {
        tree.remove(i);
        check_health(&tree);
    }

    expected_values.retain(|(k, _)| !to_delete.contains(&k));
    assert_tree_contains(&tree, expected_values);
}
pub(crate) fn to_key_values(vector: &Vec<i32>) -> Vec<(i32, i32)> {
    vector
        .iter()
        .zip(vector.iter())
        .map(|(a, b)| (*a, *b))
        .collect()
}
pub(crate) fn assert_tree_contains(tree: &AvlTree<i32, i32>, expected_values: Vec<(i32, i32)>) {
    assert_tree_range_contains(tree, i32::MIN..i32::MAX, expected_values);
}
pub(crate) fn assert_tree_range_contains<R: RangeBounds<i32>>(
    tree: &AvlTree<i32, i32>,
    range: R,
    expected_values: Vec<(i32, i32)>,
) {
    let all_elements_in_tree: Vec<(i32, i32)> = tree.range(range).collect();
    assert_eq!(all_elements_in_tree, expected_values);
}
pub(crate) fn assert_tree_range_back_contains<R: RangeBounds<i32>>(
    tree: &AvlTree<i32, i32>,
    range: R,
    expected_values: Vec<(i32, i32)>,
) {
    let all_elements_in_tree: Vec<(i32, i32)> = tree.range_back(range).collect();
    assert_eq!(all_elements_in_tree, expected_values);
}
