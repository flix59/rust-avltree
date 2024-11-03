#[cfg(test)]
mod get_and_get_mut {

    use crate::{tests::avl_tree_health::check_health, AvlTree};
    fn update_value(tree: &mut AvlTree<i32, i32>, key: i32, new_value: i32) -> Option<i32> {
        let test = tree.get_mut(&key)?;
        let old_value = test.clone();
        *test = new_value;
        Some(old_value)
    }

    fn tree_with_initial_data(vector: Vec<i32>) -> AvlTree<i32, i32> {
        let mut tree = AvlTree::new();
        for i in vector.iter() {
            tree.insert(*i, *i);
            check_health(&tree);
        }
        tree
    }

    #[test]
    fn test_get_mut() {
        let mut tree = tree_with_initial_data((10..30).collect());

        let output = update_value(&mut tree, 9, 1232132);
        assert_eq!(output, None);
        tree.insert(1, 10002132);
        let output = update_value(&mut tree, 1, -1);
        assert_eq!(output, Some(10002132));
        tree.insert(-2132123, 2132);
        let output = update_value(&mut tree, 1, -2);
        assert_eq!(output, Some(-1));
        let output = update_value(&mut tree, 9, 1232132);
        assert_eq!(output, None);
        tree.insert(9, -3);
        let output = update_value(&mut tree, 9, 1232132);
        assert_eq!(output, Some(-3));
    }

    #[test]
    fn test_get() {
        let mut tree = tree_with_initial_data((10..30).collect());

        let output = tree.get(&9);
        assert_eq!(output, None);
        tree.insert(1, 10002132);
        let output = tree.get(&1);
        assert_eq!(output, Some(&10002132));
        tree.insert(-2132123, 2132);
        let output = tree.get(&1);
        assert_eq!(output, Some(&10002132));
        let output = tree.get(&2132123);
        assert_eq!(output, None);
        let output = tree.get(&-2132124);
        assert_eq!(output, None);
        let output = tree.get(&-2132123);
        assert_eq!(output, Some(&2132));
    }
}
