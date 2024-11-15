#[cfg(test)]
mod avltree_delete {
    use std::collections::HashMap;

    use crate::{
        tests::{
            avl_tree_health::check_health,
            utils::{assert_tree_contains, test_range, to_key_values},
        },
        AvlTree,
    };

    #[test]
    fn remove_last_inserted() {
        // Tree after inserting 35 without balance:
        //       74
        //     5    48
        //      27    90
        //       35
        // Tree after balance of 5:
        //       74
        //     27    48
        //   5   35    90
        // Tree after insert:
        //       74
        //     27    48
        //   5   35    90
        //  1 6       82  99
        // Tree after deletion of last inserted node:
        //       74
        //     27    48
        //   5   35    90
        //  1         82 99
        let vector = vec![74, 5, 48, 27, 90, 35, 82, 99, 1, 6];
        let to_delete = vec![6];
        test_range(vector, to_delete);
    }

    #[test]
    fn replace_2_layers_above() {
        // rewiring of node in the middle could go wrong because it has to be in memory.
        // Tree after inserting:
        //       18
        //  15       21
        // 12 16    20
        // Tree after deleting 18
        //       20
        //  15       21
        // 12 16
        let vector: Vec<i32> = vec![18, 15, 21, 12, 16, 20];
        let to_delete = vec![18];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_deleting_of_leaf_node_has_no_effect() {
        // rewiring of node in the middle could go wrong because it has no children
        // Tree after inserting:
        //       18
        //  15       21
        // 12 16    20
        // Tree after deleting 16
        //       18
        //  15       21
        // 12          20
        let vector: Vec<i32> = vec![18, 15, 21, 12, 16, 20];
        let to_delete = vec![16];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_replace_with_left_child_same_direction() {
        // was wrong wired in the leftover child of right child in this case the 76 had the wrong parent
        // Tree after inserting:
        //       74
        //  73       75
        // 71
        // Tree after deleting 74
        //       73
        //  71       75
        let vector = vec![74, 73, 75, 71];
        let to_delete = vec![74];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_replace_with_right_child_same_direction() {
        // was wrong wired in the leftover child of right child in this case the 76 had the wrong parent
        // Tree after inserting:
        //       74
        //  73       75
        //         76
        // Tree after deleting 74
        //       75
        //  73       76

        let vector = vec![74, 73, 75, 76];
        let to_delete = vec![74];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_replace_with_right_childdifferent_direction() {
        // was wrong wired in the leftover child of right child in this case the 76 had the wrong parent
        // Tree after inserting:
        //       74
        //  73       76
        //         75
        // Tree after deleting 74
        //       75
        //  73       76
        let vector = vec![74, 73, 76, 75];
        let to_delete = vec![74];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_delete_empty_tree() {
        let vector = vec![];
        let to_delete = vec![];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_replace_has_children() {
        // Tree after inserting:
        //         48
        //     27       81
        // 13   40    72
        //     35
        // Tree after deleting 48
        //         40
        //     27       81
        // 13   35    72
        // Orphant 35 has to find a new place at the position of 40
        let vector = vec![48, 27, 81, 13, 40, 72, 35];
        let to_delete = vec![48];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_replacement_node_still_in_range() {
        // Resulting tree:
        //             26
        //      18           34
        // 14      20      30   38
        //           22  28
        // After deleting 26:
        //            28
        //     18           34
        // 14     20     30    38
        //          22  _
        // This test checks whether the replacement node is still in the range after the deletion (the 28)

        let mut vec = vec![26, 18, 34, 14, 20, 30, 38, 22, 28];
        let mut tree = AvlTree::new();
        for i in vec.clone() {
            tree.insert(i, i);
            check_health(&tree);
        }
        tree.remove(&26);
        check_health(&tree);
        vec.remove(0);
        vec.sort();
        assert_tree_contains(&tree, to_key_values(&vec));
    }

    #[test]
    fn test_delete_root() {
        // Resulting tree:
        // 1
        //
        // After deleting 1:
        // _
        let mut tree: AvlTree<i32, i32> = AvlTree::new();
        tree.insert(1, 1);
        check_health(&tree);
        tree.remove(&1);
        check_health(&tree);
        assert_tree_contains(&tree, to_key_values(&vec![]));
    }

    #[test]
    fn test_get_before_and_after_delete() {
        let mut tree = AvlTree::new();
        tree.insert(1, 400);
        check_health(&tree);
        let output = tree.get(&1);
        assert_eq!(output, Some(&400), "Something is still present in the tree");
        let remove_output = tree.remove(&1);
        check_health(&tree);
        let deleted_output = tree.get(&1);
        assert_eq!(
            remove_output,
            Some(400),
            "One was deleted from tree and returned"
        );
        assert_eq!(deleted_output, None, "One was deleted from tree");
        let double_removed = tree.remove(&1);
        check_health(&tree);
        assert_eq!(
            double_removed, None,
            "remove did not return None after deleting non existent element"
        );
    }

    #[test]
    fn three_insert_one_delete_3_insert() {
        // This test inserts and deletes nodes in alternating order
        let mut tree = AvlTree::new();
        let mut insert = vec![];
        let mut remove = vec![];
        let mut should_be_in_tree = HashMap::new();
        for i in 0..4 {
            for mut j in 0..3 {
                j = 3 - j;
                let key = i * 3 + j;
                let value = key;
                print!("insert: --------------------- {}, {}, {} ", value, i, j);
                tree.insert(key, value);
                should_be_in_tree.insert(key, value);
                insert.push(value);
                check_health(&tree);
            }
            let key = i * 2 + 1;
            tree.remove(&key);
            should_be_in_tree.remove(&key);
            remove.push(key);
            check_health(&tree);
        }
        let mut should_be_in_tree: Vec<(i32, i32)> = should_be_in_tree.into_iter().collect();
        should_be_in_tree.sort();
        println!("insert: {:?}", insert);
        println!("remove: {:?}", remove);
        assert_tree_contains(&tree, should_be_in_tree);
    }

    #[test]
    fn test_delete_gives_correct_return_value() {
        let mut tree = AvlTree::new();
        tree.insert(1, 1);
        tree.insert(0, 1);
        tree.insert(1, 100);
        tree.insert(11, 1);
        let removed_output = tree.remove(&1);
        assert_eq!(removed_output, Some(100));
        let remove_res = tree.remove(&1);
        assert_eq!(remove_res, None);
        let remove_res = tree.remove(&0);
        assert_eq!(remove_res, Some(1));
        let remove_res = tree.remove(&0);
        assert_eq!(remove_res, None);
        tree.insert(1, 1000);
        let remove_res = tree.remove(&1);
        assert_eq!(remove_res, Some(1000));
    }

    #[test]
    fn test_delete_not_existing() {
        let mut tree = AvlTree::new();
        let remove_res = tree.remove(&1);
        assert_eq!(remove_res, None);
        tree.insert(1, 1);
        tree.insert(-23213211, 29302381);
        let remove_res = tree.remove(&29302381);
        assert_eq!(remove_res, None);
        let remove_res = tree.remove(&-23213210);
        assert_eq!(remove_res, None);
        let remove_res = tree.remove(&-23213211);
        assert_eq!(remove_res, Some(29302381));
    }

    #[test]
    fn test_shorten_was_calculated_wrong_because_balance_factor_of_delete_was_wrong() {
        // Resulting tree:
        //       5
        //   3       7
        // 1   4   8   2
        // After deleting 5:
        //      4
        //    3   7
        //  1    8  2
        let vector: Vec<i32> = vec![5, 3, 7, 1, 4, 8, 2];
        let to_delete = vec![5];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_delete_root_and_check_if_replace_parent_is_given_correct() {
        // If 2 has the wrong bf afterwards the parent was given incorrect
        // Resulting tree:
        //      6|-1
        //   2|1  7|0
        //     3|0
        // After deletion
        //     3|0
        //   2|0  7|0
        let vec = vec![6, 2, 7, 3];
        let to_delete = vec![6];
        test_range(vec, to_delete);
    }

    #[test]
    fn test_replace_parent_with_rebalance_other_direction() {
        // Resulting tree:
        //        16
        //    12      18
        //  11  13  17
        // 10
        // After deleting 12:
        //       16
        //   11      18
        // 10  13    17
        let vec = vec![16, 12, 18, 11, 13, 17, 10];
        let to_delete = vec![12];
        test_range(vec, to_delete);
    }

    #[test]
    fn test_replace_parent_with_rebalance() {
        // Resulting tree:
        //        16
        //     12      18
        //  10   13   17
        //    11
        // After deleting 12:
        //       16
        //    11    18
        //  10  13   17
        let vec = vec![16, 12, 18, 10, 13, 17, 11];
        let to_delete = vec![12];
        test_range(vec, to_delete);
    }

    #[test]
    fn test_replace_parent() {
        // Resulting tree:
        //        6
        //     2      7
        //  1   3
        // After deleting 6:
        //       6
        //    3    7
        //  1
        let vec = vec![6, 2, 7, 1, 3];
        let to_delete = vec![6];
        test_range(vec, to_delete);
    }

    #[test]
    fn delete_non_existent_and_dont_panic() {
        let vec = vec![6, 2];
        let to_delete = vec![8];
        test_range(vec, to_delete);
    }

    #[test]
    fn test_deletion_with_2_parents_above_but_only_one_balance() {
        // Resulting tree:
        //            4
        //     2              8
        //  1     3        6     10
        //               5  7   9  11
        // Resulting tree after deleting 0, 1, 2:
        //            8
        //     4           10
        //  3    6      9     11
        //     5   7

        //  Resulting tree after deleting 3
        //            8
        //       6         10
        //    4     7   9     11
        //
        let vector: Vec<i32> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let to_delete = vec![0, 1, 2, 3];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_reduce_balance_factor_after_delete() {
        // Resulting tree:
        //            25
        //     20              30
        //  10     23        26     33
        //                        31
        // Resulting tree after deleting 25:
        //            26
        //     20              30
        //  10     23              33
        //                       31
        // Since balance factor of 30 is 2 the tree needs to be rebalanced
        // Resulting tree after rebalancing:
        //            26
        //     20              31
        //  10     23        30     33
        // The right subtree of 26 its reduced height through the balancing
        // -> The balance factor of 26 also needs to be reduced
        let vector = vec![25, 20, 30, 10, 23, 26, 33, 31];
        let to_delete = vec![25];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_double_balance_after_delete() {
        // Resulting tree:
        // This is the smallest possible tree for a double balance to happen
        //                            35
        //            25                         40
        //     20              30           38        45
        //  10             26     33    36     39   43     46
        //                       31       37          44     47
        //                                                     48
        // Resulting tree after deleting 10 and update up to 25:
        //                            35
        //            30                        40
        //     25           33             38           45
        //  20    26      31             36   39     43   46
        //                                 37          44    47
        //                                                     48
        // Since the balance factor of 26 was also not 0 the parents of 25(now 30) need to be updated further.
        // 35 has a bf of 2 after the update and the tree needs to be rebalanced:
        // Resulting tree after rebalancing:
        //                            40
        //                35                     45
        //          30          38            43     46
        //     25       33    36   39           44     47
        //  20    26     31     37                       48
        let vector = vec![
            35, 25, 40, 20, 30, 38, 45, 10, 26, 33, 36, 39, 43, 46, 31, 37, 44, 47, 48,
        ];
        let to_delete = vec![25];
        test_range(vector, to_delete);
    }

    #[test]
    fn delete_is_bf_0_but_not_shorten() {
        let vector = vec![44, 39, 49, 36, 42, 46, 51, 34, 40, 43, 47, 52, 41];
        let to_delete = vec![36];
        test_range(vector, to_delete);
    }

    #[test]
    fn deletion_with_replace_direct_below() {
        // Resulting tree:
        //     15
        //  14    17
        //       16
        // After deleting 17:
        //     15
        //  14    16
        let vector: Vec<i32> = vec![15, 14, 17, 16];
        let to_delete = vec![17];
        test_range(vector, to_delete);
    }

    #[test]
    fn delete_and_balance_at_root() {
        // Resulting tree:
        //       7
        //    5     15
        //  3  6  11  17
        // 4       14 16 18
        //                 20
        // After deleting 3:
        //        15
        //     7       17
        //  5    11   16 18
        // 4  6   14      20
        let vector: Vec<i32> = vec![7, 5, 15, 3, 6, 11, 17, 4, 16, 18, 20, 14];
        let to_delete = vec![3];
        test_range(vector, to_delete);
    }

    #[test]
    fn test_replace_with_left_child_different_direction() {
        // was wrong wired in the leftover child of right child in this case the 76 had the wrong parent
        // Tree after inserting:
        //       74
        //  72       75
        //    73
        // Tree after deleting 74
        //       73
        //  72       75
        let vector = vec![74, 72, 75, 73];
        let to_delete = vec![74];
        test_range(vector, to_delete);
    }
}
