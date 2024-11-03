#[cfg(test)]
mod avltree_range {

    use crate::{
        tests::{
            avl_tree_health::check_health,
            utils::{
                assert_tree_contains, assert_tree_range_back_contains, assert_tree_range_contains,
                key_value,
            },
        },
        AvlTree, IterMutControl,
    };
    use std::{
        i32,
        ops::Bound::{Excluded, Included},
    };
    fn tree_with_initial_data(vector: Vec<i32>) -> AvlTree<i32, i32> {
        let mut tree = AvlTree::new();
        for i in vector.iter() {
            tree.insert(*i, *i);
            check_health(&tree);
        }
        tree
    }

    #[test]
    fn range_out_of_bounds() {
        let tree = tree_with_initial_data((1..5).collect());
        assert_tree_range_contains(&tree, 6..10, vec![]);
    }

    #[test]
    fn start_included_end_excluded() {
        let mut tree = tree_with_initial_data((1..5).collect());
        assert_tree_range_contains(&tree, 1..5, vec![(1, 1), (2, 2), (3, 3), (4, 4)]);
    }

    #[test]
    fn test_range_is_sorted() {
        let tree = tree_with_initial_data(vec![
            13, 24, 43, 23, 12, 23, 13, 42, 53, 54, 21, 11, 12, 14, 16,
        ]);
        assert_tree_contains(
            &tree,
            vec![
                (11, 11),
                (12, 12),
                (13, 13),
                (14, 14),
                (16, 16),
                (21, 21),
                (23, 23),
                (24, 24),
                (42, 42),
                (43, 43),
                (53, 53),
                (54, 54),
            ],
        );
    }

    #[test]
    fn test_range_back_is_sorted() {
        let tree = tree_with_initial_data(vec![
            13, 24, 43, 23, 12, 23, 13, 42, 53, 54, 21, 11, 12, 14, 16,
        ]);
        assert_tree_range_back_contains(
            &tree,
            (i32::MIN..i32::MAX),
            vec![
                (54, 54),
                (53, 53),
                (43, 43),
                (42, 42),
                (24, 24),
                (23, 23),
                (21, 21),
                (16, 16),
                (14, 14),
                (13, 13),
                (12, 12),
                (11, 11),
            ],
        );
    }

    #[test]
    fn test_range_back_only_contains_range() {
        let tree = tree_with_initial_data((10..30).collect());

        assert_tree_range_back_contains(
            &tree,
            15..25,
            vec![
                (24, 24),
                (23, 23),
                (22, 22),
                (21, 21),
                (20, 20),
                (19, 19),
                (18, 18),
                (17, 17),
                (16, 16),
                (15, 15),
            ],
        );

        let output: Vec<(i32, i32)> = tree
            .range_back((Included(15), Included(25)))
            .map(key_value)
            .collect();
        assert_eq!(
            output,
            vec![
                (25, 25),
                (24, 24),
                (23, 23),
                (22, 22),
                (21, 21),
                (20, 20),
                (19, 19),
                (18, 18),
                (17, 17),
                (16, 16),
                (15, 15)
            ]
        );

        let output: Vec<(i32, i32)> = tree
            .range_back((Excluded(15), Excluded(25)))
            .map(key_value)
            .collect();
        assert_eq!(
            output,
            vec![
                (24, 24),
                (23, 23),
                (22, 22),
                (21, 21),
                (20, 20),
                (19, 19),
                (18, 18),
                (17, 17),
                (16, 16)
            ]
        );
    }

    #[test]
    fn test_range_only_contains_range() {
        let mut tree = tree_with_initial_data((10..30).collect());

        let output: Vec<(i32, i32)> = tree.range(15..25).map(key_value).collect();
        assert_eq!(
            output,
            vec![
                (15, 15),
                (16, 16),
                (17, 17),
                (18, 18),
                (19, 19),
                (20, 20),
                (21, 21),
                (22, 22),
                (23, 23),
                (24, 24)
            ]
        );

        let output: Vec<(i32, i32)> = tree
            .range((Included(15), Included(25)))
            .map(key_value)
            .collect();
        assert_eq!(
            output,
            vec![
                (15, 15),
                (16, 16),
                (17, 17),
                (18, 18),
                (19, 19),
                (20, 20),
                (21, 21),
                (22, 22),
                (23, 23),
                (24, 24),
                (25, 25)
            ]
        );

        let output: Vec<(i32, i32)> = tree
            .range((Excluded(15), Excluded(25)))
            .map(key_value)
            .collect();
        assert_eq!(
            output,
            vec![
                (16, 16),
                (17, 17),
                (18, 18),
                (19, 19),
                (20, 20),
                (21, 21),
                (22, 22),
                (23, 23),
                (24, 24)
            ]
        );
    }

    #[test]
    fn test_range_lower_bound_not_in_tree() {
        let mut tree = tree_with_initial_data(vec![10, 12, 14, 16]);
        let output: Vec<(i32, i32)> = tree
            .range((Included(11), Included(15)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(12, 12), (14, 14)]);
        let output: Vec<(i32, i32)> = tree
            .range((Excluded(11), Excluded(16)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(12, 12), (14, 14)]);
        let output: Vec<(i32, i32)> = tree
            .range((Included(11), Included(16)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(12, 12), (14, 14), (16, 16)]);
    }

    #[test]
    fn test_range_only_contains_range_first_included() {
        let mut tree = tree_with_initial_data((10..30).collect());

        let output: Vec<(i32, i32)> = tree
            .range((Included(9), Included(10)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(10, 10)]);

        let output: Vec<(i32, i32)> = tree
            .range((Included(9), Included(11)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(10, 10), (11, 11)]);

        let output: Vec<(i32, i32)> = tree
            .range((Included(10), Included(11)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(10, 10), (11, 11)]);

        let output: Vec<(i32, i32)> = tree
            .range((Included(10), Included(12)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(10, 10), (11, 11), (12, 12)]);
    }

    #[test]
    fn test_range_only_contains_range_first_excluded() {
        let mut tree = tree_with_initial_data((10..30).collect());

        let output: Vec<(i32, i32)> = tree
            .range((Excluded(9), Excluded(10)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![]);

        let output: Vec<(i32, i32)> = tree
            .range((Excluded(9), Excluded(11)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(10, 10)]);

        let output: Vec<(i32, i32)> = tree
            .range((Excluded(10), Excluded(11)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![]);

        let output: Vec<(i32, i32)> = tree
            .range((Excluded(10), Excluded(12)))
            .map(key_value)
            .collect();
        assert_eq!(output, vec![(11, 11)]);
    }

    // #[test]
    // fn test_range_only_contains_range_last_included() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_both_included(29, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_both_included");
    //     assert_eq!(output, vec![vec![(29, 29)]]);

    //     let receipt = tree
    //         .get_range_both_included(28, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_both_included");
    //     assert_eq!(output, vec![vec![(28, 28), (29, 29)]]);

    //     let receipt = tree
    //         .get_range_both_included(28, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_both_included");
    //     assert_eq!(output, vec![vec![(28, 28), (29, 29)]]);

    //     let receipt = tree
    //         .get_range_both_included(27, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_both_included");
    //     assert_eq!(output, vec![vec![(27, 27), (28, 28), (29, 29)]]);
    // }
    // #[test]
    // fn test_range_only_contains_range_last_excluded() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_both_excluded(29, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_both_excluded(28, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_both_excluded(28, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_both_excluded");
    //     assert_eq!(output, vec![vec![(29, 29)]]);

    //     let receipt = tree
    //         .get_range_both_excluded(27, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_both_excluded");
    //     assert_eq!(output, vec![vec![(28, 28)]]);
    // }

    // #[test]
    // fn test_range_mut_only_contains_range_mut_first_included() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_mut_both_included(9, 10)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_included");
    //     assert_eq!(output, vec![vec![(10, 10, None)]]);

    //     let receipt = tree
    //         .get_range_mut_both_included(9, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_included");
    //     assert_eq!(output, vec![vec![(10, 10, Some(11)), (11, 11, None)]]);

    //     let receipt = tree
    //         .get_range_mut_both_included(10, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_included");
    //     assert_eq!(output, vec![vec![(10, 10, Some(11)), (11, 11, None)]]);

    //     let receipt = tree
    //         .get_range_mut_both_included(10, 12)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_included");
    //     assert_eq!(
    //         output,
    //         vec![vec![(10, 10, Some(11)), (11, 11, Some(12)), (12, 12, None)]]
    //     );
    // }

    // #[test]
    // fn test_range_mut_only_contains_range_mut_first_excluded() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_mut_both_excluded(9, 10)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_mut_both_excluded(9, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_excluded");
    //     assert_eq!(output, vec![vec![(10, 10, None)]]);

    //     let receipt = tree
    //         .get_range_mut_both_excluded(10, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_mut_both_excluded(10, 12)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_excluded");
    //     assert_eq!(output, vec![vec![(11, 11, None)]]);
    // }

    // #[test]
    // fn test_range_mut_only_contains_range_mut_last_included() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_mut_both_included(29, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_included");
    //     assert_eq!(output, vec![vec![(29, 29, None)]]);

    //     let receipt = tree
    //         .get_range_mut_both_included(28, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_included");
    //     assert_eq!(output, vec![vec![(28, 28, Some(29)), (29, 29, None)]]);

    //     let receipt = tree
    //         .get_range_mut_both_included(28, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_included");
    //     assert_eq!(output, vec![vec![(28, 28, Some(29)), (29, 29, None)]]);

    //     let receipt = tree
    //         .get_range_mut_both_included(27, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_included");
    //     assert_eq!(
    //         output,
    //         vec![vec![(27, 27, Some(28)), (28, 28, Some(29)), (29, 29, None)]]
    //     );
    // }

    // #[test]
    // fn test_range_mut_only_contains_range_last_excluded() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_mut_both_excluded(29, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_mut_both_excluded(28, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_mut_both_excluded(28, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_excluded");
    //     assert_eq!(output, vec![vec![(29, 29, None)]]);

    //     let receipt = tree
    //         .get_range_mut_both_excluded(27, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_mut_both_excluded");
    //     assert_eq!(output, vec![vec![(28, 28, None)]]);
    // }

    // // TODO add same tests for range_back

    // #[test]
    // fn test_range_back_only_contains_range_first_included() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_back_both_included(9, 10)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_included");
    //     assert_eq!(output, vec![vec![(10, 10)]]);

    //     let receipt = tree
    //         .get_range_back_both_included(9, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_included");
    //     assert_eq!(output, vec![vec![(11, 11), (10, 10)]]);

    //     let receipt = tree
    //         .get_range_back_both_included(10, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_included");
    //     assert_eq!(output, vec![vec![(11, 11), (10, 10)]]);

    //     let receipt = tree
    //         .get_range_back_both_included(10, 12)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_included");
    //     assert_eq!(output, vec![vec![(12, 12), (11, 11), (10, 10)]]);
    // }

    // #[test]
    // fn test_range_back_only_contains_range_first_excluded() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_back_both_excluded(9, 10)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_back_both_excluded(9, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_excluded");
    //     assert_eq!(output, vec![vec![(10, 10)]]);

    //     let receipt = tree
    //         .get_range_back_both_excluded(10, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_back_both_excluded(10, 12)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_excluded");
    //     assert_eq!(output, vec![vec![(11, 11)]]);
    // }

    // #[test]
    // fn test_range_back_only_contains_range_last_included() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_back_both_included(29, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_included");
    //     assert_eq!(output, vec![vec![(29, 29)]]);

    //     let receipt = tree
    //         .get_range_back_both_included(28, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_included");
    //     assert_eq!(output, vec![vec![(29, 29), (28, 28)]]);

    //     let receipt = tree
    //         .get_range_back_both_included(28, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_included");
    //     assert_eq!(output, vec![vec![(29, 29), (28, 28)]]);

    //     let receipt = tree
    //         .get_range_back_both_included(27, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_included");
    //     assert_eq!(output, vec![vec![(29, 29), (28, 28), (27, 27)]]);
    // }

    // #[test]
    // fn test_range_back_only_contains_range_last_excluded() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_back_both_excluded(29, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_back_both_excluded(28, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_back_both_excluded(28, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_excluded");
    //     assert_eq!(output, vec![vec![(29, 29)]]);

    //     let receipt = tree
    //         .get_range_back_both_excluded(27, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32)>> = receipt.outputs("get_range_back_both_excluded");
    //     assert_eq!(output, vec![vec![(28, 28)]]);
    // }
    // #[test]
    // fn test_range_back_mut_only_contains_range_first_included() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_back_mut_both_included(9, 10)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_included");
    //     assert_eq!(output, vec![vec![(10, 10, None)]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_included(9, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_included");
    //     assert_eq!(output, vec![vec![(11, 11, Some(10)), (10, 10, None)]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_included(10, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_included");
    //     assert_eq!(output, vec![vec![(11, 11, Some(10)), (10, 10, None)]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_included(10, 12)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_included");
    //     assert_eq!(
    //         output,
    //         vec![vec![(12, 12, Some(11)), (11, 11, Some(10)), (10, 10, None)]]
    //     );
    // }

    // #[test]
    // fn test_range_back_mut_only_contains_range_first_excluded() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_back_mut_both_excluded(9, 10)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_excluded(9, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_excluded");
    //     assert_eq!(output, vec![vec![(10, 10, None)]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_excluded(10, 11)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_excluded(10, 12)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_excluded");
    //     assert_eq!(output, vec![vec![(11, 11, None)]]);
    // }

    // #[test]
    // fn test_range_back_mut_only_contains_range_last_included() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_back_mut_both_included(29, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_included");
    //     assert_eq!(output, vec![vec![(29, 29, None)]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_included(28, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_included");
    //     assert_eq!(output, vec![vec![(29, 29, Some(28)), (28, 28, None)]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_included(28, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_included");
    //     assert_eq!(output, vec![vec![(29, 29, Some(28)), (28, 28, None)]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_included(27, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_included");
    //     assert_eq!(
    //         output,
    //         vec![vec![(29, 29, Some(28)), (28, 28, Some(27)), (27, 27, None)]]
    //     );
    // }

    // #[test]
    // fn test_range_back_mut_only_contains_range_last_excluded() {
    //     let mut tree = tree_with_initial_data((10..30).collect());

    //     let receipt = tree
    //         .get_range_back_mut_both_excluded(29, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_excluded(28, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_excluded");
    //     assert_eq!(output, vec![vec![]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_excluded(28, 30)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_excluded");
    //     assert_eq!(output, vec![vec![(29, 29, None)]]);

    //     let receipt = tree
    //         .get_range_back_mut_both_excluded(27, 29)
    //         .execute_expect_success(true);
    //     let output: Vec<Vec<(i32, i32, Option<i32>)>> =
    //         receipt.outputs("get_range_back_mut_both_excluded");
    //     assert_eq!(output, vec![vec![(28, 28, None)]]);
    // }

    #[test]
    fn test_range_after_mutating() {
        let mut tree = tree_with_initial_data((10..30).collect());

        tree.range_mut(15..25)
            .for_each(|(_, value, _): (&i32, &mut i32, Option<i32>)| {
                *value = -1;
                return IterMutControl::Continue;
            });
        assert_tree_range_contains(
            &tree,
            15..25,
            vec![
                (15, -1),
                (16, -1),
                (17, -1),
                (18, -1),
                (19, -1),
                (20, -1),
                (21, -1),
                (22, -1),
                (23, -1),
                (24, -1),
            ],
        );
        assert_tree_range_contains(
            &tree,
            25..30,
            vec![(25, 25), (26, 26), (27, 27), (28, 28), (29, 29)],
        );
    }

    #[test]
    fn test_range_after_mutating_with_max_iters() {
        let mut tree = tree_with_initial_data((10..30).collect());
        let mut count = 0;
        tree.range_mut(15..25)
            .for_each(|(_, value, _): (&i32, &mut i32, Option<i32>)| {
                *value = -1;
                count += 1;
                return if count < 5 {
                    IterMutControl::Continue
                } else {
                    IterMutControl::Break
                };
            });
        assert_tree_range_contains(
            &tree,
            15..25,
            vec![
                (15, -1),
                (16, -1),
                (17, -1),
                (18, -1),
                (19, -1),
                (20, 20),
                (21, 21),
                (22, 22),
                (23, 23),
                (24, 24),
            ],
        );
        assert_tree_range_contains(
            &tree,
            25..30,
            vec![(25, 25), (26, 26), (27, 27), (28, 28), (29, 29)],
        );
    }
}
