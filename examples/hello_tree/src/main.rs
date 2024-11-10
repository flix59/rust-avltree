use rust_avltree::{AvlTree, IterMutControl};
use std:: ops::Bound::{Excluded, Included};
pub fn fancy_operations(tree: &mut AvlTree<i32, String>) {
        /* Calculate some shenanigan add stuff and remove stuff from tree */
        tree.insert(1, "Hello".to_string());
        tree.insert(2, "World".to_string());
        // check_health(&mut tree);
        tree.insert(3, "!".to_string());
        tree.insert(4, "How".to_string());
        tree.insert(5, "are".to_string());
        tree.insert(6, "you".to_string());
        tree.insert(1000, "doing".to_string());
        tree.remove(&4);
        tree.remove(&5);
        // Override value 1
        tree.insert(1, "New Hello".to_string());
        let range = tree.range(1..5);
        let special_range = tree.range((Excluded(1), Included(5)));
        for (key, value) in range {
            // print " New Hello World ! you", since items are sorted.
            // "are" and "you" are deleted, and "doing" is not in range
            println!("{} ", value);
        }
        tree.range_mut(1..5).for_each(
            |(key, value): (&i32, &mut String)| {
                println!("{} ", value);
                IterMutControl::Continue
            }
        );
    }

pub fn main(){
    let mut tree = AvlTree::new();
    fancy_operations(&mut tree);
}