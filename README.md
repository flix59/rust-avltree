# rust-avltree

For an explanation for an avl tree: https://en.wikipedia.org/wiki/AVL_tree.

This is a port from the scrytpo-avltree and uses the normal std::collections::Hashmap instead of the scrypto KVStore. https://github.com/ociswap/scrypto-avltree 

Compared to a `red black tree` the `AVL tree` is optimised for lookup/query performance instead of insert/write performance.

To optimise lookups further this implementation combines the `AVL tree` implemention with a linked list - allowing to traverse the next left and right nodes directly in `O(1)` without needing to traverse the tree up and down which would be `O(log n)`.

# Usage

## Example
Checkout the example folder, that provides some basic usage examples.

### Dependencies
Add avl tree to your toml config:
```toml
[dependencies]
avltree = { git = "https://github.com/flix59/rust-avltree", tag = "v1.0.0" }
```

### Instantiation 
Instantiation is rather simple:
```rust
use avltree::AvlTree;
let mut tree: AvlTree<i32, String> = AvlTree::new();
```

### Insert and get
Inserting a new key value pair is also straight forward:
```rust
tree.insert(1, "value");
```
If the key is already present in the tree, the value will be overwritten and the old value will be returned.
```rust
let old_value = tree.insert(1, "new value");
assert_eq!(old_value, Some("value"));
```

### Get and get_mut
The tree can be queried by key:
```rust
let value = tree.get(&1);
```
Or to get a mutable reference to the value:
```rust
let value = tree.get_mut(&1);
```

### Range
To iterate over the tree you can use the `range`, `range_back` methods.
It accepts a range of keys and returns an iterator over the key value pairs:
The iterator implements the standard rust iterator: it provides operations like map, for_each, fold, etc.
The range is default in rust and can have inclusive or exclusive bounds.
```rust
for (key, value) in tree.range(1..10) {
    println!("key: {}, value: {}", key, value);
}
```
gives you all values for the keys between 1 and 10 ascending and excluding 10.
```rust
for (key, value) in tree.range_back(Excluded(1), Included(10)) {
    println!("key: {}, value: {}", key, value);
}
```
gives you all values for the keys between 1 and 10 descending and excluding 1.

### Mutable Range
To iterate over the tree and mutate the values you can use the `range_mut`, `range_back_mut` methods.
It accepts a range of keys and returns an iterator that can be used with the for_each callback
```rust
tree.range_mut(1..10).for_each(|(key, value): (&K, &mut V)| {
    *value=String::from("mutated");
}
tree.range_back_mut(1..10).for_each(|(key, value): (&K, &mut V)| {
    *value=String::from("mutated");
}
```
gives 10 times "mutated" as output.
Analogue to the `range` method the `range_back_mut` method gives you a descending iterator.

### Remove
To remove a key value pair from the tree you can use the `remove` method:
```rust
let value = tree.remove(&1));
println!("{}", value);
```
The method returns the value that was removed from the tree. 
None is returned, if the key is not present in the tree.

# Contribute
The AVL tree itself is implemented in `avl_tree.rs`. T