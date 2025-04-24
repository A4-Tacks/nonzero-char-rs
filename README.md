Implement NonZeroChar, like NonZeroU32

```rust
use nonzero_char::NonZeroChar;

assert_eq!(NonZeroChar::new('a').unwrap(), 'a');
assert_eq!(NonZeroChar::new('\0'), None);
```

Null Pointer Optimization:
```rust
use nonzero_char::NonZeroChar;

assert_eq!(size_of::<NonZeroChar>(), size_of::<Option<NonZeroChar>>());
```
