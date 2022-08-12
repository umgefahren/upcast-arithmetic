# upcast-arithmetic

Utility library for dealing with arithmetic on type limits by upcasting into types with higher
limits.

## Examples

###  Without `upcast_arithmetic`
```rust
let a = u8::MAX;
let b = 2u8;

let modulo = u8::MAX;

let res = (a + b) % modulo;
assert_eq!(res, 2);
```
### With `upcast_arithmetic`
```rust
use upcast_arithmetic::*;

let a = u8::MAX;
let b = 2u8;

let modulo = u8::MAX;

let res = a.upcast_add_mod(b, modulo);
assert_eq!(res, 2);
```

License: MIT
