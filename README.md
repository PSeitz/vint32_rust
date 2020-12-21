## Vint32

Fast vint u32 encoding for rust. Uses at most 5 bytes.

# Examples
```
use vint32::encode_varint_into;
let mut output = vec![];
encode_varint_into(&mut output, 50);	
assert_eq!(output.len(), 1);
```

## Tests

`cargo test --all-features`
