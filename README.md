# conum

The goal of this crate is to provide arbitrary fixed digit-width, integers and floats.
This was inspired by COBOL's type system, which specifies the size of their numbers in digits.

This is currently used in my hobby COBOL to Rust transpiler, as a way to mirror COBOL types.

If you're looking for the most optimized big number implementation, this won't be it. I recommend checking out `bnum` or `num_bigint` if that's what you need.
