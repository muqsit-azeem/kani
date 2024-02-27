![](./kani-logo.png)

**Experimental Lean4 Backend for Kani**

This branch introduces an experimental Lean4-based backend to Kani. If you're searching for the main version of Kani, please visit our [main GitHub repository](https://github.com/model-checking/kani).

Unlike the main Kani version that translates [MIR](https://blog.rust-lang.org/2016/04/19/MIR.html) to Goto and uses CBMC for verification, this branch offers a translation from MIR to [Lean4](https://github.com/leanprover/lean4) for verification with the Lean4 theorem prover. Currently, it supports a limited subset of Rust.

Since the Lean4 backend is not included in Kani's [official releases](https://github.com/model-checking/kani/releases), you'll need to clone this branch and build it from source. For detailed instructions, please refer to the [Installing from source code](https://model-checking.github.io/kani/build-from-source.html) section in our documentation.

## Prerequisites

Ensure you have the Lean4 theorem prover installed on your system. You can find the installation instructions at [Lean4's GitHub page](https://github.com/leanprover/lean4#installation).

## Using the Lean4 Backend

To utilize the Lean4 backend, include the `-Zlean` option when running the Kani command, like so:

```bash
kani test.rs -Zlean
```
or 
```
cargo kani -Zlean
```

Kani will output the path to the generated Lean4 file, for example:
```
Writing Lean4 file to /home/ubuntu/test1_main.lean
```

You will need to manually write properties on the translated program and use the Lean4 theorem prover to perform verification.

## Example
The following array example 
```
fn set_elements(mut arr: kani::array::Array<i32>, mut index:usize) -> kani::array::Array<i32> {
    if index < arr.len() {
        arr[index] = 1;
        return set_elements(arr, index+1);
    } else {
        return arr;
    }
}


pub fn set_one(mut arr: kani::array::Array<i32>) -> kani::array::Array<i32> {
    set_elements(arr, 0)
}

```
using the command 
```
./scripts/kani -Zlean lean-array-set-1.rs --function set_one --enable-unstable
```
is translated to the following:
```
-- Functions definition:
def _RNvCsa8IeKRf3yLd_16lean_array_set_112set_elements (arr: Array Int) (index: Nat) : Array Int := Id.run do
  let mut _0 : Array Int := #[0]
  let mut arr : Array Int := arr
  let mut index : Nat := index
  let mut _3 : Bool := true
  let mut _4 : Nat := 0
  let mut _5 : Array Int := #[0]
  let mut _6 : Int := 1
  let mut _7 : Array Int := #[0]
  let mut _8 : Array Int := #[0]
  let mut _9 : Nat := 0
  let mut _10 : Nat := 0
  _4 := arr.size
  _3 := index < _4
  if h1 : _3 = false then
    _0 := arr
    return _0
  else
    arr := arr.set! index 1
    _8 := arr
    _10 := index + 1
    _9 := _10
    _0 := _RNvCsa8IeKRf3yLd_16lean_array_set_112set_elements _8 _9
    return _0

def _RNvCsa8IeKRf3yLd_16lean_array_set_17set_one (arr: Array Int) : Array Int := Id.run do
  let mut _0 : Array Int := #[0]
  let mut arr : Array Int := arr
  _0 := _RNvCsa8IeKRf3yLd_16lean_array_set_112set_elements arr 0
  return _0

```

## Directory Structure
TODO


## GitHub Action

Use Kani in your CI with `model-checking/kani-github-action@VERSION`. See the
[GitHub Action section in the Kani
book](https://model-checking.github.io/kani/install-github-ci.html)
for details.

## Security
See [SECURITY](https://github.com/model-checking/kani/security/policy) for more information.

## Contributing
If you are interested in contributing to Kani, please take a look at [the developer documentation](https://model-checking.github.io/kani/dev-documentation.html).

## License
### Kani
Kani is distributed under the terms of both the MIT license and the Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for details.

### Rust
Kani contains code from the Rust project.
Rust is primarily distributed under the terms of both the MIT license and the Apache License (Version 2.0), with portions covered by various BSD-like licenses.

See [the Rust repository](https://github.com/rust-lang/rust) for details.
