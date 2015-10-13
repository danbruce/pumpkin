# Pumpkin

A cryptographically-secure pseudo-random number generator for generating large 
prime.

## What's up with the name?

Since I began writing this library around Halloween of 2015, I wanted to choose
a name that was vaguely related to the holiday. Because "pumpkin" and "prime"
both begin with the letter 'p', I decided to use that. And that's all there
really is to it!

## Purpose

`pumpkin` is a cryptographically-secure pseudo-random number generator, which is
useful for generating large prime numbers for cryptography. In fact, `pumpkin`
can ONLY be used to generate prime numbers. On the back-end, `pumpkin` uses the
wonderful [ramp](https://crates.io/crates/ramp) library for storing the large
numbers. `pumpkin` generates numbers very quickly, so you can be sure that your
program will be performative. In our testing, primes were generated anywhere
between 1s and 5s on average, though of course your mileage may vary.

## Example

```
extern crate pumpkin;

use pumpkin::Prime;

fn main() {
    let p = Prime::new(2048); // Generate a new 2048-bit prime number
    let q = Prime::new(2048);
    let e = p * q;

    println("{}", e);

    /*
     * 75222035638256552797269351238215022250546763213674706... Some massive
     * 4096-bit number.
     */
}
```

## Explanation
`Prime`s are generated much the same way that large primes are generated by
`GnuPG`:
  1) Create a large candidate number of size based on the input given to the
  `Prime::new()` method. All `Prime`s must be at least 2-bits long (thoug it
  wouldn't make much sense to be that small.

  2) Divide the candidate number by the first 1,000 prime numbers.

  3) Test the candidate number with [Fermat's Little
Theorem](https://www.wikiwand.com/en/Fermat's_little_theorem).

  4) Finally, run five iterations of the [Miller-Rabin Primality
Test](https://www.wikiwand.com/en/Miller%E2%80%93Rabin_primality_test).

`Prime`s are seeded by `rand::OsRng`, which receives its entropy via the
operating system's own entropy source (such as `/dev/urandom'). Thus, because we
can be confident that the generated candidate number is truly random (or as
close to truly random as the user can hope), we don't need to do more than five
iterations of the Miller-Rabin test to ensure primality.

`Prime`s are simple "newtype" structs; that is, it is a tuple-like struct
surrounding an `Int` type. `Prime`s have all of the basic algebraic and logical
operators implemented, thus allowing you to do any operation that you would
require.

## Contributing

`pumpkin` is dual-licenced under the MIT and Unlicense. Should you wish to
contribute updates to the project, please consider signing the included `WAVER`
file with your cryptographic digital signature (as allowed by your country's
laws). Doing so will release your changes back into the public domain to be used
freely by all. I did so with this project, and it would mean a lot if you did
too!
