#![feature(augmented_assignments)]
#![feature(core)]
#![feature(custom_derive)]
#![feature(test)]

/// # The Pumpkin Prime Number Generator
///
/// The `pumpkin` prime number generator library can be used to generate
/// prime numbers of any reasonable length, suitable for any cryptographic
/// purpose. All numbers generated are seeded from the operating system's
/// secure source of entrophy and are verified using three different primality
/// tests.
///
/// ## Examples
///
/// ```
/// extern crate pumpkin;
///
/// use pumpkin::Prime;
///
/// fn main() {
///     // Generate a 2048-bit prime number
///     let p = Prime::new(2048);
///     let q = Prime::new(2048);
///
///     let r = p * q;
///     println!("{}", r); // Some ridiculously large number
/// }
/// ```

extern crate core;
#[macro_use] extern crate custom_derive;
#[macro_use] extern crate newtype_derive;
extern crate ramp;
extern crate rand;
extern crate num;
#[macro_use(lazy_static)]
extern crate lazy_static;
extern crate test;

mod prime;
pub use prime::Prime;


#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;

    #[test]
    // generates a prime successfully
    fn synopsis() {
        println!("{} is probably prime.", Prime::new(2048));
    }

    #[bench]
    fn benchmark_synopsis(b: &mut Bencher) {
        b.iter(|| println!("{} is probably prime.", Prime::new(2048)));
    }
}
