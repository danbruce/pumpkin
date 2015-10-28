use core::ops::{Add, BitAnd, Mul, Rem, Shr, Sub};

use ramp::{Int, RandomInt};
use num::bigint::BigUint;
use num::integer::Integer;
use num::traits::One;

use rand::{OsRng, thread_rng};

use std::fmt;

// this is the product of the first 1000 primes in hex format
const PRODUCT_OF_PRIMES_STRING: &'static str =
    "6b17d7e673be26fe625ede311ab620e5c9e71434adb1edb43b10abb94dd4f053fc06baf1cb\
    2e457a10fb06532376320da5c238d4a5bca389fcebe40744f69aab7e15d1d792b644714dac3\
    666b07e31afed10b4f7202b103b234a855735dbb9bb24e503a30f3ba42475a9ccaff155d2ab\
    1febbb773c7574bf95cd628f8ed04af49012ff37c18ed0134fde88a45cb5239c25aee3ec44b\
    d8c36872d5ec5655ee12495e4a88fb0a4de57c29119a852d0e0d132e2946b6f23e86b5756fc\
    cc33d1b03e23d4e0dd8badfd176c15e3bc3f163de231555a7410cc32daba342086098347db9\
    b6833446d1143bef3a07f2b46d525e8b0a0b5f979a0ccfc3e6d6890f0c01bcdd6da8980c63f\
    57f0d872e7237c779291babf1174a9daf0d7c1c4c2563842994405c80c8dee1b596bfe8b70c\
    40ce05699efc23cf01e7c1906c0477b2fcff58bd1c5c79602e092d82515c648db974c7eb5c1\
    8839914648d15e052fbbd0af142e5bb355661ae8ad94f37c81c9113a645878ce0894ff3e837\
    bf127ba12b5fd279fa7b59a4e57c0df7a7333888648e24669dd89653c7dd503c23b6959621e\
    43d55966528b4cbf3091021b5458111085f3147d0f9c9679e76c90c46f3431323525cf537e0\
    7e5feede6563088fdd6e41092cb3902e6837b2c89efd6a303c3ed64e3a0ff3a486b79bccd07\
    a2b73251b7bb3782c402aa4b370bde346b3ff0670ef509731ec97c5b85f00d439bc0c5de111\
    a3615b778ca4d77bbcbb90d242d144709303acb8445007d6d05b58129b053f120007303e179\
    0a0424263431f15f2e430a274b0a8248c980e12ba96aa948f1f9a04ffb4f20f9ed11d14ad1b\
    0a75f02c3458b0663c434e82f9f717b67ad1e907e13c6c3e2c3547a3aeefa1f9e49d981ec00\
    cfa11248c1d79e3eed2e4a5e05decfb717c9c3558afabae651b61d59f8fce940e0c5ba73371\
    58be9437833e846bb6fbe4fd7c393c4754578a0291baeca1c28605c0c517e79d26550747578\
    cf9addf4b9f1b9e61d1002bfcd231abe73cb5bb13b45d6058153dfd27c52ab57ecac7c599ad\
    9221d613a1b806c87c0d9ea14a8c7c31dbac52ea291c22d8a51d33150b5aa5fe69336bd6238\
    c69403355856f76806391148c5830ff11d517c79dfee079f12f19a73eae0119c90198281122\
    6e640a6053b57de92cc76efc88a772dd63371111b73adff4df97dc011825f711e73667b5aa5\
    bd4bb2f1f4c26883a476602c8862eba26ae06b825164aece5c157717d0b3dfcc19242ada3c2\
    70ac0b17df1f01a6d35933f6856a39b6b9b50379d616710a651215a3d2af9f890dddc4a3745\
    109a41f1be4ff54ed83fab28141d22c3a0e2bac5c54338889d18cf35efcd8187673f2156fe3\
    4930445d9020d72c0e4dce9482b27333832c231ef1c5c48d176c5e2d2a1773733a5f307ba0f\
    0af00b264c7d3907d0b0118c1c63c90351a070947948a4aefc99809dd6169eac172a629520a\
    0e3c7b908242cb053dc7f1433aa7f45d746346e1fa90ec629aa74ae6ab272f19e51a37d2c77\
    6708f3f8f86cabaeaa8f4e7735cfc41a30bd813c58c0fc82d817823f4c130b0058aab680d9c\
    715b9c5a77f4fdf2b298765c66007e8baa97a5a9e9e3a28f5d4efcabc6233e0e6623b55f5af\
    d81e4b94d0e1585f09cea1bdb3ee9ffc966bfcd236750d1f1b50c40cf51f1d797c8b90a3988\
    49bd701db53d373e4a70453480981557443a98a4647001da8b882e9a08e52456375d3c447f0\
    52c9d5faabedc197cf8f11f3fb96624e40c585eb54bccb66d43dff09e772c2659a4b0f3a1f1\
    54c7f3c0d10a7a268344f3b6f524b398250d19559c7c1dafa9e566ee61d97124b17934b3e3a\
    6a9aaead07b680fa9921983471683d050d72b8f98e7aaabd93f4f5cf9ce538422d9071bc8fb\
    d28f2d8a17a5c886132d51786d4f934f228dcc7161ffcf5ed084d7a8a39517fd9c4ef108be7\
    abf773f866fa9db168477e13c526f53e6bf8de348fd2";

lazy_static! {
    static ref PRODUCT_OF_PRIMES: BigUint = BigUint::parse_bytes(PRODUCT_OF_PRIMES_STRING.as_bytes(), 16).unwrap();
}

/// An arbitrarily-length prime number, suitable for cryptographic purposes.
///
/// All `Prime`s are initially seeded from the `rand::OsRng` random number
/// generator, which itself uses the operating system's main source of entropy.
///
/// Primes are verified to be prime by running the following three checks
/// during initialization:
///
///     1) Taking the GCD of the candidate with the product of the first 1000
///     primes. If the GCD is not one, add two to the candidate. Otherwise,
///     go to Step 2.
///
///     2) Run a Fermat Primality Test on the candidate. If it doesn't pass,
///     add two to the candidate and goto Step 1.
///
///     3) Finally, complete five rounds of the Miller-Rabin Primality Test.
///     Should any of the tests pass, add two to the candidate and goto Step 1.
///
/// The preceding steps mirror those used by GnuPG, a leading PGP implementation
/// used by thousands of users all across the world. Because the intial prime
/// number candidate is generated from the operating system's source of
/// entropy, we can be reasonably sure that the generated `Prime` is, in fact,
/// prime.
///
/// `Prime`s are built upon the `Int` type as defined in the `ramp` crate. In
/// fact, all operations that you can do with `Int`s, you can do with `Prime`s
/// as well. `Prime`s simply claim that the number you're dealing with is a
/// prime number.
custom_derive! {
    #[derive(Debug, NewtypeAdd, NewtypeSub, NewtypeMul, NewtypeDiv)]
    pub struct Prime(Int); 
}

impl Prime {
    /// Constructs a new `Prime` with a size of `bit_length` bits.
    ///
    /// The `bit_length` must be at least 2. While it doesn't make much sense
    /// to only generate a 2-bit random number, them's the rules.
    pub fn new(bit_length: usize) -> Prime {
        debug_assert!(bit_length >= 2);
        let mut rngesus = match OsRng::new() {
            Ok(rng) => rng,
            Err(reason) => panic!("Error initializing RNG: {}", reason)
        };

        Prime::from_rng(bit_length, &mut rngesus)
    }

    /// Constructs a new `Prime` with the size of `bit_length` bits, sourced
    /// from an already-created `OsRng`. Not that you can **ONLY** use an
    /// `OsRng`, as it uses the operating system's secure source of entropy.
    pub fn from_rng(bit_length: usize, rngesus: &mut OsRng) -> Prime {
        debug_assert!(bit_length >= 2);
        let one = Int::one();
        let two = &one + &one;
        let mut candidate = rngesus.gen_uint(bit_length);

        // Make sure candidate is odd before continuing...
        if &candidate & (&one) == 0 {
            candidate += &one;
        }
        while !is_prime(&candidate) {
            candidate += &two;
        }

        Prime(candidate)
    }
}

impl fmt::Display for Prime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let &Prime(ref num) = self;
        write!(f, "{}", num)
    }
}

fn is_prime(candidate: &Int) -> bool {

    // check if the GCD of the candidate and the prime_product is one
    if !gcd_is_one(candidate) {
        return false;
    }

    // Second, do a Fermat test on the candidate
    if !fermat(candidate) {
        return false;
    }

    // Finally, do a Miller-Rabin test
    if !miller_rabin(candidate) {
        return false;
    }

    true
}

fn gcd_is_one(a: &Int) -> bool {
    let a_num = BigUint::parse_bytes(a.to_str_radix(16, true).as_bytes(), 16).unwrap();
    (a_num.gcd(&PRODUCT_OF_PRIMES) == BigUint::one())
}

fn fermat(candidate: &Int) -> bool {
    // Perform Fermat's little theorem on the candidate to determine probable
    // primality.
    let one = Int::one();
    let random = thread_rng().gen_int_range(&one, candidate);

    let result = mod_exp(&random, &candidate.sub(&one), candidate);

    if result == one {
        true
    } else {
        false
    }
}

fn miller_rabin(candidate: &Int) -> bool {
    // Perform five iterations of the Miller-Rabin test on the candidate.
    let (s, d) = rewrite(candidate);
    let one = Int::one();
    let two = (&one).add(&one);

    for _ in 0..5 {
        let basis = thread_rng().gen_int_range(&two, candidate);
        let mut x = mod_exp(&basis, &d, candidate);

        if x.eq(&one) || x.eq(&(candidate.sub(&one))) {
            continue;
        } else {
            for _ in one.clone() .. s.sub(&one) {
                x = mod_exp(&x, &two, candidate);
                if x == one.clone() {
                    return false;
                } else if x == (candidate.sub(&one)) {
                    break;
                }
            }
            return false;
        }
    }

    true
}

fn mod_exp(base: &Int, exponent: &Int, modulus: &Int) -> Int {
    let (zero, one) = (Int::zero(), Int::one());
    let mut result = one.clone();
    let mut base = base.clone();
    let mut exponent = exponent.clone();

    while &exponent > &zero {
        if (&exponent).bitand(&one) == (one.clone()) {
            result = ((&result).mul(&base)).rem(modulus);
        }

        base = ((&base).mul(&base)).rem(modulus);
        exponent = exponent.clone().shr(1);
    }

    result
}

fn rewrite(candidate: &Int) -> (Int, Int) {
    let one = Int::one();

    let mut d = candidate.sub(&one);
    let mut s = Int::zero();

    while (&d).bitand(&one) == one {
        d = d.clone().shr(1);
        s = (&s).add(&one);
    }

    (s, d)
}
