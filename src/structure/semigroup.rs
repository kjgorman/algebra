// Copyright 2013-2014 The Num-rs Developers.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use structure::MagmaAdditiveApprox;
use structure::MagmaAdditive;
use structure::MagmaMultiplicativeApprox;
use structure::MagmaMultiplicative;

/// A type that is closed over an approximately associative addition operator.
///
/// The addition operator must satisfy:
///
/// ~~~notrust
/// (a + b) + c ≈ a + (b + c)           ∀ a, b, c ∈ Self
/// ~~~
pub trait SemigroupAdditiveApprox
    : MagmaAdditiveApprox
    + Copy
{
    /// Returns `true` if associativity over addition holds approximately for
    /// the given arguments.
    fn prop_add_is_associative_approx(args: (Self, Self, Self)) -> bool where Self : Sized {
        // TODO: use ApproxEq
        let (a, b, c) = args;
        (a + b) + c == a + (b + c)
    }
}

impl SemigroupAdditiveApprox for u8    {}
impl SemigroupAdditiveApprox for u16   {}
impl SemigroupAdditiveApprox for u32   {}
impl SemigroupAdditiveApprox for u64   {}
impl SemigroupAdditiveApprox for usize {}
impl SemigroupAdditiveApprox for i8    {}
impl SemigroupAdditiveApprox for i16   {}
impl SemigroupAdditiveApprox for i32   {}
impl SemigroupAdditiveApprox for i64   {}
impl SemigroupAdditiveApprox for isize {}

/// A type that is closed over an associative addition operator.
///
/// The addition operator must satisfy:
///
/// ~~~notrust
/// (a + b) + c = a + (b + c)           ∀ a, b, c ∈ Self
/// ~~~
pub trait SemigroupAdditive
    : MagmaAdditive
    + SemigroupAdditiveApprox
    + Copy
{
    /// Returns `true` if associativity over addition holds for the given
    /// arguments.
    fn prop_add_is_associative(args: (Self, Self, Self)) -> bool where Self : Sized {
        let (a, b, c) = args;
        (a + b) + c == a + (b + c)
    }
}

impl SemigroupAdditive for u8    {}
impl SemigroupAdditive for u16   {}
impl SemigroupAdditive for u32   {}
impl SemigroupAdditive for u64   {}
impl SemigroupAdditive for usize {}
impl SemigroupAdditive for i8    {}
impl SemigroupAdditive for i16   {}
impl SemigroupAdditive for i32   {}
impl SemigroupAdditive for i64   {}
impl SemigroupAdditive for isize {}

/// A type that is closed over an approximately associative multiplication operator.
///
/// The multiplication operator must satisfy:
///
/// ~~~notrust
/// (a * b) * c ≈ a * (b * c)           ∀ a, b, c ∈ Self
/// ~~~
pub trait SemigroupMultiplicativeApprox
    : MagmaMultiplicativeApprox
    + Copy
{
    /// Returns `true` if associativity over multiplication holds approximately for
    /// the given arguments.
    fn prop_mul_is_associative_approx(args: (Self, Self, Self)) -> bool where Self : Sized {
        // TODO: use ApproxEq
        let (a, b, c) = args;
        (a * b) * c == a * (b * c)
    }
}

impl SemigroupMultiplicativeApprox for u8    {}
impl SemigroupMultiplicativeApprox for u16   {}
impl SemigroupMultiplicativeApprox for u32   {}
impl SemigroupMultiplicativeApprox for u64   {}
impl SemigroupMultiplicativeApprox for usize {}
impl SemigroupMultiplicativeApprox for i8    {}
impl SemigroupMultiplicativeApprox for i16   {}
impl SemigroupMultiplicativeApprox for i32   {}
impl SemigroupMultiplicativeApprox for i64   {}
impl SemigroupMultiplicativeApprox for isize {}

/// A type that is closed over an associative multiplication operator.
///
/// The multiplication operator must satisfy:
///
/// ~~~notrust
/// (a * b) * c = a * (b * c)           ∀ a, b, c ∈ Self
/// ~~~
pub trait SemigroupMultiplicative
    : MagmaMultiplicative
    + SemigroupMultiplicativeApprox
    + Copy
{
    /// Returns `true` if associativity over multiplication holds for the given
    /// arguments.
    fn prop_mul_is_associative(args: (Self, Self, Self)) -> bool where Self : Sized {
        let (a, b, c) = args;
        (a * b) * c == a * (b * c)
    }
}

impl SemigroupMultiplicative for u8    {}
impl SemigroupMultiplicative for u16   {}
impl SemigroupMultiplicative for u32   {}
impl SemigroupMultiplicative for u64   {}
impl SemigroupMultiplicative for usize {}
impl SemigroupMultiplicative for i8    {}
impl SemigroupMultiplicative for i16   {}
impl SemigroupMultiplicative for i32   {}
impl SemigroupMultiplicative for i64   {}
impl SemigroupMultiplicative for isize {}

#[cfg(test)]
mod tests {
    macro_rules! check_isize {
        ($T:ident) => {
            mod $T {
                use structure::SemigroupAdditiveApprox;
                use structure::SemigroupAdditive;
                use structure::SemigroupMultiplicativeApprox;
                use structure::SemigroupMultiplicative;

                #[quickcheck]
                fn prop_add_is_associative_approx(args: ($T, $T, $T)) -> bool {
                    SemigroupAdditiveApprox::prop_add_is_associative_approx(args)
                }
                #[quickcheck]
                fn prop_add_is_associative(args: ($T, $T, $T)) -> bool {
                    SemigroupAdditive::prop_add_is_associative(args)
                }

                #[quickcheck]
                fn prop_mul_is_associative_approx(args: ($T, $T, $T)) -> bool {
                    SemigroupMultiplicativeApprox::prop_mul_is_associative_approx(args)
                }
                #[quickcheck]
                fn prop_mul_is_associative(args: ($T, $T, $T)) -> bool {
                    SemigroupMultiplicative::prop_mul_is_associative(args)
                }
            }
        }
    }
    check_isize!(u8);
    check_isize!(u16);
    check_isize!(u32);
    check_isize!(u64);
    check_isize!(usize);
    check_isize!(i8);
    check_isize!(i16);
    check_isize!(i32);
    check_isize!(i64);
    check_isize!(isize);
}
