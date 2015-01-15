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

#![allow(missing_docs)]

use ops::Recip;
use std::ops::{Div, Neg, Sub};
use structure::MagmaAdditiveApprox;
use structure::MagmaAdditive;
use structure::MagmaMultiplicativeApprox;
use structure::MagmaMultiplicative;

/// An additive magma that for which subtraction is always possible.
pub trait QuasigroupAdditiveApprox
    : MagmaAdditiveApprox
    + Sub<Output = Self>
    + Neg<Output = Self>
    + Copy
{
    fn prop_sub_is_latin_square_approx(args: (Self, Self)) -> bool where Self : Sized {
        let (a, b) = args;

        a == (a + -b) + b &&
        a == (a + b) + -b &&
        a == (a - b) + b &&
        a == (a + b) - b

        // TODO: psuedo inverse?
    }
}

impl QuasigroupAdditiveApprox for u8    {}
impl QuasigroupAdditiveApprox for u16   {}
impl QuasigroupAdditiveApprox for u32   {}
impl QuasigroupAdditiveApprox for u64   {}
impl QuasigroupAdditiveApprox for usize {}
impl QuasigroupAdditiveApprox for i8    {}
impl QuasigroupAdditiveApprox for i16   {}
impl QuasigroupAdditiveApprox for i32   {}
impl QuasigroupAdditiveApprox for i64   {}
impl QuasigroupAdditiveApprox for isize {}

/// An additive magma that for which subtraction is always possible.
pub trait QuasigroupAdditive
    : MagmaAdditive
    + QuasigroupAdditiveApprox
    + Copy
{
    fn prop_sub_is_latin_square(args: (Self, Self)) -> bool where Self : Sized {
        let (a, b) = args;

        a == (a + -b) + b &&
        a == (a + b) + -b &&
        a == (a - b) + b &&
        a == (a + b) - b

        // TODO: psuedo inverse?
    }
}

impl QuasigroupAdditive for u8    {}
impl QuasigroupAdditive for u16   {}
impl QuasigroupAdditive for u32   {}
impl QuasigroupAdditive for u64   {}
impl QuasigroupAdditive for usize {}
impl QuasigroupAdditive for i8    {}
impl QuasigroupAdditive for i16   {}
impl QuasigroupAdditive for i32   {}
impl QuasigroupAdditive for i64   {}
impl QuasigroupAdditive for isize {}

/// An multiplicative magma that for which division is always possible.
pub trait QuasigroupMultiplicativeApprox
    : MagmaMultiplicativeApprox
    + Div<Output = Self>
    + Recip<Self>
    + Copy
{
    fn prop_div_is_latin_square_approx(args: (Self, Self)) -> bool where Self : Sized {
        let (a, b) = args;

        a == (a * b.recip()) * b &&
        a == (a * b) * b.recip() &&
        a == (a / b) * b &&
        a == (a * b) / b

        // TODO: psuedo inverse?
    }
}

/// An multiplicative magma that for which division is always possible.
pub trait QuasigroupMultiplicative
    : MagmaMultiplicative
    + QuasigroupMultiplicativeApprox
    + Copy
{
    fn prop_div_is_latin_square(args: (Self, Self)) -> bool where Self : Sized {
        let (a, b) = args;

        a == (a * b.recip()) * b &&
        a == (a * b) * b.recip() &&
        a == (a / b) * b &&
        a == (a * b) / b

        // TODO: psuedo inverse?
    }
}

#[cfg(test)]
mod tests {
    macro_rules! check_isize {
        ($T:ident) => {
            mod $T {
                use structure::QuasigroupAdditiveApprox;
                use structure::QuasigroupAdditive;

                #[quickcheck]
                fn prop_sub_is_latin_square_approx(args: ($T, $T)) -> bool {
                    QuasigroupAdditiveApprox::prop_sub_is_latin_square_approx(args)
                }
                #[quickcheck]
                fn prop_sub_is_latin_square(args: ($T, $T)) -> bool {
                    QuasigroupAdditive::prop_sub_is_latin_square(args)
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
