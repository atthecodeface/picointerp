/*a Copyright

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

  http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@file    picovalue
@brief   Value trait and some implementationss for the picointerpreter
 */

//a Imports

//a PicoValue
//pt PicoValue
/// The value used by the interpreter this is notionally forced to be an integer of some size whose bottom bit is 0 for an object (with the value being usable as an index)
pub trait PicoValue : Sized + Clone + Copy + std::fmt::Debug {
    /* const */ fn unit() -> Self;
    /* const */ fn int(n:isize) -> Self;
    /* const */ fn is_int(self) -> bool;
    /* const */ fn is_object(self) -> bool { ! self.is_int() }
    /* const */ fn as_isize(self) -> isize;
    /* const */ fn as_usize(self) -> usize;
    /* const */ fn as_heap_index(self) -> usize; // Guaranteed to be invoked only if is_object
    fn negate(self) -> Self;
    fn add(self, other:Self) -> Self;
    fn sub(self, other:Self) -> Self;
    fn mul(self, other:Self) -> Self;
    fn div(self, other:Self) -> Self;
    fn rem(self, other:Self) -> Self;
    fn and(self, other:Self) -> Self;
    fn or(self, other:Self) -> Self;
    fn xor(self, other:Self) -> Self;
    fn lsl(self, other:Self) -> Self;
    fn lsr(self, other:Self) -> Self;
    fn asr(self, other:Self) -> Self;
    fn cmp_eq(self, other:Self) -> bool;
    fn cmp_ne(self, other:Self) -> bool;
    fn cmp_lt(self, other:Self) -> bool;
    fn cmp_le(self, other:Self) -> bool;
    fn cmp_gt(self, other:Self) -> bool;
    fn cmp_ge(self, other:Self) -> bool;
    fn cmp_ult(self, other:Self) -> bool;
    fn cmp_uge(self, other:Self) -> bool;
}

//ip PicoValue for isize
impl PicoValue for isize {
    #[inline]
    /* const */ fn unit() -> Self { 0 }
    #[inline]
    /* const */ fn int(n:isize) -> Self { (n<<1) | 1 }
    #[inline]
    /* const */ fn is_int(self) -> bool { self & 1 == 1 }
    #[inline]
    /* const */ fn is_object(self) -> bool { self & 1 == 0 }
    #[inline]
    /* const */ fn as_isize(self) -> isize { self >> 1 }
    #[inline]
    /* const */ fn as_usize(self) -> usize { (self >> 1) as usize }
    #[inline]
    /* const */ fn as_heap_index(self) -> usize { self as usize }
    #[inline]
    fn negate(self) -> Self          { (! self) ^ 1 }
    #[inline]
    fn add(self, other:Self) -> Self { self + (other-1) }
    #[inline]
    fn sub(self, other:Self) -> Self { self - (other-1) }
    #[inline]
    fn mul(self, other:Self) -> Self { (self>>1) * (other>>1) + 1 }
    #[inline]
    fn div(self, other:Self) -> Self { (self>>1) / (other>>1) }
    #[inline]
    fn rem(self, other:Self) -> Self { (self>>1) % (other>>1) }
    #[inline]
    fn and(self, other:Self) -> Self { self & other }
    #[inline]
    fn or(self, other:Self) -> Self  { self | other }
    #[inline]
    fn xor(self, other:Self) -> Self { (self ^ other) + 1 }
    #[inline]
    fn lsl(self, other:Self) -> Self { ((self-1) << (other>>1)) + 1 }
    #[inline]
    fn lsr(self, other:Self) -> Self { (((self-1) as usize) >> (other>>1)) as isize + 1 }
    #[inline]
    fn asr(self, other:Self) -> Self { ((self-1) >> (other>>1)) + 1 }
    #[inline]
    fn cmp_eq(self, other:Self) -> bool { self == other }
    #[inline]
    fn cmp_ne(self, other:Self) -> bool { self != other }
    #[inline]
    fn cmp_lt(self, other:Self) -> bool { self < other }
    #[inline]
    fn cmp_le(self, other:Self) -> bool { self <= other }
    #[inline]
    fn cmp_gt(self, other:Self) -> bool { self > other }
    #[inline]
    fn cmp_ge(self, other:Self) -> bool { self >= other }
    #[inline]
    fn cmp_ult(self, other:Self) -> bool { (self as usize) <  (other as usize) }
    #[inline]
    fn cmp_uge(self, other:Self) -> bool { (self as usize) >= (other as usize) }
}

