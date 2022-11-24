#![feature(test, generic_const_exprs)]

extern crate test;

use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr, ShrAssign};
use std::cmp::{Eq, PartialEq};

/// An efficient Bitset with a known size at compile-time.
/// N defines the length in bits.
///
/// Bits outside of the size of the bitset are undefined, but can be accessed.
/// They might have any value.
#[derive(Clone, Copy, Hash)]
pub struct Bitset<const N: usize>
where [(); (N+63)/64]: Sized {
    state: [u64; (N+63)/64],
}

impl<const N: usize> Bitset<N>
where [(); (N+63)/64]: Sized {

    pub const fn new() -> Self {
        Bitset{
            state: [0; (N+63)/64]
        }
    }

    pub const fn from_array(arr: [u64; (N+63)/64]) -> Self {
        Bitset{
            state: arr
        }
    }

    /// Returns a new Bitset with only the specifies bit set to true
    pub fn with_bit_set(idx: usize) -> Self {
        let mut ret = Self::new();
        ret.set_bit(idx);
        ret
    }

    /// Creates a bitset with all bits in the specified range set.
    /// Note that the bitset might contain more bits, which are still
    /// accessible but will not be set in this function.
    pub const fn with_all_bits_set() -> Self {
        let mut ret = Self::new();
        let mut i = 0;
        loop {
            if i == N {
                break
            }
            ret.state[i>>6] |= 1<<i%64;
            i += 1;
        }
        ret
    }

    /// Sets the bit at position to true
    pub fn set_bit(&mut self, position: usize) {
        let i = position >> 6;
        let offset = position & 63;
        self.state[i] |= 1_u64<<offset;
    }
    
    /// Sets the bit at position to false
    pub fn unset_bit(&mut self, position: usize) {
        let i = position >> 6;
        let offset = position & 63;
        self.state[i] &= !(1_u64<<offset);
    }

    /// Sets the bit at position to value
    pub fn set(&mut self, position: usize, value: bool) {
        if value {
            self.set_bit(position)
        } else {
            self.unset_bit(position)
        }
    }
    
    /// Get the bit at index position
    /// Panics if position is out of range
    pub fn get(&self, position: usize) -> bool {
        let i = position / 64;
        let offset = position & 63;
        (self.state[i]>>offset) & 1 == 1
    }

    /// Returns `true` if at least one bit is set to `true`
    pub fn any(&self) -> bool {
        for x in self.state {
            if x != 0 {
                return true
            }
        }
        false
    }

    /// Returns the number of ones in the Bitset
    pub fn count_ones(&self) -> u32 {
        let mut ones = 0;
        for x in self.state {
            ones += x.count_ones();
        }
        ones
    }

    /// Returns the number of zeros in the Bitset
    pub fn count_zeros(&self) -> u32 {
        let mut zeros = 0;
        for x in self.state {
            zeros += x.count_zeros();
        }
        zeros
    }
}

impl<const N: usize> std::fmt::Debug for Bitset<N>
where [(); (N+63)/64]: Sized {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut result = String::new();
        for i in 0..(N+63)/64 {
            result += "_";
            for j in 0..64 {
                result += if self.get(((N+63)/64 - i - 1) * 64 + (63 - j)) {
                    "1"
                } else {
                    "0"
                };
            }
        }
        write!(f, "0b{}", result)
    }
}

impl<const N: usize> PartialEq<Self> for Bitset<N>
where [(); (N+63)/64]: Sized {
    fn eq(&self, other: &Self) -> bool {
        for i in 0..(N+63)/64 {
            if self.state[i] != other.state[i] {
                return false
            }
        }
        true
    }
}

impl<const N: usize> Eq for Bitset<N> where [(); (N+63)/64]: Sized {}

impl<const N: usize> Not for Bitset<N>
where [(); (N+63)/64]: Sized {
    type Output = Self;
    fn not(self) -> Self {
        let mut ret = Self::new();
        for i in 0..(N+63)/64 {
            ret.state[i] = !self.state[i];
        }
        ret
    }
}

impl<const N: usize> BitAnd for Bitset<N>
where [(); (N+63)/64]: Sized {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let lhs = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let rhs = std::mem::transmute::<[u64; 2], u128>([rhs.state[0], rhs.state[1]]);
                let res_u128 = lhs & rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                let mut res = Self::new();
                res.state.copy_from_slice(&res_arr);
                return res
            }
        }

        let mut ret = Self::new();
        for i in 0..(N+63)/64 {
            ret.state[i] = self.state[i] & rhs.state[i];
        }
        ret
    }
}

impl<const N: usize> BitAndAssign for Bitset<N>
where [(); (N+63)/64]: Sized {
    fn bitand_assign(&mut self, rhs: Self) {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let lhs = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let rhs = std::mem::transmute::<[u64; 2], u128>([rhs.state[0], rhs.state[1]]);
                let res_u128 = lhs & rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                self.state.copy_from_slice(&res_arr);
                return
            }
        }

        for i in 0..(N+63)/64 {
            self.state[i] &= rhs.state[i];
        }
    }
}

impl<const N: usize> BitOr for Bitset<N>
where [(); (N+63)/64]: Sized {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let lhs = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let rhs = std::mem::transmute::<[u64; 2], u128>([rhs.state[0], rhs.state[1]]);
                let res_u128 = lhs | rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                let mut res = Self::new();
                res.state.copy_from_slice(&res_arr);
                return res
            }
        }

        let mut ret = Self::new();
        for i in 0..(N+63)/64 {
            ret.state[i] = self.state[i] | rhs.state[i];
        }
        ret
    }
}

impl<const N: usize> BitOrAssign for Bitset<N>
where [(); (N+63)/64]: Sized {
    fn bitor_assign(&mut self, rhs: Self) {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let lhs = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let rhs = std::mem::transmute::<[u64; 2], u128>([rhs.state[0], rhs.state[1]]);
                let res_u128 = lhs | rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                self.state.copy_from_slice(&res_arr);
                return
            }
        }

        for i in 0..(N+63)/64 {
            self.state[i] |= rhs.state[i];
        }
    }
}

impl<const N: usize> BitXor for Bitset<N>
where [(); (N+63)/64]: Sized {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let lhs = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let rhs = std::mem::transmute::<[u64; 2], u128>([rhs.state[0], rhs.state[1]]);
                let res_u128 = lhs ^ rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                let mut res = Self::new();
                res.state.copy_from_slice(&res_arr);
                return res
            }
        }

        let mut ret = Self::new();
        for i in 0..(N+63)/64 {
            ret.state[i] = self.state[i] ^ rhs.state[i];
        }
        ret
    }
}

impl<const N: usize> BitXorAssign for Bitset<N>
where [(); (N+63)/64]: Sized {
    fn bitxor_assign(&mut self, rhs: Self) {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let lhs = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let rhs = std::mem::transmute::<[u64; 2], u128>([rhs.state[0], rhs.state[1]]);
                let res_u128 = lhs ^ rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                self.state.copy_from_slice(&res_arr);
                return
            }
        }

        for i in 0..(N+63)/64 {
            self.state[i] ^= rhs.state[i];
        }
    }
}

impl<const N: usize> Shl<usize> for Bitset<N>
where [(); (N+63)/64]: Sized {
    type Output = Self;
    fn shl(self, rhs: usize) -> Self {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let x = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let res_u128 = x << rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                let mut ret2 = Self::new();
                ret2.state.copy_from_slice(&res_arr);
                return ret2
            }
        }

        let mut ret = Self::new();
        let trailing_zeros = rhs >> 6;
        let actual_shift = rhs & 63;
        let l = (N+63)/64;
        if trailing_zeros >= l {
            return ret
        }
        if actual_shift == 0 {
            for i in 0..(l-trailing_zeros) {
                ret.state[l-i-1] = self.state[l-i-1-trailing_zeros];
            }
        } else {
            for i in 0..(l-1-trailing_zeros) {
                ret.state[l-i-1] = (self.state[l-i-1-trailing_zeros]<<actual_shift) | (self.state[l-i-2-trailing_zeros]>>(64-actual_shift));
            }
            ret.state[trailing_zeros] = self.state[0]<<actual_shift;
        }
        ret
    }
}

impl<const N: usize> ShlAssign<usize> for Bitset<N>
where [(); (N+63)/64]: Sized {
    fn shl_assign(&mut self, rhs: usize) {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let x = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let res_u128 = x << rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                self.state.copy_from_slice(&res_arr);
                return
            }
        }

        let trailing_zeros = rhs >> 6;
        let actual_shift = rhs & 63;
        let l = (N+63)/64;
        if actual_shift == 0 {
            for i in 0..(l-trailing_zeros) {
                self.state[l-i-1] = self.state[l-i-1-trailing_zeros];
            }
        } else {
            for i in 0..(l-1-trailing_zeros) {
                self.state[l-i-1] = (self.state[l-i-1-trailing_zeros]<<actual_shift) | (self.state[l-i-2-trailing_zeros]>>(64-actual_shift));
            }
            self.state[trailing_zeros] = self.state[0]<<actual_shift;
        }
        for i in 0..trailing_zeros {
            self.state[i] = 0;
        }
    }
}

impl<const N: usize> Shr<usize> for Bitset<N>
where [(); (N+63)/64]: Sized {
    type Output = Self;
    fn shr(self, rhs: usize) -> Self {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let x = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let res_u128 = x >> rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                let mut ret2 = Self::new();
                ret2.state.copy_from_slice(&res_arr);
                return ret2
            }
        }

        let mut ret = Self::new();
        let leading_zeros = rhs >> 6;
        let actual_shift = rhs & 63;
        let l = (N+63)/64;
        if leading_zeros >= l {
            return ret
        }
        if actual_shift == 0 {
            for i in 0..(l-leading_zeros) {
                ret.state[i] = self.state[i+leading_zeros];
            }
        } else {
            for i in 0..(l-1-leading_zeros) {
                ret.state[i] = (self.state[i+leading_zeros]>>actual_shift) | (self.state[i+1+leading_zeros]<<(64-actual_shift));
            }
            if leading_zeros < l {
                ret.state[l-1-leading_zeros] = self.state[l-1]>>actual_shift;
            }
        }
        ret
    }
}

impl<const N: usize> ShrAssign<usize> for Bitset<N>
where [(); (N+63)/64]: Sized {
    fn shr_assign(&mut self, rhs: usize) {
        // Optimization for 128 wide bitsets
        if (N+63)/64 == 2 {
            unsafe {
                let x = std::mem::transmute::<[u64; 2], u128>([self.state[0], self.state[1]]);
                let res_u128 = x >> rhs;
                let res_arr = std::mem::transmute::<u128, [u64; 2]>(res_u128);
                self.state.copy_from_slice(&res_arr);
                return
            }
        }

        let leading_zeros = rhs >> 6;
        let actual_shift = rhs & 63;
        let l = (N+63)/64;
        if actual_shift == 0 {
            for i in 0..(l-leading_zeros) {
                self.state[i] = self.state[i+leading_zeros];
            }
        } else {
            for i in 0..(l-1-leading_zeros) {
                self.state[i] = (self.state[i+leading_zeros]>>actual_shift) | (self.state[i+1+leading_zeros]<<(64-actual_shift));
            }
            if leading_zeros < l {
                self.state[l-1-leading_zeros] = self.state[l-1]>>actual_shift;
            }
        }
        for i in 0..leading_zeros {
            self.state[l-1-i] = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;

    #[test]
    fn test_shl() {
        let x = Bitset::<256>{state: [1, 0, 0, 0]};
        println!("{:?}", x<<129);
        assert!((x<<129).state[0] == 0);
        assert!((x<<129).state[2] == 2);
    }

    #[test]
    fn test_shl_shr() {
        let x = Bitset::<256>{state: [1, 0, 0, 0]};
        let y = (x<<129)>>129;
        println!("{:?}", y);
        assert!(x == y);
    }

    #[test]
    fn test_shl_or() {
        let x = Bitset::<256>{state: [1, 0, 0, 0]};
        let mut y = Bitset::<256>{state: [0, 0, 0, 0]};
        for i in 0..256 {
            y |= x << i;
        }
        println!("{:?}", y);
        assert!(y.state[0] == u64::MAX);
        assert!(y.state[1] == u64::MAX);
    }

    #[test]
    fn test_shl_assign() {
        let mut x = Bitset::<256>{state: [1, 0, 0, 0]};
        x <<= 129;
        println!("{:?}", x);
        assert!(x.state[0] == 0);
        assert!(x.state[2] == 2);
    }

    #[test]
    fn test_shl_assign_or() {
        let mut x = Bitset::<256>{state: [1, 0, 0, 0]};
        let mut y = Bitset::<256>{state: [1, 0, 0, 0]};
        for _ in 0..256 {
            x <<= 1;
            y |= x;
        }
        println!("{:?}", y);
        assert!(y.state[0] == u64::MAX);
        assert!(y.state[1] == u64::MAX);
    }

    #[test]
    fn test_shr_or() {
        let x = Bitset::<256>{state: [0, 0, 0, 1]};
        let mut y = Bitset::<256>{state: [0, 0, 0, 0]};
        for i in 0..256 {
            y |= x >> i;
        }
        println!("{:?}", y);
        assert!(y.state[0] == u64::MAX);
        assert!(y.state[3] == 1);
    }

    #[test]
    fn test_shl_assign_shr_assign() {
        let mut x = Bitset::<256>{state: [1, 0, 0, 0]};
        x <<= 130;
        x >>= 129;
        println!("{:?}", x);
        assert!(x.state[0] == 2);
        assert!(x.state[1] == 0);
    }

    #[test]
    fn test_shr() {
        let x = Bitset::<64>{state: [2]};
        println!("{:?}", x>>1);
        assert!((x>>1).state[0] == 1);
    }

    #[test]
    fn test_shr_assign() {
        let mut x = Bitset::<64>{state: [2]};
        x >>= 1;
        println!("{:?}", x);
        assert!(x.state[0] == 1);
    }

    #[bench]
    fn bench_get_bit(b: &mut Bencher) {
        let x = Bitset::<128>{state: [1, 0]};
        let mut y = false;
        b.iter(|| {
            for i in 0..128 {
                y |= x.get(i);
            }
            y
        })
    }

    #[bench]
    fn bench_set_bit(b: &mut Bencher) {
        let mut x = Bitset::<128>{state: [1, 0]};
        b.iter(|| {
            for i in 0..128 {
                x.unset_bit(i);
            }
            x
        })
    }

    #[bench]
    fn bench_shl_or_bitset_8(b: &mut Bencher) {
        let x = Bitset::<1024>{state: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]};
        let mut y = Bitset::<1024>{state: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]};
        b.iter(|| {
            for i in 0..128 {
                y |= x << i;
            }
            y
        })
    }

    #[bench]
    fn bench_shl_or_bitset_1(b: &mut Bencher) {
        let x = Bitset::<{11*11}>{state: [1, 0]};
        let mut y = Bitset::<{11*11}>{state: [0, 0]};
        b.iter(|| {
            for i in 0..128 {
                y |= x << i;
            }
            y
        })
    }

    #[bench]
    fn bench_shl_or_u64(b: &mut Bencher) {
        let x = 1_u64;
        let mut y = 0_u64;
        b.iter(|| {
            for i in 0..64 {
                y |= x << i;
            }
            y
        })
    }
}
