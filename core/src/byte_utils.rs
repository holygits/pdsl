// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of pDSL.
//
// pDSL is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// pDSL is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with pDSL.  If not, see <http://www.gnu.org/licenses/>.

//! Utilities to operate on byte or slices of bytes.

/// Flips all bytes in the byte slice inplace.
fn invert_bytes(bytes: &mut [u8]) {
	for byte in bytes.into_iter() {
		*byte = !*byte;
	}
}

/// Negate the given bytes inplace.
///
/// Interprets the bytes as twos-complement number.
pub fn negate_bytes(bytes: &mut [u8]) {
	invert_bytes(bytes);
	bytes_add_bytes(bytes, &[0x01]);
}

macro_rules! impl_slice_as_array {
	( $name:ident, $n:expr ) => {
		/// Interprets the slice as exact size array if possible.
		///
		/// Otherwise returns `None`.
		pub fn $name<T>(slice: &[T]) -> Option<&[T; $n]> {
			if slice.len() != $n {
				return None
			}
			Some(unsafe {
				core::mem::transmute::<*const T, &[T; $n]>(slice.as_ptr())
			})
		}
	};
}

impl_slice_as_array!(slice4_as_array4, 4);
impl_slice_as_array!(slice8_as_array8, 8);
impl_slice_as_array!(slice16_as_array16, 16);

/// Generic carry add/sub implementation
/// between a byte slice and a byte.
///
/// Used by `bytes_add_byte` and `bytes_sub_byte`.
///
/// Returns `true` if there was an overflow.
///
/// # Note
///
/// Interprets the byte slices and the byte
/// as big-endian twos-complement numbers.
///
/// # Panics
///
/// If `lhs` is an empty slice.
fn bytes_ops_byte<F>(lhs: &mut [u8], rhs: u8, ops: F) -> bool
where
	F: Copy + Fn(u8, u8) -> (u8, bool)
{
	assert!(lhs.len() >= 1);
	let mut carry = rhs;
	for lhs in lhs.into_iter().rev() {
		if carry == 0 {
			return false
		}
		let (res, ovfl) = ops(*lhs, carry);
		*lhs = res;
		carry = u8::from(ovfl);
	}
	if carry == 0 { false } else { true }
}

/// Generic carry-operation implementation for two byte slices
/// of equal sizes.
///
/// # Note
///
/// Interprets the byte slices as big-endian twos-complement numbers.
///
/// # Panics
///
/// - If `lhs` and `rhs` do not have the same lengths.
/// - If `lhs` or `rhs` is empty slice.
fn bytes_ops_bytes_eq<F>(lhs: &mut [u8], rhs: &[u8], ops: F) -> bool
where
	F: Copy + Fn(u8, u8) -> (u8, bool)
{
	assert_eq!(lhs.len(), rhs.len());
	assert!(lhs.len() > 0);
	debug_assert!(rhs.len() > 0);
	let mut carry = 0;
	for (lhs, rhs) in lhs.into_iter().zip(rhs.into_iter()).rev() {
		let (res1, carry1) = ops(*lhs, carry);
		let (res2, carry2) = ops(res1, *rhs);
		debug_assert!(!(carry1 && carry2));
		*lhs = res2;
		carry = u8::from(carry1 || carry2);
	}
	if carry == 0 { false } else { true }
}

/// Generic carry-operation implementation for two byte slices.
///
/// Used as underlying implementation of
/// `bytes_add_bytes` and `bytes_sub_bytes`.
///
/// # Note
///
/// Interprets the byte slices as big-endian twos-complement numbers.
///
/// # Panics
///
/// - If the length of `lhs` is less than the length of `rhs`.
/// - If `lhs` or `rhs` is empty slice.
fn bytes_ops_bytes<F>(lhs: &mut [u8], rhs: &[u8], ops: F) -> bool
where
	F: Copy + Fn(u8, u8) -> (u8, bool),
{
	let lhs_len = lhs.len();
	let rhs_len = rhs.len();
	assert!(lhs_len > 0);
	assert!(rhs_len > 0);
	assert!(lhs_len >= rhs_len);
	if rhs_len == 1 {
		return bytes_ops_byte(lhs, rhs[0], ops)
	}
	if lhs_len == rhs_len {
		return bytes_ops_bytes_eq(lhs, rhs, ops)
	}
	let (lhs_msb, lhs_lsb) = lhs.split_at_mut(lhs_len - rhs_len);
	assert_eq!(lhs_lsb.len(), rhs_len);
	let ovfl = bytes_ops_bytes_eq(lhs_lsb, rhs, ops);
	if ovfl {
		return bytes_ops_byte(lhs_msb, 0x1, ops);
	}
	false
}

/// Adds the given bytes slices inplace.
///
/// Returns `true` if there was an overflow.
///
/// # Note
///
/// Interprets the byte slices as big-endian twos-complement numbers.
///
/// # Panics
///
/// - If the length of `lhs` is less than the length of `rhs`.
/// - If `lhs` or `rhs` is empty slice.
pub fn bytes_add_bytes(lhs: &mut [u8], rhs: &[u8]) -> bool {
	bytes_ops_bytes(lhs, rhs, u8::overflowing_add)
}

/// Subtracts the given bytes slices inplace.
///
/// Returns `true` if there was an overflow.
///
/// # Note
///
/// Interprets the byte slices as big-endian twos-complement numbers.
///
/// # Panics
///
/// - If the length of `lhs` is less than the length of `rhs`.
/// - If `lhs` or `rhs` is empty slice.
pub fn bytes_sub_bytes(lhs: &mut [u8], rhs: &[u8]) -> bool {
	bytes_ops_bytes(lhs, rhs, u8::overflowing_sub)
}

#[cfg(all(test, feature = "std"))]
mod tests {
	use super::*;

	use crate::test_utils::run_test;

	#[test]
	fn test_negate_bytes() {
		run_test(|| {
			fn negate_bytes_copy(bytes: &[u8]) -> Vec<u8> {
				let mut buf = bytes.to_vec();
				negate_bytes(&mut buf);
				buf
			}
			fn test_for(bytes: &[u8], expected: &[u8]) {
				assert_eq!(negate_bytes_copy(bytes), expected)
			}
			// Test for '0'
			test_for(&[0x00], &[0x00]);
			// Test for '1'
			test_for(&[0x00, 0x01], &[0xFF, 0xFF]);
			// Test for '-1' == '0xFF'
			test_for(&[0xFF, 0xFF], &[0x00, 0x01]);
			// Test for '42' == '0x2A'
			//
			// 0000 0000 0010 1010 | input
			// 1111 1111 1101 0101 | flipped
			// 1111 1111 1101 0110 | +1
			//    F    F    D    6 | hex
			test_for(&[0x00, 0x2A], &[0xFF, 0xD6]);
		})
	}

	#[test]
	fn test_slice_as_array() {
		run_test(|| {
			assert_eq!(slice4_as_array4::<i32>(&[]), None);
			assert_eq!(slice4_as_array4(&[1, 2, 3, 4, 5]), None);
			assert_eq!(slice4_as_array4(&[1, 2, 3, 4]), Some(&[1, 2, 3, 4]));
			assert_eq!(slice4_as_array4(&[1, 2, 3]), None);
		})
	}

	#[test]
	fn test_bytes_add_bytes_eq() {
		run_test(|| {
			fn test_for(lhs: &[u8], rhs: &[u8], expected: &[u8]) {
				fn bytes_add_bytes_copy(lhs: &[u8], rhs: &[u8]) -> Vec<u8> {
					let mut lhs_vec = lhs.to_vec();
					bytes_add_bytes(&mut lhs_vec, rhs);
					lhs_vec
				}
				assert_eq!(
					bytes_add_bytes_copy(lhs, rhs).as_slice(),
					expected
				);
				// Changing lhs with rhs should not change the result.
				assert_eq!(
					bytes_add_bytes_copy(rhs, lhs).as_slice(),
					expected
				);
			}
			// 0 + 0 == 0
			test_for(
				&[0x00, 0x00, 0x00, 0x00],
				&[0x00, 0x00, 0x00, 0x00],
				&[0x00, 0x00, 0x00, 0x00],
			);
			// 0 + 0x42 == 0x42
			test_for(
				&[0x00, 0x00, 0x00, 0x00],
				&[0x00, 0x00, 0x00, 0x42],
				&[0x00, 0x00, 0x00, 0x42],
			);
			// u32::MAX + 1 == 0
			test_for(
				&[0xFF, 0xFF, 0xFF, 0xFF],
				&[0x00, 0x00, 0x00, 0x01],
				&[0x00, 0x00, 0x00, 0x00],
			);
			// 0 + u32::MAX == u32::MAX
			test_for(
				&[0x00, 0x00, 0x00, 0x00],
				&[0xFF, 0xFF, 0xFF, 0xFF],
				&[0xFF, 0xFF, 0xFF, 0xFF],
			);
			// 0x12345678 + 0x9ABCDEF0 = 0xACF13568
			test_for(
				&[0x12, 0x34, 0x56, 0x78],
				&[0x9A, 0xBC, 0xDE, 0xF0],
				&[0xAC, 0xF1, 0x35, 0x68],
			);
		})
	}

	#[test]
	fn test_bytes_add_bytes() {
		run_test(|| {
			fn test_for(lhs: &[u8], rhs: &[u8], expected: &[u8]) {
				fn bytes_add_bytes_copy(lhs: &[u8], rhs: &[u8]) -> Vec<u8> {
					let mut lhs_vec = lhs.to_vec();
					bytes_add_bytes(&mut lhs_vec, rhs);
					lhs_vec
				}
				assert_eq!(
					bytes_add_bytes_copy(lhs, rhs).as_slice(),
					expected
				);
			}
			// 0 + 0 == 0
			test_for(
				&[0x00, 0x00, 0x00, 0x00],
				&[0x00],
				&[0x00, 0x00, 0x00, 0x00],
			);
			// 0 + 0x42 == 0x42
			test_for(
				&[0x00, 0x00, 0x00, 0x00],
				&[0x42],
				&[0x00, 0x00, 0x00, 0x42],
			);
			// 0xAB_CD_00_00 + 0x00_00_98_76 == 0xAB_CD_98_76
			test_for(
				&[0xAB, 0xCD, 0x00, 0x00],
				&[0x98, 0x76],
				&[0xAB, 0xCD, 0x98, 0x76],
			);
			// 0xFFFF + 0xFFFF == 0x0001_FFFE
			test_for(
				&[0x00, 0x00, 0xFF, 0xFF],
				&[0xFF, 0xFF],
				&[0x00, 0x01, 0xFF, 0xFE],
			);
		})
	}
}
