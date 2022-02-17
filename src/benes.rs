//! This file is for Beneš network related functions
//!
//! For the implementation strategy, see
//! “McBits Revisited” by Tung Chou (2017)
//! <https://eprint.iacr.org/2017/793.pdf>

use crate::gf::Gf;
use crate::transpose;
use crate::util;

/// Layers of the Beneš network.
/// Used in the variants mceliece348864 and mceliece348864f.
fn layer(data: &mut [u64; 64], bits: &[u64], lgs: usize) {
    let mut d: u64;
    let mut index = 0;

    let s = 1 << lgs;

    let mut i = 0usize;
    while i < 64 {
        for j in i..(i + s) {
            d = data[j + 0] ^ data[j + s];
            d &= bits[index];
            index += 1;

            data[j + 0] ^= d;
            data[j + s] ^= d;
        }
        i += s * 2;
    }
}

/// Inner layers of the Beneš network.
/// Used in the variants different from mceliece348864 and mceliece348864f.
fn layer_in(data: &mut [[u64; 64]; 2], bits: &[u64], lgs: usize) {
    let mut d: u64;
    let mut index = 0;

    let s = 1 << lgs;

    let mut i = 0usize;
    while i < 64 {
        for j in i..(i + s) {
            d = data[0][j + 0] ^ data[0][j + s];
            d &= bits[index];
            index += 1;

            data[0][j + 0] ^= d;
            data[0][j + s] ^= d;

            d = data[1][j + 0] ^ data[1][j + s];
            d &= bits[index];
            index += 1;

            data[1][j + 0] ^= d;
            data[1][j + s] ^= d;
        }
        i += s * 2;
    }
}

/// Exterior layers of the Beneš network
// TODO this implementation is quite different from the C implementation
// attempt maybe iterators
// for item in 2darray.iter().flatten() { … }
// or try https://docs.rs/bytemuck/1.7.2/bytemuck/ crate.
/// Used in the variants different from mceliece348864 and mceliece348864f.
fn layer_ex(data: &mut [[u64; 64]; 2], bits: &mut [u64], lgs: usize) {
    let mut d: u64;
    let mut index = 0;
    let mut index2 = 32;

    let s = 1 << lgs;
    if s == 64 {
        for j in 0..64 {
            d = data[0][j + 0] ^ data[1][j];
            d &= bits[index];
            index += 1;

            data[0][j + 0] ^= d;
            data[1][j] ^= d;
        }
    } else {
        let mut i: usize = 0;
        while i < 64 {
            for j in i..(i + s) {
                d = data[0][j + 0] ^ data[0][j + s];
                d &= bits[index];
                index += 1;

                data[0][j + 0] ^= d;
                data[0][j + s] ^= d;

                d = data[1][j + 0] ^ data[1][j + s];
                d &= bits[index2]; // 64
                index2 += 1;

                data[1][j + 0] ^= d;
                data[1][j + s] ^= d;
            }
            i += s * 2;
        }
    }
}

/// Apply Beneš network in-place to array `r` based on configuration `bits` and `rev`.
/// Here, `r` is a sequence of bits to be permuted.
/// `bits` defines the condition bits configuring the Beneš network and
/// `rev` toggles between normal application (0) or its inverse (!0).
/// Used in the variants mceliece348864 and mceliece348864f (“small”).
pub fn apply_benes_small<const GFBITS: usize>(r: &mut [u8; (1 << GFBITS) / 8], bits: &[u8], rev: usize) {
    let mut bs = [0u64; 64];
    let mut cond = [0u64; 64];

    if rev == 0 {
        for i in 0..64 {
            bs[i] = util::load8(&r[i*8..(i + 1)*8]);
        }

        transpose::transpose_64x64_inplace(&mut bs);

        for low in 0..6 {
            for i in 0..64 {
                cond[i] = util::load4(&bits[low*256 + i*4..]) as u64;
            }
            transpose::transpose_64x64_inplace(&mut cond);
            layer(&mut bs, &cond, low);
        }

        transpose::transpose_64x64_inplace(&mut bs);

        for low in 0..6 {
            for i in 0..32 {
                cond[i] = util::load8(&bits[(low + 6)*256 + i*8..]);
            }
            layer(&mut bs, &cond, low);
        }
        for low in (0..5).rev() {
            for i in 0..32 {
                cond[i] = util::load8(&bits[(4 - low + 6 + 6)*256 + i*8..]);
            }
            layer(&mut bs, &cond, low);
        }

        transpose::transpose_64x64_inplace(&mut bs);

        for low in (0..6).rev() {
            for i in 0..64 {
                cond[i] = util::load4(&bits[(5 - low + 6 + 6 + 5)*256 + i*4..]) as u64;
            }
            transpose::transpose_64x64_inplace(&mut cond);
            layer(&mut bs, &cond, low);
        }

        transpose::transpose_64x64_inplace(&mut bs);

        for i in 0..64 {
            util::store8(&mut r[i*8..], bs[i]);
        }

    } else {
        for i in 0..64 {
            bs[i] = util::load8(&r[i*8..(i + 1)*8]);
        }

        transpose::transpose_64x64_inplace(&mut bs);

        for low in 0..6 {
            for i in 0..64 {
                cond[i] = util::load4(&bits[(2 * GFBITS - 2) * 256 - low * 256 + i*4..]) as u64;
            }
            transpose::transpose_64x64_inplace(&mut cond);
            layer(&mut bs, &cond, low);
        }

        transpose::transpose_64x64_inplace(&mut bs);

        for low in 0..6 {
            for i in 0..32 {
                cond[i] = util::load8(&bits[(2 * GFBITS - 2 - 6) * 256 - low * 256 + i*8..]);
            }
            layer(&mut bs, &cond, low);
        }
        for low in (0..5).rev() {
            for i in 0..32 {
                cond[i] = util::load8(&bits[(2 * GFBITS - 2 - 6 - 6) * 256 - (4-low) * 256 + i*8..]);
                layer(&mut bs, &cond, low);
            }
        }

        transpose::transpose_64x64_inplace(&mut bs);

        for low in (0..6).rev() {
            for i in 0..64 {
                cond[i] = util::load4(&bits[(2 * GFBITS - 2 - 6 - 6 - 5) * 256 - (5-low) * 265 +  i*4..]) as u64;
            }
            transpose::transpose_64x64_inplace(&mut cond);
            layer(&mut bs, &cond, low);
        }

        transpose::transpose_64x64_inplace(&mut bs);

        for i in 0..64 {
            util::store8(&mut r[i*8..], bs[i]);
        }
    }
}

/// Apply Beneš network in-place to array `r` based on configuration `bits` and `rev`.
/// Here, `r` is a sequence of bits to be permuted.
/// `bits` defines the condition bits configuring the Beneš network and
/// `rev` toggles between normal application (0) or its inverse (!0).
/// Used in the variants different from mceliece348864 and mceliece348864f (“big”).
pub fn apply_benes_big<const GFBITS: usize>(r: &mut [u8; (1 << GFBITS) / 8], bits: &[u8], rev: usize) {
    let mut r_int_v = [[0u64; 64]; 2];
    let mut r_int_h = [[0u64; 64]; 2];
    let mut b_int_v = [0u64; 64];
    let mut b_int_h = [0u64; 64];

    let mut calc_index = if rev == 0 { 0 } else { 12288 };

    let mut i: usize = 0;
    for chunk in r.chunks_mut(16) {
        let (subchunk1, subchunk2) = chunk.split_at_mut(8);
        r_int_v[0][i] = util::load8(subchunk1);
        r_int_v[1][i] = util::load8(subchunk2);

        i += 1;
    }

    transpose::transpose(&mut r_int_h[0], r_int_v[0]);
    transpose::transpose(&mut r_int_h[1], r_int_v[1]);

    let mut iter = 0;
    while iter <= 6 {
        i = 0;
        for chunk in bits[calc_index..(calc_index + 512)].chunks(8) {
            b_int_v[i] = util::load8(chunk);
            i += 1;
            if i == 64 {
                break;
            }
        }

        calc_index = if rev == 0 {
            calc_index + 512
        } else {
            calc_index - 1024
        };

        transpose::transpose(&mut b_int_h, b_int_v);

        layer_ex(&mut r_int_h, &mut b_int_h, iter);

        iter += 1;
    }

    transpose::transpose(&mut r_int_v[0], r_int_h[0]);
    transpose::transpose(&mut r_int_v[1], r_int_h[1]);

    let mut iter: usize = 0;
    while iter <= 5 {
        for (i, chunk) in bits[calc_index..(calc_index + 512)].chunks(8).enumerate() {
            b_int_v[i] = util::load8(chunk);
        }

        calc_index = if rev == 0 {
            calc_index + 512
        } else {
            calc_index - 1024
        };

        layer_in(&mut r_int_v, &mut b_int_v, iter);

        iter += 1;
    }

    for iter in (0..=4).rev() {
        for (i, chunk) in bits[calc_index..(calc_index + 512)].chunks(8).enumerate() {
            b_int_v[i] = util::load8(chunk);
        }
        calc_index = if rev == 0 {
            calc_index + 512
        } else {
            calc_index - 1024
        };

        layer_in(&mut r_int_v, &mut b_int_v, iter);
    }

    transpose::transpose(&mut r_int_h[0], r_int_v[0]);
    transpose::transpose(&mut r_int_h[1], r_int_v[1]);

    for iter in (0..=6).rev() {
        for (i, chunk) in bits[calc_index..(calc_index + 512)].chunks(8).enumerate() {
            b_int_v[i] = util::load8(chunk);
        }
        calc_index = if rev == 0 {
            calc_index + 512
        } else {
            calc_index - 1024
        };

        transpose::transpose(&mut b_int_h, b_int_v);

        layer_ex(&mut r_int_h, &mut b_int_h, iter);
    }

    transpose::transpose(&mut r_int_v[0], r_int_h[0]);
    transpose::transpose(&mut r_int_v[1], r_int_h[1]);

    for (i, chunk) in r.chunks_mut(16).enumerate() {
        let (subchunk1, subchunk2) = chunk.split_at_mut(8);
        util::store8(subchunk1, r_int_v[0][i]);
        util::store8(subchunk2, r_int_v[1][i]);
    }
}

/// Apply Beneš network in-place to array `r` based on configuration `bits` and `rev`.
/// Here, `r` is a sequence of bits to be permuted.
/// `bits` defines the condition bits configuring the Beneš network and
/// `rev` toggles between normal application (0) or its inverse (!0).
pub fn apply_benes<const GFBITS: usize>(r: &mut [u8], bits: &[u8], rev: usize) {
    match GFBITS {
        12 => apply_benes_small(r, bits, rev),
        _ => apply_benes_big(r, bits, rev),
    }
}

pub fn support_gen<const SYS_N: usize, const GFBITS: usize>(s: &mut [Gf; SYS_N], c: &[u8]) {
    let mut a: Gf;
    let mut l = [[0u8; (1 << GFBITS) / 8]; GFBITS];

    for i in 0..(1 << GFBITS) {
        a = util::bitrev(i as Gf);

        for j in 0..GFBITS {
            l[j][i / 8] |= (((a >> j) & 1) << (i % 8)) as u8;
        }
    }

    for j in 0..GFBITS {
        apply_benes(&mut l[j], c, 0);
    }

    for i in 0..SYS_N {
        s[i] = 0;
        for j in (0..=(GFBITS - 1)).rev() {
            s[i] <<= 1;
            s[i] |= ((l[j][i / 8] >> (i % 8)) & 1) as u16;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryFrom;

    #[test]
    fn test_apply_benes() {
        // Basic testcase
        let mut l = [31u8; (1 << GFBITS) / 8];
        let mut bits = [0u8; CRYPTO_SECRETKEYBYTES + 40];
        bits[0] = 255;

        let mut compare_array = [31u8; (1 << GFBITS) / 8];
        compare_array[0] = 47;
        compare_array[1] = 47;

        apply_benes(&mut l, &mut bits, 0);

        assert_eq!(l, compare_array);
    }

    #[test]
    fn test_layer_in() {
        let test_348864 = |variant: &str| {
            let get = |name: &str| {
                let fullname = format!("{}_{}", variant, name);
                crate::TestData::new().u64vec(&fullname)
            };
            let get64 = |name: &str| {
                <[u64; 64]>::try_from(get(name).as_slice()).unwrap()
            };

            let mut data_arg = get64("benes_layer_data_before");
            let bits_arg = get("benes_layer_bits");
            layer(&mut data_arg, &bits_arg, 0);
            let actual_data = data_arg;

            let expected_data = get64("benes_layer_data_after");

            assert_eq!(actual_data, expected_data);
        };

        let test_other = |variant: &str| {
            let get = |name: &str| {
                let fullname = format!("{}_{}", variant, name);
                crate::TestData::new().u64vec(&fullname)
            };
            let get64 = |name: &str| {
                <[u64; 64]>::try_from(get(name).as_slice()).unwrap()
            };

            let data0_arg = get64("benes_layer_in_data0_before");
            let data1_arg = get64("benes_layer_in_data1_before");
            let mut data_arg = [data0_arg, data1_arg];
            let bits_arg = get("benes_layer_in_bits");
            layer_in(&mut data_arg, &bits_arg, 0);
            let actual_data = data_arg;

            let expected_data0 = get64("benes_layer_in_data0_after");
            let expected_data1 = get64("benes_layer_in_data1_after");
            let expected_data = [expected_data0, expected_data1];

            assert_eq!(actual_data, expected_data);
        };

        let cme348864 = crate::ClassicMcEliece::mceliece348864();
        test_348864(cme348864.crypto_primitive);
        let cme348864f = crate::ClassicMcEliece::mceliece348864f();
        test_348864(cme348864f.crypto_primitive);

        let cme460896 = crate::ClassicMcEliece::mceliece460896();
        test_other(cme460896.crypto_primitive);
        let cme460896f = crate::ClassicMcEliece::mceliece460896f();
        test_other(cme460896f.crypto_primitive);
        let cme6688128 = crate::ClassicMcEliece::mceliece6688128();
        test_other(cme6688128.crypto_primitive);
        let cme6688128f = crate::ClassicMcEliece::mceliece6688128f();
        test_other(cme6688128f.crypto_primitive);
        let cme6960119 = crate::ClassicMcEliece::mceliece6960119();
        test_other(cme6960119.crypto_primitive);
        let cme6960119f = crate::ClassicMcEliece::mceliece6960119f();
        test_other(cme6960119f.crypto_primitive);
        let cme8192128 = crate::ClassicMcEliece::mceliece8192128();
        test_other(cme8192128.crypto_primitive);
        let cme8192128f = crate::ClassicMcEliece::mceliece8192128f();
        test_other(cme8192128f.crypto_primitive);
    }
}
