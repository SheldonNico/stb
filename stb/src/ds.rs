// https://internals.rust-lang.org/t/ergonomics-of-wrapping-operations/1756/13
use std::num::Wrapping as W;
const SIPHASH_C_ROUNDS: usize = 1;
const SIPHASH_D_ROUNDS: usize = 1;
const USIZE_BITS: usize = std::mem::size_of::<usize>() * 8;

macro_rules! rotate {
    (left, $val:expr, $n:expr) => {
        ($val << $n) | ($val >> (USIZE_BITS - $n))
    };
    (right, $val:expr, $n:expr) => {
        ($val >> $n) | ($val << (USIZE_BITS - $n))
    };
}

pub fn hash_string(string: &str, seed: usize) -> usize {
    let mut hash = seed;
    for &c in string.as_bytes() {
        hash = rotate!(left, hash, 9) + c as usize;
    }

    // Thomas Wang 64-to-32 bit mix function, hopefully also works in 32 bits
    hash ^= seed;
    hash = (!hash) + (hash << 18);
    hash ^= hash ^ rotate!(right, hash, 31);
    hash = hash * 21;
    hash ^= hash ^ rotate!(right, hash, 11);
    hash += hash << 6;
    hash ^= rotate!(right, hash, 22);

    hash + seed
}

pub fn hash_bytes(bytes: &[u8], seed: usize) -> usize {
    if cfg!(feature = "siphash_2_4") {
        siphash_bytes(bytes, seed)
    } else {
        if bytes.len() == 4 {
            let mut h32 = W(bytes[0] as u32) | (W(bytes[1] as u32) << 8) | (W(bytes[2] as u32) << 16) | (W(bytes[3] as u32) << 24);
            let s32 = W(seed as u32);

            /*
             * // HASH32-A  Bob Jenkin's hash function w/o large constants
             * h32 ^= s32;
             * h32 -= h32 << 6;
             * h32 ^= h32 >> 17;
             * h32 -= h32 << 9;
             * h32 ^= s32;
             * h32 ^= h32 << 4;
             * h32 -= h32 << 3;
             * h32 ^= h32 << 10;
             * h32 ^= h32 >> 15;
             */

            // HASH32-BB  Bob Jenkin's presumably-accidental version of Thomas Wang hash with rotates turned into shifts.
            // Note that converting these back to rotates makes it run a lot slower, presumably due to collisions, so I'm
            // not really sure what's going on.
            h32 ^= s32;
            h32 = (h32 ^ W(61)) ^ (h32 >> 16);
            h32 = h32 + (h32 << 3);
            h32 = h32 ^ (h32 >> 4);
            h32 = h32 * W(0x27d4eb2d);
            h32 ^= s32;
            h32 = h32 ^ (h32 >> 15);

            /*
             * // HASH32-C   -  Murmur3
             * h32 ^= s32;
             * h32 *= 0xcc9e2d51;
             * h32 = (h32 << 17) | (h32 >> 15);
             * h32 *= 0x1b873593;
             * h32 ^= s32;
             * h32 = (h32 << 19) | (h32 >> 13);
             * h32 = h32*5 + 0xe6546b64;
             * h32 ^= h32 >> 16;
             * h32 *= 0x85ebca6b;
             * h32 ^= s32;
             * h32 ^= h32 >> 13;
             * h32 *= 0xc2b2ae35;
             * h32 ^= h32 >> 16;
             */

            let r = ((W(h32.0 as usize) << 16 << 16) | W(h32.0 as usize)) ^ W(seed);
            r.0
        } else if bytes.len() == 8 && std::mem::size_of::<usize>() == 8 {
            // usize == u64
            let mut h64 = W(((bytes[0] as i32) | ((bytes[1] as i32) << 8) | ((bytes[2] as i32) << 16) | ((bytes[3] as i32) << 24)) as u64);
            h64 |= (W(bytes[4] as u64) | (W(bytes[5] as u64) << 8) | (W(bytes[6] as u64) << 16) | (W(bytes[7] as u64) << 24)) << 16 << 16;
            let s64 = W(seed as u64);

            h64 ^= s64;
            h64 = (!h64) + (h64 << 21);
            h64 ^= rotate!(right, h64, 24);
            h64 *= 265;
            h64 ^= rotate!(right, h64, 14);
            h64 ^= s64;
            h64 *= 21;
            h64 ^= rotate!(right, h64, 28);
            h64 += h64 << 31;
            h64 = (!h64) + (h64 << 18);

            h64.0 as usize
        } else {
            siphash_bytes(bytes, seed)
        }
    }
}

fn siphash_bytes(bytes: &[u8], seed: usize) -> usize {
    // hash that works on 32- or 64-bit registers without knowing which we have
    // (computes different results on 32-bit and 64-bit platform)
    // derived from siphash, but on 32-bit platforms very different as it uses 4 32-bit state not 4
    // 64-bit

    let mut v0: W<usize> = (((W(0x736f6d65usize) << 16) << 16) + W(0x70736575usize)) ^ W(seed);
    let mut v1: W<usize> = (((W(0x646f7261usize) << 16) << 16) + W(0x6e646f6dusize)) ^ W(!seed);
    let mut v2: W<usize> = (((W(0x6c796765usize) << 16) << 16) + W(0x6e657261usize)) ^ W(seed);
    let mut v3: W<usize> = (((W(0x74656462usize) << 16) << 16) + W(0x79746573usize)) ^ W(!seed);

    if cfg!(feature = "siphash_2_4") {
        // hardcoded with key material in the siphash test vectors
        v0 ^= W(0x0706050403020100usize) ^ W(seed);
        v1 ^= W(0x0f0e0d0c0b0a0908usize) ^ W(!seed);
        v2 ^= W(0x0706050403020100usize) ^ W(seed);
        v3 ^= W(0x0f0e0d0c0b0a0908usize) ^ W(!seed);
    }

    macro_rules! sip_round {
        () => {{
            v0 += v1; v1 = rotate!(left, v1, 13); v1 ^= v0; v0 = rotate!(left, v0, USIZE_BITS / 2);
            v2 += v3; v3 = rotate!(left, v3, 16); v3 ^= v2;
            v2 += v1; v1 = rotate!(left, v1, 17); v1 ^= v2; v2 = rotate!(left, v2, USIZE_BITS / 2);
            v0 += v3; v3 = rotate!(left, v3, 21); v3 ^= v0;
        }};
    }

    let step = std::mem::size_of::<usize>();
    debug_assert!(step == 8 || step == 4);
    for chunk in bytes.chunks_exact(step) {
        let mut data = ((chunk[0] as i32) | ((chunk[1] as i32) << 8) | ((chunk[2] as i32) << 16) | ((chunk[3] as i32) << 24)) as usize;
        if chunk.len() == 8 {
            data |= ((chunk[4] as usize) | ((chunk[5] as usize) << 8) | ((chunk[6] as usize) << 16) | ((chunk[7] as usize) << 24)) << 16 << 16; // discarded if usize = u32
        }

        v3 ^= W(data);
        for _ in 0..SIPHASH_C_ROUNDS {
            sip_round!()
        }
        v0 ^= W(data);
    }

    let mut data = bytes.len() << (USIZE_BITS - 8);
    let chunk = &bytes[(8*(bytes.len() / 8))..];
    if chunk.len() >= 7 { data |= ((chunk[6] as usize) << 24) << 24; }
    if chunk.len() >= 6 { data |= ((chunk[5] as usize) << 20) << 20; }
    if chunk.len() >= 5 { data |= ((chunk[4] as usize) << 16) << 16; }
    // WTF: i32, check the original code, the literal conversion.
    if chunk.len() >= 4 { data |= ((chunk[3] as i32) << 24) as usize; }
    if chunk.len() >= 3 { data |= ((chunk[2] as i32) << 16) as usize; }
    if chunk.len() >= 2 { data |= ((chunk[1] as i32) << 8) as usize; }
    if chunk.len() >= 1 { data |=   chunk[0] as usize      ; }
    v3 ^= W(data);
    for _ in 0..SIPHASH_C_ROUNDS {
        sip_round!()
    }
    v0 ^= W(data);

    v2 ^= 0xff;
    for _ in 0..SIPHASH_D_ROUNDS {
        sip_round!()
    }

    if cfg!(feature = "siphash_2_4") {
        (v0 ^ v1 ^ v2 ^ v3).0
    } else {
        (v1 ^ v2 ^ v3).0 // slightly stronger since v0^v3 in above cancels out final round operation? I tweeted at the authors of SipHash about this but they didn't reply
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::quickcheck;

    quickcheck! {
        fn same_hash(data: Vec<u8>, seed: usize) -> bool {
            let h_sys = unsafe {
                let p = data.as_ptr() as *mut _;
                let len = data.len();

                stb_sys::stbds_hash_bytes(p, len, seed)
            };
            let h_stb = hash_bytes(&data, seed);

            eprintln!("{:?} {}: {}, {} =, {}", &data, seed, h_stb, h_sys, h_stb == h_sys);
            h_stb == h_sys
        }
    }
}
