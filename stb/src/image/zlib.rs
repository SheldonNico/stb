use super::{Result, Error};

const ZFAST_BITS: usize = 9;
const ZFAST_MASK: usize = (1 << ZFAST_BITS) - 1;
const ZNSYMS: usize = 288;
const ZDEFAULT_LENGTH: [u8; ZNSYMS] = [
   8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8, 8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,
   8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8, 8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,
   8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8, 8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,
   8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8, 8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,
   8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8, 9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
   9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9, 9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
   9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9, 9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
   9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9, 9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
   7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7, 7,7,7,7,7,7,7,7,8,8,8,8,8,8,8,8,
];
const ZDEFAULT_DISTANCE: [u8; 32] = [
   5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5
];
const ZLENGTH_BASE: [usize; 31] = [
    3,4,5,6,7,8,9,10,11,13,
    15,17,19,23,27,31,35,43,51,59,
    67,83,99,115,131,163,195,227,258,0,0
];
const ZLENGTH_EXTRA: [u8; 31]= [
    0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0,0,0
];
const ZDIST_BASE: [usize; 32] = [
    1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,
    257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577,0,0
];
const ZDIST_EXTRA: [u8; 32] = [
    0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,0,0
];

/// zlib-from-memory implementation for PNG reading
///    because PNG allows splitting the zlib stream arbitrarily,
///    and it's annoying structurally to have PNG call ZLIB call PNG,
///    we require PNG read all the IDATs and combine them into a single
///    memory buffer
struct Zbuf<'r> {
    zbuffer: &'r [u8],

    num_bits: u8,
    code_buffer: u32,

    zout: Vec<u8>,
    z_expandable: bool,

    z_length: Option<Huffman>,
    z_distance: Option<Huffman>,
}

impl<'r> Zbuf<'r> {
    fn new(zbuffer: &'r [u8], zout: Vec<u8>, z_expandable: bool) -> Self {
        Self {
            zbuffer,

            num_bits: 0,
            code_buffer: 0,

            zout,
            z_expandable,

            z_length: Some(Huffman::new()),
            z_distance: Some(Huffman::new()),
        }
    }

    fn eof(&self) -> bool {
        self.zbuffer.len() == 0
    }

    fn get8(&mut self) -> u8 {
        if self.eof() {
            0
        } else {
            let o = self.zbuffer[0];
            self.zbuffer = &self.zbuffer[1..];
            o
        }
    }

    fn fill_bits(&mut self) {
        while self.num_bits <= 24 {
            // 检查 code_buffer 和 num_bits 是否匹配
            if self.code_buffer >= 1 << self.num_bits {
                self.zbuffer = &self.zbuffer[self.zbuffer.len()..];
                return;
            }

            self.code_buffer |= (self.get8() as u32) << self.num_bits;
            self.num_bits += 8;
        }
    }

    #[inline(always)]
    fn receive(&mut self, n: u8) -> u32 {
        debug_assert!(n < 32);
        if self.num_bits < n {
            self.fill_bits();
        }

        let k: u32 = self.code_buffer & ((1 << n) - 1);
        self.code_buffer >>= n;
        self.num_bits -= n;
        k
    }

    fn parse_header(&mut self) -> Result<()> {
        let cmf = self.get8() as u32;
        let cm = cmf & 15;
        let flg = self.get8() as u32;
        // let cinfo = cmf >> 4;
        if self.eof() { return Err(Error::corrupt("Bad zlib header: eof")); }
        if (cmf*256+flg) % 31 != 0 { return Err(Error::corrupt("bad zlib header: bad cmf and flg")); }
        if flg & 32 > 0 { return Err(Error::corrupt("no preset dict")); }
        if cm != 8 { return Err(Error::corrupt("bad compression")); }
        // window = 1 << (8 + cinfo)... but who cares, we fully buffer output
        Ok(())
    }

    fn parse_uncompressed_block(&mut self) -> Result<()> {
        let mut header: [u8; 4] = [0; 4];

        // 去除 code_buffer 不足 8 bit的数据
        if (self.num_bits & 0b111) > 0 {
            self.receive((self.num_bits & 0b111) as _); // discard
        }

        // drain the bit-packed data into header
        let mut k = 0;
        while self.num_bits > 0 {
            // 上一步已经确保了 self.num_bits % 8 == 0
            if self.num_bits < 8 { return Err(Error::corrupt("zlib corrupt")); }
            header[k] = (self.code_buffer & ((1u32 << 8) - 1)) as u8;
            k += 1;
            self.code_buffer >>= 8;
            self.num_bits -= 8;
        }

        // now fill header the normal way
        while k < 4 {
            header[k] = self.get8();
            k += 1;
        }

        // parsing
        let len = header[1] as usize * 256 + header[0] as usize;
        let nlen = header[3] as usize * 256 + header[2] as usize;
        if nlen != len ^ 0xffff { return Err(Error::corrupt("zlib corrut")); }
        if len > self.zbuffer.len() { return Err(Error::corrupt("read past buffer")); }
        if self.zout.len() + len > self.zout.capacity() {
            self.expand(len as usize)?;
        }
        self.zout.extend_from_slice(&self.zbuffer[..len]);
        self.zbuffer = &self.zbuffer[len..];
        Ok(())
    }

    fn expand(&mut self, n: usize) -> Result<()> {
        if !self.z_expandable { return Err(Error::corrupt("output buffer limit")); }
        if usize::MAX - n < self.zout.len() { return Err(Error::corrupt("Out of memory")); }
        self.zout.reserve(n);
        Ok(())
    }

    fn compute_huffman_codes(&mut self) -> Result<()> {
        const LENGTH_DEZIGZAG: [u8; 19] = [ 16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15 ];
        let mut z_codelength: Huffman = Huffman::new();
        let mut lencodes: [u8; 286+32+137] = [0; 286+32+137]; // padding for maximum single op
        let mut codelength_sizes: [u8; 19] = [0; 19];

        let hlit = self.receive(5) as usize + 257;
        let hdist = self.receive(5) as usize + 1;
        let hclen = self.receive(4) as usize + 4;
        let ntot = hlit + hdist;

        for i in 0..hclen {
            let s = self.receive(3);
            codelength_sizes[LENGTH_DEZIGZAG[i] as usize] = s as u8;
        }
        z_codelength.build(&codelength_sizes)?;

        let mut n = 0;
        while n < ntot {
            let mut c = z_codelength.decode(self).ok_or(Error::corrupt("bad code_lengths"))? as usize;
            if c >= 19 { return Err(Error::corrupt("bad codelengths")); }
            if c < 16 {
                lencodes[n] = c as u8;
                n += 1;
            } else {
                let mut fill: u8 = 0;
                match c {
                    16 => {
                        c = self.receive(2) as usize + 3;
                        if n == 0 { return Err(Error::corrupt("bad codelengths")); }
                        fill = lencodes[n-1];
                    },
                    17 => {
                        c = self.receive(3) as usize + 3;
                    },
                    18 => {
                        c = self.receive(7) as usize + 11;
                    },
                    _ => {
                        return Err(Error::corrupt("bad codelengths"));
                    }
                }

                if ntot - n < c {
                    return Err(Error::corrupt("bad codelengths"));
                }
                lencodes[n..n+c].fill(fill);
                n += c;
            }
        }

        if n != ntot { return Err(Error::corrupt("bad codelengths")); }
        self.z_length.as_mut().unwrap().build(&lencodes[..hlit])?;
        self.z_distance.as_mut().unwrap().build(&lencodes[hlit..hlit+hdist])?;

        Ok(())
    }

    fn parse_huffman_block(&mut self) -> Result<()> {
        let z_length = self.z_length.take().unwrap();
        let z_distance = self.z_distance.take().unwrap();

        let r = self._parse_huffman_block(&z_length, &z_distance);

        self.z_length = Some(z_length);
        self.z_distance = Some(z_distance);

        r
    }

    fn _parse_huffman_block(&mut self, z_length: &Huffman, z_distance: &Huffman) -> Result<()> {
        loop {
            let mut z = z_length.decode(self).ok_or(Error::corrupt("bad huffman code"))? as usize;
            if z < 256 {
                if self.zout.len() >= self.zout.capacity() {
                    self.expand(1)?;
                }
                self.zout.push(z as u8);
            } else {
                // zlib block finish
                if z == 256 { return Ok(()); }
                z -= 257;
                let mut len = ZLENGTH_BASE[z];
                if ZLENGTH_EXTRA[z] > 0 {
                    len += self.receive(ZLENGTH_EXTRA[z]) as usize;
                }

                z = z_distance.decode(self).ok_or(Error::corrupt("bad huffman code"))? as usize;
                let mut dist = ZDIST_BASE[z];
                if ZDIST_EXTRA[z] > 0 {
                    dist += self.receive(ZDIST_EXTRA[z]) as usize;
                }

                if self.zout.len() < dist { return Err(Error::corrupt("bad dist")); }
                if self.zout.len() + len > self.zout.capacity() {
                    self.expand(len)?;
                }

                /*
                 * // if condition here: make code fast, reduce jump (looking for p)
                 * if dist == 1 {
                 *     // run of one byte; common in images.
                 *     let p = self.zout[self.zout.len() - dist];
                 *     for _ in 0..len {
                 *         self.zout.push(p);
                 *     }
                 * } else {
                 *     let mut p = self.zout.len() - dist;
                 *     for _ in 0..len {
                 *         self.zout.push(self.zout[p]);
                 *         p += 1;
                 *     }
                 * }
                 */

                let mut p = self.zout.len() - dist;
                for _ in 0..len {
                    self.zout.push(self.zout[p]);
                    p += 1;
                 }
            }
        }
    }

    fn do_zlib(&mut self, is_parse_header: bool) -> Result<()> {
        if is_parse_header {
            self.parse_header()?;
        }

        self.num_bits = 0;
        self.code_buffer = 0;
        let mut is_final = false;
        while !is_final {
            is_final = self.receive(1) > 0;
            let ztype = self.receive(2);
            match ztype {
                0 => {
                    self.parse_uncompressed_block()?;
                },
                3 => {
                    break;
                },
                _ => {
                    if ztype == 1 {
                        self.z_length.as_mut().unwrap().build(&ZDEFAULT_LENGTH)?;
                        self.z_distance.as_mut().unwrap().build(&ZDEFAULT_DISTANCE)?;
                    } else {
                        self.compute_huffman_codes()?;
                    }
                    self.parse_huffman_block()?;
                },
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
struct Huffman {
    fast: [u16; 1 << ZFAST_BITS],
    first_code: [u16; 16],
    max_code: [u32; 17],
    first_symbol: [u16; 16],
    size: [u8; ZNSYMS],
    value: [u16; ZNSYMS],
}

impl Huffman {
    fn new() -> Self {
        Self {
            fast: [0; 1 << ZFAST_BITS],
            first_code: [0; 16],
            max_code: [0; 17],
            first_symbol: [0; 16],
            size: [0; ZNSYMS],
            value: [0; ZNSYMS],
        }
    }

    fn build(&mut self, size_list: &[u8]) -> Result<()> {
        // DEFLATE spec for generating codes
        let mut sizes = [0; 17];
        self.fast.fill(0);
        sizes[0] = 0;
        for idx in 0..size_list.len() {
            sizes[size_list[idx] as usize] += 1;
        }
        for idx in 1..16 {
            if sizes[idx] > (1 << idx) {
                return Err(Error::corrupt("bad sizes"));
            }
        }

        let mut code = 0u32;
        let mut k = 0u32;
        let mut next_code = [0u32; 16];
        for idx in 1..16 {
            next_code[idx] = code;
            self.first_code[idx] = code as u16;
            self.first_symbol[idx] = k as u16;
            code = code + sizes[idx];
            if sizes[idx] > 0 {
                if code - 1 >= (1 << idx) {
                    return Err(Error::corrupt("bad codelengths"));
                }
            }
            self.max_code[idx] = code << (16-idx); // preshift for inner loop
            code <<= 1;
            k += sizes[idx];
        }

        self.max_code[16] = 0x10000; // sentinel
        for idx in 0..size_list.len() {
            let s = size_list[idx] as usize;
            if s > 0 {
                let c = next_code[s] as usize - self.first_code[s] as usize + self.first_symbol[s] as usize;
                let fastv: u16 = ((s << 9) | idx) as u16;
                self.size[c] = s as u8;
                self.value[c] = idx as u16;

                if s <= ZFAST_BITS {
                    let mut j = Self::bit_reverse(next_code[s], s) as usize;
                    while j < (1 << ZFAST_BITS) {
                        self.fast[j] = fastv;
                        j += 1 << s;
                    }
                }

                next_code[s] += 1;
            }
        }

        Ok(())
    }

    fn bit_reverse16(mut n: u32) -> u32 {
        n = ((n & 0xAAAA) >>  1) | ((n & 0x5555) << 1);
        n = ((n & 0xCCCC) >>  2) | ((n & 0x3333) << 2);
        n = ((n & 0xF0F0) >>  4) | ((n & 0x0F0F) << 4);
        n = ((n & 0xFF00) >>  8) | ((n & 0x00FF) << 8);
        n
    }

    fn bit_reverse(n: u32, bits: usize) -> u32 {
        debug_assert!(bits <= 16);
        Self::bit_reverse16(n) >> (16-bits)
    }

    fn decode_slowpath<'r>(&self, zbuf: &'r mut Zbuf) -> Option<u16> {
        // not resolved by fast table, so compute it the slow way
        // use jpeg approach, which requires MSbits at top
        let k = Self::bit_reverse(zbuf.code_buffer, 16);
        let mut s = ZFAST_BITS;
        loop {
            s += 1;
            if k < self.max_code[s] { break; }
        }

        if s >= 16 { return None; }
        // code size is s, so:
        let b = (k >> (16-s)) as usize - self.first_code[s] as usize + self.first_symbol[s] as usize;
        if b >= ZNSYMS || (self.size[b] as usize) != s { return None; }
        zbuf.code_buffer >>= s;
        zbuf.num_bits -= s as u8;
        Some(self.value[b])
    }

    fn decode<'r>(&self, zbuf: &'r mut Zbuf) -> Option<u16> {
        if zbuf.num_bits < 16 {
            if zbuf.eof() { return None; }
            zbuf.fill_bits();
        }
        let b = self.fast[(zbuf.code_buffer as usize) & ZFAST_MASK];
        if b > 0 {
            let s = (b >> 9) as usize;
            zbuf.code_buffer >>= s;
            zbuf.num_bits -= s as u8;
            return Some(b & 511)
        }

        self.decode_slowpath(zbuf)
    }
}

pub fn zlib_decode_malloc_guessize_headerflag(zbuffer: &[u8], initial_size: usize, is_parse_header: bool) -> Result<Vec<u8>> {
    let mut zbuf: Zbuf = Zbuf::new(zbuffer, Vec::with_capacity(initial_size), true);
    zbuf.do_zlib(is_parse_header)?;
    Ok(zbuf.zout)
}
