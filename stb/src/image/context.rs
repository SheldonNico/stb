use super::{Result, Error};
use super::zlib::*;

use std::io::{Read, BufReader, SeekFrom, Seek, self};
use log::{debug, trace};

const MAX_DIMENSIONS: usize = 1 << 24;

const F_NONE        : u8 = 0;
const F_SUB         : u8 = 1;
const F_UP          : u8 = 2;
const F_AVG         : u8 = 3;
const F_PAETH       : u8 = 4;
const F_AVG_FIRST   : u8 = 5;
const F_PAETH_FIRST : u8 = 6;
const FIRST_ROW_FILTER: [u8; 5] = [
    F_NONE,
    F_SUB,
    F_NONE,
    F_AVG_FIRST,
    F_PAETH_FIRST
];
const DEPTH_SCALE_TABLE: [u8; 9] = [ 0, 0xff, 0x55, 0, 0x11, 0,0,0, 0x01 ];

pub struct Context<R> {
    pub(crate) img_x: usize,
    pub(crate) img_y: usize,
    pub(crate) img_n: usize,
    pub(crate) img_out_n: usize,

    pub(crate) buf: BufReader<R>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Order {
    RGB,
    BGR,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scan {
    Load,
    Type,
    Header,
}

pub struct ResultInfo {
    bits_per_channel: u32,
    num_channels: u32,
    channel_order: Order,
}

impl Default for ResultInfo {
    fn default() -> Self {
        Self {
            bits_per_channel: 8,
            num_channels: 0,
            channel_order: Order::RGB,
        }
    }
}

impl<R: Read+Seek> Context<R> {
    pub fn new(reader: R) -> Self {
        Self {
            img_x: 0,
            img_y: 0,

            img_n: 0,
            img_out_n: 0,

            buf: BufReader::with_capacity(128, reader),
        }
    }

    pub fn load_and_postprocess_8bit(&mut self, req_comp: usize) -> Result<Vec<u8>> {
        let mut ri = ResultInfo::default();

        let mut result = self.load_main(req_comp, &mut ri, 8)?;
        assert!(ri.bits_per_channel == 8 || ri.bits_per_channel == 16);

        if ri.bits_per_channel == 16 {
            trace!("original png is 16 bits, convert to 8");
            result = convert_16_to_8(result, self.img_x, self.img_y, if req_comp == 0 { self.img_n } else { req_comp });
            ri.bits_per_channel = 8;
        }

        Ok(result)
    }

    fn load_main(&mut self, req_comp: usize, ri: &mut ResultInfo, bits_per_channel: usize) -> Result<Vec<u8>> {
        if self.png_test()? { return self.png_load(req_comp, ri); }

        return Err(Error::custom("Image not of any known type, or corrupt"));
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    fn png_test(&mut self) -> Result<bool> {
        let r = self.check_png_header();
        self.buf.seek(SeekFrom::Start(0))?;
        r
    }

    fn check_png_header(&mut self) -> Result<bool> {
        static PNG_SIG: &[u8; 8] = &[ 137,80,78,71,13,10,26,10 ];
        let mut sig = vec![0; PNG_SIG.len()];
        self.buf.read_exact(&mut sig)?;
        Ok(sig == PNG_SIG)
    }

    fn png_load(&mut self, req_comp: usize, ri: &mut ResultInfo) -> Result<Vec<u8>> {
        if req_comp > 4 { return Err(Error::internal("bad req_comp")); }
        let mut p = Png::new(self);
        p.do_png(req_comp, ri)
    }

    fn get_chunk_header(&mut self) -> io::Result<(usize, u32)> {
        return Ok((self.read_u32_be()? as usize, self.read_u32_be()?))
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    fn read_u8(&mut self) -> io::Result<u8> {
        // https://www.reddit.com/r/rust/comments/nxmqu0/readwrite_only_one_byte/
        let mut o = 0;
        self.buf.read_exact(std::slice::from_mut(&mut o))?;
        Ok(o)
    }

    fn read_u16_be(&mut self) -> io::Result<u16> {
        let mut s = [0; 2];
        self.buf.read_exact(&mut s)?;
        Ok(u16::from_be_bytes(s))
    }

    fn read_u32_be(&mut self) -> io::Result<u32> {
        let mut s = [0; 4];
        self.buf.read_exact(&mut s)?;
        Ok(u32::from_be_bytes(s))
    }

    fn skip(&mut self, n: usize) -> io::Result<()> {
        self.buf.seek(SeekFrom::Current(n as i64))?;
        Ok(())
    }

    fn getn(&mut self, out: &mut [u8]) -> io::Result<()> {
        self.buf.read_exact(out)
    }
}

pub struct Png<'a, R> {
    s: &'a mut Context<R>,

    idata: Vec<u8>,
    expanded: Vec<u8>,
    out: Vec<u8>,
    depth: usize,
}

impl<'a, R: Read+Seek> Png<'a, R> {
    fn new(s: &'a mut Context<R>) -> Self {
        Self {
            s,
            idata: vec![],
            expanded: vec![],
            out: vec![],
            depth: 0,
        }
    }

    fn do_png(&mut self, req_comp: usize, ri: &mut ResultInfo) -> Result<Vec<u8>> {
        if req_comp > 4 { return Err(Error::internal("bad req_comp")); }
        self.parse_png_file(Scan::Load, req_comp)?;

        if self.depth <= 8 {
            ri.bits_per_channel = 8;
        } else if self.depth == 16 {
            ri.bits_per_channel = 16;
        } else {
            return Err(Error::not_support("PNG not supported: unsupported color depth"));
        }

        let mut result = std::mem::replace(&mut self.out, Default::default());

        if req_comp > 0 && req_comp != self.s.img_out_n {
            if ri.bits_per_channel == 8 {
                debug!("convert from 8 to 16");
                result = convert_format(result, self.s.img_out_n, req_comp, self.s.img_x, self.s.img_y)?;
            } else {
                debug!("convert from 16 to 8");
                result = convert_format16(&result, self.s.img_out_n, req_comp, self.s.img_x, self.s.img_y)?;
            }
        }

        Ok(result)
    }

    #[allow(non_upper_case_globals)]
    fn parse_png_file(&mut self, scan: Scan, req_comp: usize) -> Result<()> {
        let (mut palette, mut pal_img_n) = ([0u8; 1024], 0usize);
        let (mut has_trans, mut tc) = (false, [0u8; 3]);
        let mut tc16 = [0u16; 3];
        let (mut ioff, mut idata_limit, mut pal_len) = (0usize, 0u32, 0usize);
        let (mut is_first, mut is_iphone, mut color, mut interlace) = (true, false, 0, 0);

        let s = &mut self.s;
        s.check_png_header()?;

        if scan == Scan::Type { return Ok(()); }

        macro_rules! ptype {
            ($u1:literal, $u2:literal, $u3:literal, $u4:literal) => {
                u32::from_be_bytes([$u1 as u8, $u2 as u8, $u3 as u8, $u4 as u8])
            };
        }

        const PTYPE_CgBI: u32 = ptype!['C', 'g', 'B', 'I'];
        const PTYPE_IHDR: u32 = ptype!['I', 'H', 'D', 'R'];
        const PTYPE_PLTE: u32 = ptype!['P', 'L', 'T', 'E'];
        const PTYPE_tRNS: u32 = ptype!['t', 'R', 'N', 'S'];
        const PTYPE_IDAT: u32 = ptype!['I', 'D', 'A', 'T'];
        const PTYPE_IEND: u32 = ptype!['I', 'E', 'N', 'D'];
        trace!(
            "PTYPE_CgBI={}, PTYPE_IHDR={}, PTYPE_PLTE={}, PTYPE_tRNS={}, PTYPE_IDAT={}, PTYPE_IEND={}",
            PTYPE_CgBI, PTYPE_IHDR, PTYPE_PLTE, PTYPE_tRNS, PTYPE_IDAT, PTYPE_IEND,
        );

        loop {
            let (length, ptype) = s.get_chunk_header()?;
            trace!("chunk {}@{}", ptype, length);
            match ptype {
                PTYPE_CgBI => {
                    is_iphone = true;
                    s.skip(length)?;
                },
                PTYPE_IHDR => {
                    if !is_first { return Err(Error::corrupt("multiple IHDR")); }
                    is_first = false;
                    if length != 13 { return Err(Error::corrupt("bad IHDR len")); }

                    s.img_x = s.read_u32_be()? as _;
                    s.img_y = s.read_u32_be()? as _;

                    if s.img_x > MAX_DIMENSIONS { return Err(Error::corrupt("Very large image (corrupt?)")) }
                    if s.img_y > MAX_DIMENSIONS { return Err(Error::corrupt("Very large image (corrupt?)")) }

                    self.depth = s.read_u8()? as _; if self.depth != 1 && self.depth != 2 && self.depth != 4 && self.depth != 8 && self.depth != 16 { return Err(Error::bad_depth("PNG not supported: 1/2/4/8/16-bit only")); }

                    color = s.read_u8()?; if color > 6 { return Err(Error::corrupt("bad ctype, color > 6")); }
                    if color == 3 && self.depth == 16              { return Err(Error::corrupt("bad ctype, color=3, depth=16")); }
                    if color == 3 { pal_img_n = 3; } else if (color & 1) > 0 { return Err(Error::corrupt("bad ctype, color & 1 > 0")); }

                    let comp   = s.read_u8()?; if comp > 0 { return Err(Error::corrupt("bad comp method")); }
                    let filter = s.read_u8()?; if filter > 0 { return Err(Error::corrupt("bad filter method")); }
                    interlace = s.read_u8()?; if interlace > 1 { return Err(Error::corrupt("bad interlace method"))? }

                    if s.img_x == 0 || s.img_y == 0 { return Err(Error::corrupt("0-pixel image")) }
                    if pal_img_n == 0 {
                        s.img_n = if (color & 2) > 0 { 3 } else { 1 } + if (color & 4) > 0 { 1 } else { 0 };
                        if (1 << 30 ) / s.img_x / s.img_n < s.img_y { return Err(Error::corrupt("image too large to decode")); }
                        if scan == Scan::Header { return Ok(()); }
                    } else {
                        s.img_n = 1;
                        if (1 << 30) / s.img_x / 4 < s.img_y { return Err(Error::corrupt("too large")); }
                    }
                },
                PTYPE_PLTE => {
                    if is_first { return Err(Error::corrupt("first not IHDR")); }
                    if length > 256*3 { return Err(Error::corrupt("invalid PLTE")); }
                    pal_len = length / 3;
                    if pal_len as usize * 3 != length { return Err(Error::corrupt("invalid PLTE")); }
                    for i in 0..pal_len {
                        palette[i*4+0] = s.read_u8()?;
                        palette[i*4+1] = s.read_u8()?;
                        palette[i*4+2] = s.read_u8()?;
                        palette[i*4+3] = 255;
                    }
                },
                PTYPE_tRNS => {
                    if is_first { return Err(Error::corrupt("first not IHDR")); }
                    if self.idata.len() > 0 { return Err(Error::corrupt("tRNS after IDAT")); }
                    if pal_img_n > 0 {
                        if scan == Scan::Header { s.img_n = 4; return Ok(()); }
                        if pal_len == 0 { return Err(Error::corrupt("tRNS before PLTE")); }
                        if length > pal_len { return Err(Error::corrupt("bad tRNS len")); }
                        pal_img_n = 4;
                        for i in 0..length {
                            palette[i*4+3] = s.read_u8()?;
                        }
                    } else {
                        if (s.img_n & 1) == 0 { return Err(Error::corrupt("tRNS with alpha")); }
                        if length != s.img_n * 2 { return Err(Error::corrupt("bad tRNS len")); }
                        has_trans = true;
                        if self.depth == 16 {
                            for k in 0..s.img_n {
                                tc16[k] = s.read_u16_be()?;
                            }
                        } else {
                            for k in 0..s.img_n {
                                tc[k] = ((s.read_u16_be()? & 255) * (DEPTH_SCALE_TABLE[self.depth] as u16)) as u8;
                            }
                        }
                    }
                },
                PTYPE_IDAT => {
                    if is_first { return Err(Error::corrupt("first not IHDR")); }
                    if pal_img_n > 0 && pal_len == 0 { return Err(Error::corrupt("no PLTE")); }
                    if scan == Scan::Header { return Ok(()) }
                    self.idata.resize(ioff+length, 0u8);
                    s.getn(&mut self.idata[ioff..ioff+length])?;
                    ioff += length;
                },
                PTYPE_IEND => {
                    if is_first { return Err(Error::corrupt("first not IHDR")); }
                    if scan != Scan::Load { return Ok(()); }
                    if self.idata.len() == 0 { return Err(Error::corrupt("idata length is zero.")); }
                    // initial guess for decoed data size to avoid unnecessary realloc
                    let bpl = (s.img_x * self.depth + 7) / 8;
                    let raw_len = bpl * s.img_y * s.img_n;

                    self.expanded = zlib_decode_malloc_guessize_headerflag(&mut self.idata, raw_len, !is_iphone)?;
                    self.idata.clear();
                    if ((req_comp == s.img_n+1) && (req_comp != 3) && pal_img_n == 0) || has_trans {
                        s.img_out_n = s.img_n + 1;
                    } else {
                        s.img_out_n = s.img_n;
                    }

                    self.create_png_image(self.s.img_out_n, color, interlace)?;

                    // borrow s again. patch for borrow checker.
                    if has_trans {
                        if self.depth == 16 {
                            self.compute_transparency16(tc16, self.s.img_out_n);
                        } else {
                            self.compute_transparency(tc, self.s.img_out_n);
                        }
                    }
                    // TODO: handle iphone with flag, should be option here.
                    if is_iphone && self.s.img_out_n > 2 && false {
                        todo!()
                    }
                    if pal_img_n > 0 {
                        // pal_img_n == 3 or 4
                        self.s.img_n = pal_img_n; // record the actual colors we had
                        self.s.img_out_n = pal_img_n;
                        if req_comp >= 3 { self.s.img_out_n = req_comp; }
                        self.expand_png_palette(&palette, self.s.img_out_n)?;
                    } else if has_trans {
                        // non-paletted image with tRNS -> source image has (constant) alpha
                        self.s.img_n += 1;
                    }

                    let _ = self.s.read_u32_be()?; // end of PNG, read and skip CRC
                    return Ok(())
                },
                _ => {
                    if is_first { return Err(Error::corrupt("first not IHDR")); }
                    if (ptype & (1 << 29)) == 0 {
                        let ptype: Vec<_> = ptype.to_be_bytes().iter().map(|&c| c as char).collect();
                        return Err(Error::not_support(format!("unknown PNG chunk type: {:?}", ptype)));
                    }
                    s.skip(length)?;
                }
            }

            s.read_u32_be()?;
        }
    }

    fn compute_transparency16(&mut self, tc: [u16; 3], out_n: usize) {
        let pixel_count = self.s.img_x * self.s.img_y;
        let mut p = 0;

        // compute color-based transparency, assuming we've
        // already got 255 as the alpha value in the output
        assert!(out_n == 2 || out_n == 4);

        if out_n == 2 {
            for _ in 0..pixel_count {
                let num1 = u16::from_ne_bytes([self.out[p], self.out[p+1]]);
                let num2 = if num1 == tc[0] { 0 } else { 65535 };
                self.out[p+2..p+4].copy_from_slice(&u16::to_ne_bytes(num2));
                p += 4;
            }
        } else {
            for _ in 0..pixel_count {
                let num1 = u16::from_ne_bytes([self.out[p  ], self.out[p+1]]);
                let num2 = u16::from_ne_bytes([self.out[p+2], self.out[p+3]]);
                let num3 = u16::from_ne_bytes([self.out[p+4], self.out[p+5]]);
                if [num1, num2, num3] == tc {
                    self.out[p+6..p+8].copy_from_slice(&u16::to_ne_bytes(0));
                }

                p += 8;
            }
        }
    }

    fn compute_transparency(&mut self, tc: [u8; 3], out_n: usize) {
        let pixel_count = self.s.img_x * self.s.img_y;
        let mut p = 0;

        // compute color-based transparency, assuming we've
        // already got 255 as the alpha value in the output
        assert!(out_n == 2 || out_n == 4);

        if out_n == 2 {
            for _ in 0..pixel_count {
                self.out[p+1] = if self.out[p] == tc[0] { 0 } else { 255 };
                p += 2;
            }
        } else {
            for _ in 0..pixel_count {
                if self.out[p..p+3] == tc {
                    self.out[p+3] =0;
                }
                p += 4;
            }
        }
    }

    fn expand_png_palette(&mut self, palette: &[u8], pal_img_n: usize) -> Result<()> {
        let pixel_count = self.s.img_x * self.s.img_y;
        if !mad2sizes_valid(pixel_count, pal_img_n, 0) { return Err(Error::out_of_mem("expand_png_palette failed")); }
        let mut temp_out = vec![0; pixel_count*pal_img_n+0];
        let mut p = 0;

        if pal_img_n == 3 {
            for i in 0..pixel_count {
                let n = self.out[i] as usize * 4;
                temp_out[p+0] = palette[n  ];
                temp_out[p+1] = palette[n+1];
                temp_out[p+2] = palette[n+2];
                p += 3;
            }
        } else {
            for i in 0..pixel_count {
                let n = self.out[i] as usize * 4;
                temp_out[p+0] = palette[n  ];
                temp_out[p+1] = palette[n+1];
                temp_out[p+2] = palette[n+2];
                temp_out[p+3] = palette[n+3];
                p += 4;
            }
        }
        self.out = temp_out;
        Ok(())
    }

    fn create_png_image_raw(&mut self, out_n: usize, x: usize, y: usize, depth: usize, color: u8) -> Result<()> {
        trace!("create_png_image_raw: out_n={}, x={}, y={}, depth={}, color={}", out_n, x, y, depth, color);
        // renaming variable to make code clean.
        let s = &self.s;
        let img_n = s.img_n; // copy it into a local for later

        // init state
        let bytes = if self.depth == 16 { 2 } else { 1 };
        let stride = x*out_n*bytes;
        let output_bytes = out_n * bytes;
        let mut filter_bytes = img_n * bytes;
        let mut width = x;

        debug_assert!(out_n == img_n || out_n == img_n+1);
        if !mad3sizes_valid(x, y, output_bytes, 0) { return Err(Error::out_of_mem(format!("too large: x={}, y={}, output_bytes={}", x, y, output_bytes))); }
        self.out = vec![0; x*y*output_bytes];

        if !mad3sizes_valid(img_n, x, depth, 7) { return Err(Error::out_of_mem("too large")); }
        let img_width_bytes = (img_n * x * depth + 7) >> 3;
        let img_len = (img_width_bytes + 1) * y;

        // we used to check for exact match between raw_len and img_len on non-interlaced PNGs,
        // but issue #276 reported a PNG in the wild that had extra data at the end (all zeros),
        // so just check for raw_len < img_len always
        if self.expanded.len() < img_len { return Err(Error::corrupt("not enouth pixels")); }

        let mut raw = 0;
        for j in 0..y {
            // pointer on out: cur, prior
            // pointer on expanded: raw
            let mut cur = stride * j;
            let mut filter = self.expanded[raw]; raw += 1;

            if filter > 4 { return Err(Error::corrupt("invalid filter")); }

            if self.depth < 8 {
                if img_width_bytes > x { return Err(Error::corrupt("invalid width")); }
                cur += x*out_n - img_width_bytes; // store output to the rightmost img_len bytes, so we can decode in place
                filter_bytes = 1;
                width = img_width_bytes;
            }
            // bugfix: need to compute this after 'cur +=' computation above
            // png格式确保了不会在j=0时候读取prior的值
            // debug_assert!(cur >= stride);
            let mut prior = if cur >= stride { cur - stride } else { 0 };

            // if first row, use special filter that doesn't sample previous row
            if j == 0 { filter = FIRST_ROW_FILTER[filter as usize]; }

            // handle first byte explicitly
            for k in 0..filter_bytes {
                let delta = match filter {
                    F_NONE        => { 0 },
                    F_SUB         => { 0 },
                    F_UP          => { self.out[prior+k] as i32},
                    F_AVG         => { (self.out[prior+k]) as i32 >> 1 },
                    F_PAETH       => { paeth(0, self.out[prior+k] as _, 0) },
                    F_AVG_FIRST   => { 0 }
                    F_PAETH_FIRST => { 0 }
                    _ => unreachable!(),
                };
                self.out[cur+k] = (self.expanded[raw+k] as i32 + delta) as u8;
            }

            match self.depth {
                8 => {
                    if img_n != out_n {
                        self.out[cur+img_n] = 255; // first pixel
                    }
                    raw += img_n;
                    cur += out_n;
                    prior += out_n;
                },
                16 => {
                    if img_n != out_n {
                        self.out[cur+filter_bytes] = 255;   // first pixel top byte
                        self.out[cur+filter_bytes+1] = 255; // first pixel bottom byte
                    }
                    raw += filter_bytes;
                    cur += output_bytes;
                    prior += output_bytes;
                },
                _ => {
                    raw += 1;
                    cur += 1;
                    prior += 1;
                }
            }

            // NOTE: original code u8 + u8 is promoted to u16. And the rule is extremely rare.
            // (127u8 + 142u8) >> 1 = (269u32) >> 1u32 = 134u32 = 134u8 WTF?
            //
            // is the 1 literal default to 1u32? https://en.cppreference.com/w/cpp/language/integer_literal
            if self.depth < 8 || img_n == out_n {
                let nk = (width - 1) * filter_bytes;
                match filter {
                    F_NONE => {
                        self.out[cur..cur+nk].copy_from_slice(&self.expanded[raw..raw+nk]);
                    },
                    _ => {
                        for k in 0..nk {
                            let delta = match filter {
                                F_SUB         => self.out[cur+k-filter_bytes] as i32,
                                F_UP          => self.out[prior+k] as i32,
                                F_AVG         => (self.out[prior+k] as i32 + self.out[cur+k-filter_bytes] as i32) >> 1,
                                F_PAETH       => paeth(self.out[cur+k-filter_bytes] as _, self.out[prior+k] as _, self.out[prior+k-filter_bytes] as _),
                                F_AVG_FIRST   => (self.out[cur+k-filter_bytes] as i32) >> 1,
                                F_PAETH_FIRST => paeth(self.out[cur+k-filter_bytes] as _, 0, 0),
                                _ => unreachable!(),
                            };
                            self.out[cur+k] = (self.expanded[raw+k] as i32 + delta) as u8;
                        }
                    },
                }
                raw += nk;
            } else {
                debug_assert!(img_n+1 == out_n);

                for _ in 1..x {
                    for k in 0..filter_bytes {
                        let delta = match filter {
                            F_NONE        => 0,
                            F_SUB         => self.out[cur+k-output_bytes] as i32,
                            F_UP          => self.out[prior+k] as i32,
                            F_AVG         => (self.out[prior+k] as i32 + self.out[cur+k-output_bytes] as i32) >> 1,
                            F_PAETH       => paeth(self.out[cur+k-output_bytes] as _, self.out[prior+k] as _, self.out[prior+k-output_bytes] as _),
                            F_AVG_FIRST   => (self.out[cur+k-output_bytes] as i32) >> 1,
                            F_PAETH_FIRST => paeth(self.out[cur+k-output_bytes] as _, 0, 0),
                            _ => unreachable!()
                        };
                        self.out[cur+k] = (self.expanded[raw+k] as i32 + delta) as u8;
                    }
                    self.out[cur+filter_bytes] = 255;
                    raw += filter_bytes;
                    cur += output_bytes;
                    prior += output_bytes;
                }

                // the loop above sets the high byte of the pixels' alpha, but for
                // 16 bit png files we also need the low byte set. we'll do that here
                if depth == 16 {
                    cur = stride*j;
                    for _ in 0..x {
                        self.out[cur+filter_bytes+1] = 255;
                        cur += output_bytes;
                    }
                }
            }
        }

        // we make a separate pass to expand bits to pixels; for performance,
        // this could run two scanlines behind the above code, so it won't
        // intefere with filtering but will still be in the cache
        if self.depth < 8 {
            for j in 0..y {
                let mut cur = stride * j;
                let mut in_ = stride * j + x*out_n - img_width_bytes;
                // unpack 1/2/4-bit into a 8-bit buffer. allows us to keep the common 8-bit path optimal at minimal cost for 1/2/4-bit
                // png guarante byte alignment, if width is not multiple of 8/4/2 we'll decode dummy trailing data that will be skipped in the later loop
                let scale = if color == 0 { DEPTH_SCALE_TABLE[depth] } else { 1 }; // scale grayscale values to 0..255 range

                match depth {
                    4 => {
                        let mut k = x*img_n;
                        while k >= 2 {
                            self.out[cur] = scale *  (self.out[in_] >> 4)        ; cur += 1;
                            self.out[cur] = scale * ((self.out[in_]     ) & 0x0f); cur += 1;

                            k -= 2;
                            in_ += 1;
                        }
                        if k > 0 { self.out[cur] = scale *  (self.out[in_] >> 4)        ;           }
                    },
                    2 => {
                        let mut k = x*img_n;
                        while k >= 4 {
                            self.out[cur] = scale *  (self.out[in_] >> 6)        ; cur += 1;
                            self.out[cur] = scale * ((self.out[in_] >> 4) & 0x03); cur += 1;
                            self.out[cur] = scale * ((self.out[in_] >> 2) & 0x03); cur += 1;
                            self.out[cur] = scale * ((self.out[in_]     ) & 0x03); cur += 1;

                            k -= 4;
                            in_ += 1;
                        }
                        if k > 0 { self.out[cur] = scale *  (self.out[in_] >> 6)        ; cur += 1; }
                        if k > 1 { self.out[cur] = scale * ((self.out[in_] >> 4) & 0x03); cur += 1; }
                        if k > 2 { self.out[cur] = scale * ((self.out[in_] >> 2) & 0x03);           }
                    },
                    1 => {
                        let mut k = x*img_n;
                        while k >= 8 {
                            self.out[cur] = scale *  (self.out[in_] >> 7)        ; cur += 1;
                            self.out[cur] = scale * ((self.out[in_] >> 6) & 0x01); cur += 1;
                            self.out[cur] = scale * ((self.out[in_] >> 5) & 0x01); cur += 1;
                            self.out[cur] = scale * ((self.out[in_] >> 4) & 0x01); cur += 1;
                            self.out[cur] = scale * ((self.out[in_] >> 3) & 0x01); cur += 1;
                            self.out[cur] = scale * ((self.out[in_] >> 2) & 0x01); cur += 1;
                            self.out[cur] = scale * ((self.out[in_] >> 1) & 0x01); cur += 1;
                            self.out[cur] = scale * ((self.out[in_]     ) & 0x01); cur += 1;

                            k -= 8;
                            in_ += 1;
                        }

                        if k > 0 { self.out[cur] = scale *  (self.out[in_] >> 7)        ; cur += 1; }
                        if k > 1 { self.out[cur] = scale * ((self.out[in_] >> 6) & 0x01); cur += 1; }
                        if k > 2 { self.out[cur] = scale * ((self.out[in_] >> 5) & 0x01); cur += 1; }
                        if k > 3 { self.out[cur] = scale * ((self.out[in_] >> 4) & 0x01); cur += 1; }
                        if k > 4 { self.out[cur] = scale * ((self.out[in_] >> 3) & 0x01); cur += 1; }
                        if k > 5 { self.out[cur] = scale * ((self.out[in_] >> 2) & 0x01); cur += 1; }
                        if k > 6 { self.out[cur] = scale * ((self.out[in_] >> 1) & 0x01);           }
                    },
                    _ => {  },
                }

                if img_n != out_n {
                    cur = stride * j;
                    if img_n == 1 {
                        for q in (0..x).rev() {
                            self.out[cur+q*2+1] = 255;
                            self.out[cur+q*2+0] = self.out[cur+q];
                        }
                    } else {
                        debug_assert!(img_n == 3);
                        for q in (0..x).rev() {
                            self.out[cur+q*4+3] = 255;
                            self.out[cur+q*4+2] = self.out[cur+q*3+2];
                            self.out[cur+q*4+1] = self.out[cur+q*3+1];
                            self.out[cur+q*4+0] = self.out[cur+q*3+0];
                        }
                    }
                }
            }
        } else if depth == 16 {
            let mut cur = 0;

            // force the image data from big-endian to platform-native.
            // this is done in a separate pass due to the decoding relying
            // on the data being untouched, but could probably be done
            // per-line during decode if care is taken.
            for _ in 0..x*y*out_n {
                let cur16: u16 = ((self.out[cur] as u16) << 8) | self.out[cur+1] as u16;
                self.out[cur..cur+2].copy_from_slice(&cur16.to_ne_bytes());
                cur += 2;
            }
        }

        Ok(())
    }

    fn create_png_image(&mut self, out_n: usize, color: u8, interlace: u8) -> Result<()> {
        trace!("creating out from depth={}, expanded={}, interlace={}", self.depth, self.expanded.len(), interlace);
        // expanded + depth -> out
        let bytes = if self.depth == 16 { 2 } else { 1 };
        let out_bytes = out_n * bytes;
        if interlace == 0 {
            return self.create_png_image_raw(out_n, self.s.img_x, self.s.img_y, self.depth, color);
        }

        // de-interlacing
        if !mad3sizes_valid(self.s.img_x, self.s.img_y, out_bytes, 0) { return Err(Error::out_of_mem("too large")); }
        let mut out = vec![0; self.s.img_x * self.s.img_y * out_bytes + 0];
        for p in 0..7 {
            let xorig = [ 0,4,0,2,0,1,0 ];
            let yorig = [ 0,0,4,0,2,0,1 ];
            let xspc  = [ 8,8,4,4,2,2,1 ];
            let yspc  = [ 8,8,8,4,4,2,2 ];

            // rearange math order to avoid subtract overflow
            let x = (self.s.img_x + xspc[p] - xorig[p] - 1) / xspc[p];
            let y = (self.s.img_y + yspc[p] - yorig[p] - 1) / yspc[p];

            if x > 0 && y > 0 {
                let img_len = ((((self.s.img_n * x * self.depth) + 7) >> 3) + 1) * y;
                self.create_png_image_raw(out_n, x, y, self.depth, color)?;

                for j in 0..y {
                    for i in 0..x {
                        let out_y = j*yspc[p]+yorig[p];
                        let out_x = i*xspc[p]+xorig[p];
                        let ox = out_y * self.s.img_x * out_bytes + out_x*out_bytes;
                        let oy = (j*x+i)*out_bytes;
                        out[ox..ox+out_bytes].copy_from_slice(&self.out[oy..oy+out_bytes]);
                    }
                }

                self.out.clear();
                self.expanded = self.expanded.split_off(img_len);
            }

        }
        self.out = out;
        Ok(())
    }
}

fn convert_16_to_8(orig: Vec<u8>, w: usize, h: usize, channels: usize) -> Vec<u8> {
    let img_len = w * h * channels;

    let mut reduced = vec![0; img_len];

    // top half of each byte is sufficient approx of 16->8 bit scaling
    for idx in 0..img_len {
        let num16 = u16::from_ne_bytes([orig[idx*2], orig[idx*2+1]]);
        reduced[idx] = (num16 >> 8) as u8;
    }

    reduced
}

fn convert_format(data: Vec<u8>, img_n: usize, req_comp: usize, x: usize, y: usize) -> Result<Vec<u8>> {
    todo!()
}

fn convert_format16(data: &[u8], img_n: usize, req_comp: usize, x: usize, y: usize) -> Result<Vec<u8>> {
    for code in data.chunks_exact(2) {
        let code = ((code[0] as u16) << 8) | code[1] as u16;
    }

    todo!()
}

fn mul2sizes_valid(a: usize, b: usize) -> bool {
    if b == 0 { return true; }
    a <= usize::MAX / b
}

fn addsizes_valid(a: usize, b: usize) -> bool {
    return a <= usize::MAX - b;
}

fn mad3sizes_valid(a: usize, b: usize, c: usize, add: usize) -> bool {
    mul2sizes_valid(a, b) && mul2sizes_valid(a*b, c) && addsizes_valid(a*b*c, add)
}

fn mad2sizes_valid(a: usize, b: usize, add: usize) -> bool {
    mul2sizes_valid(a, b) && addsizes_valid(a*b, add)
}

fn paeth(a: i32, b: i32, c: i32) -> i32 {
    let p = a + b - c;
    let pa = (p-a).abs();
    let pb = (p-b).abs();
    let pc = (p-c).abs();
    if pa <= pb && pa <= pc { return a; }
    if pb <= pc { return b; }
    c
}
