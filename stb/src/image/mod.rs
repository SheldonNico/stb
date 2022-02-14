#![allow(unused_variables)]
#![allow(dead_code)]
pub mod error;
pub mod context;
pub mod zlib;

pub use error::Error;
pub use context::Context;

use std::io::{Seek, Read};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, PartialEq)]
pub struct Image<T> {
    pub width: usize,
    pub height: usize,
    pub depth: usize,
    pub data: Vec<T>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImageMix {
    F32(Image<f32>),
    U8(Image<u8>),
}

impl ImageMix {
    // 8-bits-per-channel interface
    pub fn load_from_reader<R: Read+Seek>(reader: R, desired_channels: usize) -> Result<Self> {
        let mut ctx = Context::new(reader);
        let data = ctx.load_and_postprocess_8bit(desired_channels)?;
        Ok(Self::U8(Image {
            data,
            width: ctx.img_x,
            height: ctx.img_y,
            depth: ctx.img_n,
        }))
    }

    pub fn load_with_depth<P: AsRef<std::path::Path>>(fname: P, desired_channels: usize) -> Result<Self> {
        let f = std::fs::File::open(fname)?;
        Self::load_from_reader(f, desired_channels)
    }

    pub fn load<P: AsRef<std::path::Path>>(fname: P) -> Result<Self> {
        Self::load_with_depth(fname, 0)
    }
}

#[cfg(feature = "stb_sys")]
pub fn from_sys(r: stb_sys::LoadResult) -> Result<ImageMix> {
    match r {
        stb_sys::LoadResult::ImageU8(stb_sys::Image { width, height, depth, data }) => Ok(
            ImageMix::U8(
                Image {
                    width,
                    height,
                    depth,
                    data,
                }
            )
        ),
        stb_sys::LoadResult::ImageF32(stb_sys::Image { width, height, depth, data }) => Ok(
            ImageMix::F32(
                Image {
                    width,
                    height,
                    depth,
                    data,
                }
            )
        ),
        stb_sys::LoadResult::Error(err) => Err(Error::custom(err)),
    }
}
