// ref to: https://github.com/servo/rust-stb-image/blob/master/src/stb_image.rs
use libc::*;
use std::path::Path;
use std::ffi::{CString, CStr};

#[allow(non_camel_case_types)]
pub type stbi_uc = c_uchar;

extern "C" {
    pub fn stbi_load_from_file(
        f: *mut FILE,
        x: *mut c_int,
        y: *mut c_int,
        comp: *mut c_int,
        req_comp: c_int,
    ) -> *mut stbi_uc;

    pub fn stbi_load_from_memory(
        buffer: *const stbi_uc,
        len: c_int,
        x: *mut c_int,
        y: *mut c_int,
        comp: *mut c_int,
        req_comp: c_int,
    ) -> *mut stbi_uc;
    pub fn stbi_loadf_from_memory(
        buffer: *const stbi_uc,
        len: c_int,
        x: *mut c_int,
        y: *mut c_int,
        comp: *mut c_int,
        req_comp: c_int,
    ) -> *mut c_float;
    pub fn stbi_image_free(retval_from_stbi_load: *mut c_void);
    pub fn stbi_is_hdr(filename: *const c_char) -> c_int;
    pub fn stbi_is_hdr_from_memory(buffer: *const stbi_uc, len: c_int) -> c_int;
    pub fn stbi_load(
        filename: *const c_char,
        x: *mut c_int,
        y: *mut c_int,
        comp: *mut c_int,
        req_comp: c_int,
    ) -> *mut stbi_uc;
    pub fn stbi_loadf(
        filename: *const c_char,
        x: *mut c_int,
        y: *mut c_int,
        comp: *mut c_int,
        req_comp: c_int,
    ) -> *mut c_float;
    pub fn stbi_failure_reason() -> *const c_char;

    pub fn stbds_hash_bytes(p: *mut c_void, len: usize, seed: size_t) -> size_t;
}

#[derive(Debug, Clone)]
pub enum LoadResult {
    Error(String),
    ImageU8(Image<u8>),
    ImageF32(Image<f32>),
}

#[derive(Debug, Clone)]
pub struct Image<T> {
    pub width: usize,
    pub height: usize,
    pub depth: usize,
    pub data: Vec<T>,
}

pub fn load<P: AsRef<Path>>(path: P) -> LoadResult {
    load_with_depth(path, 0, false)
}

pub fn load_with_depth<P: AsRef<Path>>(
    path: P,
    force_depth: usize,
    convert_hdr: bool,
) -> LoadResult {
    let mut width = 0 as c_int;
    let mut height = 0 as c_int;
    let mut depth = 0 as c_int;
    let force_depth = force_depth as c_int;
    let path_as_cstr = match path.as_ref().as_os_str().to_str() {
        Some(s) => match CString::new(s.as_bytes()) {
            Ok(s) => s,
            Err(_) => return LoadResult::Error("path contains null character".to_string()),
        },
        None => return LoadResult::Error("path is not valid utf8".to_string())
    };
    unsafe {
        let bytes = path_as_cstr.as_ptr();
        if !convert_hdr && stbi_is_hdr(bytes) != 0 {
            let buffer = stbi_loadf(bytes, &mut width, &mut height, &mut depth, force_depth);
            if buffer.is_null() {
                LoadResult::Error(fetch_reason().unwrap_or("stbi_loadf failed".to_string()))
            } else {
                let actual_depth = if force_depth != 0 { force_depth } else { depth };
                LoadResult::ImageF32(load_internal(buffer, width, height, actual_depth))
            }
        } else {
            let buffer = stbi_load(bytes, &mut width, &mut height, &mut depth, force_depth);
            if buffer.is_null() {
                LoadResult::Error(fetch_reason().unwrap_or("stbi_load failed".to_string()))
            } else {
                let actual_depth = if force_depth != 0 { force_depth } else { depth };
                LoadResult::ImageU8(load_internal(buffer, width, height, actual_depth))
            }
        }
    }
}

pub fn load_from_memory_with_depth(
    buffer: &[u8],
    force_depth: usize,
    convert_hdr: bool,
) -> LoadResult {
    let mut width = 0 as c_int;
    let mut height = 0 as c_int;
    let mut depth = 0 as c_int;
    let force_depth = force_depth as c_int;

    unsafe {
        if !convert_hdr && stbi_is_hdr_from_memory(buffer.as_ptr(), buffer.len() as c_int) != 0 {
            let buffer = stbi_loadf_from_memory(
                buffer.as_ptr(), buffer.len() as c_int, &mut width, &mut height, &mut depth, force_depth
            );
            if buffer.is_null() {
                LoadResult::Error(fetch_reason().unwrap_or("stbi_loadf_from_memory failed".to_string()))
            } else {
                let actual_depth = if force_depth != 0 { force_depth } else { depth };
                LoadResult::ImageF32(load_internal(buffer, width, height, actual_depth))
            }
        } else {
            let buffer = stbi_load_from_memory(
                buffer.as_ptr(), buffer.len() as c_int, &mut width, &mut height, &mut depth, force_depth
            );
            if buffer.is_null() {
                LoadResult::Error(fetch_reason().unwrap_or("stbi_load_from_memory failed".to_string()))
            } else {
                let actual_depth = if force_depth != 0 { force_depth } else { depth };
                LoadResult::ImageU8(load_internal(buffer, width, height, actual_depth))
            }
        }
    }
}

fn load_internal<T: Clone>(buf: *mut T, w: c_int, h: c_int, d: c_int) -> Image<T> {
    unsafe {
        // copy
        let data = std::slice::from_raw_parts(buf, (w*h*d) as usize).to_vec();
        stbi_image_free(buf as *mut c_void);
        Image::<T> {
            width: w as usize,
            height: h as usize,
            depth: d as usize,
            data,
        }
    }
}

fn fetch_reason() -> Option<String> {
    unsafe {
        let ptr = stbi_failure_reason();
        if ptr.is_null() {
            None
        } else {
            let cs = CStr::from_ptr(ptr);
            Some(cs.to_str().unwrap_or("error is not utf8 str").to_string())
        }
    }
}
