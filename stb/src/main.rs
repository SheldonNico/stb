fn main() {
    let data = vec![0, 0, 0, 128, 0, 0, 0, 0, 0]; let seed = 0;
    let h_sys = unsafe {
        let p = data.as_ptr() as *mut _;
        let len = data.len();

        stb_sys::stbds_hash_bytes(p, len, seed)
    };
    let h_stb = stb::ds::hash_bytes(&data, seed);

    eprintln!("{:?} {}: {}, {} =, {}", &data, seed, h_stb, h_sys, h_stb == h_sys);
}
