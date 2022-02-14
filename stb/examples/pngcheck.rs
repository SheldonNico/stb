// cargo r --example pngcheck -- '3rdparty/stb/tests/pngsuite/**/*.png'
use log::{info, error, trace};
use stb::image::*;

fn display_arr<T: Into<f32>+Copy>(r: &[T]) -> Vec<f32> {
    let n = r.len();
    let step = (n / 10) + if n % 10 == 0 { 0 } else { 1 };
    let mut out = vec![];
    for chunk in r.chunks(step) {
        let len = chunk.len() as f32;
        let mean: f32 = chunk.iter().map(|&i| i.into() / len).sum();
        out.push(mean.round());
    }

    out
}

fn display_result(r: &Result<ImageMix>) -> String {
    match r {
        Ok(ImageMix::U8(r)) => {
            format!("{}x{}x{} ({}): {:?}", r.width, r.height, r.depth, r.data.len(), &display_arr(&r.data))
        },
        Ok(ImageMix::F32(r)) => {
            format!("{}x{}x{} ({}): {:?}", r.width, r.height, r.depth, r.data.len(), &display_arr(&r.data))
        },
        Err(e) => {
            e.to_string()
        }
    }
}

#[cfg(not(feature = "stb_sys"))]
pub fn main() {
    println!("need stb_sys");
}

#[cfg(feature = "stb_sys")]
pub fn main() {
    dotenv::dotenv().ok();
    env_logger::init();

    let pattern = std::env::args().nth(1).unwrap();

    for entry in glob::glob(&pattern).expect("Fail to read glob pattern") {
        let fpath = &entry.expect("entry list failed");
        trace!("check... {}", fpath.display());

        let img2 = stb::image::from_sys(stb_sys::load(fpath));
        let img1 = stb::image::ImageMix::load(fpath);

        match (&img1, &img2) {
            (Ok(ImageMix::U8(r1)), Ok(ImageMix::U8(r2))) => {
                if r1.width == r2.width && r1.height == r2.height && r1.depth == r2.depth && r1.data == r2.data {
                    info!("EQ {}: {}", fpath.display(), display_result(&img1));
                } else {
                    eprintln!("(stb) {:?}", &r1.data[95..200]);
                    eprintln!("(sys) {:?}", &r2.data[95..200]);
                    error!("NE {}:\n\t(stb){}\n\t(sys){}", fpath.display(), display_result(&img1), display_result(&img2));
                }
            },
            (Ok(ImageMix::F32(r1)), Ok(ImageMix::F32(r2))) => {
                if r1.width == r2.width && r1.height == r2.height && r1.depth == r2.depth && r1.data == r2.data {
                    info!("EQ {}: {}", fpath.display(), display_result(&img1));
                } else {
                    error!("NE {}:\n\t(stb){}\n\t(sys){}", fpath.display(), display_result(&img1), display_result(&img2));
                }
            },
            (Err(e1), Err(e2)) => {
                info!("EQ {}(maybe): {:?} {:?}", fpath.display(), e1, e2);
            },
            _ => {
                error!("NE {}:\n\t(stb){}\n\t(sys){}", fpath.display(), display_result(&img1), display_result(&img2));
            },
        };
    }
}

