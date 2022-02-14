fn main() {
    cc::Build::new()
        .file("./src/stb.c")
        .include("./3rdparty/stb")
        .compile("stb");
}
