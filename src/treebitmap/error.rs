#[derive(Debug)]
pub enum Error {
    UnsupportedStrideSize(u8),
    UnsupportedTotalStrideSize,
}