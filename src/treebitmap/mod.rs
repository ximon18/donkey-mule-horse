/// Based on: https://blog.nlnetlabs.nl/donkeys-mules-horses/#pointerfree
///
/// An implementaton of a variable stride tree bitmap using nightly Rust support for const generics to represent with a
/// single Rust struct definition multiple different sized pfxbitarr and ptrbitarr bit arrays which via monomorphization
/// will be expanded at compile time to multiple different implementations. Bit arrays are defined as fixed length byte
/// arrays whose length is fixed at compile time for the stride size being represented. It is likely more efficient to
/// use different sized types instead of variable numbers of bytes, e.g. use u64 instead of [u8; 8], so this is just an
/// experimental approach, it is not expected to be fast enough for production use. An alternative approach might be to
/// use associated types for the bit arrays such as u64.
mod bitarrops;
mod error;
mod node;
mod tree;
mod variablenode;

pub use error::Error;
pub use tree::TreeBitMap;
