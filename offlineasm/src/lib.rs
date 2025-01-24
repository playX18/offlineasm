#[doc(hidden)]
pub use offlineasm_proc::{offlineasm_expand, offlineasm_internal};

#[macro_export]
macro_rules! offlineasm {
    ($($args:tt)*) => {
        $crate::offlineasm_internal! { $($args)* }
    }
}

pub mod instructions;