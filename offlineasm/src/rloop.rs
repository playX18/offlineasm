// Register is the storage for an emulated CPU register.
// It defines the policy of how ints smaller than `isize` are packed into the
// pseudo register, as well as hides endianness differences.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Register {
    pub value: u64,
}

impl Register {
    pub fn i(self) -> isize {
        self.value as isize
    }

    pub fn i_mut(&mut self) -> *mut isize {
        &mut self.value as *mut u64 as *mut isize
    }

    pub fn u(self) -> usize {
        self.value as usize
    }

    pub fn u_mut(&mut self) -> *mut usize {
        &mut self.value as *mut u64 as *mut usize
    }

    pub fn f64_mut(&mut self) -> *mut f64 {
        &mut self.value as *mut u64 as *mut f64
    }

    pub fn f32_mut(&mut self) -> *mut f32 {
        &mut self.value as *mut u64 as *mut f32
    }

    pub fn i32(self) -> i32 {
        self.value as i32
    }

    pub fn i32_mut(&mut self) -> *mut i32 {
        &mut self.value as *mut u64 as *mut i32
    }

    pub fn u32(self) -> u32 {
        self.value as u32
    }

    pub fn u32_mut(&mut self) -> *mut u32 {
        &mut self.value as *mut u64 as *mut u32
    }

    pub fn i8(self) -> i8 {
        self.value as i8
    }

    pub fn i8_mut(&mut self) -> *mut i8 {
        &mut self.value as *mut u64 as *mut i8
    }

    pub fn u8(self) -> u8 {
        self.value as u8
    }

    pub fn u8_mut(&mut self) -> *mut u8 {
        &mut self.value as *mut u64 as *mut u8
    }

    pub fn ip(self) -> *mut isize {
        self.value as *mut isize
    }

    pub fn ip_mut(&mut self) -> *mut *mut isize {
        &mut self.value as *mut u64 as *mut *mut isize
    }

    pub fn ptr(self) -> *mut u8 {
        self.value as *mut u8
    }

    pub fn ptr_mut(&mut self) -> *mut *mut u8 {
        &mut self.value as *mut u64 as *mut *mut u8
    }

    pub fn reg_ptr(self) -> *mut Register {
        self.value as *mut Register
    }

    pub fn reg_ptr_mut(&mut self) -> *mut *mut Register {
        &mut self.value as *mut u64 as *mut *mut Register
    }

    pub fn i64(self) -> i64 {
        self.value as i64
    }

    pub fn u64(self) -> u64 {
        self.value as u64
    }

    pub fn i64_mut(&mut self) -> *mut i64 {
        &mut self.value as *mut u64 as *mut i64
    }

    pub fn u64_mut(&mut self) -> *mut u64 {
        &mut self.value as *mut u64 as *mut u64
    }

    pub fn f64(self) -> f64 {
        f64::from_bits(self.value)
    }

    pub fn f32(self) -> f32 {
        f32::from_bits(self.value as u32)
    }

    pub fn bits_as_f64(self) -> f64 {
        f64::from_bits(self.value)
    }

    pub fn bits_as_f32(self) -> f32 {
        f32::from_bits(self.value as u32)
    }

    pub fn bits_as_i64(self) -> i64 {
        self.value as i64
    }

    pub fn bits_as_u64(self) -> u64 {
        self.value
    }

    pub fn from_u(u: usize) -> Self {
        Self { value: u as u64 }
    }

    pub fn from_i(i: isize) -> Self {
        Self { value: i as u64 }
    }

    pub fn from_i8(i: i8) -> Self {
        Self { value: i as u64 }
    }

    pub fn from_u8(u: u8) -> Self {
        Self { value: u as u64 }
    }

    pub fn from_i32(i: i32) -> Self {
        Self { value: i as u64 }
    }

    pub fn from_u32(u: u32) -> Self {
        Self { value: u as u64 }
    }

    pub fn from_i64(i: i64) -> Self {
        Self { value: i as u64 }
    }

    pub fn from_u64(u: u64) -> Self {
        Self { value: u }
    }

    pub fn from_f64(f: f64) -> Self {
        Self { value: f.to_bits() }
    }

    pub fn from_f32(f: f32) -> Self {
        Self {
            value: f.to_bits() as u64,
        }
    }
}

pub struct Stack {
    ptr: *mut u8,
    size: usize,
}

impl Stack {
    pub fn new(size: usize) -> Self {
        let ptr = unsafe {
            let layout = ::alloc::alloc::Layout::from_size_align(size, 8).unwrap();
            let ptr = ::alloc::alloc::alloc(layout);
            ptr as *mut u8
        };
        Self { ptr, size }
    }

    pub fn start(&self) -> *mut u8 {
        self.ptr
    }

    pub fn end(&self) -> *mut u8 {
        unsafe { self.ptr.add(self.size) }
    }

    pub fn size(&self) -> usize {
        self.size
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        unsafe {
            ::alloc::alloc::dealloc(
                self.ptr as *mut u8,
                ::alloc::alloc::Layout::from_size_align(self.size, 8).unwrap(),
            );
        }
    }
}

impl From<usize> for Register {
    fn from(value: usize) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<isize> for Register {
    fn from(value: isize) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<u8> for Register {
    fn from(value: u8) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<i8> for Register {
    fn from(value: i8) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<i16> for Register {
    fn from(value: i16) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<u16> for Register {
    fn from(value: u16) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<i32> for Register {
    fn from(value: i32) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<u32> for Register {
    fn from(value: u32) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<u64> for Register {
    fn from(value: u64) -> Self {
        Self { value }
    }
}
impl From<i64> for Register {
    fn from(value: i64) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl From<f64> for Register {
    fn from(value: f64) -> Self {
        Self {
            value: value.to_bits(),
        }
    }
}

impl From<f32> for Register {
    fn from(value: f32) -> Self {
        Self {
            value: value.to_bits() as u64,
        }
    }
}

impl Into<usize> for Register {
    fn into(self) -> usize {
        self.value as usize
    }
}

impl Into<isize> for Register {
    fn into(self) -> isize {
        self.value as isize
    }
}

impl Into<u64> for Register {
    fn into(self) -> u64 {
        self.value
    }
}

impl Into<i64> for Register {
    fn into(self) -> i64 {
        self.value as i64
    }
}

impl Into<f64> for Register {
    fn into(self) -> f64 {
        f64::from_bits(self.value)
    }
}

impl Into<f32> for Register {
    fn into(self) -> f32 {
        f32::from_bits(self.value as u32)
    }
}

impl Into<i32> for Register {
    fn into(self) -> i32 {
        self.value as i32
    }
}

impl Into<u32> for Register {
    fn into(self) -> u32 {
        self.value as u32
    }
}

impl Into<i16> for Register {
    fn into(self) -> i16 {
        self.value as i16
    }
}

impl Into<u16> for Register {
    fn into(self) -> u16 {
        self.value as u16
    }
}

impl Into<i8> for Register {
    fn into(self) -> i8 {
        self.value as i8
    }
}

impl Into<u8> for Register {
    fn into(self) -> u8 {
        self.value as u8
    }
}

impl Into<()> for Register {
    fn into(self) -> () {
        ()
    }
}

impl<T> From<*mut T> for Register {
    fn from(value: *mut T) -> Self {
        Self {
            value: value as u64,
        }
    }
}

impl<T> From<*const T> for Register {
    fn from(value: *const T) -> Self {
        Self {
            value: value as u64,
        }
    }
}
