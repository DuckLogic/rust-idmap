use std::ptr;

pub unsafe trait ArbitraryBytes: Copy {}
unsafe impl ArbitraryBytes for u8 {}
unsafe impl ArbitraryBytes for u32 {}
unsafe impl ArbitraryBytes for u64 {}

pub fn fill_bytes<T: ArbitraryBytes>(target: &mut Vec<T>, amount: usize, value: u8) {
    if amount > 0 {
        let len = target.len();
        target.reserve(amount);
        unsafe {
            let ptr = target.as_mut_ptr().offset(len as isize);
            ptr::write_bytes(ptr, value, amount);
            target.set_len(len + amount);
        }
    }
}
