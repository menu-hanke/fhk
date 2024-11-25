//! Compile-time slice concat.

// shamelessly yoinked from this reddit thread:
// https://old.reddit.com/r/rust/comments/zqwggh/how_to_concat_two_const_slices_in_a_const_way/

macro_rules! concat_slices {
    ($(,)?) => {
        // special cased because the compiler will complain about unused variables in the
        // below case with zero expressions
        []
    };
    ($($v:expr),* $(,)?) => {{
        let mut v = [0; 0 $(+ $v.len())*];
        let mut base = 0;
        $({
            let mut i = 0;
            while i < $v.len() {
                v[base+i] = $v[i];
                i += 1;
            }
            #[allow(unused_assignments)]
            { base += $v.len(); }
        })*
        v
    }};
}

pub(crate) use concat_slices;
