//! Compile-time slice concat.

// idea from this reddit thread:
//   https://old.reddit.com/r/rust/comments/zqwggh/how_to_concat_two_const_slices_in_a_const_way/
// modified to make it expand each argument only once because otherwise the compiler chokes when
// nesting these

macro_rules! concat_slices {
    (@ignore $($_:tt)*) => {};
    ($(,)?) => {
        // special cased because the compiler will complain about unused variables in the
        // below case with zero expressions
        []
    };
    ($ty:ty; $($v:expr),* $(,)?) => {{
        const VS: &[&[$ty]] = &[$($v),*];
        let mut v = [0; {
            let mut num = 0;
            let mut i = 0;
            while i < VS.len() {
                num += VS[i].len();
                i += 1;
            }
            num
        }];
        let mut i = 0;
        let mut idx = 0;
        while i < VS.len() {
            let mut j = 0;
            while j < VS[i].len() {
                v[idx] = VS[i][j];
                j += 1;
                idx += 1;
            }
            i += 1;
        }
        v
    }};
    // ($($v:expr),* $(,)?) => {{
    //     let mut v = [0; 0 $(+ $v.len())*];
    //     let mut base = 0;
    //     $({
    //         let mut i = 0;
    //         while i < $v.len() {
    //             v[base+i] = $v[i];
    //             i += 1;
    //         }
    //         #[allow(unused_assignments)]
    //         { base += $v.len(); }
    //     })*
    //     v
    // }};
}

pub(crate) use concat_slices;
