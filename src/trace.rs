//! Debug output.

#[cfg(feature="trace")]
pub mod trace_impl {

    use core::sync::atomic::{AtomicU8, Ordering};

    use enumset::{EnumSet, EnumSetType};

    #[derive(EnumSetType)]
    pub enum TraceFlag {
        PARSE,
        TYPE,
        LOWER,
        OPTIMIZE,
        MEM,
        SCHEDULE,
        MCODE,
        CLIF,
        LINK
    }

    const FLAGS_UNSET: u8 = !0;
    static FLAGS: AtomicU8 = AtomicU8::new(FLAGS_UNSET);

    #[cold]
    fn init_flags() -> EnumSet<TraceFlag> {
        extern crate std;
        use TraceFlag::*;
        let mut flags: EnumSet<TraceFlag> = Default::default();
        if let Ok(v) = std::env::var("FHK_TRACE") {
            for &f in v.as_bytes() {
                flags.insert_all(match f {
                    b'p' => PARSE.into(),
                    b't' => TYPE.into(),
                    b'l' => LOWER.into(),
                    b'o' => OPTIMIZE.into(),
                    b'm' => MEM.into(),
                    b's' => SCHEDULE.into(),
                    b'c' => MCODE.into(),
                    b'f' => CLIF.into(),
                    b'k' => LINK.into(),
                    b'a' => EnumSet::all(),
                    _ => continue
                });
            }
        }
        FLAGS.store(flags.as_u8_truncated(), Ordering::Relaxed);
        flags
    }

    pub fn trace_flags() -> EnumSet<TraceFlag> {
        match FLAGS.load(Ordering::Relaxed) {
            FLAGS_UNSET => init_flags(),
            flags       => EnumSet::from_u8_truncated(flags)
        }
    }

    macro_rules! trace {
        () => { true };
        ($flag:ident) => {
            $crate::trace::trace_impl::trace_flags()
                .contains($crate::trace::trace_impl::TraceFlag::$flag)
        };
        ($fmt:literal $($v:tt)*) => {{
            extern crate std;
            std::eprintln!($fmt $($v)*);
        }};
        ($flag:ident $($v:tt)+) => {
            if $crate::trace::trace_impl::trace!($flag) {
                $crate::trace::trace_impl::trace!(
                    "{:-6} {}",
                    stringify!($flag),
                    format_args!($($v)+)
                )
            }
        };
    }

    pub(crate) use trace;

}

#[cfg(not(feature="trace"))]
mod trace_impl {
    macro_rules! trace {
        () => { false };
        ($_:ident) => { false };
        ($fmt: literal $($v:tt)*) => { if false { let _ = format_args!($fmt $($v)*); } };
        ($_:ident $($v:tt)+) => { if false { let _ = format_args!($($v)*); } };
    }
    pub(crate) use trace;
}

pub(crate) use trace_impl::trace;
