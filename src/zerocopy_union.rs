//! Safe unions.

macro_rules! zerocopy_union {
    (impl($vis:vis) $name:ident $($field:ident $fieldmut:ident: $type:ty),*) => {
        impl $name {
            $(
                #[allow(dead_code)]
                $vis fn $field(&self) -> &$type {
                    zerocopy::transmute_ref!(self)
                }
                #[allow(dead_code)]
                $vis fn $fieldmut(&mut self) -> &mut $type {
                    zerocopy::transmute_mut!(self)
                }
            )*
        }
    };
    (
        $vis:vis union $name:ident {
            $firstname:ident $firstname_mut:ident: $first:ty
            $(,$restname:ident $restname_mut:ident: $rest:ty)*
        }
    ) => {
        #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
        $vis struct $name(#[expect(dead_code)] $first);
        $crate::zerocopy_union::zerocopy_union!(impl($vis) $name $firstname $firstname_mut: $first
            $(, $restname $restname_mut: $rest)*);
    };
}

pub(crate) use zerocopy_union;
