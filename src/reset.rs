//! Reset management.

use zerocopy::Unalign;

use crate::bitmap::bitmap_array;
use crate::hash::HashMap;
use crate::index::{index, IndexArray};
use crate::mem::Offset;
use crate::obj::ObjRef;

// glossary:
//   reset id:         user code identifier for grouping variables that are reset together
//   reset set:        set of reset ids
//   reset map:        mapping of objref to the set of reset ids it is assigned to
//   breakpoints:      division of vmctx memory into disjoint intervals
//   reset mask:       set of breakpoints (intervals)
//   reset assignment: mapping of reset ids to reset masks

