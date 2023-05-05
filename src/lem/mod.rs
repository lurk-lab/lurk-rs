mod ptr;
mod step;
mod store;
mod tag;

use std::collections::{BTreeMap, HashMap};

use crate::field::LurkField;

use self::{ptr::Ptr, store::Store, tag::Tag};

#[derive(PartialEq, Clone, Copy)]
pub struct MetaPtr<'a>(&'a str);

impl<'a> MetaPtr<'a> {
    #[inline]
    pub fn name(self) -> &'a str {
        self.0
    }
}

#[derive(Clone)]
pub enum LEMOP<'a, F: LurkField> {
    Set(MetaPtr<'a>, F, F),
    Copy(MetaPtr<'a>, MetaPtr<'a>),
    // Hide(MetaPtr<'a>, F, MetaPtr<'a>),
    // Open(MetaPtr<'a>, F),
    Hash2Ptrs(MetaPtr<'a>, F, [MetaPtr<'a>; 2]),
    Hash3Ptrs(MetaPtr<'a>, F, [MetaPtr<'a>; 3]),
    Hash4Ptrs(MetaPtr<'a>, F, [MetaPtr<'a>; 4]),
    Unhash2Ptrs([MetaPtr<'a>; 2], MetaPtr<'a>),
    Unhash3Ptrs([MetaPtr<'a>; 3], MetaPtr<'a>),
    Unhash4Ptrs([MetaPtr<'a>; 4], MetaPtr<'a>),
    MatchTag(MetaPtr<'a>, BTreeMap<F, LEMOP<'a, F>>, Box<LEMOP<'a, F>>),
    MatchVal(MetaPtr<'a>, BTreeMap<F, LEMOP<'a, F>>, Box<LEMOP<'a, F>>),
    Err(&'a str),
    Seq(Vec<LEMOP<'a, F>>),
}

impl<'a, F: LurkField + std::cmp::Ord> LEMOP<'a, F> {
    pub fn assert_tag_eq(
        ptr: MetaPtr<'a>,
        val: F,
        ff: LEMOP<'a, F>,
        tt: LEMOP<'a, F>,
    ) -> LEMOP<'a, F> {
        let mut map = BTreeMap::new();
        map.insert(val, tt);
        LEMOP::MatchTag(ptr, map, Box::new(ff))
    }

    pub fn assert_tag_or(
        ptr: MetaPtr<'a>,
        val1: F,
        val2: F,
        ff: LEMOP<'a, F>,
        tt: LEMOP<'a, F>,
    ) -> LEMOP<'a, F> {
        let mut map = BTreeMap::new();
        map.insert(val1, tt.clone());
        map.insert(val2, tt);
        LEMOP::MatchTag(ptr, map, Box::new(ff))
    }

    pub fn assert_list(ptr: MetaPtr<'a>, ff: LEMOP<'a, F>, tt: LEMOP<'a, F>) -> LEMOP<'a, F> {
        Self::assert_tag_or(ptr, Tag::Cons.to_field(), Tag::Nil.to_field(), ff, tt)
    }

    pub fn mk_cons(o: &'a str, i: [MetaPtr<'a>; 2]) -> LEMOP<'a, F> {
        LEMOP::Hash2Ptrs(MetaPtr(o), Tag::Cons.to_field(), i)
    }

    pub fn mk_strcons(o: &'a str, i: [MetaPtr<'a>; 2]) -> LEMOP<'a, F> {
        Self::assert_tag_eq(
            i[0],
            Tag::Char.to_field(),
            LEMOP::Err("strcons requires a char as the first argument"),
            Self::assert_tag_eq(
                i[1],
                Tag::Str.to_field(),
                LEMOP::Err("strcons requires a str as the second argument"),
                LEMOP::Hash2Ptrs(MetaPtr(o), Tag::Str.to_field(), i),
            ),
        )
    }

    pub fn mk_fun(o: &'a str, i: [MetaPtr<'a>; 3]) -> LEMOP<'a, F> {
        Self::assert_list(
            i[0],
            LEMOP::Err("The arguments must be a list"),
            Self::assert_list(
                i[2],
                LEMOP::Err("The closed env must be a list"),
                LEMOP::Hash3Ptrs(MetaPtr(o), Tag::Fun.to_field(), i),
            ),
        )
    }

    pub fn mk_match_tag(
        i: MetaPtr<'a>,
        cases: Vec<(F, LEMOP<'a, F>)>,
        def: LEMOP<'a, F>,
    ) -> LEMOP<'a, F> {
        let mut match_map = BTreeMap::default();
        for (f, op) in cases.iter() {
            match_map.insert(*f, op.clone());
        }
        LEMOP::MatchTag(i, match_map, Box::new(def))
    }

    pub fn mk_match_val(
        i: MetaPtr<'a>,
        cases: Vec<(F, LEMOP<'a, F>)>,
        def: LEMOP<'a, F>,
    ) -> LEMOP<'a, F> {
        let mut match_map = BTreeMap::default();
        for (f, op) in cases.iter() {
            match_map.insert(*f, op.clone());
        }
        LEMOP::MatchVal(i, match_map, Box::new(def))
    }
}

pub struct LEM<'a, F: LurkField> {
    input: [&'a str; 3],
    output: [&'a str; 3],
    lem_op: LEMOP<'a, F>,
}

impl<'a, F: LurkField + std::cmp::Ord + std::hash::Hash> LEM<'a, F> {
    pub fn check(&self) {
        for s in self.input.iter() {
            assert!(
                !self.output.contains(&s),
                "Input and output must be disjoint"
            )
        }
        // TODO: assert that all tag field elements are in range
        // TODO: assert that used pointers have been previously defined
        // TODO: assert that input pointers aren't overwritten (including the input)
        // TODO: assert that all input pointers are used
        // TODO: assert that all output pointers are defined
    }

    // pub fn compile should generate the circuit

    pub fn run(
        &self,
        i: [Ptr; 3],
        store: &mut Store<F>,
    ) -> Result<([Ptr; 3], HashMap<&'a str, Ptr>), String> {
        // key/val pairs on this map should never be overwritten
        let mut map: HashMap<&'a str, Ptr> = HashMap::default();
        map.insert(self.input[0], i[0]);
        map.insert(self.input[1], i[1]);
        map.insert(self.input[2], i[2]);
        let mut stack = vec![&self.lem_op];
        while let Some(op) = stack.pop() {
            match op {
                LEMOP::Set(tgt, tag, val) => {
                    let (idx, _) = store.ptr1_store.insert_full((*tag, *val));
                    let tgt_ptr = Ptr {
                        tag: Tag::from_field(*tag).unwrap(),
                        idx,
                    };
                    if map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined. Malformed LEM", tgt.name()));
                    }
                }
                LEMOP::Copy(tgt, src) => {
                    let src_ptr = map.get(src.name()).unwrap();
                    if map.insert(tgt.name(), src_ptr.clone()).is_some() {
                        return Err(format!("{} already defined. Malformed LEM", tgt.name()));
                    }
                }
                LEMOP::Hash2Ptrs(tgt, tag, src) => {
                    let src_ptr1 = map.get(src[0].name()).unwrap();
                    let src_ptr2 = map.get(src[1].name()).unwrap();
                    let (idx, _) = store.ptr2_store.insert_full((*src_ptr1, *src_ptr2));
                    let tgt_ptr = Ptr {
                        tag: Tag::from_field(*tag).unwrap(),
                        idx,
                    };
                    if map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined. Malformed LEM", tgt.name()));
                    }
                }
                LEMOP::Hash3Ptrs(tgt, tag, src) => {
                    let src_ptr1 = map.get(src[0].name()).unwrap();
                    let src_ptr2 = map.get(src[1].name()).unwrap();
                    let src_ptr3 = map.get(src[2].name()).unwrap();
                    let (idx, _) = store
                        .ptr3_store
                        .insert_full((*src_ptr1, *src_ptr2, *src_ptr3));
                    let tgt_ptr = Ptr {
                        tag: Tag::from_field(*tag).unwrap(),
                        idx,
                    };
                    if map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined. Malformed LEM", tgt.name()));
                    }
                }
                LEMOP::Hash4Ptrs(tgt, tag, src) => {
                    let src_ptr1 = map.get(src[0].name()).unwrap();
                    let src_ptr2 = map.get(src[1].name()).unwrap();
                    let src_ptr3 = map.get(src[2].name()).unwrap();
                    let src_ptr4 = map.get(src[3].name()).unwrap();
                    let (idx, _) = store
                        .ptr4_store
                        .insert_full((*src_ptr1, *src_ptr2, *src_ptr3, *src_ptr4));
                    let tgt_ptr = Ptr {
                        tag: Tag::from_field(*tag).unwrap(),
                        idx,
                    };
                    if map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined. Malformed LEM", tgt.name()));
                    }
                }
                LEMOP::Unhash2Ptrs(tgts, src) => {
                    let src_ptr = map.get(src.name()).unwrap();
                    let (x, y) = store.ptr2_store.get_index(src_ptr.idx).unwrap();
                    if map.insert(tgts[0].name(), *x).is_some() {
                        return Err(format!("{} already defined. Malformed LEM", tgts[0].name()));
                    }
                    if map.insert(tgts[1].name(), *y).is_some() {
                        return Err(format!("{} already defined. Malformed LEM", tgts[1].name()));
                    }
                }
                LEMOP::Seq(ops) => stack.extend(ops.iter().rev()),
                LEMOP::Err(s) => return Err(s.to_string()), // this should use the error continuation
                _ => todo!(),
            }
        }
        Ok((
            [
                *map.get(self.output[0]).unwrap(),
                *map.get(self.output[1]).unwrap(),
                *map.get(self.output[2]).unwrap(),
            ],
            map,
        ))
    }
}
