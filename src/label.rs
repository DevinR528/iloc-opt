use std::{
    borrow::Borrow,
    collections::{hash_map::Entry, HashMap},
    fmt, hash,
    sync::Mutex,
};

static LABEL_MAP: std::lazy::SyncLazy<Mutex<HashMap<String, OrdLabel>>> =
    std::lazy::SyncLazy::new(|| Mutex::new(HashMap::new()));

#[derive(Clone)]
pub struct OrdLabel(isize, String);

impl OrdLabel {
    // Create a new `OrdLabel, removing the `:` and without the sorting filler in the
    // front of the label.
    pub fn new(label: &str) -> Self { Self(111, label.to_string()) }

    pub fn new_add(sort: isize, label: &str) -> Self {
        match LABEL_MAP.lock().unwrap().entry(label.to_string()) {
            Entry::Occupied(o) => o.get().clone(),
            Entry::Vacant(v) => {
                let l = OrdLabel(sort, label.to_string());
                v.insert(l.clone());
                l
            }
        }
    }

    pub fn update(sort: isize, label: &str) {
        match LABEL_MAP.lock().unwrap().entry(label.to_string()) {
            Entry::Occupied(mut o) => {
                o.get_mut().0 = sort;
            }
            Entry::Vacant(_) => {
                unreachable!()
            }
        }
    }

    pub fn from_known(label: &str) -> Self { LABEL_MAP.lock().unwrap().get(label).unwrap().clone() }

    pub fn new_start(start: &str) -> Self {
        let l = Self(-1, format!(".F_{}", start));
        LABEL_MAP.lock().unwrap().entry(format!(".F_{}", start)).or_insert(l).clone()
    }

    pub fn as_str(&self) -> &str { &self.1 }
}

impl fmt::Display for OrdLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.as_str().fmt(f) }
}

impl fmt::Debug for OrdLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // write!(f, "({} {})", self.0, self.1)
        self.as_str().fmt(f)
    }
}

impl PartialEq for OrdLabel {
    fn eq(&self, other: &Self) -> bool { self.as_str().eq(other.as_str()) }
}

impl Eq for OrdLabel {}

impl hash::Hash for OrdLabel {
    fn hash<H: hash::Hasher>(&self, state: &mut H) { self.1.hash(state); }
}

impl PartialOrd for OrdLabel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.0.partial_cmp(&other.0) {
            Some(core::cmp::Ordering::Equal) => self.1.partial_cmp(&other.1),
            ord => ord,
        }
    }
}

impl Ord for OrdLabel {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            core::cmp::Ordering::Equal => self.1.cmp(&other.1),
            ord => ord,
        }
    }
}

impl PartialEq<str> for OrdLabel {
    fn eq(&self, other: &str) -> bool { self.as_str().eq(other) }
}

impl PartialEq<String> for OrdLabel {
    fn eq(&self, other: &String) -> bool { self.as_str().eq(other) }
}

impl Borrow<str> for OrdLabel {
    fn borrow(&self) -> &str { self.as_str() }
}
