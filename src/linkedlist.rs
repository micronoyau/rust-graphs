pub struct LinkedList<T: Ord> {
    pub next: Option<Box<LinkedList<T>>>,
    pub value: T,
}

impl<T: Ord> LinkedList<T> {
    pub fn push_front(self, value: T) -> Self {
        Self {
            next: Some(Box::new(self)),
            value,
        }
    }

    pub fn new(value: T) -> Self {
        LinkedList { next: None, value }
    }
}
