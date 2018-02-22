use petgraph::visit::VisitMap;

use super::{IdSet, IntegerId};

impl<T: IntegerId> VisitMap<T> for IdSet<T> {
	#[inline]
	fn visit(&mut self, a: T) -> bool {
		!self.insert(a)
	}
	#[inline]
	fn is_visited(&self, value: &T) -> bool {
		self.contains(value)
	}
}