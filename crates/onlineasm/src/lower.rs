use super::Lbl;
use std::collections::HashMap;

/// Lowering failure from the shared expansion.
pub use offlineasm_ir::ExpandError as LowerError;

/// Mark for one `#[patch]` site in the emitted code. Turn it into a
/// location in the finished image with [`Finished::location`](crate::Finished::location).
#[derive(Clone, Copy, Debug)]
pub enum PatchHandle {
    /// A jump or call whose target can be changed.
    Jump(asmkit::PatchableJump),
    /// An immediate that can be rewritten.
    Data(asmkit::DataLabel),
}

impl PatchHandle {
    /// Returns the jump, or `None` when this is an immediate.
    pub fn jump(self) -> Option<asmkit::PatchableJump> {
        match self {
            PatchHandle::Jump(j) => Some(j),
            _ => None,
        }
    }

    /// Returns the immediate, or `None` when this is a jump.
    pub fn data(self) -> Option<asmkit::DataLabel> {
        match self {
            PatchHandle::Data(d) => Some(d),
            _ => None,
        }
    }

    /// Returns the jump.
    ///
    /// # Panics
    ///
    /// Panics if this is an immediate.
    #[allow(clippy::expect_used)]
    pub fn expect_jump(self) -> asmkit::PatchableJump {
        self.jump()
            .expect("onlineasm: patch handle is an immediate, not a jump")
    }

    /// Returns the immediate.
    ///
    /// # Panics
    ///
    /// Panics if this is a jump.
    #[allow(clippy::expect_used)]
    pub fn expect_data(self) -> asmkit::DataLabel {
        self.data()
            .expect("onlineasm: patch handle is a jump, not an immediate")
    }
}

/// Resolves IR labels to backend labels, minting fresh ones on demand.
pub struct LabelResolver<'a> {
    labels: &'a [asmkit::Label],
    fresh: HashMap<u32, asmkit::Label>,
}

impl<'a> LabelResolver<'a> {
    /// Creates a resolver over the bound `labels`.
    pub fn new(labels: &'a [asmkit::Label]) -> Self {
        Self {
            labels,
            fresh: HashMap::new(),
        }
    }

    /// Returns the backend label for `l`, minting one with `new_label` when
    /// the handle has no label yet.
    pub fn resolve(&mut self, l: Lbl, new_label: impl FnOnce() -> asmkit::Label) -> asmkit::Label {
        match l {
            Lbl::Bound(h) => self
                .labels
                .get(h.0 as usize)
                .copied()
                .unwrap_or_else(new_label),
            Lbl::Fresh(i) => *self.fresh.entry(i).or_insert_with(new_label),
        }
    }
}
