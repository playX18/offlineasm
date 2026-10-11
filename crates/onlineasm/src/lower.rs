use super::Lbl;
use std::collections::HashMap;

/// Lowering failure from the shared expansion.
pub use offlineasm_ir::ExpandError as LowerError;

/// Mark for one `#[patch]` site in the emitted code.
///
/// Bound by `#[patch = name]` / `#[patch_abs = name]` in
/// [`onlineasm!`](crate::onlineasm), or returned by
/// [`Assembler::emit_patched`](crate::Assembler::emit_patched) (see it for
/// which instructions are patchable). Turn it into a location in the finished
/// image with [`Finished::location`](crate::Finished::location), then retarget
/// a jump with [`asmkit::repatch_jump_span`](crate::asmkit::repatch_jump_span)
/// or rewrite an immediate with
/// [`repatch_u64`](crate::repatch_u64).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PatchHandle {
    /// A jump or call (`#[patch]` on `jmp`/`call`/branches) whose target can
    /// be changed.
    Jump(asmkit::PatchableJump),
    /// An immediate (`#[patch]` on `move`, or the address slot of
    /// `#[patch_abs]`) that can be rewritten.
    Data(asmkit::DataLabel),
    /// A site recorded by a backward assembler. It holds no code position
    /// until [`finish`](crate::Assembler::finish) replays the tape. Resolve
    /// it with [`Finished::location`](crate::Finished::location) afterwards.
    Virtual(u32),
}

impl PatchHandle {
    /// Returns the jump, or `None` when this is an immediate or an
    /// unresolved backward handle.
    pub fn jump(self) -> Option<asmkit::PatchableJump> {
        match self {
            PatchHandle::Jump(j) => Some(j),
            _ => None,
        }
    }

    /// Returns the immediate, or `None` when this is a jump or an unresolved
    /// backward handle.
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
    /// Panics if this is an immediate or an unresolved backward handle.
    #[allow(clippy::panic)]
    pub fn expect_jump(self) -> asmkit::PatchableJump {
        match self {
            PatchHandle::Jump(j) => j,
            PatchHandle::Virtual(_) => panic!(
                "onlineasm: backward patch handle is unresolved; use `Finished::location` after `finish`"
            ),
            PatchHandle::Data(_) => panic!("onlineasm: patch handle is an immediate, not a jump"),
        }
    }

    /// Returns the immediate.
    ///
    /// # Panics
    ///
    /// Panics if this is a jump or an unresolved backward handle.
    #[allow(clippy::panic)]
    pub fn expect_data(self) -> asmkit::DataLabel {
        match self {
            PatchHandle::Data(d) => d,
            PatchHandle::Virtual(_) => panic!(
                "onlineasm: backward patch handle is unresolved; use `Finished::location` after `finish`"
            ),
            PatchHandle::Jump(_) => panic!("onlineasm: patch handle is a jump, not an immediate"),
        }
    }
}

/// Resolves IR labels to backend labels, creating fresh ones on demand.
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

    /// Returns the backend label for `l`, creating one with `new_label` when
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
