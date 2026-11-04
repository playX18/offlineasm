use super::Lbl;
use crate::ir::Label;
use smallvec::SmallVec;

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
    /// Handle number of `labels[0]` (see [`crate::Assembler::reset`]).
    base: u32,
    // A handful of virtual labels at most, and usually none. A `HashMap`
    // here pays for hashing and thread-local state on every instruction.
    fresh: SmallVec<[(u32, asmkit::Label); 2]>,
}

impl<'a> LabelResolver<'a> {
    /// Creates a resolver over the bound `labels`, whose first handle is
    /// `base`.
    pub fn new(labels: &'a [asmkit::Label], base: u32) -> Self {
        Self {
            labels,
            base,
            fresh: SmallVec::new(),
        }
    }

    /// Returns the backend label for `l`, creating one with `new_label` when
    /// the handle has no label yet.
    pub fn resolve(&mut self, l: Lbl, new_label: impl FnOnce() -> asmkit::Label) -> asmkit::Label {
        match l {
            Lbl::Bound(h) => {
                h.0.checked_sub(self.base)
                    .and_then(|i| self.labels.get(i as usize))
                    .copied()
                    .unwrap_or_else(new_label)
            }
            Lbl::Fresh(i) => {
                if let Some(pos) = self.fresh.iter().position(|&(id, _)| id == i) {
                    return self.fresh[pos].1;
                }
                let label = new_label();
                self.fresh.push((i, label));
                label
            }
        }
    }

    /// Returns the already-created backend label for the frontend handle `l`,
    /// or `None` when the handle does not belong to this assembler.
    ///
    /// Unlike [`LabelResolver::resolve`], this never creates a label, so it
    /// can be called from `&self` methods such as operand lowering.
    pub fn get(&self, l: Label) -> Option<asmkit::Label> {
        l.0.checked_sub(self.base)
            .and_then(|i| self.labels.get(i as usize))
            .copied()
    }
}
