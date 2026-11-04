//! Reverse-order recording for [`Assembler<true>`](crate::Assembler).
//!
//! A backward assembler records every emission as a [`TapeItem`] instead of
//! lowering it immediately. [`crate::Assembler::finish`] then replays the tape
//! in reverse through the normal forward lowering, so the last-written
//! instruction executes first. Label handles creaed while recording are
//! virtual indices, the replay maps them onto real labels.

use super::ir::{Disp, Label, Lbl, Mnemonic, Op};
use super::lower::PatchHandle;
use smallvec::SmallVec;

/// Recorded operands. Instructions have at most a few, so the inline buffer
/// keeps recording allocation-free.
pub(super) type Ops = SmallVec<[Op; 4]>;

/// One recorded backward-assembler action.
///
/// `Bind` and `Embed` carry virtual labels (see [`ReverseTape`]); `Emit` and
/// `EmitPatched` operands may reference them through [`Lbl::Bound`].
pub(super) enum TapeItem {
    /// A recorded [`crate::Assembler::emit`] call.
    Emit { mnemonic: Mnemonic, ops: Ops },
    /// A recorded [`crate::Assembler::emit_patched`] call. The virtual patch
    /// id is implicit: `EmitPatched` items in record order own ids
    /// `0..patch_count`, so the replay collects their handles in reverse
    /// and flips the vector once.
    EmitPatched { mnemonic: Mnemonic, ops: Ops },
    /// A recorded [`crate::Assembler::bind`] of a virtual label.
    Bind(Label),
    /// A recorded [`crate::Assembler::align`].
    Align(u32),
    /// A recorded [`crate::Assembler::embed_data`]; `label` is virtual.
    Embed { data: Box<[u8]>, label: Label },
    /// A recorded raw-data write ([`crate::Assembler::emit_data`] or
    /// [`crate::Assembler::bind_data`]); `label` is virtual when present.
    Data {
        data: Box<[u8]>,
        label: Option<Label>,
        align: u32,
    },
}

/// Recording tape for a backward assembler.
///
/// Virtual labels are indices into the replay's label map, allocated densely
/// from zero by `label()` and `embed_data()`. Virtual patch ids are likewise
/// dense in record order over the [`TapeItem::EmitPatched`] items.
pub(super) struct ReverseTape {
    items: Vec<TapeItem>,
    next_virtual: u32,
    next_patch: u32,
    // Handles stay unique across `reset`: the next image numbers its labels
    // and patch sites from where the previous image stopped.
    virtual_base: u32,
    patch_base: u32,
}

impl ReverseTape {
    pub(super) fn new() -> Self {
        Self {
            items: Vec::new(),
            next_virtual: 0,
            next_patch: 0,
            virtual_base: 0,
            patch_base: 0,
        }
    }

    /// Drops the recorded items, keeping their allocations and advancing the
    /// handle bases so stale handles don't alias the next image.
    pub(super) fn reset(&mut self) {
        self.items.clear();
        self.virtual_base = self.virtual_base.saturating_add(self.next_virtual);
        self.patch_base = self.patch_base.saturating_add(self.next_patch);
        self.next_virtual = 0;
        self.next_patch = 0;
    }

    /// First virtual label number of the current image.
    pub(super) fn virtual_base(&self) -> u32 {
        self.virtual_base
    }

    /// First virtual patch number of the current image.
    pub(super) fn patch_base(&self) -> u32 {
        self.patch_base
    }

    pub(super) fn push_emit(&mut self, mnemonic: Mnemonic, ops: &[Op]) {
        self.items.push(TapeItem::Emit {
            mnemonic,
            ops: SmallVec::from_slice(ops),
        });
    }

    pub(super) fn push_emit_patched(&mut self, mnemonic: Mnemonic, ops: &[Op]) -> PatchHandle {
        let id = self.patch_base.saturating_add(self.next_patch);
        self.next_patch += 1;
        self.items.push(TapeItem::EmitPatched {
            mnemonic,
            ops: SmallVec::from_slice(ops),
        });
        PatchHandle::Virtual(id)
    }

    pub(super) fn push_bind(&mut self, label: Label) {
        self.check_virtual(label);
        self.items.push(TapeItem::Bind(label));
    }

    pub(super) fn push_align(&mut self, alignment: u32) {
        self.items.push(TapeItem::Align(alignment));
    }

    pub(super) fn push_embed(&mut self, data: &[u8]) -> Label {
        let label = self.next_virtual();
        self.items.push(TapeItem::Embed {
            data: data.into(),
            label,
        });
        label
    }

    /// Records a raw-data write. `label` (when binding) must be virtual.
    pub(super) fn push_data(&mut self, label: Option<Label>, align: u32, data: &[u8]) {
        if let Some(label) = label {
            self.check_virtual(label);
        }
        self.items.push(TapeItem::Data {
            data: data.into(),
            label,
            align,
        });
    }

    pub(super) fn next_virtual(&mut self) -> Label {
        let id = self.virtual_base.saturating_add(self.next_virtual);
        self.next_virtual += 1;
        Label(id)
    }

    /// Reports whether `label` is a virtual label created by this tape for
    /// the current image.
    pub(super) fn is_virtual(&self, label: Label) -> bool {
        label.0 >= self.virtual_base && label.0 - self.virtual_base < self.next_virtual
    }

    /// Returns the virtual-label count.
    pub(super) fn virtual_count(&self) -> u32 {
        self.next_virtual
    }

    /// Returns the virtual patch id count.
    pub(super) fn patch_count(&self) -> u32 {
        self.next_patch
    }

    /// Takes the recorded items, leaving an empty tape behind.
    pub(super) fn take(&mut self) -> Vec<TapeItem> {
        std::mem::take(&mut self.items)
    }

    #[allow(clippy::panic)]
    fn check_virtual(&self, label: Label) {
        if !self.is_virtual(label) {
            panic!("onlineasm: label handle does not belong to this assembler");
        }
    }
}

/// Resolves virtual label `v` to its replayed label.
///
/// `base` is [`ReverseTape::virtual_base`] for the replayed image.
///
/// # Panics
///
/// Panics when `v` is not a virtual label of this replay.
#[allow(clippy::panic)]
pub(super) fn remap_label(v: Label, real: &[Label], base: u32) -> Label {
    let index = v.0.checked_sub(base).and_then(|i| usize::try_from(i).ok());
    match index.and_then(|i| real.get(i)) {
        Some(&r) => r,
        None => panic!("onlineasm: label handle does not belong to this assembler"),
    }
}

/// Rewrites the [`Lbl::Bound`] virtual labels in `op` through `real`.
///
/// `Fresh` labels are scoped to one lowering and pass through untouched.
///
/// # Panics
///
/// Panics when a bound label is not a virtual label of this replay.
pub(super) fn remap_op(op: Op, real: &[Label], base: u32) -> Op {
    match op {
        Op::Label(Lbl::Bound(v)) => Op::Label(Lbl::Bound(remap_label(v, real, base))),
        Op::Mem(mut m) => {
            m.disp = match m.disp {
                Disp::Label(v) => Disp::Label(remap_label(v, real, base)),
                Disp::LabelFar(v) => Disp::LabelFar(remap_label(v, real, base)),
                other => other,
            };
            Op::Mem(m)
        }
        other => other,
    }
}

/// Rewrites the [`Lbl::Bound`] virtual labels in every operand of `ops` in
/// place.
///
/// See [`remap_op`].
pub(super) fn remap_ops(ops: &mut [Op], real: &[Label], base: u32) {
    for op in ops {
        *op = remap_op(*op, real, base);
    }
}
