import Platform.WMX
import Proof.Wire_3_5.Selection.SortRound

/-! # K3 `RecLoop`: a loop over a stream of framed records

The near-cubic-gates paper machine model: "When an algorithm consults a large table inside a loop, it first sorts the
relevant records by key and then merges, which costs a logarithmic factor over reading the records once." Every
pass over a table is one loop over its records. A **record stream** is the base sorter's format
(`StablePartition.stream`): the frames of nonempty words, then one `false` (**`recStream`**). Records here have one
fixed width `L` (numbers in records are fixed-width words, as in `BinW`).

`recLoop I Wk CI CW body`: for every record `w` of the stream on `I`, copy it to the work stream `Wk` (so `Wk` holds
`frame w`, head `0`: for a one-number record this is `NumOn Wk L (value w)`), then run `body`; at the end return `I`'s
head to `0`. The registers `CI` (position on `I`) and `CW` are the loop's counters. **`recLoop_spec`** is
invariant-style: from the consumer's per-record specs (`hbody`, record `i` taking `c i` steps) the loop reaches
`Inv N`, in `Σ_i (c i + 50L + 30) + 3` steps. The record copy is proof 3's `copyPair` loop (`Sort.copyLoop_rst`).
A nested loop is `recLoop` inside `recLoop` (the inner stream is rewound by the inner loop itself): `nestLoop`. -/

set_option autoImplicit false

namespace NearCubicGates.Close.Platform
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (copyPair emitB rst copyLoop_rst emitB_rst fwdA_rst rd_app0)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## Record streams -/

/-! ## Copying one record to the work stream -/

/-! ## The loop -/

section Loop

end Loop


/-! ## Output streams: appending records -/

/-- An output stream being written: `O` holds the bits `out` written so far over its old contents `L0`, its head
(counted in `CO`) just after them. -/
def OutOn (σ : WState ns nr) (O : Fin (ns + 1)) (CO : Fin nr) (out L0 : List Bool) : Prop :=
  σ.st O = overlay out L0 ∧ σ.sh O = out.length ∧ σ.val CO = out.length


/-! Programs are opaque to consumers: use the spec theorems. -/

end NearCubicGates.Close.Platform
