import Proof.Wire_3_5.Primitive.Writers.WriterIfaceBase

/-! # PA (d): the batch writers' interface, v2 (residues on the work tapes)

`WriterIface.outBank` leaves `[]` on every tape but the two ports. No machine with scratch halts there:
`writeTapeBit` never yields `[]` (base `Statement.lean:1115-1120`) and `ClockJoin.ReadyRun` compares the final tapes
exactly. This file restates the machine types with the residues allowed (**`outBankJ`**: ports as before, tape `j`
holds `J j`), bounded by the writer's time bound (**`WriterRun`**: `∃ J, (∀ j, |J j| ≤ B) ∧ ReadyRun M B …`).

Everything else is imported unchanged from `WriterIface` (verified): the tapes `symTape`, `thrTape`,
`hashTape`, their values `sym_hD`, `thr_hD`, `hash_val`, `sym_entsOk`, `thr_entsOk`, the request words, `inBank`,
`WriterStage`.

* `outBankJ`, `WriterRun`; `outBankJ_in`, `outBankJ_out` (the ports), `WriterRun.of_ready` (the old form implies v2);
* **`SymWriterAtJ`**, **`ThrWriterAtJ`**, **`HashWriterAtJ`**, `WritersAtJ`, **`WriterLeafJ`** (SeedFixLeaf's order of
  choice: `fe`, then `E_W`, then `F`, then `c_W`).

Paper quantities of the main types: `SeedFix.symStateBits`/`thrStateBits` (row:matrix) through `symTape`/`thrTape`
(C4's `BAT` word) and the auxiliary filter on `thrZres` through `hashTape` (as in v1). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- **The writers' output bank, v2**: `frame w` kept on the input tape, the tape word `v` on the output tape, the
residue `J j` on every other tape. -/
def outBankJ {t : ℕ} (i o : Fin t) (w v : List Bool) (J : Fin t → List Bool) : Fin t → List Bool :=
  fun j => if j = i then frame w else if j = o then v else J j

theorem outBankJ_in {t : ℕ} (i o : Fin t) (w v : List Bool) (J : Fin t → List Bool) : outBankJ i o w v J i = frame w := by
  simp [outBankJ]

theorem outBankJ_out {t : ℕ} (i o : Fin t) (hio : i ≠ o) (w v : List Bool) (J : Fin t → List Bool) :
    outBankJ i o w v J o = v := by
  simp [outBankJ, Ne.symm hio]

/-- **A writer's run, v2**: from `inBank i w`, within `B` steps, the machine halts with every head at `0`, the input
kept, `v` on the output tape and residues of length at most `B` elsewhere. -/
def WriterRun {t s : ℕ} (M : Machine t s) (B : ℕ) (i o : Fin t) (w v : List Bool) : Prop :=
  ∃ J : Fin t → List Bool, (∀ j, (J j).length ≤ B) ∧ ClockJoin.ReadyRun M B (inBank i w) (outBankJ i o w v J)

section Writers
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

end Writers

end NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ
