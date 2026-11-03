import Proof.Wire_3_5.UnionMachine.NumsPh2Base
import Proof.Wire_3_5.FinalPass.CoreIfaceBase

/-! # NW: the phase interface v3 over the relaxed contract `NumsMJ` (types only)

The `CoreWordsMJ` lets a writer's scratch residue hold ANY content, of length at most
`C_s F·(|fpIn|+1)^{D_s fe}`. v3 keeps v2's bank, roles, values (`NumsPh2.eOf`, `mOf`, `vOf`, `DenSplit`) and phase
shapes, and changes the residue:

* **`ResidJ σ B`**: every stream but `sIn`, `sW0`, `sW1` of length `≤ B` (any content);
* **`AfterC`** (c)'s exit: every stream but `sIn` exactly `[]` (phase (c) never writes a stream), so (a) and (b) dock
  raw machines (`dataDock`) on fresh streams; **`AfterV`**, **`DBank`**, **`Final`**: the word streams `[]` until (d)
  (tapes never shrink), the rest `ResidJ`;
* **`PhC`**, **`PhA`**, **`PhB`**, **`PhD`** (as v2, residues as above) and **`NumsOfPhases x l : PhC x l → PhA x l →
  PhB x l → PhD x → NumsMJ l`**.

Paper quantity of the main types: the final pass's denominator `Den` in `T_f`-bit binary (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsPh3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Finish NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

variable (x : ℕ)

/-- **The residue** (any content): every stream but `sIn`, `sW0`, `sW1` of length at most `B`. -/
def ResidJ (σ : St x) (B : ℕ) : Prop := ∀ i, i ≠ sIn x → i ≠ sW0 x → i ≠ sW1 x → (σ.st i).length ≤ B

section Bank

end Bank

/-- **(d)'s entry** (generic): `T`, `e`, `v` in `rT`, `rE`, `rV`, the input `w` on `sIn`, the word streams blank,
residue `B`. -/
structure DBank (σ : St x) (w : List Bool) (T e v B : ℕ) : Prop where
  hin : σ.st (sIn x) = w
  hw0 : σ.st (sW0 x) = []
  hw1 : σ.st (sW1 x) = []
  heads : ∀ i, σ.sh i = 0
  cell : σ.cell = false
  resid : ResidJ x σ B
  ht : σ.val rT = T
  he : σ.val rE = e
  hv : σ.val rV = v

/-- **The writer's exit** (`CoreWordsMJ.run`'s conclusion at the words `T`, `D`). -/
structure Final (σ : St x) (w : List Bool) (T D B : ℕ) : Prop where
  hw0 : σ.st (sW0 x) = frame (binary T 0)
  hw1 : σ.st (sW1 x) = frame (binary T D)
  hin : σ.st (sIn x) = w
  resid : ResidJ x σ B
  heads : ∀ i, σ.sh i = 0
  regs : ∀ q, σ.val q = 0

section Phases

end Phases

end NearCubicWires.WireExponent3_5.UnionMachine.NumsPh3
