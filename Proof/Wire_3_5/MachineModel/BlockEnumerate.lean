import Proof.Wire_3_5.MachineModel.BlockArith

/-! # Block v3 (S5): enumeration of all `w`-bit strings with a counter tape

Paper: the primitive's loops enumerate all strings of a fixed width.
- The final pass (P3:3046-3048): "At each of `2^{n−k}` columns, evaluate the reported lookup at these `Q`
  pairs."
- The common-coset selection (P3:1339-1340): "compute each candidate's objective. Enumerate its `2^k`
  error rows."
- Seed fixing counts over all completions (P3:2946-2952).

The paper quantity of the main type is the enumerated index: iteration `j` sees `binary (w+1) j` on the
counter tape. Its low `w` bits are the `j`-th `w`-bit string (`binary_succ_low`), and the output is the
concatenation of the per-string emissions `(List.range (2^w)).flatMap emit`.

`EnumBody` is a uniform work machine on `t` user tapes plus the counter bank, with a `Step` for every
`j < 2^w`. The work may read the counter but not move it. `EnumBody.cells` appends the counter
increment (`incrementBlock`, docked on the counter bank) and presents the result as a bounded loop
(`BlockPlatform.Cells`, bound `2^w`). `EnumBody.enumerate` is the whole loop as one `Step`, and
`EnumBody.within` puts its cost `2^w·(cost + 2w + 8) + 3` in any class whose exponent is at least `w`.
That is the "enumerate `2^w`" rule of the cost calculus, instantiated with a real machine. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.RecoveryRootRound

/-- The counter bank: `binary (w+1) j` and the increment's `w+1`-cell workspace. -/
def counterTapes (w j : ℕ) : Fin 2 → List Bool := ![binary (w + 1) j, List.replicate (w + 1) false]

/-- The layout of an enumeration cell: `t` user tapes, then the counter bank. -/
def enumTapes {t : ℕ} (D : Fin t → List Bool) (w j : ℕ) : Fin (t + 2) → List Bool :=
  Fin.addCases (m := t) (n := 2) (motive := fun _ => List Bool) D (counterTapes w j)

def enumHeads {t : ℕ} (H : Fin t → ℕ) : Fin (t + 2) → ℕ :=
  Fin.addCases (m := t) (n := 2) (motive := fun _ => ℕ) H (fun _ => 0)

/-- A uniform enumeration body: the work machine on the enumeration layout. At every `j < 2^w` it runs
from the cell with user data `data j out` and counter `j` to the cell with user data
`data (j+1) (out ++ emit j)` and the counter unchanged. -/
structure EnumBody (t s w : ℕ) where
  work : Machine (t + 2) s
  cost : ℕ
  heads : Fin t → ℕ
  data : ℕ → List Bool → Fin t → List Bool
  emit : ℕ → List Bool
  step : ∀ j, j < 2 ^ w → ∀ out, Step work cost (enumHeads heads) (enumTapes (data j out) w j)
    (enumHeads heads) (enumTapes (data (j + 1) (out ++ emit j)) w j)

namespace EnumBody
variable {t s w : ℕ}

theorem increment_step (w j : ℕ) (hj : j < 2 ^ w) :
    Step (Rewind.machine BinaryIncrement.machine) (2 * (w + 1) + 2) (fun _ => 0) (counterTapes w j)
      (fun _ => 0) (counterTapes w (j + 1)) := by
  have hj' : j + 1 < 2 ^ (w + 1) := by rw [pow_succ]; omega
  obtain ⟨hA, hH, hA', hH', _⟩ := incrementBlock_spec (w + 1) j hj'
  have h := (incrementBlock (w + 1) j hj').run
  rw [hA, hH, hA', hH'] at h
  exact h

end EnumBody

/-! ## Executable twin -/


end NearCubicWires.WireExponent3_5.Block
