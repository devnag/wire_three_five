import Proof.MachineModel.RuntimeShape
import Proof.SourceAssembly.SourceClearBound
import Proof.SourceAssembly.SourceLiveCount

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.Dimension
noncomputable section

/-! ## 1. Zero-head docking -/

/-! ## 2. The local layout -/

/-- First free tape after the `hR` polynomial block: `Rc`'s output. -/
def o1 (hR : ℕ) : ℕ := 64 + 2*hR
/-- `V`'s output. -/
def o2 (hR hV : ℕ) : ℕ := o1 hR + 15 + 2*hV
/-- The local universe. -/
def P (hR hV : ℕ) : ℕ := o2 hR hV + 2

variable (hR hV : ℕ)

def aV (i : ℕ) : ℕ := i
def lcV (j : ℕ) : ℕ := if j = 0 then 1 else 2 + j
def cV' (i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then 27 else if i = 2 then 29 else 30
def dV (i : ℕ) : ℕ := if i = 0 then 29 else if i = 1 then 31 else 32
def eV (j : ℕ) : ℕ := if j = 0 then 31 else 32 + j
def fV (i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then 49 else 50
def gV (j : ℕ) : ℕ := if j = 0 then 49 else 50 + j
def hVal (i : ℕ) : ℕ :=
  if i = 0 then 53 + 2*hR else if i = 1 then 45 else if i = 2 then o1 hR else o1 hR + 1
def iV (j : ℕ) : ℕ := if j = 0 then 49 else o1 hR + 1 + j
def jV (i : ℕ) : ℕ :=
  if i = 0 then o1 hR + 4 + 2*hV else if i = 1 then 45 else if i = 2 then o2 hR hV else o2 hR hV + 1

/-- Unfold the layout values and close an index (in)equality. -/
macro "lay" : tactic => `(tactic| (
  simp only [aV, lcV, cV', dV, eV, fV, gV, hVal, iV, jV, o1, o2, P,
    BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at *
  try split_ifs at *
  all_goals omega))

def aSl : Fin 3 → Fin (P hR hV) := fun i => ⟨aV i.val, by have := i.isLt; lay⟩
def lcSl : Fin 27 → Fin (P hR hV) := fun j => ⟨lcV j.val, by have := j.isLt; lay⟩
def cSl : Fin 4 → Fin (P hR hV) := fun i => ⟨cV' i.val, by have := i.isLt; lay⟩
def dSl : Fin 3 → Fin (P hR hV) := fun i => ⟨dV i.val, by have := i.isLt; lay⟩
def eSl : Fin 17 → Fin (P hR hV) := fun j => ⟨eV j.val, by have := j.isLt; lay⟩
def fSl : Fin 3 → Fin (P hR hV) := fun i => ⟨fV i.val, by have := i.isLt; lay⟩
def gSl : Fin (BlockPlatform.UnaryCalc.tapes hR) → Fin (P hR hV) :=
  fun j => ⟨gV j.val, by have := j.isLt; lay⟩
def hSl : Fin 4 → Fin (P hR hV) := fun i => ⟨hVal hR i.val, by have := i.isLt; lay⟩
def iSl : Fin (BlockPlatform.UnaryCalc.tapes hV) → Fin (P hR hV) :=
  fun j => ⟨iV hR j.val, by have := j.isLt; lay⟩
def jSl : Fin 4 → Fin (P hR hV) := fun i => ⟨jV hR hV i.val, by have := i.isLt; lay⟩

macro "injv" : tactic => `(tactic| (
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [aSl, lcSl, cSl, dSl, eSl, fSl, gSl, hSl, iSl, jSl] at hv
  apply Fin.ext
  lay))


/-! ## 3. The machine and its cost -/

/-! ## 4. The ten stages, each an exact `Step` on its own tapes (heads `0` in and out) -/

/-! ## 5. Bookkeeping: where each stage writes -/

macro "slv" : tactic => `(tactic| (
  intro j
  have hj := j.isLt
  simp only [aSl, lcSl, cSl, dSl, eSl, fSl, gSl, hSl, iSl, jSl] at *
  lay))



/-! ## 6. The named outputs -/


/-! ## 7. The pipeline run -/

/-! ## 8. Budget class, and the erasure condition -/

end
end NearCubicWires.SourceConstruction.Dimension
end
