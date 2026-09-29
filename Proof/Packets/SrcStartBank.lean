import Mathlib
import Proof.Packets.PacketsGlueMetaMul
import Proof.SourceAssembly.SourcePoolAdmissions

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Bank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. The layout -/

/-- The tail size (a closed function of `a`; here a constant). -/
def kOf (_a : DecompositionAlgorithm) : ℕ := 194

theorem kOf_eq (a : DecompositionAlgorithm) : kOf a = 194 := rfl

theorem base_eq (a : DecompositionAlgorithm) : Cold.Base a = SB a + 14 := rfl

theorem tapes_ge (a : DecompositionAlgorithm) : SB a + 28 ≤ Cold.tapes a := by
  simp only [Cold.tapes, Cold.Base, Cold.Power, CT, T, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]
  omega

/-- A tail tape. -/
def tl (a : DecompositionAlgorithm) (o : ℕ) (h : o < 194) : Fin (132 + Cold.tapes a + kOf a) :=
  ⟨132 + Cold.tapes a + o, by rw [kOf_eq]; omega⟩

/-- A bank tape. -/
def bk (a : DecompositionAlgorithm) (i : ℕ) (h : i < 132 + Cold.tapes a) : Fin (132 + Cold.tapes a + kOf a) :=
  ⟨i, by rw [kOf_eq]; omega⟩

@[simp] theorem tl_val (a : DecompositionAlgorithm) (o : ℕ) (h : o < 194) : (tl a o h).val = 132 + Cold.tapes a + o := rfl
@[simp] theorem bk_val (a : DecompositionAlgorithm) (i : ℕ) (h : i < 132 + Cold.tapes a) : (bk a i h).val = i := rfl

/-- The template tape (Cold `SB + 10`) and the capacity tape (Cold `Base`) of the bank. -/
def tT (a : DecompositionAlgorithm) : Fin (132 + Cold.tapes a + kOf a) := bk a (132 + SB a + 10) (by have := tapes_ge a; omega)
def tP (a : DecompositionAlgorithm) : Fin (132 + Cold.tapes a + kOf a) := bk a (132 + Cold.Base a) (by rw [base_eq]; have := tapes_ge a; omega)

@[simp] theorem tT_val (a : DecompositionAlgorithm) : (tT a).val = 132 + SB a + 10 := rfl
@[simp] theorem tP_val (a : DecompositionAlgorithm) : (tP a).val = 132 + SB a + 14 := rfl

/-! ## 2. The slot maps of the many-tape stages -/

/-! ## 3. The stage machines and the composite -/

section machines


end machines

end
end NearCubicWires.SourceStart.Bank

