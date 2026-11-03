import Proof.Wire_3_5.Primitive.Writers.C3WCostPoly
import Proof.Wire_3_5.Compiler.MachineC3aDecBound

/-! # C3 request writer, part 18: C3a′'s steps at a call's pool request

`C3a.Class.cost_le_Y` with the request's numbers `h`, `Q'` bounded by the same `Z₀` as the input (the writer's
numbers are only bounded by `c_N(Ψ+1)`, not by a polynomial in `n`): **`c3a_cost_le`**.

Paper quantity: C3a′'s construction cost (P3:1612-1614, 1661-1664). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Lay
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Bound NearCubicWires.WireExponent3_5.CompilerMachine.C3a.DecBound
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.DecompositionSource

variable (a : DecompositionAlgorithm)

/-- **C3a′'s steps below the degree-4 polynomial at `Y = Z₀²(C+2)`** (plus the decomposition's cost). -/
theorem c3a_cost_le (R : PoolReq) (hR : R.Pre) (Z0 : ℕ) (hin : (C3a.c3aInput R).length ≤ Z0) (hn : R.n ≤ Z0)
    (hw : R.width ≤ Z0) (hh : R.h ≤ Z0) (hQ : R.Q ≤ Z0) (hG : R.gates.length ≤ Z0) (hF : R.flips.length ≤ Z0)
    (h1 : 1 ≤ Z0) :
    c3aCost a R ≤ 10246 * (Z0 * Z0 * (SourceEnvelope.capacity a (segR R).length + 2)) ^ 4 + cst4 a R := by
  have hq : R.n ≤ (segR R).length := C3a.Dec.arity_le_seg R.n R.gates
  have hi : (segment R.gates (List.replicate R.n true)).length ≤ 1000 * ((segR R).length + 2) ^ 2 :=
    C3a.Dec.seg_le_sq R.n R.gates
  have hPC : (segR R).length ≤ SourceEnvelope.capacity a (segR R).length :=
    SourceEnvelope.source_position a R.gates (List.replicate R.n true) _ hi
  obtain ⟨_, hBC, _, _, _, _⟩ := SourceEnvelope.actual_capacity a R.gates (List.replicate R.n true) _ hq hi
  generalize hCdef : SourceEnvelope.capacity a (segR R).length = C at hPC hBC
  generalize hYdef : Z0 * Z0 * (C + 2) = Y
  have hZZ : Z0 ≤ Z0 * Z0 := Nat.le_mul_of_pos_left _ (by omega)
  have hYZ : Z0 * Z0 ≤ Y := by rw [← hYdef]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hYC : C + 2 ≤ Y := by
    rw [← hYdef]
    have : 1 ≤ Z0 * Z0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact le_trans (le_of_eq (Nat.one_mul _).symm) (Nat.mul_le_mul_right _ this)
  have hYZC : Z0 * C ≤ Y := by
    rw [← hYdef]
    exact Nat.mul_le_mul hZZ (by omega)
  have hY1 : 1 ≤ Y := by omega
  have hBs := B_eq_sum a R.gates
  have hnL : nLeft R.side R.n ≤ R.n := by
    rw [C3a.Run.nLeft_eq R.side R.n hR.1, ← hR.1]; exact List.length_filter_le _ _
  have hnR : nRight R.side R.n ≤ R.n := by
    rw [C3a.Run.nRight_eq R.side R.n hR.1, ← hR.1]; exact List.length_filter_le _ _
  have hFB : R.flips.length * B a R.gates ≤ Y := le_trans (Nat.mul_le_mul hF (show B a R.gates ≤ C by omega)) hYZC
  have hFG : R.flips.length * R.gates.length ≤ Y := le_trans (Nat.mul_le_mul hF hG) hYZ
  have hGS : (GS a R.gates).length ≤ Y := by
    have : (GS a R.gates).length = B a R.gates := rfl
    omega
  have hpc : pcR a R ≤ poolT Y := by
    unfold pcR WcR BR FR
    rw [← hBs]
    exact pool_le _ _ _ _ _ _ _ _ _ _ _ _ Y (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hGS (by omega) (by omega) (by rw [counts_length]; omega)
  exact (c3aCost_le_gA a R Y (by omega) (by omega) (by omega) (by unfold BR; omega) (by unfold FR; omega)
    (by rw [hR.1]; omega) (by omega) (by omega) (by omega) (by unfold GR; omega) (by unfold PexR FR BR; omega)
    (by unfold kLR; omega) (by unfold kRR; omega) (by unfold FR GR; omega) (by unfold FR; rw [← hBs]; omega) hpc).trans
    (gA_le Y (cst4 a R) hY1)

/-- **C3a′'s steps, in the gate stream's length** (the decomposition's capacity and cost, `cap_le`, `dec_le`). -/
theorem c3a_cost_le2 (R : PoolReq) (hR : R.Pre) (Z0 : ℕ) (hin : (C3a.c3aInput R).length ≤ Z0) (hn : R.n ≤ Z0)
    (hw : R.width ≤ Z0) (hh : R.h ≤ Z0) (hQ : R.Q ≤ Z0) (hG : R.gates.length ≤ Z0) (hF : R.flips.length ≤ Z0)
    (h1 : 1 ≤ Z0) :
    c3aCost a R ≤ 10246 * (Z0 * Z0 * ((SourceEnvelope.coefficient a + 1) *
      ((segR R).length + 2) ^ (2 * degD a + 2) + 1)) ^ 4 + Kd a * ((segR R).length + 2) ^ (2 * degD a + 3) := by
  have c1 := c3a_cost_le a R hR Z0 hin hn hw hh hQ hG hF h1
  have c2 := cap_le a R.n R.gates
  have c3 := dec_le a R.n R.gates
  have e : SourceEnvelope.capacity a (segR R).length + 2 ≤
      (SourceEnvelope.coefficient a + 1) * ((segR R).length + 2) ^ (2 * degD a + 2) + 1 := by
    have : SourceEnvelope.capacity a (C3a.Dec.segOf R.n R.gates).length + 1 ≤ _ := c2
    unfold segR; omega
  have e4 : (Z0 * Z0 * (SourceEnvelope.capacity a (segR R).length + 2)) ^ 4 ≤
      (Z0 * Z0 * ((SourceEnvelope.coefficient a + 1) * ((segR R).length + 2) ^ (2 * degD a + 2) + 1)) ^ 4 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ e) 4
  have e5 : cst4 a R ≤ Kd a * ((segR R).length + 2) ^ (2 * degD a + 3) := c3
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
