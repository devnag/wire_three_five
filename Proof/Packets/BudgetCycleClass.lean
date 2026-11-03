import Proof.SourceAssembly.AdmissionPhase
import Proof.SourceAssembly.SourcePhaseFuel
import Proof.MachineModel.TopDownPaidBinaryReserves
import Proof.CaseAnalysis.FinalAppendPositioning
import Proof.Assembly.Family
import Proof.Assembly.NativeBase

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.Admission NearCubicWires.RuntimeShape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator

noncomputable section

/-! ## 1. The uniform capacity `V` and the three reserves -/

/-- The workspace reserve `(2·coef+20)(V+1)` in the classes, from `V`'s class. -/
theorem workspace_inClasses (printer : WilliamsAlgorithm) {dP hT hS m L n qn cP cT cS V : ℕ}
    (hV : InClasses dP hT hS m L n qn cP cT cS V) :
    InClasses dP hT hS m L n qn ((2*P1TopDownPaidReusableReserves.coefficient printer+20)*(cP+1))
      ((2*P1TopDownPaidReusableReserves.coefficient printer+20)*cT)
      ((2*P1TopDownPaidReusableReserves.coefficient printer+20)*cS)
      (P1TopDownPaidReusableReserves.workspace printer V) := by
  unfold P1TopDownPaidReusableReserves.workspace
  exact (hV.add_const 1).smul _

/-- The rewind reserve `(coef+2)(V+1)`. -/
theorem rewind_inClasses (printer : WilliamsAlgorithm) {dP hT hS m L n qn cP cT cS V : ℕ}
    (hV : InClasses dP hT hS m L n qn cP cT cS V) :
    InClasses dP hT hS m L n qn ((P1TopDownPaidReusableReserves.coefficient printer+2)*(cP+1))
      ((P1TopDownPaidReusableReserves.coefficient printer+2)*cT)
      ((P1TopDownPaidReusableReserves.coefficient printer+2)*cS)
      (P1TopDownPaidReusableReserves.rewind printer V) := by
  unfold P1TopDownPaidReusableReserves.rewind
  exact (hV.add_const 1).smul _

/-- The buffer reserve `V+1`. -/
theorem buffer_inClasses {dP hT hS m L n qn cP cT cS V : ℕ}
    (hV : InClasses dP hT hS m L n qn cP cT cS V) :
    InClasses dP hT hS m L n qn (cP+1) cT cS (P1TopDownPaidReusableReserves.buffer V) := by
  unfold P1TopDownPaidReusableReserves.buffer
  exact hV.add_const 1

/-! ## 2. Polynomial bookkeeping -/

/-- Products and sums of two `n`-polynomial quantities under one monomial. -/
theorem poly_mul {a b A B e f n : ℕ} (ha : a ≤ A*(n+1)^e) (hb : b ≤ B*(n+1)^f) :
    a*b ≤ (A*B)*(n+1)^(e+f) := by
  calc a*b ≤ (A*(n+1)^e)*(B*(n+1)^f) := Nat.mul_le_mul ha hb
    _ = (A*B)*(n+1)^(e+f) := by rw [pow_add]; ring

theorem poly_raise {a A e E n : ℕ} (ha : a ≤ A*(n+1)^e) (h : e ≤ E) : a ≤ A*(n+1)^E :=
  ha.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h))

/-! ## 3. The per-entry family fuel (`SourceTrace`'s `familyCost` bound) -/

/-! ## 4. The row family (`cycFuel`'s `Family.budget` summand) -/

/-- **The row family in the classes.** `|rows|·(rowFuel+3)+3` with `rowFuel ≤ rowBudget` in the classes and
the row count `q`-polynomial (`paper.tex:1203-1207`: the rows multiply the one-row charges once). -/
theorem familyBudget_inClasses {printer : WilliamsAlgorithm} {t : ℕ} {q L : ℕ} (F : PCJ9eff70d512234a4c_Fixed.Packets.Family q L)
    (s : PCJ38fbfed565f64139_Family.State (t := t) printer)
    {dP hT hS m L' n qn cP cT cS rb nC nE : ℕ}
    (hrow : s.rowFuel ≤ rb) (hrb : InClasses dP hT hS m L' n qn cP cT cS rb)
    (hNn : F.rows.length ≤ nC*(n+1)^nE) (hNq : F.rows.length ≤ nC*(qn+1)^nE) :
    InClasses (nE+dP) (nE+hT) (nE+hS) m L' n qn (nC*(cP+3) + 3) (nC*cT) (nC*cS)
      (PCJ38fbfed565f64139_Family.budget printer F s) := by
  unfold PCJ38fbfed565f64139_Family.budget
  rw [List.length_attach]
  have h1 := ((hrb.add_const 3).count2 hNn hNq).add_const 3
  refine InClasses.mono ?_ (h1.raise le_rfl le_rfl le_rfl)
  have := Nat.mul_le_mul_left F.rows.length (Nat.add_le_add_right hrow 3)
  omega

end
end NearCubicWires.SourceBudget

