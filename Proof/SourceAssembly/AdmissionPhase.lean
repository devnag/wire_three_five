import Proof.SourceAssembly.AdmissionRuntime
import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.PCP.PCPPQueryCachedBounds

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierEstimator NearCubicWires.RuntimeShape
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal

noncomputable section

section
variable {dP hT hS m L n qn : ℕ}

/-- **Multiplicities, two-sided**: a count bounded polynomially in both `n` and `qn` multiplies a class
quantity into the classes (no relation between `n` and `qn` needed). -/
theorem InClasses.count2 {cP cT cS x N nC nE : ℕ} (hNn : N ≤ nC*(n+1)^nE) (hNq : N ≤ nC*(qn+1)^nE)
    (hx : InClasses dP hT hS m L n qn cP cT cS x) :
    InClasses (nE+dP) (nE+hT) (nE+hS) m L n qn (nC*cP) (nC*cT) (nC*cS) (N*x) := by
  unfold InClasses splitRHS at *
  set T := 2^(qn - normalizedLiveCount qn L)
  set S := 2^(qn/m)
  have h1 : N*(cP*(n+1)^dP) ≤ nC*cP*(n+1)^(nE+dP) := by
    calc N*(cP*(n+1)^dP) ≤ nC*(n+1)^nE*(cP*(n+1)^dP) := Nat.mul_le_mul_right _ hNn
      _ = nC*cP*(n+1)^(nE+dP) := by rw [pow_add]; ring
  have h2 : N*(cT*((qn+1)^hT*T)) ≤ nC*cT*((qn+1)^(nE+hT)*T) := by
    calc N*(cT*((qn+1)^hT*T)) ≤ nC*(qn+1)^nE*(cT*((qn+1)^hT*T)) := Nat.mul_le_mul_right _ hNq
      _ = nC*cT*((qn+1)^(nE+hT)*T) := by rw [pow_add]; ring
  have h3 : N*(cS*((qn+1)^hS*S)) ≤ nC*cS*((qn+1)^(nE+hS)*S) := by
    calc N*(cS*((qn+1)^hS*S)) ≤ nC*(qn+1)^nE*(cS*((qn+1)^hS*S)) := Nat.mul_le_mul_right _ hNq
      _ = nC*cS*((qn+1)^(nE+hS)*S) := by rw [pow_add]; ring
  have hm := Nat.mul_le_mul_left N hx
  have e : N*(cP*(n+1)^dP + cT*((qn+1)^hT*T) + cS*((qn+1)^hS*S)) =
      N*(cP*(n+1)^dP) + N*(cT*((qn+1)^hT*T)) + N*(cS*((qn+1)^hS*S)) := by ring
  omega

/-- A constant `c` added to a class quantity. -/
theorem InClasses.add_const {cP cT cS x : ℕ} (c : ℕ) (hx : InClasses dP hT hS m L n qn cP cT cS x) :
    InClasses dP hT hS m L n qn (cP+c) cT cS (x+c) := by
  have h := hx.add (InClasses.const (dP := dP) (hT := hT) (hS := hS) (m := m) (L := L) (n := n)
    (qn := qn) c)
  simpa using h

/-- A polynomial count (in `n`) at an exponent `≤ dP` is source-polynomial. -/
theorem InClasses.poly {x c e : ℕ} (hx : x ≤ c*(n+1)^e) (he : e ≤ dP) :
    InClasses dP hT hS m L n qn c 0 0 x := by
  unfold InClasses splitRHS
  have := Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega : 0 < n+1) he)
  omega

end

/-! ## Per clause: `SourceTrace.budget` -/

/-! ## Per phase: `MaskedPhase`'s fuel -/

/-! ## Per branch: J5 from the three phases -/


end
end NearCubicWires.Admission
