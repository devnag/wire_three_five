import Proof.Packets.BudgetRestFree

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section

/-- **The two unary stages are small class** (their own `cost_le`, and AD `small_poly` at each degree). -/
theorem stages_small {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP) (rq : Request)
    (m sC sE tC tE : ℕ)
    (hse : (rq.smallSize a)^se.degree ≤ sC*smallClass m sE rq.q)
    (hsp : (rq.smallSize a)^sp.degree ≤ tC*smallClass m tE rq.q) :
    se.cost rq + sp.cost rq ≤ (se.coefficient*sC + sp.coefficient*tC) * smallClass m (sE + tE) rq.q := by
  have h1 := se.cost_le rq
  have h2 := sp.cost_le rq
  have m1 : smallClass m sE rq.q ≤ smallClass m (sE + tE) rq.q := smallClass_mono (by omega)
  have m2 : smallClass m tE rq.q ≤ smallClass m (sE + tE) rq.q := smallClass_mono (by omega)
  have a1 : se.cost rq ≤ se.coefficient*sC * smallClass m (sE + tE) rq.q :=
    calc se.cost rq ≤ se.coefficient * (rq.smallSize a)^se.degree := h1
      _ ≤ se.coefficient * (sC*smallClass m sE rq.q) := Nat.mul_le_mul_left _ hse
      _ ≤ se.coefficient * (sC*smallClass m (sE + tE) rq.q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ m1)
      _ = se.coefficient*sC * smallClass m (sE + tE) rq.q := by ring
  have a2 : sp.cost rq ≤ sp.coefficient*tC * smallClass m (sE + tE) rq.q :=
    calc sp.cost rq ≤ sp.coefficient * (rq.smallSize a)^sp.degree := h2
      _ ≤ sp.coefficient * (tC*smallClass m tE rq.q) := Nat.mul_le_mul_left _ hsp
      _ ≤ sp.coefficient * (tC*smallClass m (sE + tE) rq.q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ m2)
      _ = sp.coefficient*tC * smallClass m (sE + tE) rq.q := by ring
  have e : (se.coefficient*sC + sp.coefficient*tC) * smallClass m (sE + tE) rq.q =
      se.coefficient*sC * smallClass m (sE + tE) rq.q + sp.coefficient*tC * smallClass m (sE + tE) rq.q := by ring
  omega

/-- **The two binary counts are small class**, from polynomial bounds of the counts in `smallSize = S ≥ 1`. -/
theorem counts_small (e p S ce de cp dp : ℕ) (hS : 1 ≤ S) (he : e ≤ ce*S^de) (hp : p ≤ cp*S^dp)
    (m sC sE q : ℕ) (hsm : S^(2*(de+dp)) ≤ sC*smallClass m sE q) :
    CloseoutRowsCountBinary.budget e + CloseoutRowsCountBinary.budget p ≤
      (992*(ce+cp+1)^2*sC) * smallClass m sE q := by
  set X := (ce+cp+1)*S^(de+dp) with hX
  have hS1 : S^de ≤ S^(de+dp) := Nat.pow_le_pow_right hS (by omega)
  have hS2 : S^dp ≤ S^(de+dp) := Nat.pow_le_pow_right hS (by omega)
  have hpos : 1 ≤ S^(de+dp) := Nat.one_le_pow _ _ hS
  have hX1 : 1 ≤ X := Nat.mul_pos (by omega) hpos
  have he' : e ≤ X := he.trans (le_trans (Nat.mul_le_mul_left _ hS1) (Nat.mul_le_mul_right _ (by omega)))
  have hp' : p ≤ X := hp.trans (le_trans (Nat.mul_le_mul_left _ hS2) (Nat.mul_le_mul_right _ (by omega)))
  have hee : e*e ≤ X*X := Nat.mul_le_mul he' he'
  have hpp : p*p ≤ X*X := Nat.mul_le_mul hp' hp'
  have hXX : X ≤ X*X := Nat.le_mul_of_pos_left _ hX1
  have hcb : CloseoutRowsCountBinary.budget e + CloseoutRowsCountBinary.budget p ≤ 248*(X*X) := by
    unfold CloseoutRowsCountBinary.budget
    have e1 : e^2 = e*e := by ring
    have e2 : p^2 = p*p := by ring
    rw [e1, e2]
    omega
  have hXsq : X*X = (ce+cp+1)^2 * S^(2*(de+dp)) := by rw [hX]; ring
  calc CloseoutRowsCountBinary.budget e + CloseoutRowsCountBinary.budget p ≤ 248*(X*X) := hcb
    _ = 248*((ce+cp+1)^2 * S^(2*(de+dp))) := by rw [hXsq]
    _ ≤ 248*((ce+cp+1)^2 * (sC*smallClass m sE q)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsm)
    _ ≤ (992*(ce+cp+1)^2*sC) * smallClass m sE q := by
        have : 248*((ce+cp+1)^2 * (sC*smallClass m sE q)) = 248*((ce+cp+1)^2*sC) * smallClass m sE q := by ring
        rw [this]
        exact Nat.mul_le_mul_right _ (by nlinarith)

end
end NearCubicWires.SourceBudget
end

