import Lean
import Proof.Wire_3_5.Recovery.RecoveryBudgetBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoveryCaseTwo
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Recovery.RecoverySetupTwo
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion


noncomputable section


/-! # The Case-2 ledger at one source length (P3:3399-3430, 3616-3626, 3669-3697; D1.5)

Realizes `tr:completeness`'s conditions at the union machine's width `q = q(N)` of one source length, at the gate's
constants: the grid (P3:3399-3403), the star hypotheses (P3:1188-1189), the fit conditions (P3:3106-3107), the name
count (P3:3078), the envelopes (P3:3068-3072), the parity (P3:3409-3410), the cap `tr:B` (P3:3425-3430), the endpoint
and propagated errors (P3:3075-3076, 3616-3624), and the guess budget (P3:3675-3680).

Paper quantities: the gate relations the recovery needs (**`GateRel l G`**: `A_pad`, the grid `s = C_δΛ̄²` at `C_Λ = 2`,
`C_par = 2`, `1/β⁻¹ ≤ β`, positive native coefficients, name count `≥ 2`, `kDeg ≥ 2`, `descDeg, carrierDeg ≥ 26`) and
the record `CaseTwoLedger` at one source length (**`ledger_at`**), from the per-length facts. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)

/-- **The gate relations of the recovery leaf** (the gate constants the union's completeness reads). -/
structure GateRel (l : Literals) (G : Split.Gate) : Prop where
  apad : G.Apad = gateApad l
  sp : G.row.sp = rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l)
  cpar : G.row.cap.Cpar = 2
  betaInv : 1 ≤ G.row.cap.betaInv
  beta : 1 / (G.row.cap.betaInv : ℝ) ≤ ((gateCParams1 l).β : ℝ)
  aT : 1 ≤ G.row.cap.aT
  aS : 1 ≤ G.row.cap.aS
  name : 2 ≤ G.nameCount
  kdeg : 2 ≤ G.kDeg
  desc : 26 ≤ G.descDeg
  carrier : 26 ≤ G.carrierDeg

section LedgerAt
variable (l : Literals) (G : Split.Gate) (hG : GateRel l G) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

include hG in
/-- **The Case-2 ledger at one source length** from the per-length facts at `q = q(N)`. -/
noncomputable def ledger_at (P : FusedPrimitive (G.inputs kclk coef A a ha)) (m : Mode) {N : ℕ} (z : BitInput N)
    (Γ : NearCubicGates.Close.Outer.OuterGuess ((recSetup2 l G kclk coef A a ha).width N))
    (q : ℕ) (hq : ((recSetup2 l G kclk coef A a ha).request z Γ).arity = q) (hq1 : 1 ≤ q)
    (hstar : Even (rowBr G.row.cr q) ∧ 2 ≤ rowBr G.row.cr q ∧ 4 * rowBr G.row.cr q ≤ q ∧
      Lq q ≤ starWidth (rowBr G.row.cr q) q ∧ starWidth (rowBr G.row.cr q) q ≤ Lq q ^ G.kDeg)
    (hfit : (G.budget kclk coef A a ha).FitsAt q)
    (W : ℕ) (hW : (W : ℝ) ≤ wireCap G.row.cap m q) (hW4 : W + 1 ≤ 2 * (q + 1) ^ 4) (hWq : q ≤ W)
    (hsp : G.row.sp q ≤ q)
    (Ldesc : ℕ) (hLd : Ldesc ≤ (q + 1) ^ 26) (hLd1 : 1 ≤ Ldesc)
    (hξ : 1 / (2 : ℝ) ^ (G.filterErrDeg * Nat.clog 2 (q + 2)) ≤ ((gateCParams1 l).ξ : ℝ))
    (hD : (1 + (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q : ℝ)) ^ 4 * (q : ℝ) ^ (-(G.D : ℝ)) ≤
      ((gateParams1 l).eps0 : ℝ))
    (Ko Kc : ℕ) (hO : (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairWord Γ).length ≤ Ko)
    (hcodeC : ∀ C : m.Circuit q, m.descriptionBits C ≤ Ldesc → (natWord (m.code C)).length ≤ Kc)
    (hbudget : 1 + Ko + (((recSetup2 l G kclk coef A a ha).pcppOf z Γ).systematicBits +
      ((recSetup2 l G kclk coef A a ha).pcppOf z Γ).auxiliaryBits) * (G.row.sp q * (4 + Kc)) ≤ N / 16) :
    CaseTwoLedger (recSetup2 l G kclk coef A a ha) z Γ m P (gateCParams1 l)
      (massCap (gateCParams1 l).ζ (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) W Ldesc := by
  have hδ := gateDelta_pos l
  have hCδ := gateCδ1_pos l
  have hStar : (G.inputs kclk coef A a ha).StarAt ((recSetup2 l G kclk coef A a ha).request z Γ).arity := by
    rw [hq]; exact hstar
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hcarr : (q + 1) ^ 26 ≤ (q + 1) ^ G.carrierDeg := Nat.pow_le_pow_right (by omega) hG.carrier
  have hdescd : (q + 1) ^ 26 ≤ (q + 1) ^ G.descDeg := Nat.pow_le_pow_right (by omega) hG.desc
  have h4 : (q + 1) ^ 4 ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hc' : ∀ C : m.Circuit ((recSetup2 l G kclk coef A a ha).request z Γ).arity,
      m.descriptionBits C ≤ Ldesc → (natWord (m.code C)).length ≤ Kc := by
    rw [hq]; exact hcodeC
  exact
  { hA := by
      show _ ≤ ((gridMassOf (gateCδ1 l) G.row.sp ((recSetup2 l G kclk coef A a ha).request z Γ).arity : ℚ) : ℝ)
      rw [hq, hG.sp]
      exact massCap_le_gridMass (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hΛ := by
      show 1 ≤ ((gridMassOf (gateCδ1 l) G.row.sp ((recSetup2 l G kclk coef A a ha).request z Γ).arity : ℚ) : ℝ)
      rw [hq, hG.sp]
      exact one_le_gridMass (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hs := by
      show 1 ≤ G.row.sp ((recSetup2 l G kclk coef A a ha).request z Γ).arity
      rw [hq, hG.sp]
      exact one_le_gridSize (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hsδ := gridMass_hsδ (gateCδ1 l) G.row.sp _ hδ.le (gateCδ1_spec l) _
    hStar := hStar
    hFit := by rw [hq]; exact hfit
    hname := hG.name
    hdesc := by rw [hq]; exact hLd.trans hdescd
    hdescK := by
      show m.descriptionBits (unionConstAtom m _) ≤ _
      rw [unionConstAtom_descriptionBits]
      exact Nat.one_le_pow _ _ (by omega)
    hdescP := fun Sp => by
      show m.descriptionBits (unionParityAtom m _ Sp) ≤ _
      refine (unionParityAtom_descriptionBits_le m _ Sp).trans ?_
      rw [hq]; exact h4.trans hdescd
    hKP := fun Sp => by
      show (m.gates (unionParityAtom m _ Sp)).length ≤ W
      refine (unionParityAtom_gates_length m _ Sp).trans ?_
      rw [hq]; exact hWq
    hlen := by
      rw [hq]
      have h1 : (G.row.sp q + 1) * W ≤ (q + 1) * (2 * (q + 1) ^ 4) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (q + 1) * (2 * (q + 1) ^ 4) ≤ (q + 1) ^ 26 := by
        have e : (q + 1) * (2 * (q + 1) ^ 4) = 2 * (q + 1) ^ 5 := by ring
        have h5 : 2 * (q + 1) ^ 5 ≤ (q + 1) ^ 6 := by
          calc 2 * (q + 1) ^ 5 ≤ (q + 1) * (q + 1) ^ 5 := Nat.mul_le_mul_right _ (by omega)
            _ = (q + 1) ^ 6 := by ring
        have h6 : (q + 1) ^ 6 ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
      exact (h1.trans h2).trans hcarr
    hbC := by rw [hq]; exact hLd.trans hcarr
    hbP := fun Sp gt hgt => by
      have h1 := unionParityAtom_encodingBits_le m _ Sp gt hgt
      have key : ∀ n : ℕ, 2 * n + 1 ≤ (n + 1) ^ G.carrierDeg := fun n => by
        have h2 : 2 * n + 1 ≤ (n + 1) ^ 2 := by
          calc 2 * n + 1 ≤ n * n + 2 * n + 1 := by omega
            _ = (n + 1) ^ 2 := by ring
        exact h2.trans (Nat.pow_le_pow_right (by omega) (by have := hG.carrier; omega))
      exact h1.trans (key _)
    Cpar := 2
    hCpar := by norm_num
    hwP := fun Sp => by
      have h1 := unionParityAtom_wires_le m ((recSetup2 l G kclk coef A a ha).request z Γ).arity Sp
      have h2 : (((m.gates (unionParityAtom m _ Sp)).wires : ℕ) : ℝ) ≤
          ((2 * ((recSetup2 l G kclk coef A a ha).request z Γ).arity ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact h2
    hcap := by
      have hq1' : 1 ≤ ((recSetup2 l G kclk coef A a ha).request z Γ).arity := by rw [hq]; exact hq1
      have hW' : (W : ℝ) ≤ wireCap G.row.cap m ((recSetup2 l G kclk coef A a ha).request z Γ).arity := by
        rw [hq]; exact hW
      have hc := hcap_of G.row.cap m ((G.inputs kclk coef A a ha).starParams _ hStar)
        (G.row.sp ((recSetup2 l G kclk coef A a ha).request z Γ).arity) W _ hq1' rfl
        hG.betaInv ((gateCParams1 l).β : ℝ) hG.beta hW'
      rw [hG.cpar] at hc
      push_cast at hc
      exact hc
    hξ := by rw [hq]; exact hξ
    hD := by
      show (1 + ((gridMassOf (gateCδ1 l) G.row.sp _ : ℚ) : ℝ)) ^ 4 * _ ≤ _
      rw [hq, hG.sp, gridMassOf_rowB (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q]
      exact_mod_cast hD
    Ko := Ko
    Ks := 4
    Kc := Kc
    hO := hO
    hKs := intWord_grid_le
    hcodeC := hc'
    hcodeK := hc' _ (by
      show m.descriptionBits (unionConstAtom m _) ≤ Ldesc
      rw [unionConstAtom_descriptionBits]; exact hLd1)
    hbudget := by
      have e : (recSetup2 l G kclk coef A a ha).gridSize ((recSetup2 l G kclk coef A a ha).request z Γ).arity =
          G.row.sp q := by
        show G.row.sp _ = _
        rw [hq]
      rw [e]; exact hbudget }

end LedgerAt
end Transfer
end WireExponent3_5
end NearCubicWires
end
