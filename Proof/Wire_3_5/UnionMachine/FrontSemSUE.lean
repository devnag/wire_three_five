import Proof.Wire_3_5.UnionMachine.FrontSemRun
import Proof.Wire_3_5.UnionMachine.FrontCaps

/-! # C6 front, the semantic core (7): the pinned setup's facts the front's run reads (P3:3633, 3669-3691)

At the pinned setup `SUE` (both branches: the refuter's hierarchy at `recL`, the language's elsewhere): the parity and
constant atoms are the union's, the grid is row B's (`sue_gridSize`, `sue_gridMass`), the thresholds and the oracle
degree are the gate's; the hierarchy the front simulates (**`hhOf`**), the substituted source's width
(**`sue_hq`**) and its PCPP output word (**`sue_hPO`**, `recSetup2_pcppOutput` / `unionSetupS1_pcppOutput`).

Paper quantity of the main types: the pinned setup's PCPP output of the substituted circuit. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemSUE
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.RepairRepresentation (pcppOutput)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU)

section SUE
variable (l : Literals) (F : GateFree l) (e coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

/-- **The hierarchy the front simulates**: the refuter's at `recL`, the language's elsewhere. -/
noncomputable def hhOf : OrdinaryHierarchy (fun n => n ^ (kE l e + 2)) := by
  classical exact if L = recL l (kE l e) then refH l (kE l e) else hierarchyOf hL

theorem sue_eq_rec (h : L = recL l (kE l e)) :
    SUE l F e coef A L hL = recSetup2 l (gate0 l F) (kE l e) coef A (aE l e) (haE l e) :=
  setupF_eq_rec l F (kE l e) coef A (aE l e) (haE l e) L hL h

theorem sue_eq_other (h : L ≠ recL l (kE l e)) :
    SUE l F e coef A L hL = unionSetupS1 l (gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL :=
  setupF_eq_other l F (kE l e) coef A (aE l e) (haE l e) L hL h

theorem hh_rec (h : L = recL l (kE l e)) : hhOf l e L hL = refH l (kE l e) := by
  unfold hhOf; rw [if_pos h]

theorem hh_other (h : L ≠ recL l (kE l e)) : hhOf l e L hL = hierarchyOf hL := by
  unfold hhOf; rw [if_neg h]

theorem sue_parity : (SUE l F e coef A L hL).parityAtom = unionParityAtom := by
  by_cases h : L = recL l (kE l e)
  · rw [sue_eq_rec l F e coef A L hL h]; rfl
  · rw [sue_eq_other l F e coef A L hL h]; rfl

theorem sue_const : (SUE l F e coef A L hL).constAtom = unionConstAtom := by
  by_cases h : L = recL l (kE l e)
  · rw [sue_eq_rec l F e coef A L hL h]; rfl
  · rw [sue_eq_other l F e coef A L hL h]; rfl

theorem sue_v0 : (SUE l F e coef A L hL).params.v0 = (gateParams1 l).v0 := by
  by_cases h : L = recL l (kE l e)
  · rw [sue_eq_rec l F e coef A L hL h]; rfl
  · rw [sue_eq_other l F e coef A L hL h]; rfl

theorem sue_thr : (SUE l F e coef A L hL).params.threshold = (gateParams1 l).threshold := by
  by_cases h : L = recL l (kE l e)
  · rw [sue_eq_rec l F e coef A L hL h]; rfl
  · rw [sue_eq_other l F e coef A L hL h]; rfl

theorem sue_G : (SUE l F e coef A L hL).G = recOracleDeg l := by
  by_cases h : L = recL l (kE l e)
  · rw [sue_eq_rec l F e coef A L hL h]; rfl
  · rw [sue_eq_other l F e coef A L hL h]; rfl

theorem sue_alg : (SUE l F e coef A L hL).pcppAlg = gatePCPP l := by
  by_cases h : L = recL l (kE l e)
  · rw [sue_eq_rec l F e coef A L hL h]; rfl
  · rw [sue_eq_other l F e coef A L hL h]; rfl

theorem sue_gridSize (q : ℕ) :
    (SUE l F e coef A L hL).gridSize q = rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) q := by
  rw [FrontCaps.S2_gridSize l (gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL]; rfl

theorem sue_gridMass (q : ℕ) :
    (SUE l F e coef A L hL).gridMass q = (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q : ℚ) := by
  rw [FrontCaps.S2_gridMass l (gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL]
  exact gridMassOf_rowB (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCδ1_pos l) q

/-- **The substituted source's width** is within the setup's width. -/
theorem sue_hq {N : ℕ} (x : BitInput N) :
    PCPPNativeHierarchyNodes.width (gateSource l) (kE l e) (hhOf l e L hL).coefficient (cpadOf (hhOf l e L hL))
      (VerifierEncoding.code (hhOf l e L hL).verifier) x ≤ (SUE l F e coef A L hL).pcp.nativeWidth N := by
  by_cases h : L = recL l (kE l e)
  · rw [hh_rec l e L hL h, sue_eq_rec l F e coef A L hL h]
    show _ ≤ max _ _
    exact nativeWidth_le l (refH l (kE l e)) (paddedWidth l (gate0 l F) (refH l (kE l e))) (fun _ => le_max_left _ _) x
  · rw [hh_other l e L hL h, sue_eq_other l F e coef A L hL h]
    show _ ≤ max _ _
    exact nativeWidth_le l (hierarchyOf hL) (paddedWidth l (gate0 l F) (hierarchyOf hL)) (fun _ => le_max_left _ _) x

/-- **The setup's PCPP output word is the substituted circuit's.** -/
theorem sue_hPO {N : ℕ} (x : BitInput N) :
    ∀ (O : BooleanCircuit ((SUE l F e coef A L hL).pcp.nativeWidth N))
      (hq : PCPPNativeHierarchyNodes.width (gateSource l) (kE l e) (hhOf l e L hL).coefficient (cpadOf (hhOf l e L hL))
        (VerifierEncoding.code (hhOf l e L hL).verifier) x ≤ (SUE l F e coef A L hL).pcp.nativeWidth N),
      pcppOutput ((SUE l F e coef A L hL).request x O) ((SUE l F e coef A L hL).pcppOf x O) =
        pcppOutput (PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) (kE l e)
          (hhOf l e L hL).coefficient (cpadOf (hhOf l e L hL)) (VerifierEncoding.code (hhOf l e L hL).verifier) x
          (le_max_right _ _) hq O))
          ((gatePCPP l).output (PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) (kE l e)
            (hhOf l e L hL).coefficient (cpadOf (hhOf l e L hL)) (VerifierEncoding.code (hhOf l e L hL).verifier) x
            (le_max_right _ _) hq O))) := by
  by_cases h : L = recL l (kE l e)
  · rw [hh_rec l e L hL h, sue_eq_rec l F e coef A L hL h]
    intro O hq
    exact recSetup2_pcppOutput l F (kE l e) coef A (aE l e) (haE l e) x O hq
  · rw [hh_other l e L hL h, sue_eq_other l F e coef A L hL h]
    intro O hq
    exact unionSetupS1_pcppOutput l F (kE l e) coef A (aE l e) (haE l e) L hL x O hq

end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemSUE
