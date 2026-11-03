import Lean
import Proof.Wire_3_5.UnionMachine.FrontSemRunBase
import Proof.Wire_3_5.UnionMachine.FrontCaps
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Recovery.RecoverySetupTwo
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.PlanW2
import Proof.Wire_3_5.UnionMachine.UnionSetup
import Proof.Wire_3_5.UnionMachine.UnionCallCount
import Proof.Wire_3_5.UnionMachine.FrontCapsBase


noncomputable section
set_option maxRecDepth 120000


/-! # C6 front, the semantic core (7): the pinned setup's facts the front's run reads (P3:3633, 3669-3691)

At the pinned setup `SUE` (both branches: the refuter's hierarchy at `recL`, live; the language's elsewhere, dead):
the parity and constant atoms are the union's, the grid is row B's (`sue_gridSize`, `sue_gridMass`), the thresholds,
the oracle degree, the short PCP and the pointwise PCPP are the gate's; at `recL` the setup is live with the
succinct verifier `gateSV l` and the width `q(N)` of the ledger (**`sue_live`**, **`sue_width`**).

Paper quantity of the main types: the pinned setup's outer data (`𝒱_G`, `q(N)`, liveness). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemSUE
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.RepairRepresentation (pcppOutput)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU)

section SUE
variable (l : Literals) (F : GateFree l) (e coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

theorem sue_eq_rec (h : L = recL l (kE l e)) :
    SUE l F e coef A L hL = recSetup2 l (gate0 l F) (kE l e) coef A (aE l e) (haE l e) := by
  subst h; exact unionSetupS2_recL l (gate0 l F) (kE l e) coef A (aE l e) (haE l e) hL

theorem sue_eq_other (h : L ≠ recL l (kE l e)) :
    SUE l F e coef A L hL = unionSetupS1 l (gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL :=
  UnionCallCount.unionSetupS2_ne l (gate0 l F) coef A (aE l e) (kE l e) (haE l e) L hL h

/-- The recovered setup is live. -/
theorem sue_live (h : L = recL l (kE l e)) : (SUE l F e coef A L hL).live = true := by
  rw [sue_eq_rec l F e coef A L hL h]; rfl

/-- Off the recovered language the setup is dead. -/
theorem sue_dead (h : L ≠ recL l (kE l e)) : (SUE l F e coef A L hL).live = false := by
  rw [sue_eq_other l F e coef A L hL h]; rfl

/-- **The recovered setup's width is the ledger's `q(N)`** at `A_pad = gateApad l`. -/
theorem sue_width (h : L = recL l (kE l e)) (N : ℕ) :
    (SUE l F e coef A L hL).width N = Ledger.nativeWidth kclk (gateApad l) N := by
  rw [sue_eq_rec l F e coef A L hL h]; rfl

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

end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemSUE

end
