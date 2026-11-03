import Lean
import Proof.Wire_3_5.Recovery.RecoveryLeaf
import Proof.Foundations.ProjectionPCPPadding
import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.PCP.PCPPSubstitutionCircuit
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Proof.CaseAnalysis.NativeWidthStep
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionSetup


noncomputable section


/-! # The re-pinned union setup `S₂`: the outer step at the refuter's hierarchy (Lemma H.7; order of the constants)

Realizes the union setup at the recovered language `L = recL`: the refuter's hierarchy `refH l kclk` itself, its
succinct verifier `𝒱_G` at `λ_a` (`recSV`; Lemma H.6), the short PCP (§H.1 item 1), the pointwise PCPP, the explicit
constants and the oracle degree; live. Elsewhere it is `S₁` (dead: the machine rejects outright).

Paper quantities: `refH l kclk` with `refH_spec`; `recSV`, `recWidth` (`q(N)`, (57)); **`recSetup2`**;
**`unionSetupS2 l G : G.Setup`** and `unionSetupS2_recL`; at the gate's clock `kclk = 41`: `recSV_kclk`
(`= gateSV l`), `recWidth_kclk`, and `recSetup2_width` (the setup's width IS the ledger's `q(N)` at `A_pad`, by the
width bridge `widthOf_eq_nativeWidth`); `native_lower` (`q(2^s) ≥ s + 1`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)

section S2
variable (l : Literals) (G : Split.Gate)

/-- The refuter's hierarchy at the clock `N^{kclk+2}`. -/
noncomputable def refH (kclk : ℕ) : OrdinaryHierarchy (fun n => n ^ (kclk + 2)) := (recRefuter l kclk).hierarchy

theorem refH_spec (kclk : ℕ) :
    ∀ n (x : BitInput n), recL l kclk n x = true ↔ (refH l kclk).verifier.language (refH l kclk).time n x :=
  fun n x => hierarchy_language_exact _ n x

/-- **`𝒱_G`** (Lemma H.6) for the refuter's hierarchy at the clock `N^{kclk+2}`, at the description length `λ_a`; at the
gate's clock it is the gate's `gateSV` (`recSV_kclk`). -/
noncomputable def recSV (kclk : ℕ) : NearCubicGates.Close.Outer.SuccinctVerifier (refH l kclk) (lenG l) :=
  Classical.choice (NearCubicGates.Close.Succinct.succinctVerifier_exists (refH l kclk) (lenG l))

/-- **The setup at the recovered language**: the outer data at the refuter's hierarchy (`𝒱_G = recSV`), live. -/
noncomputable def recSetup2 (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : UnionSetup (G.inputs kclk coef A a ha) :=
  setupOf (G.inputs kclk coef A a ha) (recL l kclk) (refH l kclk) (refH_spec l kclk) (gateMW l) (lenG l)
    (recSV l kclk) (gatePCPP l) true (recOracleDeg l) (gateParams1 l) (gateOuterError_pos l)
    (gridMassOf (gateCδ1 l) G.row.sp) (fun _ => by unfold gridMassOf; positivity) G.row.sp

/-- **The re-pinned union setup `S₂`**: the outer data at the refuter's hierarchy at `recL` (live), `S₁` (dead)
elsewhere. -/
noncomputable def unionSetupS2 : G.Setup := fun kclk coef A a ha L hL => by
  classical
  exact if h : L = recL l kclk then
    setupOf (G.inputs kclk coef A a ha) L (refH l kclk) (by subst h; exact refH_spec l kclk) (gateMW l) (lenG l)
      (recSV l kclk) (gatePCPP l) true (recOracleDeg l) (gateParams1 l) (gateOuterError_pos l)
      (gridMassOf (gateCδ1 l) G.row.sp) (fun _ => by unfold gridMassOf; positivity) G.row.sp
  else unionSetupS1 l G kclk coef A a ha L hL

theorem unionSetupS2_recL (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (hL : InNTIME (fun n => n ^ (kclk + 2)) (recL l kclk)) :
    unionSetupS2 l G kclk coef A a ha (recL l kclk) hL = recSetup2 l G kclk coef A a ha := by
  unfold unionSetupS2
  rw [dif_pos rfl]
  rfl

/-- At the gate's clock the setup's width is the ledger's `q(N)` exactly, once the gate's `A_pad` is `gateApad`
(order item (5)). -/
theorem recSetup2_width (coef A a : ℕ) (ha : a ≤ kclk + 1) (hApad : G.Apad = gateApad l) (N : ℕ) :
    (recSetup2 l G kclk coef A a ha).width N = Ledger.nativeWidth kclk G.Apad N := by
  rw [hApad]; rfl

end S2

end NearCubicWires.WireExponent3_5.Transfer

end
