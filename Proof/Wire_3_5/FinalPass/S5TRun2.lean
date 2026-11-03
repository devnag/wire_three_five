import Lean
import Proof.Wire_3_5.FinalPass.S5TRun1
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.S5TJoin2
import Proof.Wire_3_5.FinalPass.S5TNum3
import Proof.Wire_3_5.FinalPass.S5TRun0
import Proof.Wire_3_5.FinalPass.S5TStage
import Proof.Wire_3_5.FinalPass.SeamsProg2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.TS4K
import Proof.Wire_3_5.Primitive.SeedFix.TS4O
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.S5TNum4


noncomputable section
set_option maxRecDepth 120000


/-! # S5-THR, part 41: the THR stage at a SYM request, and at every request (P3:3170-3181)

At a SYM request the stage parses the request and does nothing else (**`stage_sym_at`**): the THR slots stay blank,
which is what `frontWordsW` holds there (`sym_w`). **`stage_at`**: the THR stage's run, within `W − 1` steps, at
every request of every call family (the mode split).

Paper quantity of the main type: THR slots `8 … 15` of the front's words at every call (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline

section Run2
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The THR stage at a SYM request**: the parse only; the THR slots stay blank. -/
theorem stage_sym_at (Sw : SymWords) (n : ℕ) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) :
    ∃ (σE : WState (nsL (Dl l) (x6L l) (xtL l)) nrL) (c : ℕ),
      Step (stageM (Dl l) (PrimT.W6.litAlg l) 1 l F.cr (Hd l - 1) (Hd l - 1) (Hd l)) c
        (wenc (2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2)
          (σ03 (nr := nrL) (Dl l) (fs2 (Dl l) (x6L l) (xtL l)) (c0T l F) (PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩))).H
        (wenc (2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2)
          (σ03 (nr := nrL) (Dl l) (fs2 (Dl l) (x6L l) (xtL l)) (c0T l F) (PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩))).A
        (wenc (2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2) σE).H
        (wenc (2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2) σE).A ∧
      c + 1 ≤ yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) ∧
      (∀ m : Fin 8, σE.st (sSlot (Dl l) (x6L l) (xtL l) m) =
        frontWordsW l F kclk coef A a ha Sw ⟨_, hc⟩ ⟨m.val + 8, by omega⟩) ∧
      σE.st (sIn (Dl l) (x6L l) (xtL l)) = frame (PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩) ∧
      σE.st (xsN (Dl l) (x6L l) (xtL l) (Dl l)) =
        List.replicate (yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 1) false ∧
      (∀ j, σE.val j ≤ 2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2) := by
  have hfp := fpIn_sym l F kclk coef A a ha n a' ha' carriers translation Cs hc
  have hnu := FpInLen.n_le_fpIn (⟨_, hc⟩ : PlanFP.FReq l F kclk coef A a ha)
  have hsw : ∀ m : Fin 8, frontWordsW l F kclk coef A a ha Sw ⟨_, hc⟩ ⟨m.val + 8, by omega⟩ = [] := fun m =>
    sym_w (I := callInputs l F kclk coef A a ha) (alg := (gate0 l F).alg) (Sw := Sw) (n := n) (a' := a')
      (ha' := ha') (carriers := carriers) (translation := translation) (Cs' := Cs) (k := ⟨m.val + 8, by omega⟩)
      (h8 := by simp) (h16 := by simp; omega)
  unfold yOf
  generalize PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩ = u at hfp hnu ⊢
  have hnu' : n ≤ u.length := hnu
  have k0 : 100000 ≤ c0T l F := by unfold c0T; omega
  have hZD := Zx_le_Dl l
  have hZx : Zx l = 3 * Hd l + 1 := rfl
  have hH30 := one_le_Hd l
  obtain ⟨y, hy⟩ : ∃ y, y = u.length + 1 + c0T l F := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : 100000 ≤ y := by omega
  have hy1 : 1 ≤ y := by omega
  have p3 : y ^ 3 ≤ y ^ (Dl l) := Nat.pow_le_pow_right hy1 (by omega)
  have p2 : 100000 * y ^ 2 ≤ y ^ 3 := mul_pow_le hy0
  have p1 : 100000 * y ≤ y ^ 2 := by nlinarith
  have pW : 100000 * y ^ Dl l ≤ y ^ (Dl l + 1) := mul_pow_le hy0
  have hcl : (PrimAsm.Codec.codeList ⟨n, .sym, a', ha', Cs, carriers, translation⟩).length = a' := by
    simp [PrimAsm.Codec.codeList]
  have hA := PrimT.TS4.a2_le a' ha'
  have hA' := Nat.le_mul_of_pos_left (40 * 2 ^ natBitLength a' + 40) (show 0 < natBitLength a' + 2 by omega)
  have eA : 2 ^ (natBitLength a' + 1) = 2 ^ natBitLength a' * 2 := pow_succ _ _
  have hNn := PrimT.TS4.a1_le n y (by omega)
  have hNn' := Nat.le_mul_of_pos_left (40 * 2 ^ natBitLength n + 40) (show 0 < natBitLength n + 2 by omega)
  have eN : 2 ^ (natBitLength n + 1) = 2 ^ natBitLength n * 2 := pow_succ _ _
  have hlen : (PrimAsm.Data.reqW n false (PrimAsm.Codec.codeList ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      (PrimAsm.Codec.carrierCodes ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      (RepairRepresentation.natListWord translation ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg
        ⟨n, .sym, a', ha', Cs, carriers, translation⟩)).length = u.length := by rw [← hfp]
  obtain ⟨σE, hstep, hst, hreg⟩ :=
    stage_sym (Dl l) (PrimT.W6.litAlg l) 1 (2 * y ^ (Dl l + 1) + 2) l F.cr (Hd l - 1) (Hd l - 1) (Hd l)
      (σ03 (nr := nrL) (Dl l) (fs2 (Dl l) (x6L l) (xtL l)) (c0T l F) u) n
      (PrimAsm.Codec.codeList ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      (PrimAsm.Codec.carrierCodes ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      (RepairRepresentation.natListWord translation ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg
        ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      ((σ03_in (Dl l) (x6L l) (xtL l) (c0T l F) u).trans (congrArg frame hfp))
      (σ03_sh (Dl l) (x6L l) (xtL l) (c0T l F) u _)
      (by rw [σ03_tm, hlen]) (σ03_sh (Dl l) (x6L l) (xtL l) (c0T l F) u _)
      (σ03_val (Dl l) (x6L l) (xtL l) (c0T l F) u) (by rw [hcl]; omega) (by omega) (by rw [hcl]; omega)
  have hpc := parse_le n (PrimAsm.Codec.codeList ⟨n, .sym, a', ha', Cs, carriers, translation⟩).length
    ((PrimAsm.Data.reqW n false (PrimAsm.Codec.codeList ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      (PrimAsm.Codec.carrierCodes ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      (RepairRepresentation.natListWord translation ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg
        ⟨n, .sym, a', ha', Cs, carriers, translation⟩)).length + 1) y (by omega) (by rw [hcl]; omega)
      (by rw [hlen]; omega)
  refine ⟨σE, _, hstep, by omega, fun m => ?_, ?_, ?_, hreg⟩
  · rw [hsw m, hst]
    exact σ03_blank (Dl l) (x6L l) (xtL l) (c0T l F) u _ (by simp [sSlot]) (by simp [sSlot]; omega)
      (by simp [sSlot]; omega) (by simp [sSlot]; omega)
  · rw [hst]; exact σ03_in (Dl l) (x6L l) (xtL l) (c0T l F) u
  · rw [hst, σ03_xsD, hy]

/-- **The THR stage at every request** of every call family. -/
theorem stage_at (Sw : SymWords) (r : PlanFP.FReq l F kclk coef A a ha) :
    ∃ (σE : WState (nsL (Dl l) (x6L l) (xtL l)) nrL) (c : ℕ),
      Step (stageM (Dl l) (PrimT.W6.litAlg l) 1 l F.cr (Hd l - 1) (Hd l - 1) (Hd l)) c
        (wenc (2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 2)
          (σ03 (nr := nrL) (Dl l) (fs2 (Dl l) (x6L l) (xtL l)) (c0T l F) (PlanFP.fpIn l F kclk coef A a ha r))).H
        (wenc (2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 2)
          (σ03 (nr := nrL) (Dl l) (fs2 (Dl l) (x6L l) (xtL l)) (c0T l F) (PlanFP.fpIn l F kclk coef A a ha r))).A
        (wenc (2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 2) σE).H
        (wenc (2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 2) σE).A ∧
      c + 1 ≤ yOf l F kclk coef A a ha r ^ (Dl l + 1) ∧
      (∀ m : Fin 8, σE.st (sSlot (Dl l) (x6L l) (xtL l) m) =
        frontWordsW l F kclk coef A a ha Sw r ⟨m.val + 8, by omega⟩) ∧
      σE.st (sIn (Dl l) (x6L l) (xtL l)) = frame (PlanFP.fpIn l F kclk coef A a ha r) ∧
      σE.st (xsN (Dl l) (x6L l) (xtL l) (Dl l)) =
        List.replicate (yOf l F kclk coef A a ha r ^ (Dl l + 1) + 1) false ∧
      (∀ j, σE.val j ≤ 2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 2) := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hc⟩ := r
  cases mode with
  | sym => exact stage_sym_at l F kclk coef A a ha Sw n ha' Cs carriers translation hc
  | thr => exact stage_thr_at l F kclk coef A a ha Sw n ha' Cs carriers translation hc

end Run2

end NearCubicWires.WireExponent3_5.FinalPass.S5T

end
