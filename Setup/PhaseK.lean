import Setup.PhaseR
import Succinct.Check
import CheckedPCPP.EncSetup

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

noncomputable section

/-! ## CHECK's register file (`60 … 104`) -/

theorem vreg_card : Fintype.card Succinct.VReg = 45 := by decide

/-- CHECK's registers: `VReg` onto `60 … 104`. -/
noncomputable def EK (v : Succinct.VReg) : Fin nrW :=
  ⟨60 + (Fintype.equivFin Succinct.VReg v).val, by
    have := lt_of_lt_of_eq (Fintype.equivFin Succinct.VReg v).isLt vreg_card; show _ < 128; omega⟩

theorem EK_val (v : Succinct.VReg) : 60 ≤ (EK v).val ∧ (EK v).val < 105 := by
  have := lt_of_lt_of_eq (Fintype.equivFin Succinct.VReg v).isLt vreg_card; unfold EK; simp only; omega

theorem EK_inj : Function.Injective EK := by
  intro a b h
  have := congrArg Fin.val h
  unfold EK at this; simp only at this
  exact (Fintype.equivFin Succinct.VReg).injective (Fin.ext (by omega))

theorem EK_ne (v : Succinct.VReg) (r : Fin nrW) (h : r.val < 60 ∨ 105 ≤ r.val) : EK v ≠ r := by
  intro e; have := EK_val v; rw [e] at this; omega

/-! ## Register programs -/

section Regs
variable {ns : ℕ} {cap : ℕ}

def sizeNuW (C : Fin nrW) : WMX ns nrW :=
  .seq (.wm (Codec.dupR rNu pT1 dS)) (Recovery.HTParts.sizeW pT1 pH pB C)

theorem sizeNuW_exec (C : Fin nrW) (hC : ∀ r ∈ ([rNu, pT1, pH, pB, dS] : List (Fin nrW)), C ≠ r) (ν : ℕ)
    (σ : WState ns nrW) (hν : σ.val rNu = ν) (hz : ∀ r ∈ ([pT1, pH, pB, dS] : List (Fin nrW)), σ.val r = 0)
    (hC0 : σ.val C = 0) (hcap : 2 * ν + 2 ≤ cap) :
    WXExec cap (sizeNuW C) σ (σ.setv C ν.size) (60 * (ν + 1) ^ 2) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz hC
  obtain ⟨z1, zH, zB, zd⟩ := hz
  obtain ⟨c1, c2, c3, c4, c5⟩ := hC
  have hs : ν.size ≤ ν := by rw [Nat.size_le]; exact Nat.lt_two_pow_self
  have e1 := Codec.dupR_spec cap rNu pT1 dS (by decide) (by decide) (by decide) σ zd (by rw [hν, z1]; omega)
  rw [z1, hν, Nat.zero_add] at e1
  have e2 := Recovery.HTParts.sizeW_exec (cap := cap) (X := pT1) (H := pH) (B := pB) (C := C)
    (by simp [List.nodup_cons]; refine ⟨⟨by decide, by decide, Ne.symm c2⟩, ⟨by decide, Ne.symm c3⟩, Ne.symm c4⟩)
    ν (by omega) ν (σ.setv pT1 ν) le_rfl (by simp) (by rw [upd_ne _ _ (by decide)]; exact zH)
    (by rw [upd_ne _ _ (by decide)]; exact zB) (by rw [upd_ne _ _ c2, hC0]; omega)
  have hσ : (σ.setv pT1 ν).setv pT1 0 = σ := by rw [LitDecode.setv_setv, ← z1, wsetv_same]
  have hC1 : (σ.setv pT1 ν).val C = 0 := by rw [upd_ne _ _ c2]; exact hC0
  refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) e2) ?_ ?_
  · rw [hσ, hC1, Nat.zero_add]
  · have : ν.size * (12 * ν + 30) ≤ ν * (12 * ν + 30) := Nat.mul_le_mul_right _ hs
    nlinarith

def powNuW (k : ℕ) (Y : Fin nrW) : WMX ns nrW :=
  .seq (WMX.inc Y) (.seq (.wm (Codec.dupR rNu pX1 dS)) (.seq (EncSetup.powW pX1 Y pX3 pH pB k) (.wm (WM.clear pX1))))

theorem powNuW_exec (k : ℕ) (Y : Fin nrW) (hY : ∀ r ∈ ([rNu, pX1, pX3, pH, pB, dS] : List (Fin nrW)), Y ≠ r)
    (ν : ℕ) (hν1 : 1 ≤ ν) (σ : WState ns nrW) (hν : σ.val rNu = ν)
    (hz : ∀ r ∈ ([pX1, pX3, pH, pB, dS] : List (Fin nrW)), σ.val r = 0) (hY0 : σ.val Y = 0)
    (hcap : 2 * ν ^ k + ν ^ k * ν ^ k + ν + 2 ≤ cap) :
    WXExec cap (powNuW k Y) σ (σ.setv Y (ν ^ k)) (100 * (k + 1) * (ν ^ k + ν + 1) ^ 2) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz hY
  obtain ⟨z1, z3, zH, zB, zd⟩ := hz
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hY
  have hp1 : 1 ≤ ν ^ k := Nat.one_le_pow _ _ hν1
  have e1 := WXExec.inc (cap := cap) Y σ (by rw [hY0]; omega)
  rw [hY0, Nat.zero_add] at e1
  have e2 := Codec.dupR_spec cap rNu pX1 dS (by decide) (by decide) (by decide) (σ.setv Y 1)
    (by rw [upd_ne _ _ (Ne.symm c6)]; exact zd) (by rw [upd_ne _ _ (Ne.symm c1), upd_ne _ _ (Ne.symm c2), hν, z1]; omega)
  rw [show (σ.setv Y 1).setv pX1 ((σ.setv Y 1).val pX1 + (σ.setv Y 1).val rNu) = (σ.setv Y 1).setv pX1 ν by
    rw [upd_ne _ _ (Ne.symm c1), upd_ne _ _ (Ne.symm c2), hν, z1, Nat.zero_add]] at e2
  have e3 := EncSetup.powW_spec (cap := cap) (X := pX1) (Y := Y) (Z := pX3) (A2 := pH) (T := pB)
    (by simp [List.nodup_cons]; exact ⟨⟨c4, c2, c3, c5⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
      by decide⟩) (ν ^ k) k ((σ.setv Y 1).setv pX1 ν)
    (by rw [upd_ne _ _ (by decide), upd_ne _ _ (Ne.symm c3)]; exact z3)
    (by rw [upd_ne _ _ (by decide), upd_ne _ _ (Ne.symm c4)]; exact zH)
    (by rw [upd_ne _ _ (by decide), upd_ne _ _ (Ne.symm c5)]; exact zB)
    (by rw [upd_ne _ _ c2]; simp) (by simp; omega) (by omega)
  rw [show ((σ.setv Y 1).setv pX1 ν).setv Y (((σ.setv Y 1).setv pX1 ν).val Y * ((σ.setv Y 1).setv pX1 ν).val pX1 ^ k) =
      ((σ.setv Y 1).setv pX1 ν).setv Y (ν ^ k) by rw [upd_ne _ _ c2]; simp] at e3
  have e4 := wclear_spec (cap := cap) pX1 ν (((σ.setv Y 1).setv pX1 ν).setv Y (ν ^ k))
    (by rw [upd_ne _ _ (Ne.symm c2)]; simp) (by rw [upd_ne _ _ (Ne.symm c2)]; simp; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq e3 (WXExec.wm e4)))) ?_ ?_
  · apply WState.eq <;> try rfl
    funext r
    simp only [WState.setv_val]
    by_cases h1 : r = pX1
    · subst h1
      rw [Function.update_self, Function.update_of_ne (Ne.symm c2), z1]
    · rw [Function.update_of_ne h1]
      by_cases h2 : r = Y
      · subst h2; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h2]
  · have hl : (σ.setv Y 1).val rNu = ν := by rw [upd_ne _ _ (Ne.symm c1)]; exact hν
    rw [hl]
    unfold EncSetup.powCost
    have h1 : ν ≤ ν ^ k + ν + 1 := by omega
    have h2 : ν ^ k ≤ ν ^ k + ν + 1 := by omega
    obtain ⟨M, hM⟩ : ∃ M, M = ν ^ k + ν + 1 := ⟨_, rfl⟩
    rw [← hM] at h1 h2 ⊢
    have h3 : k * (40 * ν ^ k * ν ^ k + 40 * ν ^ k + 20) ≤ k * (40 * M * M + 40 * M + 20) := by
      apply Nat.mul_le_mul_left; nlinarith
    have hM1 : 1 ≤ M := by omega
    have hMM : M ≤ M * M := Nat.le_mul_self M
    have h4 : k * M ≤ k * (M * M) := Nat.mul_le_mul_left _ hMM
    have h5 : k ≤ k * (M * M) := Nat.le_mul_of_pos_right _ (by nlinarith)
    have e : 100 * (k + 1) * M ^ 2 = 100 * (k * (M * M)) + 100 * (M * M) := by ring
    have e2 : k * (40 * M * M + 40 * M + 20) = 40 * (k * (M * M)) + 40 * (k * M) + 20 * k := by ring
    rw [e]
    have hνM : ν ≤ M * M := h1.trans hMM
    omega

end Regs

/-! ## Phase K -/

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

section Prog

end Prog

theorem nodes_le_descriptor {n : ℕ} (B : BooleanCircuit n) : B.nodes.length ≤ (PCPPNative.descriptor B).length := by
  rw [PCPPNative.descriptor_eq]
  simp only [List.length_append]
  have : ∀ l : List (BooleanNode n), l.length ≤ (l.flatMap PCPPRequestNodeSchema.native).length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have : 1 ≤ (PCPPRequestNodeSchema.native a).length := by
        unfold PCPPRequestNodeSchema.native; simp <;> omega
      omega
  have := this B.nodes
  omega

theorem size_le_self (v : ℕ) : v.size ≤ v := by rw [Nat.size_le]; exact Nat.lt_two_pow_self

end

end NearCubicGates.Close.Setup
