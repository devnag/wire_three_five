import Lean
import Proof.Wire_3_5.FinalPass.CoreJ15
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Core15
import Proof.Wire_3_5.FinalPass.Core9
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.CoreJ11
import Proof.Wire_3_5.FinalPass.CoreJ12
import Proof.Wire_3_5.FinalPass.CoreJ13
import Proof.Wire_3_5.FinalPass.CoreJ14
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg2
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.S5Seam2
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.CoreJ10


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core over the writers with arbitrary residues, part J16: the core half's run (P3:3044-3048, 3170-3181)

**`core_runJ`**: from the THR half's exit (`ThrExit2`), every head at `0`, the core half's machine `coreMJ` reaches the
front's exit `exitA` (the words of `frontWordsW2`, `Num = 0` and `Den = fpDen` in `Tf`-bit binary, every other tape
`0^{blOf2}`), every head at `0`, within `coreCostJ`: the count, the mode, parts A and B, the numbers, the SYM branch,
the final pad (`stage12J`, `stageABNJ`, `stageSJ`, `stageFJ`), given the bank's register length `c = L.Kc·N^{L.Dc}`
covers `2N` and every writer's capacity and step bound.

Paper quantities: the front's words and the printed numbers' start (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Run
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {mTh : ℕ}
  (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- **The core half's cost** at a request (`c = L.Kc·N^{L.Dc}`, `N = |fpIn| + 1`). -/
noncomputable def coreCostJ (r : FReq l F kclk coef A a ha) : ℕ :=
  (1 + 1 + cntCost (fpIn l F kclk coef A a ha r).length L.Kc L.Dc) + 1 +
  ((1 + 1 + modeCost (natBitLength r.1.n) ((fpIn l F kclk coef A a ha r).length + 1)) + 1 +
  ((W.SA.nr * (6 * (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) + 17) + 1 + 1 + 1 +
      W.SA.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SA.Ds F.filterErrDeg) + 1 +
  ((W.SB.nr * (6 * (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) + 17) + 1 + 1 + 1 +
      W.SB.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SB.Ds F.filterErrDeg) + 1 +
  ((W.NW.nr * (6 * (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) + 17) + 1 + 1 + 1 +
      W.NW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.NW.Ds F.filterErrDeg) + 1 +
  ((W.SW.nr * (6 * (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) + 17) + 1 + 1 + 1 +
      W.SW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SW.Ds F.filterErrDeg + 1) + 1 +
    finCost (regList L (TcJ W L hR)).length (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc))))))

theorem Tc_regJ : L.reg (TcJ W L hR) = true := L.coreReg _ (hR.coreE_sc _)

/-- **The core half's run.** -/
theorem core_runJ (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool)
    (hE : ThrExit2 l F kclk coef A a ha Sw0 L r Ab)
    (hc2 : 2 * ((fpIn l F kclk coef A a ha r).length + 1) ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hKA : W.SA.Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SA.Dk F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hSA : W.SA.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SA.Ds F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hKB : W.SB.Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SB.Dk F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hSB : W.SB.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SB.Ds F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hKN : W.NW.Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.NW.Dk F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hSN : W.NW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.NW.Ds F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hKS : W.SW.Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SW.Dk F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hSS : W.SW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SW.Ds F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) :
    Step (coreMJ W F L hR) (coreCostJ W F kclk coef A a ha L hR r) (fun _ => 0) Ab (fun _ => 0)
      (exitA F kclk coef A a ha L r) := by
  classical
  obtain ⟨h0, hroom0, hwd0, htN0, htD0⟩ := exit_factsJ W F kclk coef A a ha L hR r Ab hE
  obtain ⟨A1, A2, s1, s2, a2in, a2T, a2M, a2inv, a2keep⟩ := stage12J W F kclk coef A a ha L hR r Ab hE hc2
  have hwd2 : ∀ k, ¬ thrSlot k → A2 (L.wd k) = [] := fun k hk => by
    rw [a2keep _ (fun i e => wd_neRJ W L hR k i e.symm)]; exact hwd0 k hk
  have htN2 : A2 L.tN = [] := by
    rw [a2keep _ (fun i e => (core_off L hR i).2.2.1 e)]; exact htN0
  have htD2 : A2 L.tD = [] := by
    rw [a2keep _ (fun i e => (core_off L hR i).2.2.2 e)]; exact htD0
  obtain ⟨A3, A4, A5, s3, s4, s5, a5A, a5B, a5N, a5in, a5T, a5inv, a5M, a5keep⟩ :=
    stageABNJ W F kclk coef A a ha L hR r _ A2 a2in a2T a2inv hwd2 htN2 htD2 hKA hSA hKB hSB hKN hSN
  have hS5 : ∀ k, A5 (outS L k) = [] := fun k => by
    rw [a5keep (outS L k) (fun i e => wd_neRJ W L hR _ i e.symm) (fun k' e => outS_ne_outA L k k' e)
      (fun k' e => outS_ne_outB L k k' e) (fun k' e => wd_ne_outN L _ k' e)]
    exact hwd2 _ (by rintro ⟨_, h2⟩; simp [symSlot] at h2)
  obtain ⟨A6, s6, a6in, a6T, a6inv, a6sym, a6thr, a6keep⟩ :=
    stageSJ W F kclk coef A a ha L hR r _ A5 a5in a5T a5inv (a5M.trans a2M) hS5 hKS hSS
  -- every tape off the room and the words is the THR half's
  have hoff : ∀ y, (∀ i, hR.coreE i ≠ y) → (∀ k, y ≠ L.wd k) → y ≠ L.tN → y ≠ L.tD → A6 y = Ab y := by
    intro y hr hw hN hD
    rw [a6keep y hr (fun k => hw _), a5keep y hr (fun k => hw _) (fun k => hw _)
      (fun k => by fin_cases k; exact hN; exact hD), a2keep y hr]
  have hlen : ∀ y ∈ regList L (TcJ W L hR),
      (A6 y).length ≤ L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1 := by
    intro y hy
    obtain ⟨_, hw, hN, hD, _⟩ := (mem_regList L _ y).1 hy
    by_cases hr : ∃ i, hR.coreE i = y
    · obtain ⟨i, rfl⟩ := hr; exact (a6inv i).1
    · have hr' : ∀ i, hR.coreE i ≠ y := fun i e => hr ⟨i, e⟩
      by_cases hy0 : y = i0 L
      · subst hy0
        have hfl : (frame (fpIn l F kclk coef A a ha r)).length = 2 * (fpIn l F kclk coef A a ha r).length + 1 := by
          simp
        rw [a6in, hfl]; omega
      · rw [hoff y hr' hw hN hD]
        cases hts : L.thrSc y
        · rw [hE.rest y (fun e => hy0 (Fin.ext e)) hw hN hD hts]; simp
        · obtain ⟨ℓ, hℓ, he⟩ := hE.thrSc y hts
          rw [he, List.length_replicate]; exact hℓ
  have s7 := stageFJ W L hR _ A6 a6T hlen
  have hs := Step.seq s1 (Step.seq s2 (Step.seq s3 (Step.seq s4 (Step.seq s5 (Step.seq s6 s7)))))
  have hfin : Function.update (fun i => if i ∈ regList L (TcJ W L hR) then
      List.replicate (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1) false else A6 i) (TcJ W L hR)
      (List.replicate (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1) false) =
      exitA F kclk coef A a ha L r := by
    funext y
    by_cases hyT : y = TcJ W L hR
    · subst hyT
      rw [Function.update_self, exitA_blank F kclk coef A a ha L r (TcJ W L hR)
        (fun k e => (core_off L hR _).2.1 k e) (fun e => (core_off L hR _).2.2.1 e)
        (fun e => (core_off L hR _).2.2.2 e)]
      unfold blOf2; rw [if_pos (Tc_regJ W L hR)]
    rw [Function.update_of_ne hyT]
    by_cases hyl : y ∈ regList L (TcJ W L hR)
    · rw [if_pos hyl]
      obtain ⟨hreg, hw, hN, hD, _⟩ := (mem_regList L _ y).1 hyl
      rw [exitA_blank F kclk coef A a ha L r y hw hN hD]
      unfold blOf2; rw [if_pos hreg]
    rw [if_neg hyl]
    by_cases hwk : ∃ k, L.wd k = y
    · obtain ⟨k, rfl⟩ := hwk
      rw [exitA_wd]
      have hkr : ∀ i, hR.coreE i ≠ L.wd k := fun i e => wd_neRJ W L hR k i e.symm
      by_cases k4 : k.val < 4
      · have hk : s4SlotA ⟨k.val, k4⟩ = k := Fin.ext rfl
        have e := a6keep (L.wd k) hkr (fun k' e => by
          have := congrArg Fin.val (L.wdInj e); simp [symSlot] at this; omega)
        rw [e]
        have h5 := a5A ⟨k.val, k4⟩
        unfold outA at h5; rw [hk] at h5
        exact h5
      by_cases k8 : k.val < 8
      · have hk : s4SlotB ⟨k.val - 4, by omega⟩ = k := Fin.ext (show 4 + (k.val - 4) = k.val by omega)
        have e := a6keep (L.wd k) hkr (fun k' e => by
          have := congrArg Fin.val (L.wdInj e); simp [symSlot] at this; omega)
        rw [e]
        have h5 := a5B ⟨k.val - 4, by omega⟩
        unfold outB at h5; rw [hk] at h5
        exact h5
      by_cases k16 : k.val < 16
      · have hts : thrSlot k := ⟨by omega, k16⟩
        have e6 := a6keep (L.wd k) hkr (fun k' e => by
          have := congrArg Fin.val (L.wdInj e); simp [symSlot] at this; omega)
        have e5 := a5keep (L.wd k) hkr (fun k' e => by
            have := congrArg Fin.val (L.wdInj e); simp [s4SlotA] at this; omega)
          (fun k' e => by have := congrArg Fin.val (L.wdInj e); simp [s4SlotB] at this; omega)
          (fun k' e => wd_ne_outN L k k' e)
        rw [e6, e5, a2keep _ hkr, hE.thr k hts, thr_agree l F kclk coef A a ha Sw0 r k hts]
      · have hk33 : k.val - 16 < 17 := by have := k.isLt; have h16 : Sw0.nw = 16 := sw0_nw; omega
        have hk : symSlot ⟨k.val - 16, hk33⟩ = k := Fin.ext (show 16 + (k.val - 16) = k.val by omega)
        cases hm : r.1.mode with
        | sym =>
          have h6 := a6sym hm ⟨k.val - 16, hk33⟩
          unfold outS at h6; rw [hk] at h6
          exact h6
        | thr =>
          have h6 := a6thr hm ⟨k.val - 16, hk33⟩
          have h5 := hS5 ⟨k.val - 16, hk33⟩
          have hb := sym_blank_thr l F kclk coef A a ha r hm ⟨k.val - 16, hk33⟩
          unfold outS at h6 h5; rw [hk] at h6 h5 hb
          rw [h6, h5, hb]
    · have hw : ∀ k, y ≠ L.wd k := fun k e => hwk ⟨k, e.symm⟩
      by_cases hyN : y = L.tN
      · subst hyN
        rw [exitA_tN]
        have e := a6keep L.tN (fun i e => (core_off L hR i).2.2.1 e) (fun k e => L.wdN _ e.symm)
        rw [e]
        have := a5N 0
        simp only [outN, Matrix.cons_val_zero] at this
        exact this
      by_cases hyD : y = L.tD
      · subst hyD
        rw [exitA_tD]
        have e := a6keep L.tD (fun i e => (core_off L hR i).2.2.2 e) (fun k e => L.wdD _ e.symm)
        rw [e]
        have := a5N 1
        simp only [outN, Matrix.cons_val_one, Matrix.head_cons] at this
        exact this
      have hnreg : L.reg y = false := by
        cases hreg : L.reg y
        · rfl
        · exact absurd ((mem_regList L _ y).2 ⟨hreg, hw, hyN, hyD, hyT⟩) hyl
      have hr : ∀ i, hR.coreE i ≠ y := fun i e => by
        have := L.coreReg _ (hR.coreE_sc i); rw [e, hnreg] at this; exact absurd this (by decide)
      have hy0 : y ≠ i0 L := fun e => by
        have := L.reg0; change L.reg (i0 L) = true at this; rw [← e, hnreg] at this; exact absurd this (by decide)
      have hts : L.thrSc y = false := by
        cases h : L.thrSc y
        · rfl
        · have := L.thrReg y h; rw [hnreg] at this; exact absurd this (by decide)
      rw [hoff y hr hw hyN hyD, hE.rest y (fun e => hy0 (Fin.ext e)) hw hyN hyD hts,
        exitA_blank F kclk coef A a ha L r y hw hyN hyD]
      unfold blOf2; rw [if_neg (by rw [hnreg]; decide)]; rfl
  rw [hfin] at hs
  exact hs

end Run

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
