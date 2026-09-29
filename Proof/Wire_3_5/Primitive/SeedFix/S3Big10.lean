import Proof.Wire_3_5.Primitive.SeedFix.S3Big9

/-! # S3, part 16: the per-point evaluator on its own layout

`Σ_{e'} R̂_{e'}(c,u,v)` (P3:3170-3178, `rsumSym`): **`evalS`** loads the seed count, runs the seed loop, rewinds the
four all-seeds table words and blanks the cell (S3 ends with `setc false`). **`evalS_spec`**: from the
invariant at zero offsets (the call's words, the point, blank scratch, every head at `0`) and the loop's registers
zero, the accumulator holds `rsumD N` and every other register, every head and every word and point stream is as
found, the scratch blank again, the cell `false`.

Paper quantity of the main type: the per-point sum `Σ_{i<N} R̂_{e'_i}(c,u,v)` in the accumulator. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall)
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)
open NearCubicWires.WireExponent3_5.PrimT.Flips (rew1 rew1_spec)

/-- Rewind circuit `j`'s all-seeds table word by its offset. -/
def rewT (j : Fin 4) : BM := rew1 (bW (wIdx 2 j)) (qOff j)

/-- **The per-point evaluator** on its layout. -/
def evalS : BM :=
  .seq (wcopyR (qN 1) qIc qTp) (.seq seedLoop (.seq (rewT 0) (.seq (rewT 1) (.seq (rewT 2) (.seq (rewT 3)
    (.setc false))))))

/-- The evaluator's cost bound. -/
def evalCost (k : SymCall) : ℕ :=
  Fintype.card k.Pl.FlatSeed * (bodyCost k + 4) + 18 * Fintype.card k.Pl.FlatSeed +
    5 * (Fintype.card k.Pl.FlatSeed * adv k 0 + Fintype.card k.Pl.FlatSeed * adv k 1 +
      Fintype.card k.Pl.FlatSeed * adv k 2 + Fintype.card k.Pl.FlatSeed * adv k 3) + 20

theorem adv_le (k : SymCall) (j : Fin 4) : adv k j ≤ tabLen k j := by
  unfold adv; split <;> omega

/-- Rewinding circuit `j`'s table word keeps the invariant at offset `0`. -/
theorem BodyInv.rew {k : SymCall} {c eu ev : BitInput k.P.n} {off : Fin 4 → ℕ} {ω τ : BS}
    (hI : BodyInv k c eu ev off ω) (j : Fin 4) (h1 : τ.sh (bW (wIdx 2 j)) = 0) (h2 : τ.val (qOff j) = 0)
    (h3 : τ.st = ω.st) (h4 : ∀ i, i ≠ bW (wIdx 2 j) → τ.sh i = ω.sh i) (h5 : ∀ q, q ≠ qOff j → τ.val q = ω.val q) :
    BodyInv k c eu ev (Function.update off j 0) τ := by
  refine ⟨fun w => by rw [h3]; exact hI.words w, by rw [h3]; exact hI.ptC, by rw [h3]; exact hI.ptU,
    by rw [h3]; exact hI.ptV, fun i => by rw [h5 _ (ne_qOff j (by have := qN_lt i; omega))]; exact hI.nums i,
    fun i hi => by rw [h3]; exact hI.sc i hi, fun i hi => by rw [h4 _ (bW_ne _ hi).symm]; exact hI.scs i hi,
    fun w hw => by rw [h4 _ (fun e => hw j (bW_inj e))]; exact hI.whead w hw, fun j' => ?_, fun j' => ?_,
    ⟨by rw [h4 _ (pt_ne_bW (i := bC) (by decide) _)]; exact hI.pth.1,
      by rw [h4 _ (pt_ne_bW (i := bU) (by decide) _)]; exact hI.pth.2.1,
      by rw [h4 _ (pt_ne_bW (i := bV) (by decide) _)]; exact hI.pth.2.2⟩,
    fun q => by rw [h5 _ (qS_ne_qOff q j)]; exact hI.hq q,
    by rw [h5 _ (ne_qOff j (by decide))]; exact hI.hct, by rw [h5 _ (ne_qOff j (by decide))]; exact hI.htp,
    by rw [h5 _ (ne_qOff j (by decide))]; exact hI.hbk, by rw [h5 _ (ne_qOff j (by decide))]; exact hI.hsk⟩
  · by_cases hjj : j' = j
    · subst hjj; rw [h1, Function.update_self]
    · rw [h4 _ (fun e => hjj (wIdx2_inj (bW_inj e))), Function.update_of_ne hjj]; exact hI.thead j'
  · by_cases hjj : j' = j
    · subst hjj; rw [h2, Function.update_self]
    · rw [h5 _ (fun e => hjj (qOff_inj e)), Function.update_of_ne hjj]; exact hI.toff j'

/-- One rewind step of the four. -/
theorem rewT_step (cap : ℕ) {k : SymCall} {c eu ev : BitInput k.P.n} {off : Fin 4 → ℕ} {ω : BS}
    (hI : BodyInv k c eu ev off ω) (j : Fin 4) (hc : off j ≤ cap) :
    ∃ τ, WExec cap (rewT j) ω τ (off j * 5 + 1) ∧ BodyInv k c eu ev (Function.update off j 0) τ ∧
      (∀ q, q ≠ qOff j → τ.val q = ω.val q) ∧ τ.cell = ω.cell := by
  obtain ⟨τ, e, t1, t2, t3, t4, t5, t6⟩ := rew1_spec cap (bW (wIdx 2 j)) (qOff j) (off j) ω (hI.toff j) (hI.thead j) hc
  exact ⟨τ, e, hI.rew j t1 t2 t3 t4 t5, t5, t6⟩

theorem evalS_spec (cap : ℕ) (k : SymCall) (c eu ev : BitInput k.P.n) (ω : BS) (hI : BodyInv k c eu ev (fun _ => 0) ω)
    (hic : ω.val qIc = 0) (hrh : ω.val qRh = 0) (hac : ω.val qAc = 0) (hacc : ω.val qAcc = 0)
    (hcap : ∀ (i : Fin (Fintype.card k.Pl.FlatSeed)) (j : Fin 4), j.val < k.a →
      CircCap cap k.Pl (seedOf k i) k.P.n (gatesJ k j) (topJ k j).length)
    (c1 : ∀ j : Fin 4, (templJ k j).length ≤ cap)
    (c2 : ∀ j : Fin 4, Fintype.card k.Pl.FlatSeed * tabLen k j ≤ cap) (c4 : 4 ≤ cap)
    (c5 : Fintype.card k.Pl.FlatSeed + 1 ≤ cap) :
    ∃ τ, WExec cap evalS ω τ (evalCost k) ∧ BodyInv k c eu ev (fun _ => 0) τ ∧
      τ.val = Function.update ω.val qAcc (rsumD k c eu ev (Fintype.card k.Pl.FlatSeed)) ∧ τ.cell = false := by
  -- load the seed count
  have hN : ω.val (qN 1) = Fintype.card k.Pl.FlatSeed := by rw [hI.nums]; rfl
  have e1 := wcopyR_spec cap (qN 1) qIc qTp (qN_ne _ (by decide)) (qN_ne _ (by decide)) (by decide) ω hic
    (by rw [hI.htp]) (by rw [hN]; omega)
  obtain ⟨ω1, hω1⟩ : ∃ y, y = ω.setv qIc (ω.val (qN 1)) := ⟨_, rfl⟩
  rw [← hω1] at e1
  have I1 : BodyInv k c eu ev (fun j => 0 * adv k j) ω1 := by
    rw [hω1]
    have e : (fun j : Fin 4 => 0 * adv k j) = fun _ => 0 := by funext j; simp
    rw [e]
    exact hI.setv _ _ (Or.inr ⟨by decide, by decide⟩)
  have v1 : ∀ r, r ≠ qIc → ω1.val r = ω.val r := fun r hr => by rw [hω1, WState.setv_val, Function.update_of_ne hr]
  -- the loop
  obtain ⟨ω2, e2, I2, i2, r2, a2, s2, o2⟩ := seedLoop_spec cap k c eu ev hcap c1 c2 c4 c5
    (Fintype.card k.Pl.FlatSeed) 0 (by omega) ω1 I1
    (by rw [hω1, WState.setv_val, Function.update_self, hN]) (by rw [v1 _ (by decide), hrh])
    (by rw [v1 _ (by decide), hac]) (by rw [v1 _ (by decide), hacc]; rfl)
  -- the rewinds
  have cj : ∀ j : Fin 4, Fintype.card k.Pl.FlatSeed * adv k j ≤ cap := fun j =>
    le_trans (Nat.mul_le_mul_left _ (adv_le k j)) (c2 j)
  obtain ⟨ω3, e3, I3, o3, cl3⟩ := rewT_step cap I2 0 (cj 0)
  obtain ⟨ω4, e4, I4, o4, cl4⟩ := rewT_step cap I3 1 (by rw [Function.update_of_ne (by decide)]; exact cj 1)
  obtain ⟨ω5, e5, I5, o5, cl5⟩ := rewT_step cap I4 2
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact cj 2)
  obtain ⟨ω6, e6, I6, o6, cl6⟩ := rewT_step cap I5 3
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)];
        exact cj 3)
  have e7 := WExec.setc (cap := cap) false ω6
  have hoffe : Function.update (Function.update (Function.update (Function.update
      (fun j => Fintype.card k.Pl.FlatSeed * adv k j) 0 0) 1 0) 2 0) 3 0 = fun _ => 0 := by
    funext j; fin_cases j <;> simp [Function.update]
  rw [hoffe] at I6
  have ho : ∀ q, (∀ j, q ≠ qOff j) → ω6.val q = ω2.val q := fun q h => by
    rw [o6 q (h 3), o5 q (h 2), o4 q (h 1), o3 q (h 0)]
  refine ⟨ω6.setc false, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7)))))) ?_, ⟨I6.words, I6.ptC, I6.ptU, I6.ptV, I6.nums, I6.sc, I6.scs, I6.whead, I6.thead, I6.toff,
    I6.pth, I6.hq, I6.hct, I6.htp, I6.hbk, I6.hsk⟩, ?_, rfl⟩
  · rw [hN] at e1
    simp only [Function.update_of_ne (show (1 : Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2 : Fin 4) ≠ 0 by decide),
      Function.update_of_ne (show (2 : Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3 : Fin 4) ≠ 0 by decide),
      Function.update_of_ne (show (3 : Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3 : Fin 4) ≠ 2 by decide)]
    unfold evalCost
    omega
  · funext r
    rw [WState.setc_val]
    by_cases hr : r = qAcc
    · subst hr
      rw [Function.update_self, ho _ (fun j => ne_qOff j (by decide)), s2]
    · rw [Function.update_of_ne hr]
      by_cases hq : ∃ j, r = qOff j
      · obtain ⟨j, rfl⟩ := hq
        rw [I6.toff, hI.toff]
      · simp only [not_exists] at hq
        rw [ho r hq]
        by_cases h1 : r = qIc
        · subst h1; rw [i2, hic]
        · by_cases h2 : r = qRh
          · subst h2; rw [r2, hrh]
          · by_cases h3 : r = qAc
            · subst h3; rw [a2, hac]
            · rw [o2 r h1 h2 h3 hr hq, v1 r h1]

end NearCubicWires.WireExponent3_5.PrimT.S3
