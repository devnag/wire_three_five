import Proof.Wire_3_5.FinalPass.SdPt2
import Proof.Wire_3_5.FinalPass.SampleEval

/-! # S4 (the seeds phase), part 7: stage 0 on the body's layout (P3:1188-1193, 1220-1222, 3044-3053)

"Draw `Q` pairs `(u, v)` of live halves" (P3:3044-3053): the sampled pairs are the words `frame (binary (s·r/2) a)` on
word `1` (`tI`); stage 0 (C5's `Sample.dec right`, verified) reads one index at the head of `tI` and writes the half's
error vector, framed, over the old frame on `tU` (left) or `tV` (right). **`decB right`**: `dec right` lifted (streams
`tI`, `tO right`; registers `156 … 167`, `rgX = 165` tracking `tI`'s head, `rgO = 166`); **`decB_spec`**: the half's
stream becomes `frameP (decWord …) ++ [false]`, `tI`'s head and `rgX` advance by `2·(s·h) + 1`, nothing else moves.

Paper quantity of the main type: a sampled half's error vector (`errorVector_decode`), on the body's layout. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Sample (DSt dec decCost decWord digitsOf)

section Lay
variable {nw nn nsc nrs : ℕ}

/-- The half's stream: `tU` (left) or `tV` (right). -/
def tO (right : Bool) : Fin (bns nw nsc + 1) := bst (if right then 3 else 2) (by split <;> omega)

/-- Stage 0's index counter register (`tI`'s head). -/
def rgX : Fin (bnr nn nrs) := brg 165 (by omega)

/-- Stage 0's streams: `tI`, then the half's. -/
def fsD (right : Bool) (i : Fin 2) : Fin (bns nw nsc + 1) := bst (if i.val = 0 then 31 else if right then 3 else 2)
  (by split_ifs <;> omega)

/-- Stage 0's registers: `156 … 167`. -/
def frD (q : Fin 12) : Fin (bnr nn nrs) := brg (156 + q.val) (by have := q.isLt; omega)

theorem fsD_inj (right : Bool) : Function.Injective (fsD (nw := nw) (nsc := nsc) right) := by
  intro a b h
  have e := congrArg Fin.val h
  simp only [fsD, bst] at e
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  split_ifs at e <;> omega

theorem frD_inj : Function.Injective (frD (nn := nn) (nrs := nrs)) := fun a b h => Fin.ext (by
  have e := congrArg Fin.val h
  simp only [frD, brg] at e
  omega)

/-- **Stage 0 on the body's layout.** -/
def decB (right : Bool) : BP nw nn nsc nrs := (dec right).liftW (fsD right) frD

/-- Stage 0's view of the body state. -/
def dview (right : Bool) (s bb h tl p : ℕ) (ω : BS nw nn nsc nrs) : DSt :=
  ⟨ω.st tI, ω.st (tO right), p, 0, s, bb, h, tl, 0, 0, 0, 0, 0, 0, ω.cell⟩

theorem fsD_1 (right : Bool) : fsD (nw := nw) (nsc := nsc) right 1 = tO right := Fin.ext (by simp [fsD, tO, bst])

theorem fsD_0 (right : Bool) : fsD (nw := nw) (nsc := nsc) right 0 = tI := Fin.ext (by simp [fsD, tI, bst])

theorem dview_w (right : Bool) (s bb h tl p : ℕ) (ω : BS nw nn nsc nrs) (hIh : ω.sh tI = p)
    (hOh : ω.sh (tO right) = 0)
    (hr : ∀ q : Fin 12, ω.val (frD q) = ![s, bb, h, tl, 0, 0, 0, 0, 0, p, 0, 0] q) :
    viewW (fsD right) frD ω = (dview right s bb h tl p ω).w' := by
  apply WState.eq
  · funext i
    fin_cases i
    · exact hIh
    · show ω.sh (fsD right 1) = 0
      rw [fsD_1]
      exact hOh
  · funext i
    fin_cases i
    · rfl
    · show ω.st (fsD right 1) = ω.st (tO right)
      rw [fsD_1]
  · funext q
    show ω.val (frD q) = _
    rw [hr q]
    simp only [dview, DSt.w']
  · rfl

/-- The body state after stage 0. -/
def decOut (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) : BS nw nn nsc nrs :=
  ((ω.sets (tO right) (frameP (decWord bb h tl right (digitsOf s h (binary (s * h) k))) ++ [false])).seth tI
    (p + 2 * (s * h) + 1)).setv rgX (p + 2 * (s * h) + 1)

/-- Stage 0's end state on its own layout. -/
def dend (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) : DSt :=
  ⟨ω.st tI, frameP (decWord bb h tl right (digitsOf s h (binary (s * h) k))) ++ false :: [], p + 2 * (s * h) + 1, 0,
    s, bb, h, tl, 0, 0, 0, 0, 0, 0, ω.cell⟩

theorem decOut_sh (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) (hOh : ω.sh (tO right) = 0) :
    (ThrPt.updW (fsD right) frD ω (dend right s bb h tl k p ω).w').sh = (decOut right s bb h tl k p ω).sh := by
  have hIO : (tI : Fin (bns nw nsc + 1)) ≠ tO right := by
    simp only [tI, tO]; apply bst_ne; split <;> omega
  funext j
  by_cases hj : ∃ i, fsD right i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [ThrPt.updW_sh_in (fsD_inj right)]
    fin_cases i
    · show p + 2 * (s * h) + 1 = (decOut right s bb h tl k p ω).sh (fsD right 0)
      rw [fsD_0]
      simp only [decOut, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_self]
    · show 0 = (decOut right s bb h tl k p ω).sh (fsD right 1)
      rw [fsD_1]
      simp only [decOut, WState.setv_sh, WState.seth_sh, WState.sets_sh]
      rw [Function.update_of_ne hIO.symm, hOh]
  · rw [ThrPt.updW_sh_out _ _ j (fun i h => hj ⟨i, h⟩)]
    have hne : j ≠ tI := fun h => hj ⟨0, (fsD_0 right).trans h.symm⟩
    simp only [decOut, WState.setv_sh, WState.seth_sh, WState.sets_sh]
    rw [Function.update_of_ne hne]

theorem decOut_st (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) :
    (ThrPt.updW (fsD right) frD ω (dend right s bb h tl k p ω).w').st = (decOut right s bb h tl k p ω).st := by
  have hIO : (tI : Fin (bns nw nsc + 1)) ≠ tO right := by
    simp only [tI, tO]; apply bst_ne; split <;> omega
  funext j
  by_cases hj : ∃ i, fsD right i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [ThrPt.updW_st_in (fsD_inj right)]
    fin_cases i
    · show ω.st tI = (decOut right s bb h tl k p ω).st (fsD right 0)
      rw [fsD_0]
      simp only [decOut, WState.setv_st, WState.seth_st, WState.sets_st]
      rw [Function.update_of_ne hIO]
    · show frameP (decWord bb h tl right (digitsOf s h (binary (s * h) k))) ++ false :: [] =
        (decOut right s bb h tl k p ω).st (fsD right 1)
      rw [fsD_1]
      simp only [decOut, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
  · rw [ThrPt.updW_st_out _ _ j (fun i h => hj ⟨i, h⟩)]
    have hne : j ≠ tO right := fun h => hj ⟨1, (fsD_1 right).trans h.symm⟩
    simp only [decOut, WState.setv_st, WState.seth_st, WState.sets_st]
    rw [Function.update_of_ne hne]

theorem decOut_val (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs)
    (hr : ∀ q : Fin 12, ω.val (frD q) = ![s, bb, h, tl, 0, 0, 0, 0, 0, p, 0, 0] q) :
    (ThrPt.updW (fsD right) frD ω (dend right s bb h tl k p ω).w').val = (decOut right s bb h tl k p ω).val := by
  have hX9 : frD 9 = (rgX : Fin (bnr nn nrs)) := Fin.ext rfl
  funext q
  by_cases hq : ∃ r, frD r = q
  · obtain ⟨r, rfl⟩ := hq
    rw [ThrPt.updW_val_in frD_inj]
    simp only [decOut, WState.setv_val, WState.seth_val, WState.sets_val]
    by_cases h9 : r = 9
    · subst h9
      rw [hX9, Function.update_self]
      simp [dend, DSt.w']
    · have hne : frD r ≠ (rgX : Fin (bnr nn nrs)) := fun h => h9 (frD_inj (h.trans hX9.symm))
      rw [Function.update_of_ne hne, hr r]
      simp only [dend, DSt.w']
      fin_cases r <;> simp_all
  · rw [ThrPt.updW_val_out _ _ q (fun r h => hq ⟨r, h⟩)]
    have hne : q ≠ rgX := fun h => hq ⟨9, hX9.trans h.symm⟩
    simp only [decOut, WState.setv_val, WState.seth_val, WState.sets_val]
    rw [Function.update_of_ne hne]

theorem decOut_eq (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) (hOh : ω.sh (tO right) = 0)
    (hr : ∀ q : Fin 12, ω.val (frD q) = ![s, bb, h, tl, 0, 0, 0, 0, 0, p, 0, 0] q) :
    ThrPt.updW (fsD right) frD ω (dend right s bb h tl k p ω).w' = decOut right s bb h tl k p ω :=
  WState.eq (decOut_sh right s bb h tl k p ω hOh) (decOut_st right s bb h tl k p ω)
    (decOut_val right s bb h tl k p ω hr) rfl

theorem decB_spec (cap : ℕ) (right : Bool) (s bb h tl k p : ℕ) (Y restI : List Bool) (ω : BS nw nn nsc nrs)
    (hbs : bb + 1 = 2 ^ s)
    (hIw : (ω.st tI).drop p = frameP (binary (s * h) k) ++ false :: restI) (hIh : ω.sh tI = p)
    (hO : ω.st (tO right) = frameP Y ++ [false]) (hY : Y.length = h * bb + h * bb + tl) (hOh : ω.sh (tO right) = 0)
    (hr : ∀ q : Fin 12, ω.val (frD q) = ![s, bb, h, tl, 0, 0, 0, 0, 0, p, 0, 0] q)
    (hcap : 2 * 2 ^ s ≤ cap) (hsc : s ≤ cap) (hih : p + 2 * (s * h) + 1 ≤ cap) (hYc : 2 * Y.length ≤ cap)
    (hbc : bb ≤ cap) (hc : h ≤ cap) (htc : tl ≤ cap) :
    WExec cap (decB right) ω (decOut right s bb h tl k p ω) (decCost s bb h tl) := by
  have e := Sample.dec_spec cap right (dview right s bb h tl p ω) s bb h tl hbs k Y [] restI rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl hIw hO hY hcap hsc hih hYc hbc hc htc
  rw [← dview_w right s bb h tl p ω hIh hOh hr] at e
  have e2 := ThrPt.WExec.liftW_upd cap (fsD_inj right) frD_inj e ω (liftW_view _ _ ω)
  exact WExec.cast cap e2 (decOut_eq right s bb h tl k p ω hOh hr) le_rfl

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
