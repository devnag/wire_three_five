import Proof.Wire_3_5.FinalPass.ThrCore
import Proof.Wire_3_5.FinalPass.HashSeed

/-! # The THR residues from FRAMED payloads, part 1: reading position, counting, the sign and the digits

(P3:2585-2623, W17.) The front end's payloads are framed (`frame c`: content bit `j` at cell `2j + 1`,
marker cells between). `DigsW` reads them in place, so the residue reader of `ThrCore` is restated at stride two:
the reading position is content index `j` at cell `2j + 1`, counted in a register `Pc` (`at2`), so that the stream can
be rewound exactly. Main declarations: `frame_read`, `at2`, `adv2W`, `cnt2W`, `head2W`, `bitLoop2W`, with their specs.
Paper quantity: the reduced coefficients `a_i` of row `(g, p)`, read from the children's words. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrRead
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

/-! ## Framed words -/

theorem frame_read (c : List Bool) (j : ℕ) (b : Bool) (rest : List Bool) (h : c.drop j = b :: rest) :
    readTapeBit (frame c) (2 * j + 1) = b := by
  have hj : j < c.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  rw [HashSeed.read_frame_odd c j hj, List.getD_eq_getElem _ _ hj]
  rw [List.drop_eq_getElem_cons hj] at h
  exact (List.cons.inj h).1

theorem frame_next (c : List Bool) (j : ℕ) (b : Bool) (rest : List Bool) (h : c.drop j = b :: rest) :
    c.drop (j + 1) = rest := by
  rw [← List.drop_drop, h]; rfl

/-! ## The reading position -/

variable {ns nr : ℕ} (cap : ℕ)

/-- Content index `j` of stream `E` at cell `2j + 1`, counted in `Pc`. -/
def at2 (σ : WState ns nr) (E : Fin (ns + 1)) (Pc : Fin nr) (j : ℕ) : WState ns nr := (σ.setv Pc j).seth E (2 * j + 1)

section At2
variable (σ : WState ns nr) (E : Fin (ns + 1)) (Pc : Fin nr) (j : ℕ)

@[simp] theorem at2_st : (at2 σ E Pc j).st = σ.st := rfl
@[simp] theorem at2_cell : (at2 σ E Pc j).cell = σ.cell := rfl
@[simp] theorem at2_sh_E : (at2 σ E Pc j).sh E = 2 * j + 1 := by simp [at2]
theorem at2_sh_ne (i : Fin (ns + 1)) (h : i ≠ E) : (at2 σ E Pc j).sh i = σ.sh i := by
  simp [at2, Function.update_apply, h]
@[simp] theorem at2_val_Pc : (at2 σ E Pc j).val Pc = j := by simp [at2]
theorem at2_val_ne (r : Fin nr) (h : r ≠ Pc) : (at2 σ E Pc j).val r = σ.val r := by
  simp [at2, Function.update_apply, h]

theorem at2_self (hs : σ.sh E = 2 * j + 1) (hp : σ.val Pc = j) : at2 σ E Pc j = σ := by
  apply WState.eq
  · funext i; by_cases hi : i = E
    · subst hi; simp [at2, hs]
    · simp [at2, Function.update_apply, hi]
  · rfl
  · funext r; by_cases hr : r = Pc
    · subst hr; simp [at2, hp]
    · simp [at2, Function.update_apply, hr]
  · rfl

end At2

/-- One framed step: two cells forward, the position counter up. -/
def adv2W (E : Fin (ns + 1)) (Pc : Fin nr) : WM ns nr := .seq (.fwd E) (.seq (.fwd E) (.inc Pc))

theorem adv2_spec (E : Fin (ns + 1)) (Pc : Fin nr) (σ : WState ns nr) (j : ℕ) (hs : σ.sh E = 2 * j + 1)
    (hp : σ.val Pc = j) (hc : j < cap) : WExec cap (adv2W E Pc) σ (at2 σ E Pc (j + 1)) 7 := by
  have d1 := WExec.fwd (cap := cap) E σ
  have d2 := WExec.fwd (cap := cap) E (σ.seth E (σ.sh E + 1))
  have d3 := WExec.inc (cap := cap) Pc ((σ.seth E (σ.sh E + 1)).seth E ((σ.seth E (σ.sh E + 1)).sh E + 1))
    (by simp [hp]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3)) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = E
    · subst hi; simp [at2, hs]; ring
    · simp [at2, Function.update_apply, hi]
  · rfl
  · funext r; by_cases hr : r = Pc
    · subst hr; simp [at2, hp]
    · simp [at2, Function.update_apply, hr]
  · rfl

/-! ## Counting ones -/

/-- `Ln +=` the number of ones before the first `0` (framed). -/
def cnt2W (E : Fin (ns + 1)) (Pc Ln : Fin nr) : WM ns nr := .whs E (.seq (.inc Ln) (adv2W E Pc))

theorem cnt2_spec (E : Fin (ns + 1)) (Pc Ln : Fin nr) (hPL : Pc ≠ Ln) (c rest : List Bool) :
    ∀ (L : ℕ) (σ : WState ns nr) (j x : ℕ), σ.st E = frame c → σ.sh E = 2 * j + 1 → σ.val Pc = j →
      c.drop j = List.replicate L true ++ false :: rest → σ.val Ln = x → x + L ≤ cap → j + L ≤ cap →
      WExec cap (cnt2W E Pc Ln) σ (at2 (σ.setv Ln (x + L)) E Pc (j + L)) (13 * L + 1)
  | 0, σ, j, x, hst, hs, hp, hd, hx, _, _ => by
    have hb : wbit σ E = false := by
      unfold wbit; rw [hst, hs]; exact frame_read c j false rest (by simpa using hd)
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    rw [Nat.add_zero, Nat.add_zero, ← hx, wsetv_same, at2_self σ E Pc j hs hp]
  | L + 1, σ, j, x, hst, hs, hp, hd, hx, hc1, hc2 => by
    have hd' : c.drop j = true :: (List.replicate L true ++ false :: rest) := by
      rw [hd]; simp [List.replicate_succ]
    have hb : wbit σ E = true := by unfold wbit; rw [hst, hs]; exact frame_read c j true _ hd'
    have d1 := WExec.inc (cap := cap) Ln σ (by omega)
    have d2 := adv2_spec cap E Pc (σ.setv Ln (σ.val Ln + 1)) j (by simpa using hs)
      (by simp [Function.update_apply, hPL, hp]) (by omega)
    have ih := cnt2_spec E Pc Ln hPL c rest L (at2 (σ.setv Ln (σ.val Ln + 1)) E Pc (j + 1)) (j + 1) (x + 1)
      (by simp [hst]) (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _) (frame_next c j true _ hd')
      (by rw [at2_val_ne _ _ _ _ _ (Ne.symm hPL)]; simp [hx]) (by omega) (by omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq d1 d2) ih) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = E
      · subst hi; simp [at2]; ring
      · simp [at2, Function.update_apply, hi]
    · rfl
    · funext r; by_cases h1 : r = Pc
      · subst h1; simp [at2]; ring
      · by_cases h2 : r = Ln
        · subst h2; simp [at2, Function.update_apply, h1, hx]; ring
        · simp [at2, Function.update_apply, h1, h2]
    · rfl

end NearCubicWires.WireExponent3_5.FinalPass.ThrRead
