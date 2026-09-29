import Proof.Wire_3_5.Primitive.SeedFix.ReadEq
import Proof.Wire_3_5.FinalPass.WordLib

/-! # S3, part 6: scratch writers read cell by cell (P3:3170-3178)

The per-point evaluator's scratch streams only READ blank at entry (`PtIn.sc`, any length) and must read blank again
at exit (`PtOut.sc`, loop-safe). Its writers are therefore stated through `readTapeBit` (C5's `writeTapeBit` pads with
blank cells; `ReadEq.readTapeBit_write`):

* `wrAdv` (one cell written, the head on, a counter up), `wrAdv_spec`;
* **`blankLoop_spec`** (`c` rounds of `k` blank cells), **`markLoop_spec`** (`c` rounds of `[1, 0]`: the frame of the
  zero accumulator `frameP (binary h 0)`), **`copyLoop_spec`** (`c` cells copied from a stream's head onto another
  from its origin): each gives every cell of the written stream by position, the heads, the counters, and nothing else
  changed.

Paper quantity of the main types: none beyond the machine model; the scratch discipline of the per-point
evaluators (`PtIn`, `PtOut`, the seam of the SYM value's numerator `Σ R̂`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq

section Writers
variable {ns nr : ℕ} (cap : ℕ)

/-- One cell written, the head on, the counter up. -/
def wrAdv (X : Fin (ns + 1)) (b : Bool) (bk : Fin nr) : WM ns nr := .seq (.wr X b) (.seq (.fwd X) (.inc bk))

theorem wrAdv_spec (X : Fin (ns + 1)) (b : Bool) (bk : Fin nr) (σ : WState ns nr) (hb : σ.val bk < cap) :
    ∃ τ, WExec cap (wrAdv X b bk) σ τ 7 ∧
      (∀ p, readTapeBit (τ.st X) p = if p = σ.sh X then b else readTapeBit (σ.st X) p) ∧
      τ.sh X = σ.sh X + 1 ∧ τ.val bk = σ.val bk + 1 ∧ (∀ i, i ≠ X → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ bk → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have e1 := WExec.wr (cap := cap) X b σ
  have e2 := WExec.fwd (cap := cap) X (σ.sets X (writeTapeBit (σ.st X) (σ.sh X) b))
  have e3 := WExec.inc (cap := cap) bk ((σ.sets X (writeTapeBit (σ.st X) (σ.sh X) b)).seth X
    ((σ.sets X (writeTapeBit (σ.st X) (σ.sh X) b)).sh X + 1)) (by simpa using hb)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by omega), fun p => ?_, ?_, ?_, fun i hi => ?_,
    fun r hr => ?_, ?_⟩
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    exact readTapeBit_write _ _ _ _
  · simp
  · simp
  · simp [Function.update_apply, hi]
  · simp [Function.update_apply, hr]
  · simp

/-- `k` cells of `b` written. -/
def wrN (X : Fin (ns + 1)) (b : Bool) (bk : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (wrAdv X b bk) (wrN X b bk k)

theorem wrN_spec (X : Fin (ns + 1)) (b : Bool) (bk : Fin nr) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val bk + k ≤ cap →
      ∃ τ, WExec cap (wrN X b bk k) σ τ (8 * k) ∧
        (∀ p, readTapeBit (τ.st X) p =
          if σ.sh X ≤ p ∧ p < σ.sh X + k then b else readTapeBit (σ.st X) p) ∧
        τ.sh X = σ.sh X + k ∧ τ.val bk = σ.val bk + k ∧ (∀ i, i ≠ X → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
        (∀ r, r ≠ bk → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | 0, σ, _ => ⟨σ, WExec.skip σ, fun p => by simp, by simp, by simp, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  | k + 1, σ, hc => by
    obtain ⟨τ1, e1, r1, s1, b1, o1, v1, c1⟩ := wrAdv_spec cap X b bk σ (by omega)
    obtain ⟨τ2, e2, r2, s2, b2, o2, v2, c2⟩ := wrN_spec X b bk k τ1 (by omega)
    refine ⟨τ2, WExec.mono (WExec.seq e1 e2) (by omega), fun p => ?_, by omega, by omega,
      fun i hi => ⟨(o2 i hi).1.trans (o1 i hi).1, (o2 i hi).2.trans (o1 i hi).2⟩,
      fun r hr => (v2 r hr).trans (v1 r hr), c2.trans c1⟩
    rw [r2 p, s1, r1 p]
    by_cases h1 : σ.sh X + 1 ≤ p ∧ p < σ.sh X + 1 + k
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : p = σ.sh X
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-- `c` rounds of `k` blank cells (the round counter `cnt`, the cell counter `bk`). -/
def blankLoop (X : Fin (ns + 1)) (cnt bk : Fin nr) (k : ℕ) : WM ns nr := .whr cnt (.seq (.dec cnt) (wrN X false bk k))

theorem blankLoop_spec (X : Fin (ns + 1)) (cnt bk : Fin nr) (hcb : cnt ≠ bk) (k : ℕ) :
    ∀ (c : ℕ) (σ : WState ns nr), σ.val cnt = c → c ≤ cap → σ.val bk + k * c ≤ cap →
      ∃ τ, WExec cap (blankLoop X cnt bk k) σ τ (c * (8 * k + 4) + 1) ∧
        (∀ p, readTapeBit (τ.st X) p =
          if σ.sh X ≤ p ∧ p < σ.sh X + k * c then false else readTapeBit (σ.st X) p) ∧
        τ.sh X = σ.sh X + k * c ∧ τ.val bk = σ.val bk + k * c ∧ τ.val cnt = 0 ∧
        (∀ i, i ≠ X → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ (∀ r, r ≠ bk → r ≠ cnt → τ.val r = σ.val r) ∧
        τ.cell = σ.cell
  | 0, σ, hc, _, _ => ⟨σ, WExec.mono (WExec.whrF hc) (by omega),
      fun p => by rw [Nat.mul_zero, Nat.add_zero, if_neg (by omega)], by simp, by simp, hc,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, rfl⟩
  | c + 1, σ, hc, hcc, hbc => by
    have hm : (c + 1) * (8 * k + 4) = c * (8 * k + 4) + (8 * k + 4) := by ring
    have e0 := WExec.dec (cap := cap) cnt σ (by omega)
    obtain ⟨τ1, e1, r1, s1, b1, o1, v1, c1⟩ := wrN_spec cap X false bk k (σ.setv cnt (σ.val cnt - 1))
      (by simp [Function.update_apply, Ne.symm hcb]; rw [Nat.mul_succ] at hbc; omega)
    obtain ⟨τ2, e2, r2, s2, b2, k2, o2, v2, c2⟩ := blankLoop_spec X cnt bk hcb k c τ1
      (by rw [v1 cnt hcb]; simp [hc]) (by omega)
      (by rw [b1]; simp [Function.update_apply, Ne.symm hcb]; rw [Nat.mul_succ] at hbc; omega)
    refine ⟨τ2, WExec.mono (WExec.whrT (by omega) (WExec.seq e0 e1) e2) (by rw [hm]; omega), fun p => ?_,
      ?_, ?_, k2, fun i hi => ?_, fun r r1 r2 => ?_, ?_⟩
    · rw [r2 p, s1, r1 p]
      simp only [WState.setv_st, WState.setv_sh]
      by_cases h1 : σ.sh X + k ≤ p ∧ p < σ.sh X + k + k * c
      · rw [if_pos h1, if_pos (by rw [Nat.mul_succ]; omega)]
      · rw [if_neg h1]
        by_cases h2 : σ.sh X ≤ p ∧ p < σ.sh X + k
        · rw [if_pos h2, if_pos (by rw [Nat.mul_succ]; omega)]
        · rw [if_neg h2, if_neg (by rw [Nat.mul_succ]; omega)]
    · rw [s2, s1]; simp only [WState.setv_sh]; rw [Nat.mul_succ]; ring
    · rw [b2, b1]; simp [Function.update_apply, Ne.symm hcb]; rw [Nat.mul_succ]; ring
    · rw [(o2 i hi).1, (o1 i hi).1, (o2 i hi).2, (o1 i hi).2]; exact ⟨rfl, rfl⟩
    · rw [v2 r r1 r2, v1 r r1]; simp [Function.update_apply, r2]
    · rw [c2, c1]; rfl

/-- `c` rounds of the frame pair `[1, 0]`. -/
def markLoop (X : Fin (ns + 1)) (cnt bk : Fin nr) : WM ns nr :=
  .whr cnt (.seq (.dec cnt) (.seq (wrAdv X true bk) (wrAdv X false bk)))

theorem markLoop_spec (X : Fin (ns + 1)) (cnt bk : Fin nr) (hcb : cnt ≠ bk) :
    ∀ (c : ℕ) (σ : WState ns nr), σ.val cnt = c → c ≤ cap → σ.val bk + 2 * c ≤ cap →
      ∃ τ, WExec cap (markLoop X cnt bk) σ τ (c * 20 + 1) ∧
        (∀ p, readTapeBit (τ.st X) p =
          if σ.sh X ≤ p ∧ p < σ.sh X + 2 * c then decide ((p - σ.sh X) % 2 = 0) else readTapeBit (σ.st X) p) ∧
        τ.sh X = σ.sh X + 2 * c ∧ τ.val bk = σ.val bk + 2 * c ∧ τ.val cnt = 0 ∧
        (∀ i, i ≠ X → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ (∀ r, r ≠ bk → r ≠ cnt → τ.val r = σ.val r) ∧
        τ.cell = σ.cell
  | 0, σ, hc, _, _ => ⟨σ, WExec.mono (WExec.whrF hc) (by omega),
      fun p => by rw [Nat.mul_zero, Nat.add_zero, if_neg (by omega)], by simp, by simp, hc,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, rfl⟩
  | c + 1, σ, hc, hcc, hbc => by
    have hm : (c + 1) * 20 = c * 20 + 20 := by ring
    have e0 := WExec.dec (cap := cap) cnt σ (by omega)
    obtain ⟨τ1, e1, r1, s1, b1, o1, v1, c1⟩ := wrAdv_spec cap X true bk (σ.setv cnt (σ.val cnt - 1))
      (by simp [Function.update_apply, Ne.symm hcb]; omega)
    obtain ⟨τ2, e2, r2, s2, b2, o2, v2, c2⟩ := wrAdv_spec cap X false bk τ1
      (by rw [b1]; simp [Function.update_apply, Ne.symm hcb]; omega)
    obtain ⟨τ3, e3, r3, s3, b3, k3, o3, v3, c3⟩ := markLoop_spec X cnt bk hcb c τ2
      (by rw [v2 cnt hcb, v1 cnt hcb]; simp [hc]) (by omega)
      (by rw [b2, b1]; simp [Function.update_apply, Ne.symm hcb]; omega)
    have sh2 : τ2.sh X = σ.sh X + 2 := by rw [s2, s1]; simp
    refine ⟨τ3, WExec.mono (WExec.whrT (by omega) (WExec.seq e0 (WExec.seq e1 e2)) e3) (by rw [hm]; omega),
      fun p => ?_, ?_, ?_, k3, fun i hi => ?_, fun r r1 r2 => ?_, ?_⟩
    · rw [r3 p, sh2, r2 p, s1, r1 p]
      simp only [WState.setv_st, WState.setv_sh]
      by_cases h1 : σ.sh X + 2 ≤ p ∧ p < σ.sh X + 2 + 2 * c
      · rw [if_pos h1, if_pos (by omega)]
        congr 1
        apply propext
        constructor <;> intro h <;> omega
      · rw [if_neg h1]
        by_cases h2 : p = σ.sh X + 1
        · rw [if_pos h2, if_pos (by omega)]
          subst h2
          simp
        · rw [if_neg h2]
          by_cases h3 : p = σ.sh X
          · rw [if_pos h3, if_pos (by omega)]
            subst h3
            simp
          · rw [if_neg h3, if_neg (by omega)]
    · rw [s3, sh2]; ring
    · rw [b3, b2, b1]; simp [Function.update_apply, Ne.symm hcb]; ring
    · rw [(o3 i hi).1, (o2 i hi).1, (o1 i hi).1, (o3 i hi).2, (o2 i hi).2, (o1 i hi).2]; exact ⟨rfl, rfl⟩
    · rw [v3 r r1 r2, v2 r r1, v1 r r1]; simp [Function.update_apply, r2]
    · rw [c3, c2, c1]; rfl

/-- One cell copied: the source's scanned bit onto the target, both heads on, both counters up. -/
def cpStep (src dst : Fin (ns + 1)) (bk sk : Fin nr) : WM ns nr :=
  .seq (.ifs src (.wr dst true) (.wr dst false)) (.seq (.fwd src) (.seq (.fwd dst) (.seq (.inc bk) (.inc sk))))

theorem cpStep_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (bk sk : Fin nr) (hbs : bk ≠ sk) (σ : WState ns nr)
    (hb : σ.val bk < cap) (hs : σ.val sk < cap) :
    ∃ τ, WExec cap (cpStep src dst bk sk) σ τ 14 ∧
      (∀ p, readTapeBit (τ.st dst) p =
        if p = σ.sh dst then readTapeBit (σ.st src) (σ.sh src) else readTapeBit (σ.st dst) p) ∧
      τ.st src = σ.st src ∧ τ.sh src = σ.sh src + 1 ∧ τ.sh dst = σ.sh dst + 1 ∧ τ.val bk = σ.val bk + 1 ∧
      τ.val sk = σ.val sk + 1 ∧ (∀ i, i ≠ src → i ≠ dst → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ bk → r ≠ sk → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  set b := readTapeBit (σ.st src) (σ.sh src) with hbit
  have e1 : WExec cap (.ifs src (.wr dst true) (.wr dst false)) σ
      (σ.sets dst (writeTapeBit (σ.st dst) (σ.sh dst) b)) 2 := by
    cases hb' : b
    · exact WExec.ifsF (by unfold wbit; rw [← hbit, hb']) (WExec.wr dst false σ)
    · exact WExec.ifsT (by unfold wbit; rw [← hbit, hb']) (WExec.wr dst true σ)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.sets dst (writeTapeBit (σ.st dst) (σ.sh dst) b) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have e2 := WExec.fwd (cap := cap) src σ1
  have e3 := WExec.fwd (cap := cap) dst (σ1.seth src (σ1.sh src + 1))
  obtain ⟨σ3, hσ3⟩ : ∃ y, y = (σ1.seth src (σ1.sh src + 1)).seth dst ((σ1.seth src (σ1.sh src + 1)).sh dst + 1) :=
    ⟨_, rfl⟩
  rw [← hσ3] at e3
  have e4 := WExec.inc (cap := cap) bk σ3 (by rw [hσ3, hσ1]; simpa using hb)
  have e5 := WExec.inc (cap := cap) sk (σ3.setv bk (σ3.val bk + 1))
    (by rw [hσ3, hσ1]; simp [Function.update_apply, Ne.symm hbs]; exact hs)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) (by omega), fun p => ?_, ?_, ?_,
    ?_, ?_, ?_, fun i i1 i2 => ?_, fun r r1 r2 => ?_, ?_⟩
  · simp only [WState.setv_st]; rw [hσ3, hσ1]
    simp only [WState.seth_st, WState.sets_st, Function.update_self]
    exact readTapeBit_write _ _ _ _
  · simp only [WState.setv_st]; rw [hσ3, hσ1]
    simp only [WState.seth_st, WState.sets_st, Function.update_of_ne hsd]
  · simp only [WState.setv_sh]; rw [hσ3, hσ1]
    simp [Function.update_apply, hsd]
  · simp only [WState.setv_sh]; rw [hσ3, hσ1]
    simp [Function.update_apply, Ne.symm hsd]
  · rw [hσ3, hσ1]; simp [Function.update_apply, hbs]
  · rw [hσ3, hσ1]; simp [Function.update_apply, Ne.symm hbs]
  · simp only [WState.setv_st, WState.setv_sh]; rw [hσ3, hσ1]
    simp [Function.update_apply, i1, i2]
  · rw [hσ3, hσ1]; simp [Function.update_apply, r1, r2]
  · rw [hσ3, hσ1]; simp

/-- `c` cells copied from the source's head onto the target from its head. -/
def copyLoop (src dst : Fin (ns + 1)) (cnt bk sk : Fin nr) : WM ns nr := .whr cnt (.seq (.dec cnt) (cpStep src dst bk sk))

theorem copyLoop_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (cnt bk sk : Fin nr) (hcb : cnt ≠ bk) (hcs : cnt ≠ sk)
    (hbs : bk ≠ sk) :
    ∀ (c : ℕ) (σ : WState ns nr), σ.val cnt = c → c ≤ cap → σ.val bk + c ≤ cap → σ.val sk + c ≤ cap →
      ∃ τ, WExec cap (copyLoop src dst cnt bk sk) σ τ (c * 18 + 1) ∧
        (∀ p, readTapeBit (τ.st dst) p = if σ.sh dst ≤ p ∧ p < σ.sh dst + c then
          readTapeBit (σ.st src) (σ.sh src + (p - σ.sh dst)) else readTapeBit (σ.st dst) p) ∧
        τ.st src = σ.st src ∧ τ.sh src = σ.sh src + c ∧ τ.sh dst = σ.sh dst + c ∧ τ.val bk = σ.val bk + c ∧
        τ.val sk = σ.val sk + c ∧ τ.val cnt = 0 ∧ (∀ i, i ≠ src → i ≠ dst → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
        (∀ r, r ≠ bk → r ≠ sk → r ≠ cnt → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | 0, σ, hc, _, _, _ => ⟨σ, WExec.mono (WExec.whrF hc) (by omega),
      fun p => by rw [Nat.add_zero, if_neg (by omega)], rfl, by simp, by simp, by simp, by simp, hc,
      fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, rfl⟩
  | c + 1, σ, hc, hcc, hbc, hsc => by
    have e0 := WExec.dec (cap := cap) cnt σ (by omega)
    obtain ⟨τ1, e1, r1, s1, hs1, hd1, b1, k1, o1, v1, c1⟩ := cpStep_spec cap src dst hsd bk sk hbs
      (σ.setv cnt (σ.val cnt - 1)) (by simp [Function.update_apply, Ne.symm hcb]; omega)
      (by simp [Function.update_apply, Ne.symm hcs]; omega)
    obtain ⟨τ2, e2, r2, s2, hs2, hd2, b2, k2, z2, o2, v2, c2⟩ := copyLoop_spec src dst hsd cnt bk sk hcb hcs hbs c τ1
      (by rw [v1 cnt hcb hcs]; simp [hc]) (by omega)
      (by rw [b1]; simp [Function.update_apply, Ne.symm hcb]; omega)
      (by rw [k1]; simp [Function.update_apply, Ne.symm hcs]; omega)
    have hm : (c + 1) * 18 = c * 18 + 18 := by ring
    refine ⟨τ2, WExec.mono (WExec.whrT (by omega) (WExec.seq e0 e1) e2) (by rw [hm]; omega), fun p => ?_,
      s2.trans s1, ?_, ?_, ?_, ?_, z2, fun i i1 i2 => ?_, fun r r1 r2 r3 => ?_, ?_⟩
    · rw [r2 p, hd1, hs1, s1, r1 p]
      simp only [WState.setv_st, WState.setv_sh]
      by_cases h1 : σ.sh dst + 1 ≤ p ∧ p < σ.sh dst + 1 + c
      · rw [if_pos h1, if_pos (by omega)]
        congr 1
        omega
      · rw [if_neg h1]
        by_cases h2 : p = σ.sh dst
        · rw [if_pos h2, if_pos (by omega)]
          subst h2
          simp
        · rw [if_neg h2, if_neg (by omega)]
    · rw [hs2, hs1]; simp; ring
    · rw [hd2, hd1]; simp; ring
    · rw [b2, b1]; simp [Function.update_apply, Ne.symm hcb]; ring
    · rw [k2, k1]; simp [Function.update_apply, Ne.symm hcs]; ring
    · rw [(o2 i i1 i2).1, (o1 i i1 i2).1, (o2 i i1 i2).2, (o1 i i1 i2).2]; exact ⟨rfl, rfl⟩
    · rw [v2 r r1 r2 r3, v1 r r1 r2]; simp [Function.update_apply, r3]
    · rw [c2, c1]; rfl

end Writers

end NearCubicWires.WireExponent3_5.PrimT.S3
