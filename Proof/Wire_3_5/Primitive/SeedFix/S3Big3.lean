import Proof.Wire_3_5.Primitive.SeedFix.S3Wr
import Proof.Wire_3_5.Primitive.SeedFix.FlipsDec
import Proof.Wire_3_5.FinalPass.HashTable

/-! # S3, part 9: counted writers that leave the registers and the heads as they found them

The evaluator prepares each circuit's scratch (the template, the seed's flat table, the population accumulators) and
blanks it again after the factor (loop-safe scratch), with loops counted by a call number
(P3:3170-3178: "At one sampled input, compute the nested counts … follow its unique reconstructed count …").
Each writer here copies the number into a counter (`Hash4.wcopyR`), runs one of `S3Wr`'s loops, and rewinds the
written stream (`Flips.rew1`):
* **`copyN`** (`copyN_spec`): the destination reads the source's next `c` cells; the source head and the offset
  register advance by `c`; **`copyTN`** also rewinds the source (every head and register as found);
* **`blankN`** (`blankN_spec`): `k·c` cells `false`; **`markN`** (`markN_spec`): `c` pairs `true, false`, the frame of
  the zero population count (`read_marks`).

Paper quantity of the main types: the stream contents the counted loops leave, `c` = the call number. -/

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
open NearCubicWires.WireExponent3_5.PrimT.Flips (rew1 rew1_spec)
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable {ns nr : ℕ} (cap : ℕ)

/-- Copy `c = num` cells from `src`'s head into `dst` (from `0`), then rewind `dst`. -/
def copyN (src dst : Fin (ns + 1)) (num cnt tmp bk sk : Fin nr) : WM ns nr :=
  .seq (wcopyR num cnt tmp) (.seq (copyLoop src dst cnt bk sk) (rew1 dst bk))

theorem copyN_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (num cnt tmp bk sk : Fin nr)
    (h1 : num ≠ cnt) (h2 : num ≠ tmp) (h3 : cnt ≠ tmp) (h4 : cnt ≠ bk) (h5 : cnt ≠ sk) (h6 : bk ≠ sk)
    (σ : WState ns nr) (hc0 : σ.val cnt = 0) (ht0 : σ.val tmp = 0) (hb0 : σ.val bk = 0) (hd0 : σ.sh dst = 0)
    (hcap1 : σ.val num ≤ cap) (hcap2 : σ.val sk + σ.val num ≤ cap) :
    ∃ τ, WExec cap (copyN src dst num cnt tmp bk sk) σ τ (41 * σ.val num + 7) ∧
      (∀ p, readTapeBit (τ.st dst) p =
        if p < σ.val num then readTapeBit (σ.st src) (σ.sh src + p) else readTapeBit (σ.st dst) p) ∧
      (∀ i, i ≠ dst → τ.st i = σ.st i) ∧ τ.sh = Function.update σ.sh src (σ.sh src + σ.val num) ∧
      τ.val = Function.update σ.val sk (σ.val sk + σ.val num) ∧ τ.cell = σ.cell := by
  obtain ⟨c, hc⟩ : ∃ c, c = σ.val num := ⟨_, rfl⟩
  rw [← hc] at hcap1 hcap2 ⊢
  have e1 := wcopyR_spec cap num cnt tmp h1 h2 h3 σ hc0 ht0 (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv cnt (σ.val num) := ⟨_, rfl⟩
  rw [← hσ1, ← hc] at e1
  have v1 : ∀ r, r ≠ cnt → σ1.val r = σ.val r := fun r hr => by
    rw [hσ1, WState.setv_val, Function.update_of_ne hr]
  have v1c : σ1.val cnt = c := by rw [hσ1, WState.setv_val, Function.update_self, hc]
  have sh1 : σ1.sh = σ.sh := by rw [hσ1]; rfl
  have st1 : σ1.st = σ.st := by rw [hσ1]; rfl
  have cl1 : σ1.cell = σ.cell := by rw [hσ1]; rfl
  obtain ⟨σ2, e2, r2, s2, hs2, hd2, b2, k2, c2, o2, v2, cl2⟩ := copyLoop_spec cap src dst hsd cnt bk sk h4 h5 h6 c σ1
    v1c (by omega) (by rw [v1 bk (Ne.symm h4), hb0]; omega) (by rw [v1 sk (Ne.symm h5)]; omega)
  obtain ⟨σ3, e3, t1, t2, t3, t4, t5, t6⟩ := rew1_spec cap dst bk c σ2 (by rw [b2, v1 bk (Ne.symm h4), hb0]; omega)
    (by rw [hd2, sh1, hd0]; omega) (by omega)
  refine ⟨σ3, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by omega), fun p => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [t3, r2 p, sh1, hd0, st1]
    simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
  · rw [t3]
    by_cases his : i = src
    · subst his; rw [s2, st1]
    · rw [(o2 i his hi).1, st1]
  · funext i
    by_cases hid : i = dst
    · subst hid; rw [t1, Function.update_of_ne (Ne.symm hsd), hd0]
    · rw [t4 i hid]
      by_cases his : i = src
      · subst his; rw [hs2, sh1, Function.update_self]
      · rw [(o2 i his hid).2, sh1, Function.update_of_ne his]
  · funext r
    by_cases hrb : r = bk
    · subst hrb; rw [t2, Function.update_of_ne h6, hb0]
    · rw [t5 r hrb]
      by_cases hrs : r = sk
      · subst hrs; rw [k2, v1 _ (Ne.symm h5), Function.update_self]
      · by_cases hrc : r = cnt
        · subst hrc; rw [c2, Function.update_of_ne hrs, hc0]
        · rw [v2 r hrb hrs hrc, v1 r hrc, Function.update_of_ne hrs]
  · rw [t6, cl2, cl1]

/-- `copyN`, then the source rewound. -/
def copyTN (src dst : Fin (ns + 1)) (num cnt tmp bk sk : Fin nr) : WM ns nr :=
  .seq (copyN src dst num cnt tmp bk sk) (rew1 src sk)

theorem copyTN_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (num cnt tmp bk sk : Fin nr)
    (h1 : num ≠ cnt) (h2 : num ≠ tmp) (h3 : cnt ≠ tmp) (h4 : cnt ≠ bk) (h5 : cnt ≠ sk) (h6 : bk ≠ sk)
    (h8 : num ≠ sk)
    (σ : WState ns nr) (hc0 : σ.val cnt = 0) (ht0 : σ.val tmp = 0) (hb0 : σ.val bk = 0) (hk0 : σ.val sk = 0)
    (hd0 : σ.sh dst = 0) (hs0 : σ.sh src = 0) (hcap1 : σ.val num ≤ cap) :
    ∃ τ, WExec cap (copyTN src dst num cnt tmp bk sk) σ τ (46 * σ.val num + 9) ∧
      (∀ p, readTapeBit (τ.st dst) p =
        if p < σ.val num then readTapeBit (σ.st src) p else readTapeBit (σ.st dst) p) ∧
      (∀ i, i ≠ dst → τ.st i = σ.st i) ∧ τ.sh = σ.sh ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, e1, r1, o1, sh1, v1, cl1⟩ := copyN_spec cap src dst hsd num cnt tmp bk sk h1 h2 h3 h4 h5 h6 σ hc0 ht0
    hb0 hd0 hcap1 (by omega)
  obtain ⟨σ2, e2, t1, t2, t3, t4, t5, t6⟩ := rew1_spec cap src sk (σ.val num) σ1
    (by rw [v1, Function.update_self, hk0, Nat.zero_add]) (by rw [sh1, Function.update_self, hs0, Nat.zero_add])
    hcap1
  refine ⟨σ2, WExec.mono (WExec.seq e1 e2) (by omega), fun p => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [t3, r1 p, hs0, Nat.zero_add]
  · rw [t3, o1 i hi]
  · funext i
    by_cases his : i = src
    · subst his; rw [t1, hs0]
    · rw [t4 i his, sh1, Function.update_of_ne his]
  · funext r
    by_cases hrs : r = sk
    · subst hrs; rw [t2, hk0]
    · rw [t5 r hrs, v1, Function.update_of_ne hrs]
  · rw [t6, cl1]

/-- Blank `k·c` cells of `X` (from `0`, `c = num`), then rewind `X`. -/
def blankN (X : Fin (ns + 1)) (num cnt tmp bk : Fin nr) (k : ℕ) : WM ns nr :=
  .seq (wcopyR num cnt tmp) (.seq (blankLoop X cnt bk k) (rew1 X bk))

theorem blankN_spec (X : Fin (ns + 1)) (num cnt tmp bk : Fin nr) (k : ℕ)
    (h1 : num ≠ cnt) (h2 : num ≠ tmp) (h3 : cnt ≠ tmp) (h4 : cnt ≠ bk)
    (σ : WState ns nr) (hc0 : σ.val cnt = 0) (ht0 : σ.val tmp = 0) (hb0 : σ.val bk = 0) (hx0 : σ.sh X = 0)
    (hcap1 : σ.val num ≤ cap) (hcap2 : k * σ.val num ≤ cap) :
    ∃ τ, WExec cap (blankN X num cnt tmp bk k) σ τ (σ.val num * (13 * k + 22) + 7) ∧
      (∀ p, readTapeBit (τ.st X) p = if p < k * σ.val num then false else readTapeBit (σ.st X) p) ∧
      (∀ i, i ≠ X → τ.st i = σ.st i) ∧ τ.sh = σ.sh ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨c, hc⟩ : ∃ c, c = σ.val num := ⟨_, rfl⟩
  rw [← hc] at hcap1 hcap2 ⊢
  have e1 := wcopyR_spec cap num cnt tmp h1 h2 h3 σ hc0 ht0 (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv cnt (σ.val num) := ⟨_, rfl⟩
  rw [← hσ1, ← hc] at e1
  have v1 : ∀ r, r ≠ cnt → σ1.val r = σ.val r := fun r hr => by
    rw [hσ1, WState.setv_val, Function.update_of_ne hr]
  have v1c : σ1.val cnt = c := by rw [hσ1, WState.setv_val, Function.update_self, hc]
  have sh1 : σ1.sh = σ.sh := by rw [hσ1]; rfl
  have st1 : σ1.st = σ.st := by rw [hσ1]; rfl
  have cl1 : σ1.cell = σ.cell := by rw [hσ1]; rfl
  obtain ⟨σ2, e2, r2, s2, b2, c2, o2, v2, cl2⟩ := blankLoop_spec cap X cnt bk h4 k c σ1 v1c (by omega)
    (by rw [v1 bk (Ne.symm h4), hb0]; omega)
  obtain ⟨σ3, e3, t1, t2, t3, t4, t5, t6⟩ := rew1_spec cap X bk (k * c) σ2 (by rw [b2, v1 bk (Ne.symm h4), hb0]; omega)
    (by rw [s2, sh1, hx0]; omega) hcap2
  refine ⟨σ3, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (le_of_eq (by ring)), fun p => ?_, fun i hi => ?_, ?_, ?_,
    ?_⟩
  · rw [t3, r2 p, sh1, hx0, st1]
    simp only [Nat.zero_le, true_and, Nat.zero_add]
  · rw [t3, (o2 i hi).1, st1]
  · funext i
    by_cases hix : i = X
    · subst hix; rw [t1, hx0]
    · rw [t4 i hix, (o2 i hix).2, sh1]
  · funext r
    by_cases hrb : r = bk
    · subst hrb; rw [t2, hb0]
    · rw [t5 r hrb]
      by_cases hrc : r = cnt
      · subst hrc; rw [c2, hc0]
      · rw [v2 r hrb hrc, v1 r hrc]
  · rw [t6, cl2, cl1]

/-- Write `c = num` pairs `true, false` into `X` (from `0`), then rewind `X`. -/
def markN (X : Fin (ns + 1)) (num cnt tmp bk : Fin nr) : WM ns nr :=
  .seq (wcopyR num cnt tmp) (.seq (markLoop X cnt bk) (rew1 X bk))

theorem markN_spec (X : Fin (ns + 1)) (num cnt tmp bk : Fin nr)
    (h1 : num ≠ cnt) (h2 : num ≠ tmp) (h3 : cnt ≠ tmp) (h4 : cnt ≠ bk)
    (σ : WState ns nr) (hc0 : σ.val cnt = 0) (ht0 : σ.val tmp = 0) (hb0 : σ.val bk = 0) (hx0 : σ.sh X = 0)
    (hcap1 : 2 * σ.val num ≤ cap) :
    ∃ τ, WExec cap (markN X num cnt tmp bk) σ τ (48 * σ.val num + 7) ∧
      (∀ p, readTapeBit (τ.st X) p = if p < 2 * σ.val num then decide (p % 2 = 0) else readTapeBit (σ.st X) p) ∧
      (∀ i, i ≠ X → τ.st i = σ.st i) ∧ τ.sh = σ.sh ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨c, hc⟩ : ∃ c, c = σ.val num := ⟨_, rfl⟩
  rw [← hc] at hcap1 ⊢
  have e1 := wcopyR_spec cap num cnt tmp h1 h2 h3 σ hc0 ht0 (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv cnt (σ.val num) := ⟨_, rfl⟩
  rw [← hσ1, ← hc] at e1
  have v1 : ∀ r, r ≠ cnt → σ1.val r = σ.val r := fun r hr => by
    rw [hσ1, WState.setv_val, Function.update_of_ne hr]
  have v1c : σ1.val cnt = c := by rw [hσ1, WState.setv_val, Function.update_self, hc]
  have sh1 : σ1.sh = σ.sh := by rw [hσ1]; rfl
  have st1 : σ1.st = σ.st := by rw [hσ1]; rfl
  have cl1 : σ1.cell = σ.cell := by rw [hσ1]; rfl
  obtain ⟨σ2, e2, r2, s2, b2, c2, o2, v2, cl2⟩ := markLoop_spec cap X cnt bk h4 c σ1 v1c (by omega)
    (by rw [v1 bk (Ne.symm h4), hb0]; omega)
  obtain ⟨σ3, e3, t1, t2, t3, t4, t5, t6⟩ := rew1_spec cap X bk (2 * c) σ2 (by rw [b2, v1 bk (Ne.symm h4), hb0]; omega)
    (by rw [s2, sh1, hx0]; omega) hcap1
  refine ⟨σ3, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by omega), fun p => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [t3, r2 p, sh1, hx0, st1]
    simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
  · rw [t3, (o2 i hi).1, st1]
  · funext i
    by_cases hix : i = X
    · subst hix; rw [t1, hx0]
    · rw [t4 i hix, (o2 i hix).2, sh1]
  · funext r
    by_cases hrb : r = bk
    · subst hrb; rw [t2, hb0]
    · rw [t5 r hrb]
      by_cases hrc : r = cnt
      · subst hrc; rw [c2, hc0]
      · rw [v2 r hrb hrc, v1 r hrc]
  · rw [t6, cl2, cl1]

/-! ## The frame of the zero count -/

open NearCubicWires.RepairOrdinary.SignedSortKey (binary) in
theorem bin0_rep : ∀ h : ℕ, binary h 0 = List.replicate h false
  | 0 => rfl
  | h + 1 => by rw [List.replicate_succ, ← bin0_rep h]; rfl

/-- **The frame of the zero count reads as `markN` writes it.** -/
theorem read_marks : ∀ (h p : ℕ), readTapeBit (frameP (List.replicate h false) ++ [false]) p =
    if p < 2 * h then decide (p % 2 = 0) else false
  | 0, p => by
    rw [if_neg (by omega)]
    unfold readTapeBit
    cases p with
    | zero => rfl
    | succ m => simp [frameP]
  | h + 1, 0 => by simp [frameP, readTapeBit, List.replicate_succ]
  | h + 1, 1 => by simp [frameP, readTapeBit, List.replicate_succ]
  | h + 1, p + 2 => by
    have e : frameP (List.replicate (h + 1) false) ++ [false] =
        true :: false :: (frameP (List.replicate h false) ++ [false]) := by
      simp [frameP, List.replicate_succ]
    have e2 : readTapeBit (true :: false :: (frameP (List.replicate h false) ++ [false])) (p + 2) =
        readTapeBit (frameP (List.replicate h false) ++ [false]) p := by
      unfold readTapeBit; simp
    rw [e, e2, read_marks h p]
    by_cases hp : p < 2 * h
    · rw [if_pos hp, if_pos (by omega), show (p + 2) % 2 = p % 2 by omega]
    · rw [if_neg hp, if_neg (by omega)]

end NearCubicWires.WireExponent3_5.PrimT.S3
