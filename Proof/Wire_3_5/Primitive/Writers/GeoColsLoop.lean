import Proof.Wire_3_5.Primitive.Writers.GeoColsCw

/-! # PA (d): the columns writer, part 2 (the columns, block by block, then the unit columns)

P3:1212-1216 (star:partition): the left half's columns of `φ` are, block by block, the code's basis vectors at the
data positions (zeros outside the block), then the unit vectors of the unblocked coordinates. The loops here emit
them in `GeoColsV.colsField_emit`'s order:

* `colM` / **`colM_spec`**: one block column `blkCol pre i post`;
* `iLoop` (over `i < b`, skipping the parity positions by the power tracker) / **`iLoop_run`**;
* `blkBody` / **`blkBody_spec`** and `blkLoop` / **`blkLoop_run`** (over the `r/2` blocks);
* `uLoop` / **`uLoop_run`** (the unit columns `unitCol (A+u) (width−A−u−1)`).

Paper quantity of the main types: the columns of `φ` (P3:1212-1216). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GeoColsLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront NearCubicWires.WireExponent3_5.PrimAsm.GeoNums
open NearCubicWires.WireExponent3_5.PrimAsm.GeoColsV NearCubicWires.WireExponent3_5.PrimAsm.GeoColsCw

variable (cap : ℕ)

/-! ## Words and lengths -/

theorem appO (σ : WState GS GR) (u : List Bool) :
    (appendO σ gOUT rOP u).st gOUT = σ.st gOUT ++ u ∧ (appendO σ gOUT rOP u).sh gOUT = σ.sh gOUT + u.length ∧
      (appendO σ gOUT rOP u).val rOP = σ.val rOP + u.length ∧
      (∀ s, s ≠ gOUT → (appendO σ gOUT rOP u).st s = σ.st s) ∧
      ∀ r, r ≠ rOP → (appendO σ gOUT rOP u).val r = σ.val r :=
  ⟨by simp, by simp, by simp, fun s hs => by simp [Function.update_of_ne hs],
    fun r hr => by simp [Function.update_of_ne hr]⟩

theorem reps_e4 (k : ℕ) : reps k (e4 false) = (List.replicate k false).flatMap e4 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [reps_succ, ih, List.replicate_succ', List.flatMap_append]; simp

theorem e4_rep_length (k : ℕ) : ((List.replicate k false).flatMap e4).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ', List.flatMap_append, List.length_append, ih]; simp [e4]; ring

theorem e4_range_length (b : ℕ) (g : ℕ → Bool) : ((List.range b).flatMap fun q => e4 (g q)).length = 4 * b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [e4]; ring

theorem blkCol_length (P : StarParams) (pre i post : ℕ) :
    (blkCol P pre i post).length = 4 * (pre + P.b + post) + 2 := by
  unfold blkCol
  simp only [List.length_append, e4_rep_length, e4_range_length]
  simp; ring

theorem unitCol_length (pre post : ℕ) : (unitCol pre post).length = 4 * (pre + 1 + post) + 2 := by
  unfold unitCol
  simp only [List.length_append, e4_rep_length]
  simp [e4]; ring

/-! ## One block column -/

/-- **One block column**: `pre` zeros, the codeword of data position `rI1 − 1`, `post` zeros, the end `[1,0]`. -/
def colM : WM GS GR :=
  .seq (repRegW gOUT rOP rPre rK rT (e4 false)) (.seq cwM (.seq (repRegW gOUT rOP rPost rK rT (e4 false))
    (emitW gOUT rOP [true, false])))

/-- The block column's cost bound. -/
def colCost (pre post b : ℕ) : ℕ := 60 * (pre + post) + cwCost b + 100

theorem colM_spec (P : StarParams) (i pre post : ℕ) (hi : i < P.b) (hpar : PrimT.C4Geo.isPar P i = false)
    (σ : WState GS GR) (hI : σ.val rI1 = i + 1) (hB : σ.val rB = P.b) (hPre : σ.val rPre = pre)
    (hPost : σ.val rPost = post) (z1 : σ.val rRem = 0) (z2 : σ.val rCi = 0) (z3 : σ.val rPwq = 0)
    (z4 : σ.val rDq = 0) (z5 : σ.val rHit = 0) (z6 : σ.val rRb = 0) (z7 : σ.val rQ = 0) (z8 : σ.val rT2 = 0)
    (z9 : σ.val rK3 = 0) (zK : σ.val rK = 0) (zT : σ.val rT = 0) (ho : σ.sh gOUT = (σ.st gOUT).length)
    (hc : σ.val rOP + (4 * (pre + P.b + post) + 2) ≤ cap) (hc2 : 4 * (P.b + 1) ≤ cap) :
    ∃ τ c, WExec cap colM σ τ c ∧ τ.st gOUT = σ.st gOUT ++ blkCol P pre i post ∧
      τ.sh gOUT = (τ.st gOUT).length ∧ τ.val rOP = σ.val rOP + (4 * (pre + P.b + post) + 2) ∧
      (∀ s, s ≠ gOUT → τ.st s = σ.st s) ∧ (∀ r, r ≠ rOP → τ.val r = σ.val r) ∧ c ≤ colCost pre post P.b := by
  have hl : (e4 false).length = 4 := rfl
  have e1 := repRegW_spec cap gOUT rOP rPre rK rT (by decide) (by decide) (by decide) (by decide) (e4 false) σ zK zT ho
    (by rw [hPre]; omega) (by rw [hPre, hl]; omega)
  rw [hPre, hl] at e1
  obtain ⟨σ1, h1⟩ : ∃ x, x = appendO σ gOUT rOP (reps pre (e4 false)) := ⟨_, rfl⟩
  rw [← h1] at e1
  obtain ⟨a1, a2, a3, a4, a5⟩ := appO σ (reps pre (e4 false))
  rw [← h1] at a1 a2 a3 a4 a5
  have len1 : (reps pre (e4 false)).length = 4 * pre := by rw [repsLen, hl]; ring
  have ho1 : σ1.sh gOUT = (σ1.st gOUT).length := by rw [a2, a1, List.length_append, ho]
  obtain ⟨σ2, c2, e2, b1, b2, b3, b4, b5, bc⟩ := cwM_spec cap P i hi hpar σ1
    (by rw [a5 _ (by decide), hI]) (by rw [a5 _ (by decide), hB]) (by rw [a5 _ (by decide), z1])
    (by rw [a5 _ (by decide), z2]) (by rw [a5 _ (by decide), z3]) (by rw [a5 _ (by decide), z4])
    (by rw [a5 _ (by decide), z5]) (by rw [a5 _ (by decide), z6]) (by rw [a5 _ (by decide), z7])
    (by rw [a5 _ (by decide), z8]) (by rw [a5 _ (by decide), z9]) ho1 (by rw [a3, len1]; omega) hc2
  have e3 := repRegW_spec cap gOUT rOP rPost rK rT (by decide) (by decide) (by decide) (by decide) (e4 false) σ2
    (by rw [b5 _ (by decide), a5 _ (by decide), zK]) (by rw [b5 _ (by decide), a5 _ (by decide), zT]) b2
    (by rw [b5 rPost (by decide), a5 rPost (by decide), hPost]; omega)
    (by rw [b5 rPost (by decide), a5 rPost (by decide), hPost, b3, a3, len1, hl]; omega)
  rw [b5 rPost (by decide), a5 rPost (by decide), hPost, hl] at e3
  obtain ⟨σ3, h3⟩ : ∃ x, x = appendO σ2 gOUT rOP (reps post (e4 false)) := ⟨_, rfl⟩
  rw [← h3] at e3
  obtain ⟨d1, d2, d3, d4, d5⟩ := appO σ2 (reps post (e4 false))
  rw [← h3] at d1 d2 d3 d4 d5
  have len3 : (reps post (e4 false)).length = 4 * post := by rw [repsLen, hl]; ring
  have ho3 : σ3.sh gOUT = (σ3.st gOUT).length := by rw [d2, d1, List.length_append, b2]
  have e4' := emitW_spec cap gOUT rOP [true, false] σ3 ho3 (by rw [d3, b3, a3, len1, len3]; simp; omega)
  obtain ⟨f1, f2, f3, f4, f5⟩ := appO σ3 [true, false]
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4')), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f1, d1, b1, a1, reps_e4, reps_e4]
    unfold blkCol
    simp only [List.append_assoc]
  · rw [f2, f1, List.length_append, ho3]
  · rw [f3, d3, b3, a3, len1, len3]; simp; ring
  · intro s hs; rw [f4 s hs, d4 s hs, b4 s hs, a4 s hs]
  · intro r hr; rw [f5 r hr, d5 r hr, b5 r hr, a5 r hr]
  · unfold colCost; simp only [List.length_cons, List.length_nil]; omega

/-! ## The data positions of one block -/

/-- One position `i` of a block: `rI1 := i+1`; a data position emits its column, a parity position steps the
power tracker (`dist := pw − 1`, `pw := 2pw`). -/
def iStep : WM GS GR := .seq (.inc rI1) (.ifr rDist (.seq (.dec rDist) colM) (dblW rPw rDist))

/-- The positions of a block. -/
def iLoop : WM GS GR := .whr rK2 (.seq (.dec rK2) iStep)

/-- A block's columns after the first `k` positions. -/
def blkWords (P : StarParams) (pre post k : ℕ) : List Bool :=
  (List.range k).flatMap (fun i => if PrimT.C4Geo.isPar P i then [] else blkCol P pre i post)

theorem blkWords_succ (P : StarParams) (pre post k : ℕ) :
    blkWords P pre post (k + 1) =
      blkWords P pre post k ++ (if PrimT.C4Geo.isPar P k then [] else blkCol P pre k post) := by
  unfold blkWords; rw [List.range_succ, List.flatMap_append]; simp

theorem blkWords_length_le (P : StarParams) (pre post k : ℕ) :
    (blkWords P pre post k).length ≤ k * (4 * (pre + P.b + post) + 2) := by
  induction k with
  | zero => simp [blkWords]
  | succ k ih =>
    rw [blkWords_succ, List.length_append, Nat.succ_mul]
    split_ifs
    · simp; omega
    · rw [blkCol_length]; omega

/-- The block loop's invariant after `k` positions. -/
def iInv (P : StarParams) (pre post : ℕ) (σ : WState GS GR) (k : ℕ) (τ : WState GS GR) : Prop :=
  τ.st gOUT = σ.st gOUT ++ blkWords P pre post k ∧ τ.sh gOUT = (τ.st gOUT).length ∧
  τ.val rOP = σ.val rOP + (blkWords P pre post k).length ∧ (∀ s, s ≠ gOUT → τ.st s = σ.st s) ∧
  (∀ r, r ≠ rI1 → r ≠ rDist → r ≠ rPw → r ≠ rOP → r ≠ rK2 → τ.val r = σ.val r) ∧ τ.val rI1 = k ∧
  ∃ t, τ.val rPw = 2 ^ t ∧ k + 1 ≤ 2 ^ t ∧ 2 ^ t < 2 * (k + 1) ∧ τ.val rDist = 2 ^ t - (k + 1)

/-- One position's cost bound. -/
def iCost (pre post b : ℕ) : ℕ := colCost pre post b + 100 * b + 100

theorem iLoop_step (P : StarParams) (pre post : ℕ) (σ : WState GS GR) (hB : σ.val rB = P.b)
    (hPre : σ.val rPre = pre) (hPost : σ.val rPost = post) (z1 : σ.val rRem = 0) (z2 : σ.val rCi = 0)
    (z3 : σ.val rPwq = 0) (z4 : σ.val rDq = 0) (z5 : σ.val rHit = 0) (z6 : σ.val rRb = 0) (z7 : σ.val rQ = 0)
    (z8 : σ.val rT2 = 0) (z9 : σ.val rK3 = 0) (zK : σ.val rK = 0) (zT : σ.val rT = 0)
    (hc : σ.val rOP + P.b * (4 * (pre + P.b + post) + 2) ≤ cap) (hc2 : 4 * (P.b + 1) ≤ cap) :
    ∀ k < P.b, ∀ τ, iInv P pre post σ k τ → τ.val rK2 = P.b - k →
      ∃ ρ, WExec cap iStep (τ.setv rK2 (P.b - k - 1)) ρ (iCost pre post P.b) ∧ iInv P pre post σ (k + 1) ρ ∧
        ρ.val rK2 = P.b - k - 1 := by
  intro k hk τ hInv _
  obtain ⟨iS, iSh, iOP, iO, iF, iI, t, iPw, iLo, iHi, iDi⟩ := hInv
  obtain ⟨τ', hτ'⟩ : ∃ x, x = τ.setv rK2 (P.b - k - 1) := ⟨_, rfl⟩
  have kv : ∀ r, r ≠ rK2 → τ'.val r = τ.val r := fun r h => by rw [hτ']; simp [Function.update_of_ne h]
  have sv : τ'.st = τ.st := by rw [hτ']; rfl
  have shv : τ'.sh = τ.sh := by rw [hτ']; rfl
  have fv : ∀ r, r ≠ rI1 → r ≠ rDist → r ≠ rPw → r ≠ rOP → r ≠ rK2 → τ'.val r = σ.val r :=
    fun r a b c d e => by rw [kv r e, iF r a b c d e]
  have hbs := b_succ_pow P
  have e1 := WExec.inc (cap := cap) rI1 τ' (by rw [kv _ (by decide), iI]; omega)
  obtain ⟨σ1, h1⟩ : ∃ x, x = τ'.setv rI1 (τ'.val rI1 + 1) := ⟨_, rfl⟩
  rw [← h1] at e1
  have k1 : ∀ r, r ≠ rI1 → σ1.val r = τ'.val r := fun r h => by rw [h1]; simp [Function.update_of_ne h]
  have v1 : σ1.val rI1 = k + 1 := by rw [h1]; simp [kv _ (show rI1 ≠ rK2 by decide), iI]
  have s1 : σ1.st = τ.st := by rw [h1]; exact sv
  have sh1 : σ1.sh = τ.sh := by rw [h1]; exact shv
  have hL := blkWords_length_le P pre post k
  have hLk : (k + 1) * (4 * (pre + P.b + post) + 2) ≤ P.b * (4 * (pre + P.b + post) + 2) :=
    Nat.mul_le_mul_right _ hk
  rw [Nat.succ_mul] at hLk
  have hD1 : σ1.val rDist = 2 ^ t - (k + 1) := by rw [k1 _ (by decide), kv _ (by decide), iDi]
  have hP1 : σ1.val rPw = 2 ^ t := by rw [k1 _ (by decide), kv _ (by decide), iPw]
  by_cases hd : 2 ^ t - (k + 1) = 0
  · -- a parity position
    have hkp : PrimT.C4Geo.isPar P k = true := (isPar_iff P k hk).2 ⟨t, by omega⟩
    have e2 := dblW_spec cap rPw rDist (by decide) (by decide) (by decide) σ1 (by rw [hD1, hd])
      (by rw [k1 _ (by decide), fv _ (by decide) (by decide) (by decide) (by decide) (by decide), z8])
      (by rw [hP1]; omega)
    obtain ⟨σ2, h2⟩ : ∃ x, x = (σ1.setv rDist (σ1.val rPw - 1)).setv rPw (2 * σ1.val rPw) := ⟨_, rfl⟩
    rw [← h2] at e2
    have k2 : ∀ r, r ≠ rDist → r ≠ rPw → σ2.val r = σ1.val r := fun r a b => by
      rw [h2]; simp [Function.update_of_ne a, Function.update_of_ne b]
    have s2 : σ2.st = τ.st := by rw [h2, ← s1]; rfl
    have sh2 : σ2.sh = τ.sh := by rw [h2, ← sh1]; rfl
    have e := WExec.seq e1 (WExec.ifrF (P := .seq (.dec rDist) colM) (by rw [hD1, hd]) e2)
    rw [hτ'] at e
    refine ⟨σ2, WExec.mono e ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, t + 1, ?_, ?_, ?_, ?_⟩, ?_⟩
    · unfold iCost colCost; rw [hP1]; omega
    · rw [s2, iS, blkWords_succ, if_pos hkp, List.append_nil]
    · rw [s2, sh2]; exact iSh
    · rw [k2 _ (by decide) (by decide), k1 _ (by decide), kv _ (by decide), iOP, blkWords_succ, if_pos hkp,
        List.append_nil]
    · intro s hs; rw [s2, iO s hs]
    · intro r a1 a2 a3 a4 a5
      rw [k2 r a2 a3, k1 r a1, fv r a1 a2 a3 a4 a5]
    · rw [k2 _ (by decide) (by decide), v1]
    · rw [h2]; simp [hP1, Nat.pow_succ]; ring
    · rw [Nat.pow_succ]; omega
    · rw [Nat.pow_succ]; omega
    · rw [h2]; simp [Function.update_apply, Fin.ext_iff, GR, hP1, Nat.pow_succ]; omega
    · rw [k2 _ (by decide) (by decide), k1 _ (by decide), hτ']; simp
  · -- a data position
    have hkp : PrimT.C4Geo.isPar P k = false := by
      cases h : PrimT.C4Geo.isPar P k
      · rfl
      · obtain ⟨t', ht'⟩ := (isPar_iff P k hk).1 h
        exact absurd ht' (not_pow_of_between k t (by omega) iHi t')
    have e2 := WExec.dec (cap := cap) rDist σ1 (by rw [hD1]; omega)
    obtain ⟨σ2, h2⟩ : ∃ x, x = σ1.setv rDist (σ1.val rDist - 1) := ⟨_, rfl⟩
    rw [← h2] at e2
    have k2 : ∀ r, r ≠ rDist → σ2.val r = σ1.val r := fun r a => by rw [h2]; simp [Function.update_of_ne a]
    have s2 : σ2.st = τ.st := by rw [h2, ← s1]; rfl
    have sh2 : σ2.sh = τ.sh := by rw [h2, ← sh1]; rfl
    have g : ∀ r, r ≠ rI1 → r ≠ rDist → r ≠ rPw → r ≠ rOP → r ≠ rK2 → σ2.val r = σ.val r :=
      fun r a b c d e => by rw [k2 r b, k1 r a, fv r a b c d e]
    have o2 : σ2.val rOP = σ.val rOP + (blkWords P pre post k).length := by
      rw [k2 _ (by decide), k1 _ (by decide), kv _ (by decide), iOP]
    obtain ⟨ρ, c3, e3, r1, r2, r3, r4, r5, rc⟩ := colM_spec cap P k pre post hk hkp σ2
      (by rw [k2 _ (by decide), v1]) (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hB])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hPre])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hPost])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z1])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z2])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z3])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z4])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z5])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z6])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z7])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z8])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), z9])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), zK])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), zT])
      (by rw [s2, sh2]; exact iSh) (by rw [o2]; omega) hc2
    have e := WExec.seq e1 (WExec.ifrT (Q := dblW rPw rDist) (by rw [hD1]; exact hd) (WExec.seq e2 e3))
    rw [hτ'] at e
    refine ⟨ρ, WExec.mono e ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, t, ?_, ?_, ?_, ?_⟩, ?_⟩
    · unfold iCost; omega
    · rw [r1, s2, iS, blkWords_succ, if_neg (by rw [hkp]; decide), List.append_assoc]
    · exact r2
    · rw [r3, o2, blkWords_succ, if_neg (by rw [hkp]; decide), List.length_append, blkCol_length]; ring
    · intro s hs; rw [r4 s hs, s2, iO s hs]
    · intro r a1 a2 a3 a4 a5
      rw [r5 r a4, g r a1 a2 a3 a4 a5]
    · rw [r5 _ (by decide), k2 _ (by decide), v1]
    · rw [r5 _ (by decide), k2 _ (by decide), hP1]
    · omega
    · omega
    · rw [r5 _ (by decide), h2]; simp [hD1]; omega
    · rw [r5 _ (by decide), k2 _ (by decide), k1 _ (by decide), hτ']; simp

/-! ## One block -/

/-- `rPost −= rB` (through `rT2`, `rZ`). -/
def PB : Fin 4 ↪ Fin GR := ⟨![47, 42, 44, 63], by decide⟩

/-- **One block**: the power tracker at `1`, the positions loop, then `pre += b`, `post −= b`. -/
def blkBody : WM GS GR :=
  .seq (.inc rPw) (.seq (FinalPass.Hash4.wcopyR rB rK2 rT2) (.seq iLoop (.seq (WM.clear rI1)
    (.seq (WM.clear rPw) (.seq (addTo rB rPre rT2) (UnaryArith.subW PB))))))

/-- One block's cost bound. -/
def bCost (pre post b : ℕ) : ℕ := b * (iCost pre post b + 4) + 80 * b + 100

theorem bCost_mono (pre post pre' post' b : ℕ) (h1 : pre ≤ pre') (h2 : post ≤ post') :
    bCost pre post b ≤ bCost pre' post' b := by
  unfold bCost iCost colCost
  have : 60 * (pre + post) + cwCost b + 100 + 100 * b + 100 + 4 ≤
      60 * (pre' + post') + cwCost b + 100 + 100 * b + 100 + 4 := by omega
  have := Nat.mul_le_mul_left b this
  omega

theorem blkBody_spec (P : StarParams) (pre post : ℕ) (σ : WState GS GR) (hB : σ.val rB = P.b)
    (hPre : σ.val rPre = pre) (hPost : σ.val rPost = post) (z1 : σ.val rRem = 0) (z2 : σ.val rCi = 0)
    (z3 : σ.val rPwq = 0) (z4 : σ.val rDq = 0) (z5 : σ.val rHit = 0) (z6 : σ.val rRb = 0) (z7 : σ.val rQ = 0)
    (z8 : σ.val rT2 = 0) (z9 : σ.val rK3 = 0) (zK : σ.val rK = 0) (zT : σ.val rT = 0) (zPw : σ.val rPw = 0)
    (zDi : σ.val rDist = 0) (zI : σ.val rI1 = 0) (zK2 : σ.val rK2 = 0) (zZ : σ.val rZ = 0)
    (ho : σ.sh gOUT = (σ.st gOUT).length)
    (hc : σ.val rOP + P.b * (4 * (pre + P.b + post) + 2) ≤ cap) (hc2 : 4 * (P.b + 1) ≤ cap)
    (hc3 : pre + P.b ≤ cap) (hc4 : post ≤ cap) :
    ∃ τ c, WExec cap blkBody σ τ c ∧ τ.st gOUT = σ.st gOUT ++ blkWords P pre post P.b ∧
      τ.sh gOUT = (τ.st gOUT).length ∧ τ.val rOP = σ.val rOP + (blkWords P pre post P.b).length ∧
      (∀ s, s ≠ gOUT → τ.st s = σ.st s) ∧ τ.val rPre = pre + P.b ∧ τ.val rPost = post - P.b ∧
      (∀ r, r ≠ rPre → r ≠ rPost → r ≠ rOP → τ.val r = σ.val r) ∧ c ≤ bCost pre post P.b := by
  have hbs := b_succ_pow P
  have e1 := WExec.inc (cap := cap) rPw σ (by rw [zPw]; omega)
  obtain ⟨σ1, h1⟩ : ∃ x, x = σ.setv rPw (σ.val rPw + 1) := ⟨_, rfl⟩
  rw [← h1] at e1
  have k1 : ∀ r, r ≠ rPw → σ1.val r = σ.val r := fun r h => by rw [h1]; simp [Function.update_of_ne h]
  have e2 := FinalPass.Hash4.wcopyR_spec cap rB rK2 rT2 (by decide) (by decide) (by decide) σ1
    (by rw [k1 _ (by decide), zK2]) (by rw [k1 _ (by decide), z8]) (by rw [k1 _ (by decide), hB]; omega)
  obtain ⟨σ2, h2⟩ : ∃ x, x = σ1.setv rK2 (σ1.val rB) := ⟨_, rfl⟩
  rw [← h2] at e2
  have k2 : ∀ r, r ≠ rK2 → σ2.val r = σ1.val r := fun r h => by rw [h2]; simp [Function.update_of_ne h]
  have s2 : σ2.st = σ.st := by rw [h2, h1]; rfl
  have sh2 : σ2.sh = σ.sh := by rw [h2, h1]; rfl
  have inv0 : iInv P pre post σ 0 σ2 := by
    refine ⟨by rw [s2]; simp [blkWords], by rw [s2, sh2]; exact ho, ?_, fun s _ => by rw [s2], ?_, ?_, 0, ?_,
      by simp, by simp, ?_⟩
    · rw [k2 _ (by decide), k1 _ (by decide)]; simp [blkWords]
    · intro r a1 a2 a3 a4 a5; rw [k2 r a5, k1 r a3]
    · rw [k2 _ (by decide), k1 _ (by decide), zI]
    · rw [k2 _ (by decide), h1]; simp [zPw]
    · rw [k2 _ (by decide), k1 _ (by decide), zDi]; rfl
  have hK2 : σ2.val rK2 = P.b := by
    rw [h2]; simp only [WState.setv_val, Function.update_self]; rw [k1 _ (by decide), hB]
  obtain ⟨τ, eL, invF, hKF⟩ := UnionMachine.Round.wloopE cap rK2 iStep (iCost pre post P.b) P.b
    (iInv P pre post σ) (by omega) (iLoop_step cap P pre post σ hB hPre hPost z1 z2 z3 z4 z5 z6 z7 z8 z9 zK zT hc hc2)
    σ2 inv0 hK2
  obtain ⟨iS, iSh, iOP, iO, iF, iI, t, iPw, iLo, iHi, iDi⟩ := invF
  have ht := t_final P t iLo iHi
  have e4' := wclear_spec cap rI1 P.b τ iI (by rw [iI]; omega)
  obtain ⟨τ1, g1⟩ : ∃ x, x = τ.setv rI1 0 := ⟨_, rfl⟩
  rw [← g1] at e4'
  have j1 : ∀ r, r ≠ rI1 → τ1.val r = τ.val r := fun r h => by rw [g1]; simp [Function.update_of_ne h]
  have e5 := wclear_spec cap rPw (P.b + 1) τ1 (by rw [j1 _ (by decide), iPw, ht]) (by rw [j1 _ (by decide), iPw, ht]; omega)
  obtain ⟨τ2, g2⟩ : ∃ x, x = τ1.setv rPw 0 := ⟨_, rfl⟩
  rw [← g2] at e5
  have j2 : ∀ r, r ≠ rPw → τ2.val r = τ1.val r := fun r h => by rw [g2]; simp [Function.update_of_ne h]
  have fr : ∀ r, r ≠ rI1 → r ≠ rDist → r ≠ rPw → r ≠ rOP → r ≠ rK2 → τ2.val r = σ.val r :=
    fun r a b c d e => by rw [j2 r c, j1 r a, iF r a b c d e]
  have e6 := addTo_spec cap rB rPre rT2 (by decide) (by decide) (by decide) τ2
    (by rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide), z8])
    (by rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide), hB]; omega)
    (by rw [fr rPre (by decide) (by decide) (by decide) (by decide) (by decide),
      fr rB (by decide) (by decide) (by decide) (by decide) (by decide), hPre, hB]; omega)
  obtain ⟨τ3, g3⟩ : ∃ x, x = τ2.setv rPre (τ2.val rPre + τ2.val rB) := ⟨_, rfl⟩
  rw [← g3] at e6
  have j3 : ∀ r, r ≠ rPre → τ3.val r = τ2.val r := fun r h => by rw [g3]; simp [Function.update_of_ne h]
  have p0 : PB 0 = rPost := rfl
  have p1 : PB 1 = rB := rfl
  have p2 : PB 2 = rT2 := rfl
  have p3 : PB 3 = rZ := rfl
  have e7 := UnaryArith.subW_spec cap PB τ3
    (by rw [p2, j3 _ (by decide), fr _ (by decide) (by decide) (by decide) (by decide) (by decide), z8])
    (by rw [p3, j3 _ (by decide), fr _ (by decide) (by decide) (by decide) (by decide) (by decide), zZ])
    (by rw [p0, j3 _ (by decide), fr _ (by decide) (by decide) (by decide) (by decide) (by decide), hPost]; omega)
    (by rw [p1, j3 _ (by decide), fr _ (by decide) (by decide) (by decide) (by decide) (by decide), hB]; omega)
  rw [p0, p1] at e7
  obtain ⟨τ4, g4⟩ : ∃ x, x = τ3.setv rPost (τ3.val rPost - τ3.val rB) := ⟨_, rfl⟩
  rw [← g4] at e7
  have j4 : ∀ r, r ≠ rPost → τ4.val r = τ3.val r := fun r h => by rw [g4]; simp [Function.update_of_ne h]
  have st4 : τ4.st = τ.st := by rw [g4, g3, g2, g1]; rfl
  have sh4 : τ4.sh = τ.sh := by rw [g4, g3, g2, g1]; rfl
  have vB : τ3.val rB = P.b := by
    rw [j3 _ (by decide), fr _ (by decide) (by decide) (by decide) (by decide) (by decide), hB]
  refine ⟨τ4, _, WExec.seq e1 (WExec.seq e2 (WExec.seq eL (WExec.seq e4' (WExec.seq e5 (WExec.seq e6 e7))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [st4, iS]
  · rw [st4, sh4]; exact iSh
  · rw [j4 _ (by decide), j3 _ (by decide), j2 _ (by decide), j1 _ (by decide), iOP]
  · intro s hs; rw [st4, iO s hs]
  · rw [j4 _ (by decide), g3]
    simp only [WState.setv_val, Function.update_self]
    rw [fr rPre (by decide) (by decide) (by decide) (by decide) (by decide),
      fr rB (by decide) (by decide) (by decide) (by decide) (by decide), hPre, hB]
  · rw [g4]
    simp only [WState.setv_val, Function.update_self]
    rw [vB, j3 _ (by decide), fr rPost (by decide) (by decide) (by decide) (by decide) (by decide), hPost]
  · intro r a1 a2 a3
    rw [j4 r a2, j3 r a1]
    by_cases hI' : r = rI1
    · subst hI'; rw [g2, g1]; simp [Function.update_apply, Fin.ext_iff, GR, zI]
    by_cases hP' : r = rPw
    · subst hP'; rw [g2]; simp [zPw]
    by_cases hD' : r = rDist
    · subst hD'; rw [j2 _ (by decide), j1 _ (by decide), iDi, ht, zDi]; omega
    by_cases hK' : r = rK2
    · subst hK'; rw [j2 _ (by decide), j1 _ (by decide), hKF, zK2]
    exact fr r hI' hD' hP' a3 hK'
  · unfold bCost
    have v2 : τ2.val rB = P.b := by rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide), hB]
    have v2' : σ1.val rB = P.b := by rw [k1 _ (by decide), hB]
    rw [v2, v2', vB]
    omega

/-! ## The blocks -/

/-- **The blocks loop.** -/
def blkLoop : WM GS GR := .whr rK1 (.seq (.dec rK1) blkBody)

/-- The first `k` blocks' columns (`Wd` the dense width). -/
def blocksWord (P : StarParams) (Wd k : ℕ) : List Bool :=
  (List.range k).flatMap (fun blk => blkWords P (blk * P.b) (Wd - blk * P.b - P.b) P.b)

theorem blocksWord_succ (P : StarParams) (Wd k : ℕ) :
    blocksWord P Wd (k + 1) = blocksWord P Wd k ++ blkWords P (k * P.b) (Wd - k * P.b - P.b) P.b := by
  unfold blocksWord; rw [List.range_succ, List.flatMap_append]; simp

theorem blkWords_block_le (P : StarParams) (Wd k : ℕ) (hk : k * P.b + P.b ≤ Wd) :
    (blkWords P (k * P.b) (Wd - k * P.b - P.b) P.b).length ≤ P.b * (4 * Wd + 2) := by
  have h := blkWords_length_le P (k * P.b) (Wd - k * P.b - P.b) P.b
  rw [show k * P.b + P.b + (Wd - k * P.b - P.b) = Wd by omega] at h
  exact h

theorem blocksWord_length_le (P : StarParams) (Wd : ℕ) :
    ∀ k, k * P.b ≤ Wd → (blocksWord P Wd k).length ≤ k * (P.b * (4 * Wd + 2)) := by
  intro k
  induction k with
  | zero => intro _; simp [blocksWord]
  | succ k ih =>
    intro hk
    rw [Nat.succ_mul] at hk
    rw [blocksWord_succ, List.length_append, Nat.succ_mul]
    have := ih (by omega)
    have := blkWords_block_le P Wd k hk
    omega

/-- The blocks loop's invariant after `k` blocks. -/
def bInv (P : StarParams) (Wd : ℕ) (σ : WState GS GR) (k : ℕ) (τ : WState GS GR) : Prop :=
  τ.st gOUT = σ.st gOUT ++ blocksWord P Wd k ∧ τ.sh gOUT = (τ.st gOUT).length ∧
  τ.val rOP = σ.val rOP + (blocksWord P Wd k).length ∧ (∀ s, s ≠ gOUT → τ.st s = σ.st s) ∧
  (∀ r, r ≠ rPre → r ≠ rPost → r ≠ rOP → r ≠ rK1 → τ.val r = σ.val r) ∧
  τ.val rPre = k * P.b ∧ τ.val rPost = Wd - k * P.b - P.b

theorem blkLoop_step (P : StarParams) (Wd nb : ℕ) (hnb : nb * P.b ≤ Wd) (σ : WState GS GR) (hB : σ.val rB = P.b)
    (z1 : σ.val rRem = 0) (z2 : σ.val rCi = 0)
    (z3 : σ.val rPwq = 0) (z4 : σ.val rDq = 0) (z5 : σ.val rHit = 0) (z6 : σ.val rRb = 0) (z7 : σ.val rQ = 0)
    (z8 : σ.val rT2 = 0) (z9 : σ.val rK3 = 0) (zK : σ.val rK = 0) (zT : σ.val rT = 0) (zPw : σ.val rPw = 0)
    (zDi : σ.val rDist = 0) (zI : σ.val rI1 = 0) (zK2 : σ.val rK2 = 0) (zZ : σ.val rZ = 0)
    (hc : σ.val rOP + nb * (P.b * (4 * Wd + 2)) ≤ cap) (hc2 : 4 * (P.b + 1) ≤ cap) (hc3 : Wd ≤ cap) :
    ∀ k < nb, ∀ τ, bInv P Wd σ k τ → τ.val rK1 = nb - k →
      ∃ ρ, WExec cap blkBody (τ.setv rK1 (nb - k - 1)) ρ (bCost Wd Wd P.b) ∧ bInv P Wd σ (k + 1) ρ ∧
        ρ.val rK1 = nb - k - 1 := by
  intro k hk τ hInv _
  obtain ⟨iS, iSh, iOP, iO, iF, iPre, iPost⟩ := hInv
  have hk1 : (k + 1) * P.b ≤ nb * P.b := Nat.mul_le_mul_right _ hk
  rw [Nat.succ_mul] at hk1
  obtain ⟨τ', hτ'⟩ : ∃ x, x = τ.setv rK1 (nb - k - 1) := ⟨_, rfl⟩
  have kv : ∀ r, r ≠ rK1 → τ'.val r = τ.val r := fun r h => by rw [hτ']; simp [Function.update_of_ne h]
  have sv : τ'.st = τ.st := by rw [hτ']; rfl
  have shv : τ'.sh = τ.sh := by rw [hτ']; rfl
  have fv : ∀ r, r ≠ rPre → r ≠ rPost → r ≠ rOP → r ≠ rK1 → τ'.val r = σ.val r :=
    fun r a b c d => by rw [kv r d, iF r a b c d]
  have hL := blocksWord_length_le P Wd k (by omega)
  have hkL : k * (P.b * (4 * Wd + 2)) + P.b * (4 * Wd + 2) ≤ nb * (P.b * (4 * Wd + 2)) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  have hsum : k * P.b + P.b + (Wd - k * P.b - P.b) = Wd := by omega
  obtain ⟨ρ, c, e, r1, r2, r3, r4, r5, r6, r7, rc⟩ := blkBody_spec cap P (k * P.b) (Wd - k * P.b - P.b) τ'
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), hB])
    (by rw [kv _ (by decide), iPre]) (by rw [kv _ (by decide), iPost])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z1])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z2])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z3])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z4])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z5])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z6])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z7])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z8])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), z9])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zK])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zT])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zPw])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zDi])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zI])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zK2])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zZ])
    (by rw [sv, shv]; exact iSh) (by rw [kv _ (by decide), iOP, hsum]; omega) hc2 (by omega) (by omega)
  rw [hτ'] at e
  refine ⟨ρ, WExec.mono e (le_trans rc (bCost_mono _ _ _ _ _ (by omega) (by omega))), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [r1, sv, iS, blocksWord_succ, List.append_assoc]
  · exact r2
  · rw [r3, kv _ (by decide), iOP, blocksWord_succ, List.length_append]; ring
  · intro s hs; rw [r4 s hs, sv, iO s hs]
  · intro r a1 a2 a3 a4; rw [r7 r a1 a2 a3, fv r a1 a2 a3 a4]
  · rw [r5, Nat.succ_mul]
  · rw [r6, Nat.succ_mul]; omega
  · rw [r7 _ (by decide) (by decide) (by decide), hτ']; simp

/-! ## The unit columns -/

/-- One unit column: `pre` zeros, a one, `post` zeros, the end; then `pre += 1`, `post −= 1`. -/
def uStep : WM GS GR :=
  .seq (repRegW gOUT rOP rPU rK rT (e4 false)) (.seq (emB true) (.seq (repRegW gOUT rOP rQU rK rT (e4 false))
    (.seq (emitW gOUT rOP [true, false]) (.seq (.inc rPU) (.dec rQU)))))

/-- **The unit columns loop.** -/
def uLoop : WM GS GR := .whr rU (.seq (.dec rU) uStep)

/-- The first `k` unit columns (`A` the blocks' coordinates, `Wd` the dense width). -/
def unitsWord (A Wd k : ℕ) : List Bool :=
  (List.range k).flatMap (fun u => unitCol (A + u) (Wd - (A + u) - 1))

theorem unitsWord_succ (A Wd k : ℕ) :
    unitsWord A Wd (k + 1) = unitsWord A Wd k ++ unitCol (A + k) (Wd - (A + k) - 1) := by
  unfold unitsWord; rw [List.range_succ, List.flatMap_append]; simp

theorem unitsWord_length (A Wd : ℕ) : ∀ k, A + k ≤ Wd → (unitsWord A Wd k).length = k * (4 * Wd + 2) := by
  intro k
  induction k with
  | zero => intro _; simp [unitsWord]
  | succ k ih =>
    intro hk
    rw [unitsWord_succ, List.length_append, ih (by omega), unitCol_length, Nat.succ_mul,
      show A + k + 1 + (Wd - (A + k) - 1) = Wd by omega]
    ring

/-- The unit loop's invariant after `k` columns. -/
def uInv (A Wd : ℕ) (σ : WState GS GR) (k : ℕ) (τ : WState GS GR) : Prop :=
  τ.st gOUT = σ.st gOUT ++ unitsWord A Wd k ∧ τ.sh gOUT = (τ.st gOUT).length ∧
  τ.val rOP = σ.val rOP + (unitsWord A Wd k).length ∧ (∀ s, s ≠ gOUT → τ.st s = σ.st s) ∧
  (∀ r, r ≠ rPU → r ≠ rQU → r ≠ rOP → r ≠ rU → τ.val r = σ.val r) ∧
  τ.val rPU = A + k ∧ τ.val rQU = Wd - A - 1 - k

/-- One unit column's cost bound. -/
def uCost (Wd : ℕ) : ℕ := 120 * Wd + 200

theorem uLoop_step (A Wd h : ℕ) (hAh : A + h ≤ Wd) (σ : WState GS GR) (zK : σ.val rK = 0) (zT : σ.val rT = 0)
    (hc : σ.val rOP + h * (4 * Wd + 2) ≤ cap) (hc3 : Wd + 1 ≤ cap) :
    ∀ k < h, ∀ τ, uInv A Wd σ k τ → τ.val rU = h - k →
      ∃ ρ, WExec cap uStep (τ.setv rU (h - k - 1)) ρ (uCost Wd) ∧ uInv A Wd σ (k + 1) ρ ∧ ρ.val rU = h - k - 1 := by
  intro k hk τ hInv _
  obtain ⟨iS, iSh, iOP, iO, iF, iPU, iQU⟩ := hInv
  have hl : (e4 false).length = 4 := rfl
  have hLen := unitsWord_length A Wd k (by omega)
  have hkL : k * (4 * Wd + 2) + (4 * Wd + 2) ≤ h * (4 * Wd + 2) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  obtain ⟨τ', hτ'⟩ : ∃ x, x = τ.setv rU (h - k - 1) := ⟨_, rfl⟩
  have kv : ∀ r, r ≠ rU → τ'.val r = τ.val r := fun r hr => by rw [hτ']; simp [Function.update_of_ne hr]
  have sv : τ'.st = τ.st := by rw [hτ']; rfl
  have shv : τ'.sh = τ.sh := by rw [hτ']; rfl
  have fv : ∀ r, r ≠ rPU → r ≠ rQU → r ≠ rOP → r ≠ rU → τ'.val r = σ.val r :=
    fun r a b c d => by rw [kv r d, iF r a b c d]
  have ho : τ'.sh gOUT = (τ'.st gOUT).length := by rw [sv, shv]; exact iSh
  have o0 : τ'.val rOP = σ.val rOP + k * (4 * Wd + 2) := by rw [kv _ (by decide), iOP, hLen]
  -- the zeros before
  have e1 := repRegW_spec cap gOUT rOP rPU rK rT (by decide) (by decide) (by decide) (by decide) (e4 false) τ'
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zK])
    (by rw [fv _ (by decide) (by decide) (by decide) (by decide), zT]) ho
    (by rw [kv _ (by decide), iPU]; omega) (by rw [kv rPU (by decide), iPU, o0, hl]; omega)
  rw [kv rPU (by decide), iPU, hl] at e1
  obtain ⟨σ1, h1⟩ : ∃ x, x = appendO τ' gOUT rOP (reps (A + k) (e4 false)) := ⟨_, rfl⟩
  rw [← h1] at e1
  obtain ⟨a1, a2, a3, a4, a5⟩ := appO τ' (reps (A + k) (e4 false))
  rw [← h1] at a1 a2 a3 a4 a5
  have len1 : (reps (A + k) (e4 false)).length = 4 * (A + k) := by rw [repsLen, hl]; ring
  have ho1 : σ1.sh gOUT = (σ1.st gOUT).length := by rw [a2, a1, List.length_append, ho]
  -- the one
  have e2 := emitW_spec cap gOUT rOP (e4 true) σ1 ho1 (by rw [a3, len1, o0]; simp [e4]; omega)
  obtain ⟨σ2, h2⟩ : ∃ x, x = appendO σ1 gOUT rOP (e4 true) := ⟨_, rfl⟩
  rw [← h2] at e2
  obtain ⟨b1, b2, b3, b4, b5⟩ := appO σ1 (e4 true)
  rw [← h2] at b1 b2 b3 b4 b5
  have ho2 : σ2.sh gOUT = (σ2.st gOUT).length := by rw [b2, b1, List.length_append, ho1]
  -- the zeros after
  have vQ : σ2.val rQU = Wd - A - 1 - k := by rw [b5 _ (by decide), a5 _ (by decide), kv _ (by decide), iQU]
  have e3 := repRegW_spec cap gOUT rOP rQU rK rT (by decide) (by decide) (by decide) (by decide) (e4 false) σ2
    (by rw [b5 _ (by decide), a5 _ (by decide), fv _ (by decide) (by decide) (by decide) (by decide), zK])
    (by rw [b5 _ (by decide), a5 _ (by decide), fv _ (by decide) (by decide) (by decide) (by decide), zT]) ho2
    (by rw [vQ]; omega) (by rw [vQ, b3, a3, len1, o0, hl]; simp [e4]; omega)
  rw [vQ, hl] at e3
  obtain ⟨σ3, h3⟩ : ∃ x, x = appendO σ2 gOUT rOP (reps (Wd - A - 1 - k) (e4 false)) := ⟨_, rfl⟩
  rw [← h3] at e3
  obtain ⟨d1, d2, d3, d4, d5⟩ := appO σ2 (reps (Wd - A - 1 - k) (e4 false))
  rw [← h3] at d1 d2 d3 d4 d5
  have len3 : (reps (Wd - A - 1 - k) (e4 false)).length = 4 * (Wd - A - 1 - k) := by rw [repsLen, hl]; ring
  have ho3 : σ3.sh gOUT = (σ3.st gOUT).length := by rw [d2, d1, List.length_append, ho2]
  -- the end
  have e4' := emitW_spec cap gOUT rOP [true, false] σ3 ho3
    (by rw [d3, b3, a3, len1, len3, o0]; simp [e4]; omega)
  obtain ⟨σ4, h4⟩ : ∃ x, x = appendO σ3 gOUT rOP [true, false] := ⟨_, rfl⟩
  rw [← h4] at e4'
  obtain ⟨f1, f2, f3, f4, f5⟩ := appO σ3 [true, false]
  rw [← h4] at f1 f2 f3 f4 f5
  have vP4 : σ4.val rPU = A + k := by
    rw [f5 _ (by decide), d5 _ (by decide), b5 _ (by decide), a5 _ (by decide), kv _ (by decide), iPU]
  have e5 := WExec.inc (cap := cap) rPU σ4 (by rw [vP4]; omega)
  obtain ⟨σ5, h5⟩ : ∃ x, x = σ4.setv rPU (σ4.val rPU + 1) := ⟨_, rfl⟩
  rw [← h5] at e5
  have k5 : ∀ r, r ≠ rPU → σ5.val r = σ4.val r := fun r hr => by rw [h5]; simp [Function.update_of_ne hr]
  have vQ5 : σ5.val rQU = Wd - A - 1 - k := by
    rw [k5 _ (by decide), f5 _ (by decide), d5 _ (by decide), vQ]
  have e6 := WExec.dec (cap := cap) rQU σ5 (by rw [vQ5]; omega)
  obtain ⟨σ6, h6⟩ : ∃ x, x = σ5.setv rQU (σ5.val rQU - 1) := ⟨_, rfl⟩
  rw [← h6] at e6
  have k6 : ∀ r, r ≠ rQU → σ6.val r = σ5.val r := fun r hr => by rw [h6]; simp [Function.update_of_ne hr]
  have s6 : σ6.st = σ4.st := by rw [h6, h5]; rfl
  have sh6 : σ6.sh = σ4.sh := by rw [h6, h5]; rfl
  have e := WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4' (WExec.seq e5 e6))))
  rw [hτ'] at e
  refine ⟨σ6, WExec.mono e ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · unfold uCost; simp only [List.length_cons, List.length_nil, e4]; omega
  · rw [s6, f1, d1, b1, a1, sv, iS, unitsWord_succ, reps_e4, reps_e4]
    unfold unitCol
    rw [show Wd - A - 1 - k = Wd - (A + k) - 1 by omega]
    simp only [List.append_assoc]
  · rw [s6, sh6, f2, f1, List.length_append, ho3]
  · have o6 : σ6.val rOP = σ.val rOP + k * (4 * Wd + 2) + 4 * (A + k) + 4 + 4 * (Wd - A - 1 - k) + 2 := by
      rw [k6 rOP (by decide), k5 rOP (by decide), f3, d3, b3, a3, len1, len3, o0]; rfl
    have u1 := unitsWord_length A Wd (k + 1) (by omega)
    rw [Nat.succ_mul] at u1
    rw [o6, u1]
    omega
  · intro s hs; rw [s6, f4 s hs, d4 s hs, b4 s hs, a4 s hs, sv, iO s hs]
  · intro r a1 a2 a3 a4
    rw [k6 r a2, k5 r a1, f5 r a3, d5 r a3, b5 r a3, a5 r a3, fv r a1 a2 a3 a4]
  · rw [k6 _ (by decide), h5]; simp [vP4]; ring
  · rw [h6]; simp [vQ5]; omega
  · rw [k6 _ (by decide), k5 _ (by decide), f5 _ (by decide), d5 _ (by decide), b5 _ (by decide), a5 _ (by decide),
      hτ']
    simp

end NearCubicWires.WireExponent3_5.PrimAsm.GeoColsLoop
