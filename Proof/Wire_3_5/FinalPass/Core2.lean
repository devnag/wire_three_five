import Proof.Wire_3_5.FinalPass.Core1

/-! # S5Core, part 2: the exact count `c = K·(|fpIn|+1)^D` on two reused tapes (P3:3170-3181)

The core half pads every register-length tape to exactly `K·N^D + 1` zeros (`N = |fpIn| + 1`, `K = L.Kc`,
`D = L.Dc`), against the reference `sent c`. The degree `D` is the bank's (fixed after the filter's error degree),
while the core's room is fixed per `l`, so the count runs on a FIXED layout: the powers alternate between two tapes,
each product written over the zeros the previous eraser left.

* `zpad`, `wbit_zpad`, **`WExec.zpadS`** (a word program run on zero-padded streams: the padding rides along);
* `zX`, `zY`, `zSt`, `zStep`, `chainZ`, **`chainZ_spec`** (after `k` products the current tape holds
  `sent (K·N^k)`, the other one zeros);
* `cntW`, **`cntW_spec`** (from the framed input: `T = sent N`, and `sent (K·N^D)` on `cX` or `cY` by the parity of
  `D`).

Paper quantity: none (the front's exact blank tapes, `FrontOut.blank`, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length lenT lenT_spec emitN emitN_spec rewSent
  rewSent_spec mulW mulW_spec mulCost eraseB eraseB_spec)
open NearCubicWires.WireExponent3_5.FinalPass.HashSeed (emit1 emit1_spec appW appW_appW appW_st appW_sh appW_val)

section Pad
variable {ns nr : ℕ} (cap : ℕ)

/-- Streams padded by zeros. -/
def zpad (σ : WState ns nr) (z : Fin (ns + 1) → ℕ) : WState ns nr :=
  ⟨σ.sh, fun i => ZeroPadding.pad (z i) (σ.st i), σ.val, σ.cell⟩

theorem wbit_zpad (σ : WState ns nr) (z : Fin (ns + 1) → ℕ) (i : Fin (ns + 1)) : wbit (zpad σ z) i = wbit σ i := by
  unfold wbit zpad; exact ZeroPadding.read_pad _ _ _

/-- **A word program on zero-padded streams**: the padding rides along. -/
theorem WExec.zpadS {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (z : Fin (ns + 1) → ℕ) :
    WExec cap P (zpad σ z) (zpad τ z) n := by
  induction h with
  | skip σ => exact WExec.skip _
  | inc r σ h => exact WExec.inc r (zpad σ z) h
  | dec r σ h => exact WExec.dec r (zpad σ z) h
  | fwd i σ => exact WExec.fwd i (zpad σ z)
  | bwd i σ => exact WExec.bwd i (zpad σ z)
  | wr i b σ =>
    refine WExec.cast cap (WExec.wr i b (zpad σ z)) ?_ le_rfl
    refine WState.eq ?_ ?_ ?_ ?_
    · rfl
    rotate_left
    · rfl
    · rfl
    funext j
    by_cases hj : j = i
    · subst hj; simp [zpad, ZeroPadding.write_pad]
    · simp [zpad, Function.update_of_ne hj]
  | setc v σ => exact WExec.setc v (zpad σ z)
  | seq _ _ ih1 ih2 => exact WExec.seq ih1 ih2
  | ifrT hv _ ih => exact WExec.ifrT hv ih
  | ifrF hv _ ih => exact WExec.ifrF hv ih
  | ifsT hb _ ih => exact WExec.ifsT (by rw [wbit_zpad]; exact hb) ih
  | ifsF hb _ ih => exact WExec.ifsF (by rw [wbit_zpad]; exact hb) ih
  | whrF hv => exact WExec.whrF hv
  | whrT hv _ _ ih1 ih2 => exact WExec.whrT hv ih1 ih2
  | whsF hb => exact WExec.whsF (by rw [wbit_zpad]; exact hb)
  | whsT hb _ _ ih1 ih2 => exact WExec.whsT (by rw [wbit_zpad]; exact hb) ih1 ih2
  | mono _ hle ih => exact WExec.mono ih hle

end Pad

/-! ## The chain of products on two tapes -/

/-- The count's streams: `0` the input, `1` the base `sent N`, `2`, `3` the chain's tapes. -/
abbrev cI : Fin 4 := 0
abbrev cT : Fin 4 := 1
abbrev cX : Fin 4 := 2
abbrev cY : Fin 4 := 3

/-- Tape `cX` after `k` products. -/
def zX (N K k : ℕ) : List Bool :=
  if k % 2 = 0 then sent (K * N ^ k) else List.replicate (K * N ^ (k - 1) + 1) false

/-- Tape `cY` after `k` products. -/
def zY (N K : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 => if k % 2 = 0 then sent (K * N ^ (k + 1)) else List.replicate (K * N ^ k + 1) false

/-- The state after `k` products. -/
def zSt (σ : WState 3 0) (N K k : ℕ) : WState 3 0 := (σ.sets cX (zX N K k)).sets cY (zY N K k)

/-- Product `k + 1`: from the current tape into the other one, then the current tape erased. -/
def zStep (k : ℕ) : WM 3 0 :=
  if k % 2 = 0 then .seq (mulW cX cT cY) (eraseB cX) else .seq (mulW cY cT cX) (eraseB cY)

/-- `k` products. -/
def chainZ : ℕ → WM 3 0
  | 0 => .skip
  | k + 1 => .seq (chainZ k) (zStep k)

/-- Its cost. -/
def zCost (N K : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => zCost N K k + 1 + (mulCost (K * N ^ k) N + 1 + (3 * (K * N ^ k) + 3 + 1 + (1 + 1 + (5 * (K * N ^ k) + 1))))

theorem pad_rep (m : ℕ) : ZeroPadding.pad m [] = List.replicate m false := by simp [ZeroPadding.pad]

theorem pad_sent_le (m v : ℕ) (h : m ≤ v + 1) : ZeroPadding.pad m (sent v) = sent v := by
  simp [ZeroPadding.pad, sent_length]; omega

/-- One product on the zero-padded target. -/
theorem mulZ_spec (X T Y : Fin 4) (hXT : X ≠ T) (hXY : X ≠ Y) (hTY : T ≠ Y) (a b m : ℕ) (hm : m ≤ a * b + 1)
    (σ : WState 3 0) (hX : σ.st X = sent a) (hXh : σ.sh X = 0) (hT : σ.st T = sent b) (hTh : σ.sh T = 0)
    (hY : σ.st Y = List.replicate m false) (hYh : σ.sh Y = 0) (cap : ℕ) :
    WExec cap (mulW X T Y) σ (σ.sets Y (sent (a * b))) (mulCost a b) := by
  have h := mulW_spec cap X T Y hXT hXY hTY a b (σ.sets Y []) (by simp [Function.update_of_ne hXY, hX]) hXh
    (by simp [Function.update_of_ne hTY, hT]) hTh (by simp) hYh
  have hp := WExec.zpadS cap h (fun i => if i = Y then m else 0)
  have e1 : zpad (σ.sets Y []) (fun i => if i = Y then m else 0) = σ := by
    refine WState.eq ?_ ?_ ?_ ?_
    · rfl
    rotate_left
    · rfl
    · rfl
    funext i
    by_cases hi : i = Y
    · subst hi; simp [zpad, pad_rep, hY]
    · simp [zpad, hi, Function.update_of_ne hi]
  have e2 : zpad ((σ.sets Y []).sets Y (sent (a * b))) (fun i => if i = Y then m else 0) = σ.sets Y (sent (a * b)) := by
    refine WState.eq ?_ ?_ ?_ ?_
    · rfl
    rotate_left
    · rfl
    · rfl
    funext i
    by_cases hi : i = Y
    · subst hi; simp [zpad, pad_sent_le m (a * b) hm]
    · simp [zpad, hi, Function.update_of_ne hi]
  rw [e1, e2] at hp
  exact hp

theorem zY_len_le (N K k : ℕ) (hN : 1 ≤ N) : (zY N K k).length ≤ K * N ^ k + 1 := by
  rcases k with _ | k
  · simp [zY]
  · simp only [zY]
    have h1 : K * N ^ k ≤ K * N ^ (k + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by omega))
    split_ifs <;> simp [sent_length] <;> omega

theorem zX_len_le (N K k : ℕ) (hN : 1 ≤ N) : (zX N K k).length ≤ K * N ^ k + 1 := by
  unfold zX
  have h1 : K * N ^ (k - 1) ≤ K * N ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by omega))
  split_ifs <;> simp [sent_length] <;> omega

theorem cTX : cT ≠ cX := by decide
theorem cTY : cT ≠ cY := by decide
theorem cXY : cX ≠ cY := by decide

theorem zSt_X (σ : WState 3 0) (N K k : ℕ) : (zSt σ N K k).st cX = zX N K k := by
  simp only [zSt, WState.sets_st]; rw [Function.update_of_ne cXY, Function.update_self]

theorem zSt_Y (σ : WState 3 0) (N K k : ℕ) : (zSt σ N K k).st cY = zY N K k := by
  simp only [zSt, WState.sets_st]; rw [Function.update_self]

theorem zSt_o (σ : WState 3 0) (N K k : ℕ) (i : Fin 4) (hX : i ≠ cX) (hY : i ≠ cY) : (zSt σ N K k).st i = σ.st i := by
  simp only [zSt, WState.sets_st]; rw [Function.update_of_ne hY, Function.update_of_ne hX]

theorem zSt_sh (σ : WState 3 0) (N K k : ℕ) : (zSt σ N K k).sh = σ.sh := rfl

/-- **The chain**: after `k` products, `zSt σ N K k`. -/
theorem chainZ_spec (cap N K : ℕ) (hN : 1 ≤ N) (σ : WState 3 0) (hT : σ.st cT = sent N) (hh : ∀ i, σ.sh i = 0) :
    ∀ k, WExec cap (chainZ k) (zSt σ N K 0) (zSt σ N K k) (zCost N K k)
  | 0 => WExec.skip _
  | k + 1 => by
    have ih := chainZ_spec cap N K hN σ hT hh k
    have hTk : (zSt σ N K k).st cT = sent N := by rw [zSt_o σ N K k cT cTX cTY, hT]
    have hhk : ∀ i, (zSt σ N K k).sh i = 0 := fun i => by rw [zSt_sh]; exact hh i
    have hpow : K * N ^ k * N = K * N ^ (k + 1) := by ring
    have hle : K * N ^ k ≤ K * N ^ (k + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by omega))
    by_cases hk : k % 2 = 0
    · have hX : (zSt σ N K k).st cX = sent (K * N ^ k) := by rw [zSt_X]; simp only [zX, if_pos hk]
      have hY : (zSt σ N K k).st cY = List.replicate (zY N K k).length false := by
        rw [zSt_Y]
        rcases k with _ | k
        · rfl
        · have hk' : ¬ k % 2 = 0 := by omega
          simp only [zY, if_neg hk', List.length_replicate]
      have e1 := mulZ_spec cX cT cY cTX.symm cXY cTY (K * N ^ k) N (zY N K k).length
        (by rw [hpow]; have := zY_len_le N K k hN; omega)
        (zSt σ N K k) hX (hhk _) hTk (hhk _) hY (hhk _) cap
      rw [hpow] at e1
      have e2 := eraseB_spec cap cX (K * N ^ k) ((zSt σ N K k).sets cY (sent (K * N ^ (k + 1))))
        (by simp only [WState.sets_st]; rw [Function.update_of_ne cXY, hX]) (by simp only [WState.sets_sh]; exact hhk _)
      have e3 := WExec.seq ih (WExec.seq e1 e2)
      have hprog : chainZ (k + 1) = .seq (chainZ k) (.seq (mulW cX cT cY) (eraseB cX)) := by
        simp only [chainZ, zStep, if_pos hk]
      rw [hprog]
      refine WExec.cast cap e3 ?_ (by simp only [zCost]; omega)
      refine WState.eq ?_ ?_ ?_ ?_
      · rfl
      rotate_left
      · rfl
      · rfl
      funext i
      have hk1 : ¬ (k + 1) % 2 = 0 := by omega
      simp only [WState.sets_st]
      by_cases h3 : i = cY
      · subst h3
        rw [Function.update_of_ne cXY.symm, Function.update_self, zSt_Y]
        simp only [zY, if_pos hk]
      · by_cases h2 : i = cX
        · subst h2
          rw [Function.update_self, zSt_X]
          simp only [zX, if_neg hk1, Nat.add_sub_cancel]
        · rw [Function.update_of_ne h2, Function.update_of_ne h3, zSt_o σ N K k i h2 h3, zSt_o σ N K (k + 1) i h2 h3]
    · have hX : (zSt σ N K k).st cY = sent (K * N ^ k) := by
        rw [zSt_Y]
        rcases k with _ | k
        · simp at hk
        · have hk' : k % 2 = 0 := by omega
          simp only [zY, if_pos hk']
      have hY : (zSt σ N K k).st cX = List.replicate (zX N K k).length false := by
        rw [zSt_X]; simp only [zX, if_neg hk, List.length_replicate]
      have e1 := mulZ_spec cY cT cX cTY.symm cXY.symm cTX (K * N ^ k) N (zX N K k).length
        (by rw [hpow]; have := zX_len_le N K k hN; omega)
        (zSt σ N K k) hX (hhk _) hTk (hhk _) hY (hhk _) cap
      rw [hpow] at e1
      have e2 := eraseB_spec cap cY (K * N ^ k) ((zSt σ N K k).sets cX (sent (K * N ^ (k + 1))))
        (by simp only [WState.sets_st]; rw [Function.update_of_ne cXY.symm, hX])
        (by simp only [WState.sets_sh]; exact hhk _)
      have e3 := WExec.seq ih (WExec.seq e1 e2)
      have hprog : chainZ (k + 1) = .seq (chainZ k) (.seq (mulW cY cT cX) (eraseB cY)) := by
        simp only [chainZ, zStep, if_neg hk]
      rw [hprog]
      refine WExec.cast cap e3 ?_ (by simp only [zCost]; omega)
      refine WState.eq ?_ ?_ ?_ ?_
      · rfl
      rotate_left
      · rfl
      · rfl
      funext i
      have hk1 : (k + 1) % 2 = 0 := by omega
      simp only [WState.sets_st]
      by_cases h3 : i = cY
      · subst h3
        rw [Function.update_self, zSt_Y]
        simp only [zY, if_neg hk]
      · by_cases h2 : i = cX
        · subst h2
          rw [Function.update_of_ne cXY, Function.update_self, zSt_X]
          simp only [zX, if_pos hk1]
        · rw [Function.update_of_ne h3, Function.update_of_ne h2, zSt_o σ N K k i h2 h3, zSt_o σ N K (k + 1) i h2 h3]

/-! ## The count program -/

/-- **The count**: `T = sent N` from the framed input, `sent K` on `cX`, then `D` products. -/
def cntW (K D : ℕ) : WM 3 0 :=
  .seq (lenT cI cT) (.seq (emit1 cX false) (.seq (emitN cX K) (.seq (rewSent cX) (chainZ D))))

/-- Its cost at `|u| = m`. -/
def cntCost (m K D : ℕ) : ℕ := 16 * m + 20 + 1 + (3 + 1 + (4 * K + 1 + (3 * K + 3 + 1 + zCost (m + 1) K D)))

/-- The count's output tape: `cX` or `cY` by the parity of `D`. -/
def cOut (D : ℕ) : Fin 4 := if D % 2 = 0 then cX else cY

theorem zSt_out (σ : WState 3 0) (N K D : ℕ) : (zSt σ N K D).st (cOut D) = sent (K * N ^ D) := by
  unfold cOut
  by_cases hD : D % 2 = 0
  · rw [if_pos hD, zSt_X]; simp only [zX, if_pos hD]
  · rw [if_neg hD, zSt_Y]
    rcases D with _ | D
    · simp at hD
    · have hD' : D % 2 = 0 := by omega
      simp only [zY, if_pos hD']

/-- **The count's run**: from the framed input on `cI` (every other stream blank, heads `0`), `T = sent N` and the
chain's state after `D` products (`sent (K·N^D)` on `cOut D`). -/
theorem cntW_spec (cap K D : ℕ) (u : List Bool) (σ : WState 3 0) (hI : σ.st cI = frame u) (hh : ∀ i, σ.sh i = 0)
    (hT : σ.st cT = []) (hX : σ.st cX = []) (hY : σ.st cY = []) :
    WExec cap (cntW K D) σ (zSt (σ.sets cT (sent (u.length + 1))) (u.length + 1) K D) (cntCost u.length K D) := by
  have e1 := lenT_spec cap cI cT (by decide) u σ hI (hh _) hT (hh _)
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.sets cT (sent (u.length + 1)) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have h1X : σ1.st cX = [] := by rw [hσ1]; simp only [WState.sets_st]; rw [Function.update_of_ne cTX.symm, hX]
  have h1Y : σ1.st cY = [] := by rw [hσ1]; simp only [WState.sets_st]; rw [Function.update_of_ne cTY.symm, hY]
  have h1T : σ1.st cT = sent (u.length + 1) := by rw [hσ1]; simp only [WState.sets_st]; rw [Function.update_self]
  have h1h : ∀ i, σ1.sh i = 0 := fun i => by rw [hσ1]; exact hh i
  have e2 := emit1_spec cap cX false σ1 (by rw [h1h, h1X]; rfl)
  have e3 := emitN_spec cap cX K (appW σ1 cX [false]) (by simp)
  rw [appW_appW] at e3
  have e4 := rewSent_spec cap cX K (appW σ1 cX ([false] ++ List.replicate K true))
    (by simp [h1X, sent]) (by simp [h1X])
  have e5 := chainZ_spec cap (u.length + 1) K (by omega) σ1 h1T h1h D
  have e0 : (appW σ1 cX ([false] ++ List.replicate K true)).seth cX 0 = zSt σ1 (u.length + 1) K 0 := by
    refine WState.eq ?_ ?_ ?_ ?_
    · funext i
      by_cases hi : i = cX
      · subst hi; simp [zSt, h1h]
      · simp [zSt, Function.update_of_ne hi]
    · funext i
      by_cases hi : i = cX
      · subst hi
        simp only [appW_st, WState.seth_st, zSt_X, Function.update_self, h1X, List.nil_append, zX]
        simp [sent]
      · by_cases hiY : i = cY
        · subst hiY
          simp only [appW_st, WState.seth_st, zSt_Y, Function.update_of_ne hi, h1Y, zY]
        · simp only [appW_st, WState.seth_st, Function.update_of_ne hi, zSt_o σ1 _ K 0 i hi hiY]
    · rfl
    · rfl
  rw [e0] at e4
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by unfold cntCost; omega)
  rw [hσ1]

end NearCubicWires.WireExponent3_5.FinalPass.Core
