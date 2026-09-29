import Proof.Wire_3_5.Selection.CosRaw

/-! # C1.5: the selected coset's word (P3:1360, 3673)

Paper: "Select a minimum objective" (P3:1360); the union machine "selects the common star translation" (P3:3673) and
reads it as the raw word `cosetWord c = natListWord c` (C6's `UnionMachine.Plan.cosetWord`). The loop leaves
the counter value `N` of the selected coset in the width-`s·r` word `BEST` (least significant bit first); its codes are
the `s`-bit digits of `N`, most significant first (`codesOfIdx`). **`outW`** writes `natWord r` (from the unary
register `r`), then walks `BEST` from its end marker backward, reading each code MSB first into a unary register
(Horner: `v := 2v + bit`, PA's `dbl`) and writing it raw (`rawNatW`). Main declarations: `blkLoop`, `blkLoop_spec`,
`codesL`, `codesL_spec`, `outW`, `outCost`, **`outW_spec`** (the output stream gains `natListWord (codesOfIdx s r N)`).
Paper quantity: the selected coset's syndrome codes on the output tape. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (dbl dbl_spec)

variable {ns nr : ℕ}

/-! ## One code, most significant bit first -/

/-- `m` rounds: step back over a bit of `B`, `v := 2v + bit`, step back over its marker (`R 8` counts down). -/
def blkLoop (B : Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WM ns nr :=
  .whr (R 8) (.seq (.dec (R 8)) (.seq (.bwd B) (.seq (.ifs B (.seq (dbl (R 0) (R 6)) (.inc (R 0))) (dbl (R 0) (R 6)))
    (.bwd B))))

theorem mod_pow_succ_split (x m : ℕ) : x % 2 ^ (m + 1) = x / 2 ^ m % 2 * 2 ^ m + x % 2 ^ m := by
  rw [Nat.mod_pow_succ]; ring

theorem blkLoop_spec (cap K N : ℕ) (B : Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) (Bd : ℕ) (hBd : 2 * Bd + 2 ≤ cap) :
    ∀ (m t : ℕ) (σ : WState ns nr) (v0 : ℕ), σ.val (R 8) = m → σ.sh B = 2 * (t + m) → t + m ≤ K →
      σ.st B = frame (binary K N) → σ.val (R 0) = v0 → σ.val (R 6) = 0 → (v0 + 1) * 2 ^ m ≤ Bd → m ≤ cap →
      WExec cap (blkLoop B R) σ (((σ.seth B (2 * t)).setv (R 0) (v0 * 2 ^ m + N / 2 ^ t % 2 ^ m)).setv (R 8) 0)
        (m * (18 * Bd + 20) + 1)
  | 0, t, σ, v0, h0, hB, _, _, hv, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = B
      · subst hj; simp [hB]
      · simp [Function.update_apply, hj]
    · rfl
    · funext j; by_cases h8 : j = R 8
      · subst h8; simp [h0]
      · by_cases h0' : j = R 0
        · subst h0'; simp [Function.update_apply, h8, hv, Nat.mod_one]
        · simp [Function.update_apply, h8, h0']
    · rfl
  | m + 1, t, σ, v0, hm, hB, htK, hst, hv, h6, hBd', hc => by
    have rne : ∀ i j : Fin 12, i ≠ j → R i ≠ R j := fun i j h => R.injective.ne h
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hv0 : 2 * v0 + 1 < Bd := by
      have : (v0 + 1) * 2 ≤ (v0 + 1) * 2 ^ (m + 1) := Nat.mul_le_mul_left _ (by
        have := Nat.one_le_two_pow (n := m); rw [hpow]; omega)
      omega
    have d := WExec.dec (cap := cap) (R 8) σ (by omega)
    set σ1 := σ.setv (R 8) (σ.val (R 8) - 1) with hσ1
    have b1 := WExec.bwd (cap := cap) B σ1
    set σ2 := σ1.seth B (σ1.sh B - 1) with hσ2
    have hsh2 : σ2.sh B = 2 * (t + m) + 1 := by simp [hσ2, hσ1, hB]; omega
    have hbit : wbit σ2 B = (N / 2 ^ (t + m) % 2 == 1) := by
      have e : σ2.sh B = 2 * (t + m) + 1 := hsh2
      simp only [wbit]
      rw [e]
      simp only [hσ2, hσ1, WState.seth_st, WState.setv_st, hst]
      exact frame_bit K N (t + m) (by omega)
    have v2 : σ2.val (R 0) = v0 := by simp [hσ2, hσ1, rne 0 8 (by decide), hv]
    have t2 : σ2.val (R 6) = 0 := by simp [hσ2, hσ1, rne 6 8 (by decide), h6]
    set bit := N / 2 ^ (t + m) % 2 with hbitv
    have hbit2 : bit < 2 := Nat.mod_lt _ (by norm_num)
    have x3 : WExec cap (.ifs B (.seq (dbl (R 0) (R 6)) (.inc (R 0))) (dbl (R 0) (R 6))) σ2 (σ2.setv (R 0) (2 * v0 + bit))
        (18 * v0 + 3 + 1 + 3 + 1) := by
      have dd := dbl_spec cap (R 0) (R 6) (rne 0 6 (by decide)) σ2 t2 (by rw [v2]; omega)
      rw [v2] at dd
      by_cases hb1 : bit = 1
      · have ii := WExec.inc (cap := cap) (R 0) (σ2.setv (R 0) (2 * v0)) (by simp; omega)
        refine WExec.ifsT (by rw [hbit, hb1]; rfl) (WExec.cast cap (WExec.seq dd ii) ?_ le_rfl)
        rw [wsetv_setv]; simp [hb1]
      · have hb0 : bit = 0 := by omega
        refine WExec.ifsF (by rw [hbit, hb0]; rfl) (WExec.mono (WExec.cast cap dd ?_ le_rfl) (by omega))
        simp [hb0]
    set σ3 := σ2.setv (R 0) (2 * v0 + bit) with hσ3
    have b4 := WExec.bwd (cap := cap) B σ3
    set σ4 := σ3.seth B (σ3.sh B - 1) with hσ4
    have ih := blkLoop_spec cap K N B R Bd hBd m t σ4 (2 * v0 + bit) (by simp [hσ4, hσ3, hσ2, hσ1, rne 8 0 (by decide), hm])
      (by simp [hσ4, hσ3, hsh2]) (by omega) (by simp [hσ4, hσ3, hσ2, hσ1, hst])
      (by simp [hσ4, hσ3]) (by simp [hσ4, hσ3, hσ2, hσ1, rne 6 0 (by decide), rne 6 8 (by decide), h6])
      (by
        have : (2 * v0 + bit + 1) * 2 ^ m ≤ (v0 + 1) * 2 ^ (m + 1) := by
          rw [hpow]; nlinarith [Nat.one_le_two_pow (n := m)]
        omega) (by omega)
    have hcost : 1 + 1 + (1 + 1 + (18 * v0 + 3 + 1 + 3 + 1 + 1 + 1)) + 2 + (m * (18 * Bd + 20) + 1) ≤
        (m + 1) * (18 * Bd + 20) + 1 := by nlinarith
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d (WExec.seq b1 (WExec.seq x3 b4))) ih) ?_ hcost
    have hval : (2 * v0 + bit) * 2 ^ m + N / 2 ^ t % 2 ^ m = v0 * 2 ^ (m + 1) + N / 2 ^ t % 2 ^ (m + 1) := by
      rw [mod_pow_succ_split, Nat.div_div_eq_div_mul, ← pow_add, hpow]
      rw [hbitv]; ring
    apply WState.eq
    · funext j; by_cases hj : j = B
      · subst hj; simp [hσ4, hσ3, hσ2, hσ1]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj]
    · rfl
    · funext j; by_cases h8 : j = R 8
      · subst h8; simp
      · by_cases h0' : j = R 0
        · subst h0'; simp [Function.update_apply, h8, hval]
        · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, h8, h0']
    · rfl

/-! ## The codes -/

/-- One code: `R 8 := s`, then the block loop into `R 0`. -/
def blkR (B : Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 11) (R 8) (R 6)) (blkLoop B R)

/-- The codes loop: `R 9` rounds of one code read and written raw. -/
def codesL (B O : Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WM ns nr :=
  .whr (R 9) (.seq (.dec (R 9)) (.seq (blkR B R) (.seq (rawNatW O R) (WM.clear (R 0)))))

theorem codesOfIdx_length (s : ℕ) : ∀ r N : ℕ, (codesOfIdx s r N).length = r
  | 0, _ => rfl
  | r + 1, N => by simp [codesOfIdx, codesOfIdx_length s r]

/-- One round's cost bound at code values below `2^s`. -/
def codeCost (s : ℕ) : ℕ :=
  18 * s + 3 + 1 + (s * (18 * 2 ^ (s + 1) + 20) + 1) + 1 + (rawCost (2 ^ s) + 1 + (3 * 2 ^ s + 1))

theorem rawCost_mono (v w : ℕ) (h : v ≤ w) : rawCost v ≤ rawCost w := by
  have hl : natBitLength v ≤ natBitLength w := by unfold natBitLength; have := Nat.log_mono_right (b := 2) h; omega
  unfold rawCost
  have h1 : natBitLength v * (9 * v + 25) ≤ natBitLength w * (9 * w + 25) := Nat.mul_le_mul hl (by omega)
  omega

theorem codesL_spec (cap s N : ℕ) (B O : Fin (ns + 1)) (hBO : B ≠ O) (R : Fin 12 ↪ Fin nr) (K : ℕ)
    (hcap : 2 * 2 ^ (s + 1) + 6 ≤ cap) (hsK : s ≤ cap) :
    ∀ (r : ℕ) (σ : WState ns nr), σ.val (R 9) = r → σ.sh B = 2 * (s * r) → s * r ≤ K →
      σ.st B = frame (binary K N) → σ.val (R 11) = s → (∀ i : Fin 12, i.val ≤ 8 → σ.val (R i) = 0) →
      σ.sh O = (σ.st O).length → r ≤ cap →
      WExec cap (codesL B O R) σ
        (((appS σ O ((codesOfIdx s r (N % 2 ^ (s * r))).flatMap RepairRepresentation.natWord)).seth B 0).setv (R 9) 0)
        (r * (codeCost s + 4) + 1)
  | 0, σ, h0, hB, _, _, _, _, hO, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ (by omega)
    simp only [codesOfIdx, List.flatMap_nil]
    rw [appS_nil σ O hO]
    apply WState.eq
    · funext j; by_cases hj : j = B
      · subst hj; simp [hB]
      · simp [Function.update_apply, hj]
    · rfl
    · funext j; by_cases h9 : j = R 9
      · subst h9; simp [h0]
      · simp [Function.update_apply, h9]
    · rfl
  | r + 1, σ, hr, hB, hK, hst, hs, hz, hO, hrc => by
    have rne : ∀ i j : Fin 12, i ≠ j → R i ≠ R j := fun i j h => R.injective.ne h
    have d := WExec.dec (cap := cap) (R 9) σ (by omega)
    set σ1 := σ.setv (R 9) (σ.val (R 9) - 1) with hσ1
    have c1 := FinalPass.Hash4.wcopyR_spec cap (R 11) (R 8) (R 6) (rne 11 8 (by decide)) (rne 11 6 (by decide))
      (rne 8 6 (by decide)) σ1 (by simp [hσ1, rne 8 9 (by decide), hz 8 (by decide)])
      (by simp [hσ1, rne 6 9 (by decide), hz 6 (by decide)]) (by simp [hσ1, rne 11 9 (by decide), hs]; omega)
    have hs1 : σ1.val (R 11) = s := by simp [hσ1, rne 11 9 (by decide), hs]
    rw [hs1] at c1
    set σ2 := σ1.setv (R 8) s with hσ2
    have hpos : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have bl := blkLoop_spec cap K N B R (2 ^ s) (by
        have : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
        omega) s (s * r) σ2 0 (by simp [hσ2])
      (by simp [hσ2, hσ1, hB]; ring) (by nlinarith) (by simp [hσ2, hσ1, hst])
      (by simp [hσ2, hσ1, rne 0 8 (by decide), rne 0 9 (by decide), hz 0 (by decide)])
      (by simp [hσ2, hσ1, rne 6 8 (by decide), rne 6 9 (by decide), hz 6 (by decide)]) (by simp) hsK
    have bl' : WExec cap (blkLoop B R) σ2 (((σ2.seth B (2 * (s * r))).setv (R 0) (N / 2 ^ (s * r) % 2 ^ s)).setv
        (R 8) 0) (s * (18 * 2 ^ (s + 1) + 20) + 1) := by
      refine WExec.mono (WExec.cast cap bl (by simp) le_rfl) ?_
      have : 2 ^ s ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    set v := N / 2 ^ (s * r) % 2 ^ s with hv
    have hvs : v < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
    have hss : 2 ^ s ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    set σ3 := ((σ2.seth B (2 * (s * r))).setv (R 0) v).setv (R 8) 0 with hσ3
    have hO3 : σ3.sh O = (σ3.st O).length := by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hBO, hO]
    have wr := rawNatW_spec cap O R σ3 (by
        intro i hi1 hi6
        have h0 : i ≠ 0 := fun e => by subst e; simp at hi1
        have h8 : i ≠ 8 := fun e => by subst e; simp at hi6
        have h9 : i ≠ 9 := fun e => by subst e; simp at hi6
        simp [hσ3, hσ2, hσ1, rne i 8 h8, rne i 0 h0, rne i 9 h9, hz i (by omega)]) hO3
      (by simp [hσ3, rne 0 8 (by decide)]; omega)
    have hv3 : σ3.val (R 0) = v := by simp [hσ3, rne 0 8 (by decide)]
    rw [hv3] at wr
    set σ4 := appS σ3 O (RepairRepresentation.natWord v) with hσ4
    have hv4 : σ4.val (R 0) = v := by simp [hσ4, hv3]
    have cl := wclear_spec (cap := cap) (R 0) v σ4 hv4 (by rw [hv4]; omega)
    set σ5 := σ4.setv (R 0) 0 with hσ5
    have ih := codesL_spec cap s N B O hBO R K hcap hsK r σ5
      (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, rne 9 0 (by decide), rne 9 8 (by decide), hr])
      (by simp [hσ5, hσ4, hσ3, Function.update_apply, hBO])
      (by nlinarith) (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hBO, hst])
      (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, rne 11 0 (by decide), rne 11 8 (by decide), rne 11 9 (by decide), hs])
      (by
        intro i hi
        by_cases h0 : i = 0
        · subst h0; simp [hσ5]
        · by_cases h8 : i = 8
          · subst h8; simp [hσ5, hσ4, hσ3, rne 8 0 (by decide)]
          · simp [hσ5, hσ4, hσ3, hσ2, hσ1, rne i 0 h0, rne i 8 h8, rne i 9 (fun e => by subst e; simp at hi),
              hz i hi])
      (appS_hO _ _ _) (by omega)
    have hcost : 1 + 1 + (18 * s + 3 + 1 + (s * (18 * 2 ^ (s + 1) + 20) + 1) + 1 + (rawCost v + 1 + (3 * v + 1))) +
        2 + (r * (codeCost s + 4) + 1) ≤ (r + 1) * (codeCost s + 4) + 1 := by
      have := rawCost_mono v (2 ^ s) hvs.le
      unfold codeCost; nlinarith
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d (WExec.seq (WExec.seq c1 bl') (WExec.seq wr cl))) ih) ?_
      hcost
    -- the codes of the counter value
    have hsplit : 2 ^ (s * (r + 1)) = 2 ^ (s * r) * 2 ^ s := by rw [Nat.mul_add, Nat.mul_one, pow_add]
    have hc : codesOfIdx s (r + 1) (N % 2 ^ (s * (r + 1))) = v :: codesOfIdx s r (N % 2 ^ (s * r)) := by
      rw [codesOfIdx, hsplit, Nat.mod_mul_right_div_self, Nat.mod_mod, Nat.mod_mul_right_mod]
    rw [hc, List.flatMap_cons]
    apply WState.eq
    · funext j; by_cases hj : j = B
      · subst hj; simp
      · by_cases hjO : j = O
        · subst hjO; simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj, Ne.symm hBO]; ring
        · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj, hjO]
    · funext j; by_cases hjO : j = O
      · subst hjO; simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hBO, List.append_assoc]
      · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hjO]
    · funext j
      by_cases h9 : j = R 9
      · subst h9; simp
      · by_cases h0 : j = R 0
        · subst h0; simp [hσ5, Function.update_apply, h9, hz 0 (by decide)]
        · by_cases h8 : j = R 8
          · subst h8; simp [hσ5, hσ4, hσ3, Function.update_apply, h9, h0, hz 8 (by decide)]
          · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, h9, h0, h8]
    · simp [hσ5, hσ4, hσ3, hσ2, hσ1]

/-! ## The output word -/

/-- **The selected coset's word**: `natWord r`, then the `r` codes of `BEST`. -/
def outW (B O : Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 10) (R 0) (R 6)) (.seq (rawNatW O R) (.seq (WM.clear (R 0))
    (.seq (.whs B (.seq (.fwd B) (.fwd B))) (.seq (FinalPass.Hash4.wcopyR (R 10) (R 9) (R 6)) (codesL B O R)))))

/-- The output's cost. -/
def outCost (r s : ℕ) : ℕ :=
  18 * r + 3 + 1 + (rawCost r + 1 + (3 * r + 1 + 1 + (5 * (s * r) + 1 + 1 + (18 * r + 3 + 1 +
    (r * (codeCost s + 4) + 1)))))

/-- **The output**: the stream `O` gains `natListWord (codesOfIdx s r N)` (the head at its end); the word `B` and its
head, the registers and every other stream come back. -/
theorem outW_spec (cap s r N : ℕ) (B O : Fin (ns + 1)) (hBO : B ≠ O) (R : Fin 12 ↪ Fin nr) (σ : WState ns nr)
    (hst : σ.st B = frame (binary (s * r) N)) (hsh : σ.sh B = 0) (hN : N < 2 ^ (s * r))
    (hz : ∀ i : Fin 12, i.val ≤ 9 → σ.val (R i) = 0) (hr : σ.val (R 10) = r) (hs : σ.val (R 11) = s)
    (hO : σ.sh O = (σ.st O).length) (hcap : 2 * 2 ^ (s + 1) + 2 * r + 6 ≤ cap) (hsK : s ≤ cap) :
    WExec cap (outW B O R) σ (appS σ O (RepairRepresentation.natListWord (codesOfIdx s r N))) (outCost r s) := by
  have rne : ∀ i j : Fin 12, i ≠ j → R i ≠ R j := fun i j h => R.injective.ne h
  have x1 := FinalPass.Hash4.wcopyR_spec cap (R 10) (R 0) (R 6) (rne 10 0 (by decide)) (rne 10 6 (by decide))
    (rne 0 6 (by decide)) σ (hz 0 (by decide)) (hz 6 (by decide)) (by rw [hr]; omega)
  rw [hr] at x1
  set σ1 := σ.setv (R 0) r with hσ1
  have x2 := rawNatW_spec cap O R σ1 (by
      intro i hi1 hi6
      have h0 : i ≠ 0 := fun e => by subst e; simp at hi1
      simp [hσ1, rne i 0 h0, hz i (by omega)]) (by simp [hσ1, hO]) (by simp [hσ1]; omega)
  have hr1 : σ1.val (R 0) = r := by simp [hσ1]
  rw [hr1] at x2
  set σ2 := appS σ1 O (RepairRepresentation.natWord r) with hσ2
  have hr2 : σ2.val (R 0) = r := by simp [hσ2, hr1]
  have x3 := wclear_spec (cap := cap) (R 0) r σ2 hr2 (by rw [hr2]; omega)
  set σ3 := σ2.setv (R 0) 0 with hσ3
  have hst3 : σ3.st B = [] ++ (frameP (binary (s * r) N) ++ false :: []) := by
    simp [hσ3, hσ2, hσ1, Function.update_apply, hBO, hst, frame_eq_frameP]
  have x4 := skipLoopB_spec cap B [] [] (binary (s * r) N) σ3 hst3 0 (by simp [hσ3, hσ2, hσ1, hBO, hsh])
    (s * r) (by simp)
  simp only [List.length_nil, binary_length, Nat.zero_add] at x4
  set σ4 := σ3.seth B (2 * (s * r)) with hσ4
  have x5 := FinalPass.Hash4.wcopyR_spec cap (R 10) (R 9) (R 6) (rne 10 9 (by decide)) (rne 10 6 (by decide))
    (rne 9 6 (by decide)) σ4 (by simp [hσ4, hσ3, hσ2, hσ1, rne 9 0 (by decide), hz 9 (by decide)])
    (by simp [hσ4, hσ3, hσ2, hσ1, rne 6 0 (by decide), hz 6 (by decide)])
    (by simp [hσ4, hσ3, hσ2, hσ1, rne 10 0 (by decide), hr]; omega)
  have hr4 : σ4.val (R 10) = r := by simp [hσ4, hσ3, hσ2, hσ1, rne 10 0 (by decide), hr]
  rw [hr4] at x5
  set σ5 := σ4.setv (R 9) r with hσ5
  have x6 := codesL_spec cap s N B O hBO R (s * r) (by omega) hsK r σ5 (by simp [hσ5]) (by simp [hσ5, hσ4])
    le_rfl (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hBO, hst])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, rne 11 9 (by decide), rne 11 0 (by decide), hs])
    (by
      intro i hi
      by_cases h9 : i = 9
      · subst h9; simp at hi
      · by_cases h0 : i = 0
        · subst h0; simp [hσ5, hσ4, hσ3, rne 0 9 (by decide)]
        · simp [hσ5, hσ4, hσ3, hσ2, hσ1, rne i 9 h9, rne i 0 h0, hz i (by omega)])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hBO]) (by omega)
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 x6))))) ?_ le_rfl
  rw [Nat.mod_eq_of_lt hN]
  have hlist : RepairRepresentation.natListWord (codesOfIdx s r N) =
      RepairRepresentation.natWord r ++ (codesOfIdx s r N).flatMap RepairRepresentation.natWord := by
    rw [RepairRepresentation.natListWord, codesOfIdx_length]
  rw [hlist]
  apply WState.eq
  · funext j; by_cases hj : j = B
    · subst hj; simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hBO, hsh]
    · by_cases hjO : j = O
      · subst hjO; simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj]; ring
      · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj, hjO]
  · funext j; by_cases hjO : j = O
    · subst hjO; simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hBO, List.append_assoc]
    · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hjO]
  · funext j
    by_cases h9 : j = R 9
    · subst h9; simp [hz 9 (by decide)]
    · by_cases h0 : j = R 0
      · subst h0; simp [hσ5, hσ4, hσ3, Function.update_apply, h9, hz 0 (by decide)]
      · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, h9, h0]
  · simp [hσ5, hσ4, hσ3, hσ2, hσ1]

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
