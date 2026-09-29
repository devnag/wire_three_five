import Proof.Wire_3_5.Primitive.Writers.WriteNat

/-! # C6 front, the C1 dock: a population's gate indices (P3:1326-1330)

C1's request names each population by the indices of its gates (`Plan.selWord`: `natListWord X.1` with
`X.1 = List.range' start len`, `FrontSelReq.selReqOn`). With the start and the length in unary registers, PA's
`writeNatM` (the framed `natWord` writer) writes the list:
* **`rngLoop_spec`**: `len` rounds append `marks (natWord (s + k))`, `k < len`;
* **`rangeW_spec`**: `marks (natListWord (List.range' s len))` appended, every scratch register back at `0`.

Paper quantity of the main type: the gate indices of one weighted carrier in `star:selection`'s request. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Rng
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord natListWord)

variable {ns nr : ℕ} (cap : ℕ)

/-- The writer's cost at values `≤ V`. -/
def wnCost (V : ℕ) : ℕ := (natBitLength V + 10) * (100 * V + 200)

theorem nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength; have := Nat.log_mono_right (b := 2) h; omega

theorem wnCost_mono {a b : ℕ} (h : a ≤ b) : wnCost a ≤ wnCost b := by
  unfold wnCost
  have := nbl_mono h
  apply Nat.mul_le_mul <;> omega

theorem marks_length (u : List Bool) : (marks u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    show (true :: b :: marks u).length = _
    simp [ih]; ring

section Loop
variable (o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (K : Fin nr)

/-- `len` rounds: write `natWord (R 0)`, then `R 0 += 1`. -/
def rngLoop : WM ns nr := .whr K (.seq (.dec K) (.seq (writeNatM o R) (.inc (R 0))))

/-- The words of the indices `s, …, s + k − 1`. -/
def rngWords (s k : ℕ) : List Bool := marks ((List.range' s k).flatMap natWord)

theorem rngWords_succ (s k : ℕ) : rngWords s (k + 1) = rngWords s k ++ marks (natWord (s + k)) := by
  unfold rngWords
  rw [List.range'_concat, List.flatMap_append]
  simp [marks_append]

theorem rngWords_mono (s k k' : ℕ) (h : k ≤ k') : (rngWords s k).length ≤ (rngWords s k').length := by
  induction k' with
  | zero => rw [show k = 0 by omega]
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hk | hk
    · rw [rngWords_succ, List.length_append]; have := ih (by omega); omega
    · rw [show k = k' + 1 by omega]

theorem rngLoop_spec (hK : ∀ i, R i ≠ K) (s len : ℕ) (σ : WState ns nr) (hs : σ.val (R 0) = s)
    (hk : σ.val K = len) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0)
    (h4 : σ.val (R 4) = 0) (h5 : σ.val (R 5) = 0) (h6 : σ.val (R 6) = 0) (ho : σ.sh o = (σ.st o).length)
    (hcap : s + len + σ.val (R 7) + (rngWords s len).length + 6 * natBitLength (s + len) + 6 ≤ cap) :
    WExec cap (rngLoop o R K) σ ((appendO σ o (R 7) (rngWords s len)).setv (R 0) (s + len) |>.setv K 0)
      (len * (wnCost (s + len) + 8) + 1) := by
  have hne : ∀ {i j : Fin 8}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  set S : ℕ → WState ns nr := fun k => ((appendO σ o (R 7) (rngWords s k)).setv (R 0) (s + k)).setv K (len - k)
    with hS
  have hS0 : S 0 = σ := by
    simp only [hS, rngWords, List.range'_zero, List.flatMap_nil]
    rw [show marks ([] : List Bool) = [] from rfl, appendO_nil]
    wgen_eq [hs, hk]
  have hloop := UnionMachine.Round.wloop cap K (.seq (writeNatM o R) (.inc (R 0))) (wnCost (s + len) + 4) len S
    (fun k _ => by simp [hS])
    (by have := rngWords_mono s 0 len (Nat.zero_le _); omega)
    (fun k hk' => by
      have hlen : (rngWords s k).length ≤ (rngWords s len).length := rngWords_mono s k len (by omega)
      have hlen1 : (rngWords s (k + 1)).length ≤ (rngWords s len).length := rngWords_mono s (k + 1) len (by omega)
      rw [rngWords_succ, List.length_append] at hlen1
      set σk := (S k).setv K (len - k - 1) with hσk
      have v0 : σk.val (R 0) = s + k := by simp [σk, hS, Function.update_apply, hK 0, (hK 0).symm]
      have vr : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → σk.val (R i) = σ.val (R i) := by
        intro i hi0 hi7
        simp [σk, hS, Function.update_apply, hK i, hne hi0, hne hi7]
      have v7 : σk.val (R 7) = σ.val (R 7) + (rngWords s k).length := by
        simp [σk, hS, Function.update_apply, hK 7, hne (show (7 : Fin 8) ≠ 0 by decide)]
      have sho : σk.sh o = (σk.st o).length := by simp [σk, hS, ho]
      have hw := writeNatM_spec cap o R σk (by rw [vr 1 (by decide) (by decide), h1])
        (by rw [vr 2 (by decide) (by decide), h2]) (by rw [vr 3 (by decide) (by decide), h3])
        (by rw [vr 4 (by decide) (by decide), h4]) (by rw [vr 5 (by decide) (by decide), h5])
        (by rw [vr 6 (by decide) (by decide), h6]) sho
        (by
          rw [v0, v7]
          have := nbl_mono (show s + k ≤ s + len by omega)
          omega)
      rw [v0] at hw
      set σw := appendO σk o (R 7) (marks (natWord (s + k))) with hσw
      have hwl : (marks (natWord (s + k))).length ≤ (rngWords s len).length := by omega
      have hi := WExec.inc (cap := cap) (R 0) σw (by
        simp [σw, Function.update_apply, hne (show (0 : Fin 8) ≠ 7 by decide), v0]; omega)
      refine WExec.mono (WExec.cast cap (WExec.seq hw hi) ?_ le_rfl) ?_
      · simp only [σw, σk, hS]
        rw [rngWords_succ, ← appendO_append]
        apply WState.eq
        · funext j; by_cases hj : j = o
          · subst hj; simp
          · simp [Function.update_apply, hj]
        · funext j; by_cases hj : j = o
          · subst hj; simp
          · simp [Function.update_apply, hj]
        · funext j
          by_cases hj0 : j = R 0
          · subst hj0; simp [Function.update_apply, hK 0, hne (show (0 : Fin 8) ≠ 7 by decide)]; omega
          · by_cases hjK : j = K
            · subst hjK; simp [Function.update_apply, (hK 0).symm, (hK 7).symm]; omega
            · by_cases hj7 : j = R 7
              · subst hj7; simp [Function.update_apply, hK 7, hne (show (7 : Fin 8) ≠ 0 by decide)]
              · simp [Function.update_apply, hj0, hjK, hj7]
        · simp
      · have := wnCost_mono (show s + k ≤ s + len by omega)
        unfold wnCost at this ⊢
        omega)
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ (le_of_eq (by ring))
  simp only [hS, Nat.sub_self]

end Loop

section Range
variable (o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (K T S LEN : Fin nr)

/-- **The index list** `natListWord (List.range' s len)` from `S = s`, `LEN = len` (kept); `K`, `T` scratch. -/
def rangeW : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR LEN (R 0) T) (.seq (writeNatM o R) (.seq (WM.clear (R 0))
    (.seq (FinalPass.Hash4.wcopyR S (R 0) T) (.seq (FinalPass.Hash4.wcopyR LEN K T) (.seq (rngLoop o R K)
      (WM.clear (R 0)))))))

theorem natListWord_range (s len : ℕ) :
    marks (natListWord (List.range' s len)) = marks (natWord len) ++ rngWords s len := by
  simp [natListWord, rngWords, marks_append]

/-- The index list's cost. -/
def rangeCost (s len : ℕ) : ℕ := 100 * (s + len) + wnCost len + len * (wnCost (s + len) + 8) + 3 * (s + len) + 50

theorem rangeW_spec (hK : ∀ i, R i ≠ K) (hT : ∀ i, R i ≠ T) (hS : ∀ i, R i ≠ S) (hL : ∀ i, R i ≠ LEN)
    (hKT : K ≠ T) (hKS : K ≠ S) (hKL : K ≠ LEN) (hTS : T ≠ S) (hTL : T ≠ LEN)
    (σ : WState ns nr) (s len : ℕ) (hs : σ.val S = s) (hl : σ.val LEN = len) (hk : σ.val K = 0) (ht : σ.val T = 0)
    (h0 : σ.val (R 0) = 0) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0)
    (h4 : σ.val (R 4) = 0) (h5 : σ.val (R 5) = 0) (h6 : σ.val (R 6) = 0) (ho : σ.sh o = (σ.st o).length)
    (hcap : s + len + σ.val (R 7) + (marks (natListWord (List.range' s len))).length + 6 * natBitLength (s + len) + 6
      ≤ cap) :
    WExec cap (rangeW o R K T S LEN) σ (appendO σ o (R 7) (marks (natListWord (List.range' s len))))
      (rangeCost s len) := by
  have hne : ∀ {i j : Fin 8}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  rw [natListWord_range] at hcap ⊢
  simp only [List.length_append] at hcap
  have hnl := nbl_mono (show len ≤ s + len by omega)
  -- 1. R 0 := len
  have e1 := FinalPass.Hash4.wcopyR_spec cap LEN (R 0) T (hL 0).symm (Ne.symm hTL) (hT 0) σ h0 ht (by omega)
  set σ1 := σ.setv (R 0) (σ.val LEN) with hσ1
  have e2 := writeNatM_spec cap o R σ1 (by simp [σ1, Function.update_apply, hne (show (1 : Fin 8) ≠ 0 by decide), h1])
    (by simp [σ1, Function.update_apply, hne (show (2 : Fin 8) ≠ 0 by decide), h2])
    (by simp [σ1, Function.update_apply, hne (show (3 : Fin 8) ≠ 0 by decide), h3])
    (by simp [σ1, Function.update_apply, hne (show (4 : Fin 8) ≠ 0 by decide), h4])
    (by simp [σ1, Function.update_apply, hne (show (5 : Fin 8) ≠ 0 by decide), h5])
    (by simp [σ1, Function.update_apply, hne (show (6 : Fin 8) ≠ 0 by decide), h6]) (by simp [σ1, ho])
    (by simp [σ1, Function.update_apply, hne (show (7 : Fin 8) ≠ 0 by decide), hl]; omega)
  have v10 : σ1.val (R 0) = len := by simp [σ1, hl]
  rw [v10] at e2
  set σ2 := appendO σ1 o (R 7) (marks (natWord len)) with hσ2
  have e3 := wclear_spec cap (R 0) len σ2 (by simp [σ2, Function.update_apply, hne (show (0 : Fin 8) ≠ 7 by decide), v10])
    (by simp [σ2, Function.update_apply, hne (show (0 : Fin 8) ≠ 7 by decide), v10]; omega)
  set σ3 := σ2.setv (R 0) 0 with hσ3
  have e4 := FinalPass.Hash4.wcopyR_spec cap S (R 0) T (hS 0).symm (Ne.symm hTS) (hT 0) σ3 (by simp [σ3])
    (by simp [σ3, σ2, σ1, Function.update_apply, hT 0, hT 7, (hT 0).symm, (hT 7).symm, Ne.symm (hT 0), ht])
    (by simp [σ3, σ2, σ1, Function.update_apply, hS 0, hS 7, Ne.symm (hS 0), Ne.symm (hS 7), hs]; omega)
  have v3S : σ3.val S = s := by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm (hS 0), Ne.symm (hS 7), hs]
  rw [v3S] at e4
  set σ4 := σ3.setv (R 0) s with hσ4
  have e5 := FinalPass.Hash4.wcopyR_spec cap LEN K T (Ne.symm hKL) (Ne.symm hTL) hKT σ4
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm (hK 0), Ne.symm (hK 7), hk])
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm (hT 0), Ne.symm (hT 7), ht])
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm (hL 0), Ne.symm (hL 7), hl]; omega)
  have v4L : σ4.val LEN = len := by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm (hL 0), Ne.symm (hL 7), hl]
  rw [v4L] at e5
  set σ5 := σ4.setv K len with hσ5
  have r5 : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → σ5.val (R i) = σ.val (R i) := by
    intro i hi0 hi7
    simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hK i, hne hi0, hne hi7]
  have v57 : σ5.val (R 7) = σ.val (R 7) + (marks (natWord len)).length := by
    simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hK 7, hne (show (7 : Fin 8) ≠ 0 by decide)]
  have e6 := rngLoop_spec cap o R K hK s len σ5 (by simp [σ5, σ4, Function.update_apply, hK 0])
    (by simp [σ5]) (by rw [r5 1 (by decide) (by decide), h1]) (by rw [r5 2 (by decide) (by decide), h2])
    (by rw [r5 3 (by decide) (by decide), h3]) (by rw [r5 4 (by decide) (by decide), h4])
    (by rw [r5 5 (by decide) (by decide), h5]) (by rw [r5 6 (by decide) (by decide), h6])
    (by simp [σ5, σ4, σ3, σ2, σ1, ho]) (by rw [v57]; omega)
  set σ6 := ((appendO σ5 o (R 7) (rngWords s len)).setv (R 0) (s + len)).setv K 0 with hσ6
  have e7 := wclear_spec cap (R 0) (s + len) σ6 (by simp [σ6, Function.update_apply, hK 0]) (by
    simp [σ6, Function.update_apply, hK 0]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7)))))) ?_ le_rfl) ?_
  · simp only [σ6, σ5, σ4, σ3, σ2, σ1]
    rw [← appendO_append]
    apply WState.eq
    · funext j; by_cases hj : j = o
      · subst hj; simp
      · simp [Function.update_apply, hj]
    · funext j; by_cases hj : j = o
      · subst hj; simp
      · simp [Function.update_apply, hj]
    · funext j
      by_cases hj0 : j = R 0
      · subst hj0; simp [Function.update_apply, hK 0, hne (show (0 : Fin 8) ≠ 7 by decide), h0]
      · by_cases hjK : j = K
        · subst hjK; simp [Function.update_apply, (hK 0).symm, (hK 7).symm, hk]
        · by_cases hj7 : j = R 7
          · subst hj7; simp [Function.update_apply, hK 7, hne (show (7 : Fin 8) ≠ 0 by decide)]
          · simp [Function.update_apply, hj0, hjK, hj7]
    · simp
  · unfold rangeCost
    have hw := wnCost_mono (show len ≤ s + len by omega)
    have hwc : wnCost len = (natBitLength len + 10) * (100 * len + 200) := rfl
    have hv3 : σ3.val S = s := v3S
    have hv4 : σ4.val LEN = len := v4L
    omega

end Range

end NearCubicWires.WireExponent3_5.UnionMachine.C1Rng
