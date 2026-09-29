import Proof.Wire_3_5.UnionMachine.RadSetupB2

/-! # RADIX, stage 3 (1): the level records' scan (P3:2604, list:flatten's windows)

W6's level records `winRecs MP` (stream `131` of the RADIX entry) are, per level `j = J, …, 0`, `true :: 1^{pow} 0 1^{W'} 0`
with `W' = topW J W j`. One pass (**`scanLoop`**) reads them into registers: `S1 += Σ W'` (the windows, so
`listBound (dataBits MP s) = 4·S1 + 1`, **`listBound_eq`**) and the position counter `c += |winRecs|`
(**`scanLoop_spec`** on any record word `recsW`, **`winRecs_eq`**); **`levelWord_length`**: the table word at `L` has
length `M + 2 + |winRecs| + (J+1)·L`.

Paper quantity of the main type: the fixed hash's windows `W_j` (their sum) and its table word's length. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadScan
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.ListEval (unary levels topW levelWord rowsOf)

variable {ns nr : ℕ} (cap : ℕ)

theorem rtb_app (l r : List Bool) (k : ℕ) : readTapeBit (l ++ r) (l.length + k) = readTapeBit r k := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

theorem rtb_rep : ∀ (n k : ℕ) (r : List Bool), k < n → readTapeBit (List.replicate n true ++ r) k = true
  | 0, k, _, h => absurd h (Nat.not_lt_zero k)
  | n + 1, 0, r, _ => by simp [readTapeBit, List.replicate_succ]
  | n + 1, k + 1, r, h => by
    have := rtb_rep n k r (by omega)
    simpa [readTapeBit, List.replicate_succ] using this

theorem rtb_rep_end (n : ℕ) (r : List Bool) : readTapeBit (List.replicate n true ++ false :: r) n = false := by
  have := rtb_app (List.replicate n true) (false :: r) 0
  rw [List.length_replicate, Nat.add_zero] at this
  rw [this]; rfl

/-! ## Record words -/

/-- One record `true :: 1^a 0 1^b 0`. -/
def recW (ab : ℕ × ℕ) : List Bool := true :: (List.replicate ab.1 true ++ false :: (List.replicate ab.2 true ++ [false]))

/-- A record word. -/
def recsW (l : List (ℕ × ℕ)) : List Bool := l.flatMap recW

theorem recW_length (ab : ℕ × ℕ) : (recW ab).length = ab.1 + ab.2 + 3 := by
  simp [recW]; omega

/-- The scan's body: past the marker, `A += a`, `S1 += b`, counting cells in `c`. -/
def scanBody (W : Fin (ns + 1)) (c A S1 : Fin nr) : WM ns nr :=
  .seq (WM.fwdC W c) (.seq (WM.readU W c A) (WM.readU W c S1))

/-- **The scan**: every record. -/
def scanLoop (W : Fin (ns + 1)) (c A S1 : Fin nr) : WM ns nr := .whs W (scanBody W c A S1)

/-- The scan's effect: the head `n` further, `c += n`, `A += a`, `S1 += b`. -/
def scanSt (σ : WState ns nr) (W : Fin (ns + 1)) (c A S1 : Fin nr) (n a b : ℕ) : WState ns nr :=
  (((σ.seth W (σ.sh W + n)).setv c (σ.val c + n)).setv A (σ.val A + a)).setv S1 (σ.val S1 + b)

section
variable (W : Fin (ns + 1)) (c A S1 : Fin nr) (hcA : c ≠ A) (hcS : c ≠ S1) (hAS : A ≠ S1)
include hcA hcS hAS

theorem scanSt_val_c (σ : WState ns nr) (n a b : ℕ) : (scanSt σ W c A S1 n a b).val c = σ.val c + n := by
  simp [scanSt, Function.update_of_ne hcS, Function.update_of_ne hcA]

theorem scanSt_val_A (σ : WState ns nr) (n a b : ℕ) : (scanSt σ W c A S1 n a b).val A = σ.val A + a := by
  simp [scanSt, Function.update_of_ne hAS]

theorem scanSt_val_S (σ : WState ns nr) (n a b : ℕ) : (scanSt σ W c A S1 n a b).val S1 = σ.val S1 + b := by
  simp [scanSt]

theorem scanSt_sh (σ : WState ns nr) (n a b : ℕ) : (scanSt σ W c A S1 n a b).sh W = σ.sh W + n := by
  simp [scanSt]

theorem scanSt_st (σ : WState ns nr) (n a b : ℕ) : (scanSt σ W c A S1 n a b).st = σ.st := by
  simp [scanSt]

theorem scanSt_scanSt (σ : WState ns nr) (n a b n' a' b' : ℕ) :
    scanSt (scanSt σ W c A S1 n a b) W c A S1 n' a' b' = scanSt σ W c A S1 (n + n') (a + a') (b + b') := by
  apply WState.eq
  · funext j
    by_cases hj : j = W
    · subst hj; simp [scanSt]; omega
    · simp [scanSt, Function.update_of_ne hj]
  · simp [scanSt]
  · funext r
    by_cases h1 : r = S1
    · subst h1; simp [scanSt]; omega
    · by_cases h2 : r = A
      · subst h2; simp [scanSt, Function.update_of_ne h1]; omega
      · by_cases h3 : r = c
        · subst h3; simp [scanSt, Function.update_of_ne h1, Function.update_of_ne h2]; omega
        · simp [scanSt, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp [scanSt]

theorem scanSt_zero (σ : WState ns nr) : scanSt σ W c A S1 0 0 0 = σ := by
  apply WState.eq
  · funext j
    by_cases hj : j = W
    · subst hj; simp [scanSt]
    · simp [scanSt, Function.update_of_ne hj]
  · simp [scanSt]
  · funext r
    by_cases h1 : r = S1
    · subst h1; simp [scanSt]
    · by_cases h2 : r = A
      · subst h2; simp [scanSt, Function.update_of_ne h1]
      · by_cases h3 : r = c
        · subst h3; simp [scanSt, Function.update_of_ne h1, Function.update_of_ne h2]
        · simp [scanSt, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp [scanSt]

/-- One record at the head. -/
theorem scanBody_spec (σ : WState ns nr) (pre rest : List Bool) (a b : ℕ) (hst : σ.st W = pre ++ recW (a, b) ++ rest)
    (hsh : σ.sh W = pre.length) (hc : σ.val c + (a + b + 3) ≤ cap) (hA : σ.val A + a ≤ cap)
    (hS : σ.val S1 + b ≤ cap) :
    WExec cap (scanBody W c A S1) σ (scanSt σ W c A S1 (a + b + 3) a b) (11 * (a + b) + 22) := by
  have e1 := wfwdC_spec cap W c σ (by omega)
  set σ1 := (σ.seth W (σ.sh W + 1)).setv c (σ.val c + 1) with hσ1
  have eX : pre ++ recW (a, b) ++ rest =
      (pre ++ [true]) ++ (List.replicate a true ++ false :: (List.replicate b true ++ false :: rest)) := by
    simp [recW]
  have hst1 : σ1.st W = (pre ++ [true]) ++ (List.replicate a true ++ false :: (List.replicate b true ++ false :: rest)) := by
    simp only [σ1, WState.setv_st, WState.seth_st]; rw [hst, eX]
  have hsh1 : σ1.sh W = (pre ++ [true]).length := by simp [σ1, hsh]
  have e2 := wreadU_spec cap W c A hcA a σ1
    (fun k hk => by rw [hst1, hsh1, rtb_app, List.append_cons (List.replicate a true), List.append_assoc]
                    exact rtb_rep a k _ hk)
    (by rw [hst1, hsh1, rtb_app]; exact rtb_rep_end a _)
    (by simp [σ1, Function.update_of_ne (Ne.symm hcA)]; omega)
    (by simp [σ1, Function.update_of_ne (Ne.symm hcA)]; omega)
  set σ2 := ((σ1.seth W (σ1.sh W + a + 1)).setv c (σ1.val c + a + 1)).setv A (σ1.val A + a) with hσ2
  have eY : (pre ++ [true]) ++ (List.replicate a true ++ false :: (List.replicate b true ++ false :: rest)) =
      ((pre ++ [true]) ++ (List.replicate a true ++ [false])) ++ (List.replicate b true ++ false :: rest) := by simp
  have hst2 : σ2.st W = ((pre ++ [true]) ++ (List.replicate a true ++ [false])) ++ (List.replicate b true ++ false :: rest) := by
    simp only [σ2, WState.setv_st, WState.seth_st]; rw [hst1, eY]
  have hsh2 : σ2.sh W = ((pre ++ [true]) ++ (List.replicate a true ++ [false])).length := by
    simp only [σ2, WState.setv_sh, WState.seth_sh, Function.update_self]; rw [hsh1]; simp; omega
  have e3 := wreadU_spec cap W c S1 hcS b σ2
    (fun k hk => by rw [hst2, hsh2, rtb_app]; exact rtb_rep b k _ hk)
    (by rw [hst2, hsh2, rtb_app]; exact rtb_rep_end b _)
    (by simp [σ2, σ1, Function.update_of_ne hcA, Function.update_of_ne hcS, Function.update_of_ne hAS, Function.update_of_ne (Ne.symm hcA), Function.update_of_ne (Ne.symm hcS), Function.update_of_ne (Ne.symm hAS)]; omega)
    (by simp [σ2, σ1, Function.update_of_ne hcA, Function.update_of_ne hcS, Function.update_of_ne hAS, Function.update_of_ne (Ne.symm hcA), Function.update_of_ne (Ne.symm hcS), Function.update_of_ne (Ne.symm hAS)]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext j
    by_cases hj : j = W
    · subst hj; simp [σ2, σ1, scanSt]; omega
    · simp [σ2, σ1, scanSt, Function.update_of_ne hj]
  · simp [σ2, σ1, scanSt]
  · funext r
    by_cases h1 : r = S1
    · subst h1
      simp [σ2, σ1, scanSt, Function.update_of_ne (Ne.symm hAS), Function.update_of_ne (Ne.symm hcS)]
    · by_cases h2 : r = A
      · subst h2
        simp [σ2, σ1, scanSt, Function.update_of_ne h1, Function.update_of_ne (Ne.symm hcA)]
      · by_cases h3 : r = c
        · subst h3
          simp [σ2, σ1, scanSt, Function.update_of_ne h1, Function.update_of_ne h2]; omega
        · simp [σ2, σ1, scanSt, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp [σ2, σ1, scanSt]

/-- **The scan over a record word** at the head, the stream ending after it. -/
theorem scanLoop_spec : ∀ (l : List (ℕ × ℕ)) (σ : WState ns nr) (pre : List Bool),
    σ.st W = pre ++ recsW l → σ.sh W = pre.length → σ.val c + (recsW l).length ≤ cap →
    σ.val A + (l.map Prod.fst).sum ≤ cap → σ.val S1 + (l.map Prod.snd).sum ≤ cap →
    WExec cap (scanLoop W c A S1) σ (scanSt σ W c A S1 (recsW l).length (l.map Prod.fst).sum (l.map Prod.snd).sum)
      (13 * (recsW l).length + 1)
  | [], σ, pre, hst, hsh, _, _, _ => by
    have hb : wbit σ W = false := by
      unfold wbit; rw [hst, hsh]; unfold readTapeBit; simp [recsW]
    simp only [recsW, List.flatMap_nil, List.length_nil, List.map_nil, List.sum_nil]
    rw [scanSt_zero W c A S1 hcA hcS hAS]
    exact WExec.mono (WExec.whsF hb) (by omega)
  | (a, b) :: l, σ, pre, hst, hsh, hc, hA, hS => by
    have hrl : recsW ((a, b) :: l) = recW (a, b) ++ recsW l := by simp [recsW]
    have hlen : (recsW ((a, b) :: l)).length = (a + b + 3) + (recsW l).length := by
      rw [hrl, List.length_append, recW_length]
    have hsA : ((a, b) :: l).map Prod.fst = a :: l.map Prod.fst := rfl
    have hsB : ((a, b) :: l).map Prod.snd = b :: l.map Prod.snd := rfl
    simp only [hsA, hsB, List.sum_cons] at hA hS ⊢
    rw [hlen] at hc ⊢
    have hb : wbit σ W = true := by
      unfold wbit
      rw [hst, hsh, hrl, show pre.length = pre.length + 0 from rfl, rtb_app]
      simp [recW, readTapeBit]
    have e1 := scanBody_spec cap W c A S1 hcA hcS hAS σ pre (recsW l) a b (by rw [hst, hrl, List.append_assoc]) hsh
      (by omega) (by omega) (by omega)
    set σ1 := scanSt σ W c A S1 (a + b + 3) a b with hσ1
    have e2 := scanLoop_spec l σ1 (pre ++ recW (a, b))
      (by rw [hσ1, scanSt_st W c A S1 hcA hcS hAS, hst, hrl, List.append_assoc])
      (by rw [hσ1, scanSt_sh W c A S1 hcA hcS hAS, hsh, List.length_append, recW_length])
      (by rw [hσ1, scanSt_val_c W c A S1 hcA hcS hAS]; omega)
      (by rw [hσ1, scanSt_val_A W c A S1 hcA hcS hAS]; omega)
      (by rw [hσ1, scanSt_val_S W c A S1 hcA hcS hAS]; omega)
    rw [hσ1, scanSt_scanSt W c A S1 hcA hcS hAS] at e2
    exact WExec.mono (WExec.whsT hb e1 e2) (by omega)

end

/-! ## The level records -/

theorem winRec_eq (J : ℕ) (Wf : ℕ → ℕ) (j : ℕ) :
    FinalPass.Hash4.winRec J Wf j = recW (FinalPass.ListEval.pow (topW J Wf j), topW J Wf j) := by
  simp [FinalPass.Hash4.winRec, recW, unary]

/-- **W6's level records are a record word.** -/
theorem winRecs_eq (MP : Filters.MajorantParams) :
    PrimThrW.Joins.winRecs MP = recsW ((levels MP.J).map fun j => (FinalPass.ListEval.pow (topW MP.J MP.W j),
      topW MP.J MP.W j)) := by
  unfold PrimThrW.Joins.winRecs recsW
  rw [List.flatMap_map]
  exact List.flatMap_congr fun j _ => winRec_eq MP.J MP.W j

theorem listSum_range (f : ℕ → ℕ) : ∀ J : ℕ, ((List.range J).map f).sum = ∑ j ∈ Finset.range J, f j
  | 0 => by simp
  | J + 1 => by rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, listSum_range f J]; simp

theorem sum_topW (J : ℕ) (Wf : ℕ → ℕ) :
    ((levels J).map fun j => topW J Wf j).sum = ∑ j ∈ Finset.range J, Wf j := by
  unfold levels
  rw [List.map_reverse, List.sum_reverse, List.range_succ, List.map_append, List.sum_append]
  have h1 : ((List.range J).map fun j => topW J Wf j) = (List.range J).map Wf := by
    apply List.map_congr_left
    intro j hj
    have hne : j ≠ J := by have := List.mem_range.mp hj; omega
    simp [topW, hne]
  rw [h1, listSum_range]
  simp [topW]

/-- **The list bound from the windows' sum.** -/
theorem listBound_eq (D : Lists.ListData) :
    ListMachine.listBound D = 4 * ∑ j ∈ Finset.range D.J, D.W j + 1 := by
  unfold ListMachine.listBound
  rw [Finset.mul_sum]

theorem sum_map_addc (f : ℕ → ℕ) (L : ℕ) : ∀ ls : List ℕ, (ls.map fun j => f j + L).sum = (ls.map f).sum + ls.length * L
  | [] => by simp
  | j :: ls => by simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_addc f L ls]; ring

/-- **The table word's length** at `L` points. -/
theorem levelWord_length (M J : ℕ) (Wf : ℕ → ℕ) (row : ℕ → List Bool) (L : ℕ) (hrow : ∀ j, (row j).length = L) :
    (levelWord M J Wf row).length = M + 2 + ((levels J).flatMap (FinalPass.Hash4.winRec J Wf)).length +
      (J + 1) * L := by
  unfold levelWord
  simp only [List.length_append, unary, List.length_replicate, List.length_singleton, List.length_flatMap]
  have e : ∀ j, (FinalPass.ListEval.record J Wf row j).length = (FinalPass.Hash4.winRec J Wf j).length + L := by
    intro j
    simp [FinalPass.ListEval.record, FinalPass.Hash4.winRec, unary, hrow j]; omega
  have hl : (levels J).length = J + 1 := by simp [levels]
  rw [List.map_congr_left (fun j _ => e j), sum_map_addc (fun j => (FinalPass.Hash4.winRec J Wf j).length) L, hl]
  ring

end NearCubicWires.WireExponent3_5.UnionMachine.RadScan
