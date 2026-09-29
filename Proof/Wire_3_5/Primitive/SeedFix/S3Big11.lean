import Proof.Wire_3_5.Primitive.SeedFix.S3Big10

/-! # S3, part 17: the evaluator's capacity and cost are polynomial in the call's size

"The implementation loops are polynomial in these descriptions and in `n`" (P3:3181-3183). At a SYM call `k`, with
`symSize k = n + Σ|words| + Σ numbers` (the seam's `ptSize`, P3:3170-3178's reported-list descriptions):
* **`symCaps`**: capacity `100·(symSize+1)³` meets every capacity the evaluator needs (`CircCap` at every seed and
  circuit, the template and table lengths, the seed count);
* **`evalCost_le`**: the evaluator's steps are at most `1100000·(symSize+1)⁶`.
Pieces: the stage costs (`coreCost_le` … `costB_le`, the majority machine `majBound_le` through its record loop
`recLoopCost_le`), and the call's atoms against its size (`size_nums`, `size_words`, `tablesJ_len`, `M_le_templ`,
`walkLen_le_tab`).

Paper quantity of the main types: the evaluator's capacity and step bounds against the call's description size. -/

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
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Term NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall)

/-! ## Powers -/

theorem pows (X : ℕ) (hX : 1 ≤ X) :
    1 ≤ X ^ 2 ∧ X ≤ X ^ 2 ∧ X ^ 2 ≤ X ^ 3 ∧ X ^ 3 ≤ X ^ 4 ∧ X ^ 4 ≤ X ^ 5 ∧ X ^ 5 ≤ X ^ 6 := by
  have h1 : X ^ 1 ≤ X ^ 2 := Nat.pow_le_pow_right hX (by norm_num)
  rw [pow_one] at h1
  exact ⟨le_trans hX h1, h1, Nat.pow_le_pow_right hX (by norm_num), Nat.pow_le_pow_right hX (by norm_num),
    Nat.pow_le_pow_right hX (by norm_num), Nat.pow_le_pow_right hX (by norm_num)⟩

/-! ## The corner word's cost -/

theorem coreCost_le (h n X : ℕ) (hh : h ≤ X) (hn : n ≤ X) (hX : 1 ≤ X) : coreCost h n ≤ 460 * X ^ 2 := by
  obtain ⟨q1, q2, -, -, -, -⟩ := pows X hX
  have a : n * (110 * h + 110) ≤ X * (110 * X + 110) := Nat.mul_le_mul hn (by omega)
  have b : X * (110 * X + 110) = 110 * X ^ 2 + 110 * X := by ring
  unfold coreCost
  omega

theorem gateCost_le (h n X : ℕ) (hh : h ≤ X) (hn : n + 1 ≤ X) (hX : 1 ≤ X) : gateCost h n ≤ 2000 * X ^ 2 := by
  obtain ⟨q1, q2, -, -, -, -⟩ := pows X hX
  have c := coreCost_le h n X hh (by omega) hX
  have a : (n + 1) * (2 * (2 * h + 1)) ≤ X * (2 * (2 * X + 1)) := Nat.mul_le_mul hn (by omega)
  have b : X * (2 * (2 * X + 1)) = 4 * X ^ 2 + 2 * X := by ring
  unfold gateCost
  omega

theorem cwCost_le (h n m X : ℕ) (hh : h ≤ X) (hn : n + 1 ≤ X) (hm : m ≤ X) (hX : 1 ≤ X) :
    cwCost h n m ≤ 2200 * X ^ 3 := by
  obtain ⟨q1, q2, q3, -, -, -⟩ := pows X hX
  have g := gateCost_le h n X hh hn hX
  have a : m * (gateCost h n + 2) ≤ X * (2000 * X ^ 2 + 2) := Nat.mul_le_mul hm (by omega)
  have b : X * (2000 * X ^ 2 + 2) = 2000 * X ^ 3 + 2 * X := by ring
  have c1 : (n + 1) * (2 * (2 * h + 1)) ≤ X * (2 * (2 * X + 1)) := Nat.mul_le_mul hn (by omega)
  have c2 : X * (2 * (2 * X + 1)) = 4 * X ^ 2 + 2 * X := by ring
  have d : m * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ X * (1 + (4 * X ^ 2 + 2 * X)) := Nat.mul_le_mul hm (by omega)
  have d2 : X * (1 + (4 * X ^ 2 + 2 * X)) = 4 * X ^ 3 + 2 * X ^ 2 + X := by ring
  unfold cwCost
  omega

/-! ## The majority machine's cost -/

theorem recLoopCost_le (M J : ℕ) (W : ℕ → ℕ) (L : ℕ) :
    Maj.recLoopCost J W L (levels J) ≤ 39 * Maj.lwLen M J W L := by
  unfold Maj.recLoopCost Maj.lwLen levelWord
  simp only [List.length_append, List.length_flatMap, List.length_singleton]
  have h : ∀ j ∈ levels J, Maj.recCost (pow (topW J W j)) (topW J W j) L + 2 ≤
      38 * (record J W (fun _ => List.replicate L false) j).length := by
    intro j _
    rw [Maj.record_len]
    simp only [List.length_replicate]
    unfold Maj.recCost
    omega
  have hs := List.sum_le_sum h
  rw [List.sum_map_mul_left] at hs
  omega

theorem majBound_le (P : FlatListParams) (e : P.FlatSeed) (L X : ℕ) (hM : P.M ≤ X) (hw : P.walkLen ≤ X)
    (hlw : Maj.lwLen P.M P.base.J P.base.W L ≤ X) (hL : L ≤ X) (hft : (flatTable P e L).length ≤ X) (hX : 1 ≤ X) :
    Maj.majBound P e L ≤ 120000 * X ^ 5 := by
  obtain ⟨q1, q2, q3, q4, q5, -⟩ := pows X hX
  have hr := recLoopCost_le P.M P.base.J P.base.W L
  have hmc : mainCost (4 * (Maj.lwLen P.M P.base.J P.base.W L + L + 1)) ≤ 109850 * X ^ 3 := by
    unfold mainCost
    have c : 4 * (Maj.lwLen P.M P.base.J P.base.W L + L + 1) + 1 ≤ 13 * X := by omega
    calc 50 * (4 * (Maj.lwLen P.M P.base.J P.base.W L + L + 1) + 1) *
          (4 * (Maj.lwLen P.M P.base.J P.base.W L + L + 1) + 1) * (4 * (Maj.lwLen P.M P.base.J P.base.W L + L + 1) + 1)
        ≤ 50 * (13 * X) * (13 * X) * (13 * X) := by gcongr
      _ = 109850 * X ^ 3 := by ring
  have hv : Maj.visitBound P L ≤ 110000 * X ^ 3 := by
    unfold Maj.visitBound Maj.visitCost Maj.copyCost
    omega
  have hs : Maj.sBodyBound P e L ≤ 111000 * X ^ 4 := by
    have a : P.walkLen * (Maj.visitBound P L + 2) ≤ X * (110000 * X ^ 3 + 2) := Nat.mul_le_mul hw (by omega)
    have b : X * (110000 * X ^ 3 + 2) = 110000 * X ^ 4 + 2 * X := by ring
    unfold Maj.sBodyBound Maj.checkCost
    omega
  have a : P.M * (Maj.sBodyBound P e L + 2) ≤ X * (111000 * X ^ 4 + 2) := Nat.mul_le_mul hM (by omega)
  have b : X * (111000 * X ^ 4 + 2) = 111000 * X ^ 5 + 2 * X := by ring
  unfold Maj.majBound
  omega

theorem costA_le (h n g : ℕ) (P : FlatListParams) (e : P.FlatSeed) (X : ℕ) (hh : h ≤ X) (hn : n + 1 ≤ X)
    (hg : g ≤ X) (hM : P.M ≤ X) (hw : P.walkLen ≤ X) (hlw : Maj.lwLen P.M P.base.J P.base.W g ≤ X)
    (hft : (flatTable P e g).length ≤ X) (hX : 1 ≤ X) : costA h n g P e ≤ 125000 * X ^ 5 := by
  obtain ⟨q1, q2, q3, q4, q5, -⟩ := pows X hX
  have c := cwCost_le h n g X hh hn hg hX
  have m := majBound_le P e g X hM hw hlw hg hft hX
  unfold costA passCost
  omega

theorem costB_le (g : ℕ) (P : FlatListParams) (e : P.FlatSeed) (W X : ℕ) (hg : g ≤ X) (hW : W ≤ X) (hM : P.M ≤ X)
    (hw : P.walkLen ≤ X) (hlw : Maj.lwLen P.M P.base.J P.base.W g ≤ X) (hft : (flatTable P e g).length ≤ X)
    (hX : 1 ≤ X) : costB g P e W ≤ 125000 * X ^ 5 := by
  obtain ⟨q1, q2, q3, q4, q5, -⟩ := pows X hX
  have m := majBound_le P e g X hM hw hlw hg hft hX
  unfold costB passCost cost8
  omega

/-! ## The call's atoms against its size -/

/-- **The call's description size** (the seam's `ptSize` at S3's words and numbers). -/
def symSize (k : SymCall) : ℕ := k.P.n + (∑ i, (symWords k i).length) + ∑ i, symNums k i

theorem size_nums (k : SymCall) (i : Fin 18) : symNums k i ≤ symSize k := by
  have := Finset.single_le_sum (f := fun i => symNums k i) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold symSize
  omega

theorem size_words (k : SymCall) (w : Fin 16) : (symWords k w).length ≤ symSize k := by
  have := Finset.single_le_sum (f := fun w => (symWords k w).length) (fun i _ => Nat.zero_le _) (Finset.mem_univ w)
  unfold symSize
  omega

theorem size_n (k : SymCall) : k.P.n ≤ symSize k := by unfold symSize; omega

theorem tablesJ_len (k : SymCall) (j : Fin 4) :
    (tablesJ k j).length = Fintype.card k.Pl.FlatSeed * tabLen k j := by
  unfold tablesJ
  rw [List.length_flatMap]
  have e : ((List.finRange (Fintype.card k.Pl.FlatSeed)).map fun i =>
      (flatTable k.Pl (seedOf k i) (gatesJ k j).length).length) =
      (List.finRange (Fintype.card k.Pl.FlatSeed)).map (fun _ => tabLen k j) :=
    List.map_congr_left (fun i _ => tabLen_eq k j _)
  rw [e, List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]

theorem M_le_templ (k : SymCall) (j : Fin 4) : k.Pl.M ≤ (templJ k j).length := by
  unfold templJ levelWord unary
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

theorem walkLen_le_tab (k : SymCall) (j : Fin 4) : k.Pl.walkLen ≤ tabLen k j := by
  unfold tabLen
  rw [flatTable_len]
  have : k.Pl.walkLen ≤ k.Pl.walkLen * (1 + (k.Pl.base.J + 1) * (2 * (gatesJ k j).length + 1)) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem topJ_le (k : SymCall) (j : Fin 4) : (topJ k j).length ≤ symSize k := by
  have h := size_words k (wIdx 1 j)
  rw [words_1, frame_len] at h
  omega

theorem atoms (k : SymCall) (j : Fin 4) :
    (gatesJ k j).length ≤ symSize k ∧ tabH (gatesJ k j) ≤ symSize k ∧ tabLen k j ≤ symSize k ∧
      (templJ k j).length ≤ symSize k ∧ Fintype.card k.Pl.FlatSeed * tabLen k j ≤ symSize k ∧
      Fintype.card k.Pl.FlatSeed ≤ symSize k ∧ k.Pl.M ≤ symSize k ∧ k.Pl.walkLen ≤ symSize k := by
  have h0 := size_nums k (nIdx 0 j)
  have h1 := size_nums k (nIdx 1 j)
  have h2 := size_nums k (nIdx 2 j)
  have h3 := size_nums k (nIdx 3 j)
  have hN := size_nums k 1
  have hT := size_words k (wIdx 2 j)
  rw [nums_0] at h0
  rw [nums_1] at h1
  rw [nums_2] at h2
  rw [nums_3] at h3
  rw [words_2, tablesJ_len] at hT
  have hN' : symNums k 1 = Fintype.card k.Pl.FlatSeed := rfl
  rw [hN'] at hN
  have hm := M_le_templ k j
  have hw := walkLen_le_tab k j
  exact ⟨h0, h1, h2, h3, hT, hN, by omega, by omega⟩

/-! ## The capacity -/

theorem symCaps (k : SymCall) (cap : ℕ) (hneed : 100 * (symSize k + 1) ^ 3 ≤ cap) :
    (∀ (i : Fin (Fintype.card k.Pl.FlatSeed)) (j : Fin 4), j.val < k.a →
      CircCap cap k.Pl (seedOf k i) k.P.n (gatesJ k j) (topJ k j).length) ∧
    (∀ j : Fin 4, (templJ k j).length ≤ cap) ∧ (∀ j : Fin 4, Fintype.card k.Pl.FlatSeed * tabLen k j ≤ cap) ∧
    4 ≤ cap ∧ Fintype.card k.Pl.FlatSeed + 1 ≤ cap := by
  obtain ⟨X, hXd⟩ : ∃ X, X = symSize k + 1 := ⟨_, rfl⟩
  rw [← hXd] at hneed
  have hX : 1 ≤ X := by omega
  obtain ⟨q1, q2, q3, -, -, -⟩ := pows X hX
  have hn := size_n k
  have hA := atoms k
  refine ⟨fun i j _ => ?_, fun j => by have := (hA j).2.2.2.1; omega, fun j => by have := (hA j).2.2.2.2.1; omega,
    by omega, by have := (hA 0).2.2.2.2.2.1; omega⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hA j
  have hT := topJ_le k j
  have hft := tabLen_eq k j (seedOf k i)
  have a : (gatesJ k j).length * (1 + (k.P.n + 1) * (2 * (2 * tabH (gatesJ k j) + 1))) ≤
      X * (1 + X * (2 * (2 * X + 1))) := Nat.mul_le_mul (by omega) (by
        have := Nat.mul_le_mul (show k.P.n + 1 ≤ X by omega) (show 2 * (2 * tabH (gatesJ k j) + 1) ≤ 2 * (2 * X + 1)
          by omega)
        omega)
  have b : X * (1 + X * (2 * (2 * X + 1))) = 4 * X ^ 3 + 2 * X ^ 2 + X := by ring
  have hlw : Maj.lwLen k.Pl.M k.Pl.base.J k.Pl.base.W (gatesJ k j).length = (templJ k j).length := rfl
  exact ⟨by omega, by omega, by omega, by omega, by omega,
    ⟨by rw [hlw]; omega, by rw [hft]; omega, by omega, by omega⟩, by unfold capOf8; omega, by omega⟩

/-! ## The steps -/

theorem guardCost_le (k : SymCall) (j : Fin 4) : guardCost k j ≤ 260000 * (symSize k + 1) ^ 5 := by
  obtain ⟨X, hXd⟩ : ∃ X, X = symSize k + 1 := ⟨_, rfl⟩
  rw [← hXd]
  have hX : 1 ≤ X := by omega
  obtain ⟨q1, q2, q3, q4, q5, -⟩ := pows X hX
  have hn := size_n k
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := atoms k j
  have hT := topJ_le k j
  have hlw : Maj.lwLen k.Pl.M k.Pl.base.J k.Pl.base.W (gatesJ k j).length = (templJ k j).length := rfl
  have hft := tabLen_eq k j (seedOf k ⟨0, PrimAsm.Enum.card_flatSeed_pos k.Pl⟩)
  have cA := costA_le (tabH (gatesJ k j)) k.P.n (gatesJ k j).length k.Pl
    (seedOf k ⟨0, PrimAsm.Enum.card_flatSeed_pos k.Pl⟩) X (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hlw]; omega) (by rw [hft]; omega) hX
  have cB := costB_le (gatesJ k j).length k.Pl (seedOf k ⟨0, PrimAsm.Enum.card_flatSeed_pos k.Pl⟩)
    (topJ k j).length X (by omega) (by omega) (by omega) (by omega) (by rw [hlw]; omega) (by rw [hft]; omega) hX
  unfold guardCost
  omega

theorem evalCost_le (k : SymCall) : evalCost k ≤ 1100000 * (symSize k + 1) ^ 6 := by
  have g0 := guardCost_le k 0
  have g1 := guardCost_le k 1
  have g2 := guardCost_le k 2
  have g3 := guardCost_le k 3
  obtain ⟨X, hXd⟩ : ∃ X, X = symSize k + 1 := ⟨_, rfl⟩
  rw [← hXd] at g0 g1 g2 g3 ⊢
  have hX : 1 ≤ X := by omega
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := pows X hX
  have hN := (atoms k 0).2.2.2.2.2.1
  have t : ∀ j : Fin 4, Fintype.card k.Pl.FlatSeed * adv k j ≤ X := fun j => by
    have := (atoms k j).2.2.2.2.1
    have := Nat.mul_le_mul_left (Fintype.card k.Pl.FlatSeed) (adv_le k j)
    omega
  have t0 := t 0
  have t1 := t 1
  have t2 := t 2
  have t3 := t 3
  have a : Fintype.card k.Pl.FlatSeed * (bodyCost k + 4) ≤ X * (1040000 * X ^ 5 + 104) :=
    Nat.mul_le_mul (by omega) (by unfold bodyCost; omega)
  have b : X * (1040000 * X ^ 5 + 104) = 1040000 * X ^ 6 + 104 * X := by ring
  unfold evalCost
  omega

end NearCubicWires.WireExponent3_5.PrimT.S3
