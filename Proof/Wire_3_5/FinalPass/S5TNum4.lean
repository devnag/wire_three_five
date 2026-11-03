import Proof.Wire_3_5.FinalPass.S5TNum3Base

/-! # S5-THR, part 38: the THR words' sizes and the data stage's side conditions (P3:2220-2231, 3170-3181)

At a fixed hash's parameters `M, t, B_*, J, ℓ₀ ≤ Y`: stage 4's input word `winWord` and table `levelWord`, the seed's
coefficients and their word, all within `1000·Y³` (**`mp_words_le`**, via **`winWord_le`**); the unary counts'
word (**`unaryList_len`**, **`counts_le`**); a power's coefficient absorbed by the base (**`kn_le_pow`**); the top
front's count conditions (**`tf2ok_of`**).

Paper quantity of the main types: the fixed hash's words and the call's counts, polynomial in the call's size
(P3:2220-2231). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.SupplierPipeline

section Sz

/-- **Stage 4's input word** at level widths `≤ Wm`. -/
theorem winWord_le (M L J Wm : ℕ) (Wf : ℕ → ℕ) (hW : ∀ j, Wf j ≤ Wm) :
    (Hash4.winWord M L J Wf).length ≤ M + L + J + 4 + (J + 1) * (5 * Wm + 5) := by
  unfold Hash4.winWord ListEval.unary
  simp only [List.length_append, List.length_replicate, List.length_singleton, List.length_flatMap]
  have hs := List.sum_le_card_nsmul ((ListEval.levels J).map fun j => (Hash4.winRec J Wf j).length)
    (5 * Wm + 5) (fun x hx => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      have hp := ThrSz.pow_le (ListEval.topW J Wf j)
      have ht : ListEval.topW J Wf j ≤ Wm := by
        unfold ListEval.topW; split_ifs
        · exact Nat.zero_le _
        · exact hW j
      simp only [Hash4.winRec, ListEval.unary, List.length_cons, List.length_append, List.length_replicate,
        List.length_singleton, List.length_nil]
      omega)
  rw [smul_eq_mul, List.length_map, ListEval.levels_length] at hs
  omega

/-- **The fixed hash's words** at parameters `≤ Y`. -/
theorem mp_words_le (MP : Filters.MajorantParams) (s : Fin (2 * MP.t * MP.ell0) → Bool) (Y : ℕ) (hY : 1 ≤ Y)
    (hM : MP.M ≤ Y) (ht : MP.t ≤ Y) (hB : MP.Bstar ≤ Y) (hJ : MP.J ≤ Y) (hl : MP.ell0 ≤ Y) :
    (Hash4.winWord MP.M MP.M MP.J MP.W).length ≤ 1000 * Y ^ 3 ∧
    (ListEval.levelWord MP.M MP.J MP.W (ListEval.rowsOf (MajorantBits.dataBits MP s) MP.M)).length ≤
      1000 * Y ^ 3 ∧
    (Hash4.coefsRev (MajorantBits.coefVal MP s)).length ≤ 2 * Y ∧
    (Hash4.seedWord MP.ell0 (Hash4.coefsRev (MajorantBits.coefVal MP s))).length ≤ 10 * Y ^ 2 := by
  have htB : MP.t * MP.Bstar ≤ Y * Y := Nat.mul_le_mul ht hB
  have y2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have y3 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by norm_num)
  have e2 : Y * Y = Y ^ 2 := by ring
  have hWm : ∀ j, MP.W j ≤ 76 * Y ^ 2 := fun j => by have := ThrSz.majW_le MP j; omega
  have hlen : (Hash4.coefsRev (MajorantBits.coefVal MP s)).length = 2 * MP.t := by
    simp [Hash4.coefsRev]
  have hJY : (MP.J + 1) * (5 * (76 * Y ^ 2) + 5) ≤ (Y + 1) * (380 * Y ^ 2 + 5) := Nat.mul_le_mul (by omega) (by omega)
  have hJY2 : (MP.J + 1) * (5 * (76 * Y ^ 2) + 5 + MP.M) ≤ (Y + 1) * (380 * Y ^ 2 + 5 + Y) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hp1 : (Y + 1) * (380 * Y ^ 2 + 5) ≤ 770 * Y ^ 3 := by nlinarith
  have hp2 : (Y + 1) * (380 * Y ^ 2 + 5 + Y) ≤ 800 * Y ^ 3 := by nlinarith
  have hy13 : Y ≤ Y ^ 3 := le_trans y2 y3
  refine ⟨?_, ?_, by omega, ?_⟩
  · have := winWord_le MP.M MP.M MP.J (76 * Y ^ 2) MP.W hWm
    omega
  · have := ThrSz.levelWord_le MP.M MP.J MP.W (ListEval.rowsOf (MajorantBits.dataBits MP s) MP.M) (76 * Y ^ 2)
      MP.M hWm (fun j => by simp [ListEval.rowsOf])
    omega
  · rw [Hash4.seedWord_length, hlen]
    have : 2 * MP.t * (2 * MP.ell0 + 2) ≤ 2 * Y * (2 * Y + 2) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

theorem unaryList_len (cs : List ℕ) : (PrimAsm.Data.unaryList cs).length = cs.sum + cs.length := by
  induction cs with
  | nil => simp [PrimAsm.Data.unaryList]
  | cons c cs ih =>
    simp only [PrimAsm.Data.unaryList, List.flatMap_cons, List.length_append, List.length_replicate,
      List.length_singleton, List.sum_cons, List.length_cons, List.length_nil] at ih ⊢
    omega

/-- The tuple's gate list within the descriptions. -/
theorem tupleG_le {n a' : ℕ} (ha : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) : (PrimT.ThrTab.tupleG Cs).length ≤ 4 * (n + 1) ^ 26 := by
  unfold PrimT.ThrTab.tupleG
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc _ ≤ ∑ _j : Fin a', (n + 1) ^ 26 := Finset.sum_le_sum (fun j _ => by
          simp only [Function.comp_apply, List.length_map]; exact (ThrSz.occ_len (Cs j)).trans (hd j))
    _ = a' * (n + 1) ^ 26 := by simp
    _ ≤ 4 * (n + 1) ^ 26 := Nat.mul_le_mul_right _ ha

/-- **The data stage's count word** at carriers within the envelope. -/
theorem counts_le {n a' : ℕ} (ha : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (hcar : carriers.length ≤ 2)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (he : ∀ X ∈ carriers, X.WithinEnvelope 26) :
    (PrimAsm.Data.unaryList (PrimAsm.ThrData.thrCounts Cs carriers)).length ≤ 6 * (n + 1) ^ 26 + 3 := by
  rw [unaryList_len]
  unfold PrimAsm.ThrData.thrCounts
  have hg := tupleG_le ha Cs hd
  have hs := List.sum_le_card_nsmul (carriers.map (·.length)) ((n + 1) ^ 26) (fun x hx => by
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
    exact (he X hX).1)
  rw [smul_eq_mul, List.length_map] at hs
  have hs2 : carriers.length * (n + 1) ^ 26 ≤ 2 * (n + 1) ^ 26 := Nat.mul_le_mul_right _ hcar
  simp only [List.sum_append, List.sum_cons, List.sum_nil, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  omega

/-- A power's coefficient absorbed by the base. -/
theorem kn_le_pow {K n d y e : ℕ} (hK : K ≤ y) (hn : n + 1 ≤ y) (hde : d + 1 ≤ e) (hy : 1 ≤ y) :
    K * (n + 1) ^ d ≤ y ^ e :=
  calc K * (n + 1) ^ d ≤ y * y ^ d := Nat.mul_le_mul hK (Nat.pow_le_pow_left hn d)
    _ = y ^ (d + 1) := by ring
    _ ≤ y ^ e := Nat.pow_le_pow_right hy hde

/-- **The top front's count conditions** at `V + (n+1)^{26}`, once a length `B` bounds `n` and every code's word. -/
theorem tf2ok_of {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (V B : ℕ)
    (ha : a' ≤ 4) (hk : codes.length ≤ 2) (hn : n + 1 ≤ B)
    (hx : ∀ x ∈ PrimAsm.ReqBridge.thrCodes Cs, (RepairRepresentation.natWord x).length ≤ B)
    (hy : ∀ y ∈ codes, (RepairRepresentation.natWord y).length ≤ B) (hV : 3 * B + 300 ≤ V) :
    PrimThrW.TopFront2.TF2Ok Cs codes (V + (n + 1) ^ 26) := by
  have hA := PrimT.TS4.a2_le a' ha
  have hK := PrimT.TS4.a2_le codes.length (by omega)
  have hN := ThrSz.nbl_le n
  have pA : 2 ^ (natBitLength a' + 1) ≤ 300 := by
    rw [pow_succ]
    have := Nat.le_mul_of_pos_left (40 * 2 ^ natBitLength a' + 40) (show 0 < natBitLength a' + 2 by omega)
    omega
  have pK : 2 ^ (natBitLength codes.length + 1) ≤ 300 := by
    rw [pow_succ]
    have := Nat.le_mul_of_pos_left (40 * 2 ^ natBitLength codes.length + 40)
      (show 0 < natBitLength codes.length + 2 by omega)
    omega
  exact ⟨hk, by omega, by omega, by omega, fun x hxm => by have := hx x hxm; omega,
    fun y hym => by have := hy y hym; omega⟩

end Sz

end NearCubicWires.WireExponent3_5.FinalPass.S5T
