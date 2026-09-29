import Proof.Wire_3_5.Selection.CosCls3

/-! # C1.5 class bound, part 4: the whole machine (P3:1335, 1358-1360)

Paper: the selection runs in `2^{n/2+O(k)}poly(n)` time (P3:1335, 1359-1360). The parse reads the request word once
(its number fields and the `2^k` counter: at most `K·W^a·2^k`), the loop runs the `2^k` cosets, the output writes the
selected codes and the cleanup clears the registers. **`bd_costF`**: the machine's whole cost `costF parseCostF R` is
at most `K·W^a·2^k·2^{s·r/2}·2^{(n+1)/2}`, `K` and `a` independent of the request. Main declarations: `bd_gsum`,
`bd_popsT`, `bd_costA`, `bd_costB`, `bd_costC`, `bd_clean`, **`bd_costF`**. Paper quantity: the selection time. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Point NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

/-- A list's mapped sum is at most its length times a bound. -/
theorem sum_map_le {α : Type} (f : α → ℕ) (c : ℕ) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ c) → (l.map f).sum ≤ l.length * c
  | [], _ => by simp
  | a :: l, hf => by
    have ih := sum_map_le f c l (fun b hb => hf b (by simp [hb]))
    have ha := hf a (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem convRec_le (R : SelectionReq) (z : ℤ) (hz : z ∈ gInts R) :
    convRecCost z (Wof R) + 4 ≤ 9 * Lof R + 30 * Wof R + 39 := by
  have := gInts_bits R z hz
  unfold convRecCost PrimT.countCost PrimT.wordCost
  omega

/-- The gate records' conversions. -/
theorem bd_gsum {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h) :
    Bd ex (fun R _ => ((gInts R).map fun z => convRecCost z (Wof R) + 4).sum) := by
  refine bd_mono (g := fun R _ => Lof R * (9 * Lof R + 30 * Wof R + 39)) (fun R _ => ?_) ?_
  · have h1 := sum_map_le (fun z => convRecCost z (Wof R) + 4) _ (gInts R) (fun z hz => convRec_le R z hz)
    have h2 := gInts_len_le R
    exact le_trans h1 (Nat.mul_le_mul_right _ (by omega))
  · refine bd_liftP hex ?_
    with_reducible cos_bd

theorem natBitLength_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  show Nat.log 2 a + 1 ≤ Nat.log 2 b + 1
  have := Nat.log_mono_right (b := 2) h
  omega

theorem popRecCost_mono (m W bn bd M BN BD : ℕ) (h1 : m ≤ M) (h2 : bn ≤ BN) (h3 : bd ≤ BD) :
    popRecCost m W bn bd ≤ popRecCost M W BN BD := by
  have e1 := natBitLength_mono h1
  have e2 : 2 ^ natBitLength m ≤ 2 ^ natBitLength M := Nat.pow_le_pow_right (by norm_num) e1
  unfold popRecCost ratReadCost PrimT.countCost PrimT.wordCost
  gcongr

/-- The population records' parse. -/
theorem bd_popsT {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h) :
    Bd ex (fun R _ => popsTCost (Wof R) R.pops) := by
  refine bd_mono (g := fun R _ => R.pops.length * (popRecCost (Lof R) (Wof R) (Lof R) (Lof R) + 4) + 1)
    (fun R _ => ?_) ?_
  · unfold popsTCost
    have := sum_map_le (fun X : List ℕ × ℚ => popRecCost X.1.length (Wof R) (natBitLength X.2.num.natAbs)
      (natBitLength X.2.den) + 4) (popRecCost (Lof R) (Wof R) (Lof R) (Lof R) + 4) R.pops (fun X hX => by
        obtain ⟨_, a, b, c⟩ := pop_bits R X hX
        have := popRecCost_mono _ (Wof R) _ _ _ _ _ c a b
        omega)
    omega
  · refine bd_liftP hex ?_
    unfold popRecCost ratReadCost PrimT.countCost PrimT.wordCost
    with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| first
    | cos_app bd_gsum
    | cos_app bd_popsT
    | cos_app bd_loop
    | cos_app bd_out)

theorem bd_costA : Bd eK (fun R h => costA R h) := by
  unfold costA lenCost numsCost shapeCost widthCost cT2 cT3 cT4 cT5
  with_reducible cos_bd

theorem bd_costB : Bd eK (fun R _ => costB R) := by
  unfold costB wordsCost
  with_reducible cos_bd

theorem bd_costC : Bd eK (fun R _ => costC R) := by
  unfold costC gatesCost
  with_reducible cos_bd

theorem vClean_le (R : SelectionReq) (h : ParamsOk R) (r : Fin 112) : vClean R h r ≤ Bof R + 2 ^ (R.r * R.s) := by
  obtain ⟨hWB, _, _, _, hB2⟩ := cap_facts R
  obtain ⟨k1, s1, b1, r1, rb1, sr1, g1, p1, gn1, L3, LW⟩ := small_facts R h
  have c : ∀ t, t ≤ Bof R → t ≤ Bof R + 2 ^ (R.r * R.s) := fun _ ht => Nat.le_add_right_of_le ht
  have e0 : hh (starParamsOf R h) = R.r / 2 := rfl
  have e3 : fL (starParamsOf R h) = (R.n - R.r * (starParamsOf R h).b + 1) / 2 := rfl
  have e4 : fR (starParamsOf R h) = (R.n - R.r * (starParamsOf R h).b) / 2 := rfl
  have v0 : hh (starParamsOf R h) ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v1 : (starParamsOf R h).b ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v2 : R.s ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v3 : fL (starParamsOf R h) ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v4 : fR (starParamsOf R h) ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v5 : Lof R + 1 ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v58 : (popTable (Wof R) R).length ≤ Bof R + 2 ^ (R.r * R.s) := c _ (popTable_le R)
  have v59 : R.pops.length ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v60 : R.n + 1 ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v64 : R.n ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v67 : R.r ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v70 : R.r / 2 ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v71 : R.n - R.r * (starParamsOf R h).b ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v72 : R.s * (R.r / 2) ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v73 : R.r * R.s ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v84 : 2 ^ (R.r * R.s) ≤ Bof R + 2 ^ (R.r * R.s) := Nat.le_add_left _ _
  have v86 : Wof R ≤ Bof R + 2 ^ (R.r * R.s) := c _ hWB
  have v87 : Bof R ≤ Bof R + 2 ^ (R.r * R.s) := c _ le_rfl
  have v88 : R.gates.length ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v95 : 2 * Wof R + 1 ≤ Bof R + 2 ^ (R.r * R.s) := c _ hB2
  have v85 : Lof R ≤ Bof R + 2 ^ (R.r * R.s) := c _ (by omega)
  have v0' : 0 ≤ Bof R + 2 ^ (R.r * R.s) := Nat.zero_le _
  unfold vClean pvP
  exact ite_le' v67 (ite_le' v2 (ite_le' v0 (ite_le' v1 (ite_le' v2 (ite_le' v3 (ite_le' v4 (ite_le' v5 (ite_le' v58
    (ite_le' v59 (ite_le' v60 (ite_le' v64 (ite_le' v67 (ite_le' v2 (ite_le' v1 (ite_le' v70 (ite_le' v71
    (ite_le' v72 (ite_le' v73 (ite_le' v84 (ite_le' v85 (ite_le' v86 (ite_le' v87 (ite_le' v88 (ite_le' v95
    v0'))))))))))))))))))))))))

/-- The cleared registers. -/
theorem bd_dsum : Bd eK (fun R h => (dirty.map fun r => 3 * vClean R h r + 2).sum) := by
  refine bd_mono (g := fun R _ => 24 * (3 * (Bof R + 2 ^ (R.r * R.s)) + 2)) (fun R h => ?_) ?_
  · have h1 := sum_map_le (fun r => 3 * vClean R h r + 2) (3 * (Bof R + 2 ^ (R.r * R.s)) + 2) dirty (fun r _ => by
      have := vClean_le R h r
      omega)
    have e : dirty.length = 24 := rfl
    rw [e] at h1
    exact h1
  · with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_dsum)

theorem bd_clean : Bd eK (fun R h => cleanCost R h) := by
  unfold cleanCost
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| first
    | cos_app bd_costA
    | cos_app bd_costB
    | cos_app bd_costC
    | cos_app bd_clean)

theorem costF_eq (R : SelectionReq) (h : ParamsOk R) : costF parseCostF R = costA R h + (costB R + costC R) + 1 +
    (loopCost R h + 1 + (18 * R.r + 3 + 1 + (18 * R.s + 3) + 1 + (outCost R.r R.s + 1 + cleanCost R h))) := by
  unfold costF parseCostF parseCost
  simp only [dif_pos h]

/-- **The machine's whole cost is `2^k·2^{s·r/2}·2^{(n+1)/2}` times a polynomial in `W`, uniformly.** -/
theorem bd_costF : Bd eK (fun R _ => costF parseCostF R) := by
  refine bd_mono (fun R h => le_of_eq (costF_eq R h)) ?_
  with_reducible cos_bd

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
