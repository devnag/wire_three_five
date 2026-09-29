import Proof.Wire_3_5.FinalPass.PopBridge
import Proof.Wire_3_5.FinalPass.WordAux
import Proof.MachineModel.CanonicalSignedGateEvaluationProgram

/-! # Final pass, stage 2: the corner words at a sampled pair, reference (P3:1645-1650, 3046-3053, 3170-3178)

"One-sided scores may be computed directly at a sampled row in polynomial time" (P3:3049-3050); "evaluating at most
`n` coordinate functions and adding polynomial-bit integers takes polynomial time" (P3:1648-1650). Every per-point
evaluator of the final pass reads the CORNER word of a gate list at the sampled pair `(c,u,v)`: the four values
`T(c+u+v), T(c+u), T(c+v), T(c)` of each gate (`cornerWord`, stage 3's input; `termOk`, `thrTermOk`, and the carriers'
residual vectors all read it). Integers are in signed binary (P3:1552-1555, `alg:model`), as a P/N pair of `h`-bit
words, so the machine adds only naturals and compares once (Theorem 2.5's `gate_eval_eq_decide`).
- `pairW h z`: `frame (binary h z⁺) ++ frame (binary h z⁻)`;
- `gateW h g`: a `true` marker, the pair of `−θ`, the pairs of the weights; `gatesW h G`: the gates, then `false`;
- `posAcc`, `negAcc`: the P and N sums of the weights at the selected coordinates;
- **`eval_acc`**: `g.eval x = [θ⁺ + N(x) ≤ θ⁻ + P(x)]` with the accumulators;
- **`mapS_add`**: the ripple-carry pass is addition of `h`-bit words; **`mapS_cmp`**: the borrow pass compares;
- `cornerIn bu bv`: the input of corner `(bu,bv)` (`c + [bu]u + [bv]v`, coordinatewise). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.CanonicalSignedGateEvaluationProgram

/-! ## Formats -/

/-- A signed integer as the P/N pair of framed `h`-bit words. -/
def pairW (h : ℕ) (z : ℤ) : List Bool := frame (binary h z.toNat) ++ frame (binary h (-z).toNat)

/-- One gate: a marker, the pair of `−θ`, the pairs of the weights. -/
def gateW (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) : List Bool :=
  true :: (pairW h (-g.threshold) ++ (List.ofFn g.weight).flatMap (pairW h))

/-- A gate list, then `false`. -/
def gatesW (h : ℕ) {n : ℕ} (G : List (NormalizedThresholdGate n)) : List Bool := G.flatMap (gateW h) ++ [false]

/-! ## The accumulators -/

/-- The P sum of the weights at the selected coordinates. -/
def posAcc : List ℤ → List Bool → ℕ
  | w :: ws, x :: xs => (if x then w.toNat else 0) + posAcc ws xs
  | _, _ => 0

/-- The N sum of the weights at the selected coordinates. -/
def negAcc : List ℤ → List Bool → ℕ
  | w :: ws, x :: xs => (if x then (-w).toNat else 0) + negAcc ws xs
  | _, _ => 0

theorem posAcc_ofFn : ∀ (n : ℕ) (w : Fin n → ℤ) (x : Fin n → Bool),
    posAcc (List.ofFn w) (List.ofFn x) = maskedPositiveSum w x
  | 0, _, _ => by simp [posAcc, maskedPositiveSum]
  | n + 1, w, x => by
    rw [List.ofFn_succ, List.ofFn_succ, posAcc, posAcc_ofFn n]
    unfold maskedPositiveSum positivePart
    rw [Fin.sum_univ_succ]

theorem negAcc_ofFn : ∀ (n : ℕ) (w : Fin n → ℤ) (x : Fin n → Bool),
    negAcc (List.ofFn w) (List.ofFn x) = maskedNegativeSum w x
  | 0, _, _ => by simp [negAcc, maskedNegativeSum]
  | n + 1, w, x => by
    rw [List.ofFn_succ, List.ofFn_succ, negAcc, negAcc_ofFn n]
    unfold maskedNegativeSum negativePart
    rw [Fin.sum_univ_succ]

/-- **The gate from the two accumulators**: `N = θ⁺ + N(x)` against `P = θ⁻ + P(x)`, where `θ⁻ = (−θ)⁺` is the
P word and `θ⁺ = (−θ)⁻` the N word of the pair of `−θ`. -/
theorem eval_acc {n : ℕ} (g : NormalizedThresholdGate n) (x : BitInput n) :
    g.eval x = decide ((-(-g.threshold)).toNat + negAcc (List.ofFn g.weight) (List.ofFn x) ≤
      (-g.threshold).toNat + posAcc (List.ofFn g.weight) (List.ofFn x)) := by
  rw [gate_eval_eq_decide, posAcc_ofFn, negAcc_ofFn, neg_neg]
  unfold positivePart negativePart
  apply decide_eq_decide.mpr
  omega

theorem posAcc_le (ws : List ℤ) (xs : List Bool) : posAcc ws xs ≤ (ws.map Int.natAbs).sum := by
  induction ws generalizing xs with
  | nil => simp [posAcc]
  | cons w ws ih =>
    cases xs with
    | nil => simp [posAcc]
    | cons x xs =>
      simp only [posAcc, List.map_cons, List.sum_cons]
      have := ih xs
      split <;> omega

theorem negAcc_le (ws : List ℤ) (xs : List Bool) : negAcc ws xs ≤ (ws.map Int.natAbs).sum := by
  induction ws generalizing xs with
  | nil => simp [negAcc]
  | cons w ws ih =>
    cases xs with
    | nil => simp [negAcc]
    | cons x xs =>
      simp only [negAcc, List.map_cons, List.sum_cons]
      have := ih xs
      split <;> omega

/-! ## The adder and the comparator -/

/-- The sum bit. -/
def addOut (x y c : Bool) : Bool := xor (xor x y) c

/-- The carry bit. -/
def addNxt (x y c : Bool) : Bool := (x && y) || (c && xor x y)

/-- The borrow comparator's carry: `x + ¬y + c`. -/
def cmpNxt (x y c : Bool) : Bool := addNxt x (!y) c

theorem binary_length' : ∀ (h x : ℕ), (binary h x).length = h
  | 0, _ => rfl
  | h + 1, x => by simp [binary, binary_length' h (x / 2)]

/-- **The ripple-carry pass is addition** of `h`-bit words. -/
theorem mapS_add : ∀ (h x y : ℕ) (c : Bool),
    (mapS addOut addNxt (binary h x) (binary h y) c).1 = binary h (x + y + c.toNat)
  | 0, _, _, _ => rfl
  | h + 1, x, y, c => by
    simp only [binary, mapS]
    have key : ∀ (x y : ℕ) (c : Bool),
        addOut (x % 2 == 1) (y % 2 == 1) c = ((x + y + c.toNat) % 2 == 1) ∧
        (x / 2 + y / 2 + (addNxt (x % 2 == 1) (y % 2 == 1) c).toNat) = (x + y + c.toNat) / 2 := by
      intro x y c
      have hx := Nat.mod_two_eq_zero_or_one x
      have hy := Nat.mod_two_eq_zero_or_one y
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;>
        simp [addOut, addNxt, hx, hy, Bool.toNat] <;> omega
    obtain ⟨k1, k2⟩ := key x y c
    rw [k1, mapS_add h (x / 2) (y / 2), k2]

/-- The kept word of a pass that writes its own bits back. -/
theorem mapS_keep (nxt : Bool → Bool → Bool → Bool) : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    (mapS keepA nxt as bs c).1 = as
  | [], [], _, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, keepA]
    rw [mapS_keep nxt as bs _ (by simpa using h)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- **The borrow pass compares**: its final carry is `[y + [¬c] ≤ x]` on the low `h` bits. -/
theorem mapS_cmp : ∀ (h x y : ℕ) (c : Bool),
    (mapS keepA cmpNxt (binary h x) (binary h y) c).2 = decide (y % 2 ^ h + (!c).toNat ≤ x % 2 ^ h)
  | 0, x, y, c => by show c = _; cases c <;> simp [Nat.mod_one]
  | h + 1, x, y, c => by
    simp only [binary, mapS]
    rw [mapS_cmp h (x / 2) (y / 2)]
    have ex : x % 2 ^ (h + 1) = 2 * (x / 2 % 2 ^ h) + x % 2 := by
      rw [pow_succ, mul_comm, Nat.mod_mul]; omega
    have ey : y % 2 ^ (h + 1) = 2 * (y / 2 % 2 ^ h) + y % 2 := by
      rw [pow_succ, mul_comm, Nat.mod_mul]; omega
    rw [ex, ey]
    generalize x / 2 % 2 ^ h = x'
    generalize y / 2 % 2 ^ h = y'
    have hx := Nat.mod_two_eq_zero_or_one x
    have hy := Nat.mod_two_eq_zero_or_one y
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;>
      simp [cmpNxt, addNxt, hx, hy, Bool.toNat] <;> omega

/-! ## The corner inputs -/

/-- The input of corner `(bu,bv)`: `c + [bu]u + [bv]v`, coordinatewise. -/
def cornerIn (bu bv : Bool) : List Bool → List Bool → List Bool → List Bool
  | c :: cs, u :: us, v :: vs => xor (xor c (bu && u)) (bv && v) :: cornerIn bu bv cs us vs
  | _, _, _ => []

theorem cornerIn_ofFn {n : ℕ} (bu bv : Bool) (c u v : BitInput n) :
    cornerIn bu bv (List.ofFn c) (List.ofFn u) (List.ofFn v) =
      List.ofFn (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i)) := by
  induction n with
  | zero => simp [cornerIn]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, cornerIn]
    have := ih (fun i => c i.succ) (fun i => u i.succ) (fun i => v i.succ)
    rw [this]
    rfl

theorem corner_in {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    corners T c u v 0 = T (xorInput (xorInput c (fun i => true && u i)) (fun i => true && v i)) ∧
    corners T c u v 1 = T (xorInput (xorInput c (fun i => true && u i)) (fun i => false && v i)) ∧
    corners T c u v 2 = T (xorInput (xorInput c (fun i => false && u i)) (fun i => true && v i)) ∧
    corners T c u v 3 = T (xorInput (xorInput c (fun i => false && u i)) (fun i => false && v i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | (show T _ = T _; congr 1; funext i; simp [xorInput])

/-! ## The accumulator width -/

end NearCubicWires.WireExponent3_5.FinalPass.Corner
