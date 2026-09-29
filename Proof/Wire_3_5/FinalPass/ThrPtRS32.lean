import Proof.Wire_3_5.FinalPass.ThrPtRS31

/-! # S2 (THR per point), part 46: the rows' and loops' step bounds at a size bound `U`

With every parameter `≤ U` (coefficients and weights `≤ p ≤ U`, reports `≤ DM ≤ U`): **`costT_le`**, **`capT_le`**,
**`rowWord_le`**, **`rowCost_le`** (one row's bound `≤ rowCostU B U V`), **`primeLoopCost_le`**,
**`gLoopCost_le`**. Paper quantity: none beyond the machine model (the run is polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem sum_le_mul (A : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ A) → l.sum ≤ l.length * A
  | [], _ => by simp
  | x :: l, h => by
    have h1 := h x List.mem_cons_self
    have h2 := sum_le_mul A l (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem map_add_le (A c : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ A) → (l.map (· + c)).sum ≤ l.length * (A + c)
  | [], _ => by simp
  | x :: l, h => by
    have h1 := h x List.mem_cons_self
    have h2 := map_add_le A c l (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem tdig_le (p A B : ℕ) : ∀ (ws tp tm : List ℕ), (∀ w ∈ ws, w ≤ A) → (∀ t ∈ tp, t ≤ B) → (∀ s ∈ tm, s ≤ B) →
    Term.digCost p ws tp tm ≤ ws.length * (A * ((B + B) * (7 * p + 27) + 23) + 14 * (B + B) + 42) + 1
  | w :: ws, t :: tp, s :: tm, hw, ht, hs => by
    have h1 := hw w List.mem_cons_self
    have h2 := ht t List.mem_cons_self
    have h3 := hs s List.mem_cons_self
    have ih := tdig_le p A B ws tp tm (fun x hx => hw x (List.mem_cons_of_mem w hx))
      (fun x hx => ht x (List.mem_cons_of_mem t hx)) (fun x hx => hs x (List.mem_cons_of_mem s hx))
    have h4 : w * ((t + s) * (7 * p + 27) + 23) + 14 * (t + s) + 42 ≤
        A * ((B + B) * (7 * p + 27) + 23) + 14 * (B + B) + 42 := by gcongr
    have e : (ws.length + 1) * (A * ((B + B) * (7 * p + 27) + 23) + 14 * (B + B) + 42) =
        ws.length * (A * ((B + B) * (7 * p + 27) + 23) + 14 * (B + B) + 42) +
          (A * ((B + B) * (7 * p + 27) + 23) + 14 * (B + B) + 42) := by ring
    simp only [Term.digCost, List.length_cons]
    rw [e]
    omega
  | [], _, _, _, _, _ => by simp [Term.digCost]
  | _ :: _, [], _, _, _, _ => by simp [Term.digCost]
  | _ :: _, _ :: _, [], _, _, _ => by simp [Term.digCost]

/-- Stage 8's step bound at a size bound. -/
def costTU (U : ℕ) : ℕ :=
  14 * U + 13 * U + (21 * U + 43) * (U * U) + 132 * U +
    (U * (U * ((U + U) * (7 * U + 27) + 23) + 14 * (U + U) + 42) + 1) +
    5 * (U + U + 2 + U * U + U + U * U + 2 * U) + 5 * (U * U + U * U + 2 * U) + 40

/-- Stage 8's capacity at a size bound. -/
def capTU (U : ℕ) : ℕ := 8 * U + U + U + U * U + U + U * U + 2 * U + U * U + U * U + 2 * U + 4

/-- The row word's length at a size bound. -/
def rowWordU (U : ℕ) : ℕ := U + 1 + (U + 1) + U * (U + 1) + U * (U + 2) + 1

variable {U V : ℕ}

theorem lsum_le (l : List ℕ) (hl : l.length ≤ U) (h : ∀ x ∈ l, x ≤ U) : l.sum ≤ U * U :=
  (sum_le_mul U l h).trans (Nat.mul_le_mul_right U hl)

theorem costT_le (p r0 L : ℕ) (as ws tp tm : List ℕ) (hp : p ≤ U) (hr : r0 ≤ U) (hL : L ≤ U)
    (has : as.length ≤ U) (hA : ∀ x ∈ as, x ≤ U) (hws : ws.length ≤ U) (hW : ∀ x ∈ ws, x ≤ U)
    (htp : tp.length ≤ U) (hT : ∀ x ∈ tp, x ≤ U) (htm : tm.length ≤ U) (hS : ∀ x ∈ tm, x ≤ U) :
    Term.costT p r0 L as ws tp tm ≤ costTU U := by
  unfold Term.costT costTU
  have s1 := lsum_le as has hA
  have s2 := lsum_le ws hws hW
  have s3 := lsum_le tp htp hT
  have s4 := lsum_le tm htm hS
  have hd : Term.digCost p ws tp tm ≤ U * (U * ((U + U) * (7 * U + 27) + 23) + 14 * (U + U) + 42) + 1 :=
    (tdig_le p U U ws tp tm hW hT hS).trans (by gcongr)
  gcongr

theorem capT_le (p r0 L : ℕ) (as ws tp tm : List ℕ) (hp : p ≤ U) (hr : r0 ≤ U) (hL : L ≤ U)
    (has : as.length ≤ U) (hA : ∀ x ∈ as, x ≤ U) (hws : ws.length ≤ U) (hW : ∀ x ∈ ws, x ≤ U)
    (htp : tp.length ≤ U) (hT : ∀ x ∈ tp, x ≤ U) (htm : tm.length ≤ U) (hS : ∀ x ∈ tm, x ≤ U) :
    Term.capT p r0 L as ws tp tm ≤ capTU U := by
  unfold Term.capT capTU
  have s1 := lsum_le as has hA
  have s2 := lsum_le ws hws hW
  have s3 := lsum_le tp htp hT
  have s4 := lsum_le tm htm hS
  gcongr

theorem rowWord_le (p r0 : ℕ) (as ws : List ℕ) (hp : p ≤ U) (hr : r0 ≤ U) (has : as.length ≤ U)
    (hA : ∀ x ∈ as, x ≤ U) (hws : ws.length ≤ U) (hW : ∀ x ∈ ws, x ≤ U) :
    (Term.rowWord p r0 as ws).length ≤ rowWordU U := by
  rw [rowWord_len]
  unfold rowWordU
  have s1 := (map_add_le U 1 as hA).trans (Nat.mul_le_mul_right (U + 1) has)
  have s2 := (map_add_le U 2 ws hW).trans (Nat.mul_le_mul_right (U + 2) hws)
  gcongr

theorem repWord_le (tp tm : List ℕ) (hl : tp.length = tm.length) (htp : tp.length ≤ U) (hT : ∀ x ∈ tp, x ≤ U)
    (hS : ∀ x ∈ tm, x ≤ U) : (Term.repWord tp tm).length ≤ U * (U + 1) + U * (U + 1) := by
  rw [repWord_length tp tm hl]
  have s1 := (map_add_le U 1 tp hT).trans (Nat.mul_le_mul_right (U + 1) htp)
  have s2 := (map_add_le U 1 tm hS).trans (Nat.mul_le_mul_right (U + 1) (hl ▸ htp))
  omega

/-- One row's step bound at a size bound (`B`: RowW's). -/
def rowCostU (B U V : ℕ) : ℕ :=
  B + 1 + (digLoopCost U U U U U U U V + 1 + ((7 * U + 1) + 1 + ((5 * (U * (U + 1) + U * (U + 1)) + 1) + 1 +
    ((costTU U + 2) + 1 + (8 + 1 + ((U * (18 * U + 50) + 1 + 1 + ((7 * U + 1) + 1 +
    (5 * (U * (U + 1) + U * (U + 1)) + 1))) + 1 + eraseRowCost U U U U U (rowWordU U)))))))

theorem rowCost_le (bW p r0 M A0 τ DM c5 B : ℕ) (as ws tp tm : List ℕ) (hb : bW ≤ B) (hp : p ≤ U) (hr : r0 ≤ U)
    (hM : M ≤ U) (hA0 : A0 ≤ U) (hτ : τ ≤ U) (hDM : DM ≤ U) (hc : c5 ≤ V) (has : as.length ≤ U)
    (hA : ∀ x ∈ as, x ≤ U) (hws : ws.length ≤ U) (hW : ∀ x ∈ ws, x ≤ U) (htl : tp.length = tm.length)
    (htp : tp.length ≤ U) (hT : ∀ x ∈ tp, x ≤ U) (hS : ∀ x ∈ tm, x ≤ U) :
    rowCost bW p r0 M A0 τ DM c5 as ws tp tm ≤ rowCostU B U V := by
  unfold rowCost rowCostU costTI
  have h1 := digLoopCost_le τ p r0 M A0 τ DM c5 hτ hp hr hM hA0 hτ hDM hc
  have h2 := repWord_le tp tm htl htp hT hS
  have h3 := costT_le p r0 M as ws tp tm hp hr hM has hA hws hW htp hT (htl ▸ htp) hS
  have h4 := eraseRowCost_le p r0 M τ A0 _ hp hr hM hτ hA0 (rowWord_le p r0 as ws hp hr has hA hws hW)
  gcongr

theorem primeLoopCost_le (C : ℕ → ℕ) (Cm : ℕ) : ∀ L : List ℕ, (∀ p ∈ L, p ≤ U ∧ C p ≤ Cm) →
    primeLoopCost C L ≤ L.length * (14 * U + 13 + Cm) + 1
  | [], _ => by simp [primeLoopCost]
  | q :: L, h => by
    have h1 := h q List.mem_cons_self
    have ih := primeLoopCost_le C Cm L (fun p hp => h p (List.mem_cons_of_mem q hp))
    simp only [primeLoopCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem gLoopCost_le (Lp : List ℕ) (C : ℕ → ℕ → ℕ) (Pm UL : ℕ) (hUL : (PrimAsm.Data.unaryList Lp).length ≤ UL) :
    ∀ m i : ℕ, (∀ j, i ≤ j → j < i + m → primeLoopCost (C j) Lp ≤ Pm) → gLoopCost Lp C i m ≤ m * (Pm + 5 * UL + 11) + 1
  | 0, _, _ => by simp [gLoopCost]
  | m + 1, i, h => by
    have h1 := h i le_rfl (by omega)
    have ih := gLoopCost_le Lp C Pm UL hUL m (i + 1) (fun j h2 h3 => h j (by omega) (by omega))
    simp only [gLoopCost, Nat.add_mul, Nat.one_mul]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
