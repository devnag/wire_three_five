import Proof.Wire_3_5.FinalPass.RowH

/-! # `RowW`, part 9: the whole row program (P3:2585-2599)

`rowTopW` = `rowAW` then `rowBW`. From the entry it writes exactly `unary p ++ unary r₀' ++ coefficients ++ digit
section ++ [false]` on `Dg` (`r₀' = (p − T) mod p`, `T` the target pass's residue) and changes nothing else. Main
declarations: `La_prefix`, `rowTopW`, `rowTB`, **`rowTop_spec`**. Paper quantity: row `(g, p)`'s word for stage 8. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires.RepairRepresentation (natWord intWord)

theorem La_prefix (bm p : ℕ) (ws : ℕ → List ℤ) (l : List Bool) : ∀ n, La bm p ws l n = l ++ La bm p ws [] n
  | 0 => by simp [La]
  | n + 1 => by rw [La, La, La_prefix bm p ws l n, List.append_assoc]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- **The row program.** -/
def rowTopW (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) : WM ns nr := .seq (rowAW R Pay Dg) (rowBW R Dg)

/-- The row program's bound. -/
def rowTB (U : ℕ) : ℕ := rowAB U + 1 + rowBB U

theorem rowTop_spec (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (hPD : ∀ i, Pay i ≠ Dg) (a' : ℕ) (ha : a' ≤ 4)
    (cD : ℕ → List Bool) (S m : ℕ → ℕ) (zs ws : ℕ → List ℤ) (t : ℕ → ℤ) (rest : ℕ → List Bool)
    (G p τ U : ℕ) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i ++ [t i]).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hGa : Gs G m a' = 0) (hp : 2 ≤ p)
    (hDs : σ.st Dg = []) (hDh : σ.sh Dg = 0)
    (hA : σ.val (R 0) = a') (hG : σ.val (R 1) = G) (hP : σ.val (R 2) = p) (hT : σ.val (R 3) = τ)
    (hz : Zs R σ allL)
    (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U) (hpU : p ≤ U) (hτU : τ ≤ U)
    (hlU : (La (Bf p (fun i => ws i ++ [t i]) a') p ws [] a').length + 2 * (p + 1) + τ * (p + 1) + p + 2 ≤ U)
    (haU : a' ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (rowTopW R Pay Dg) σ (σ.sets Dg (ListEval.unary p ++
      ListEval.unary ((p - Tf (Bf p (fun i => ws i ++ [t i]) a') p t a') % p) ++
      La (Bf p (fun i => ws i ++ [t i]) a') p ws [] a' ++ Term.digWord ((List.range τ).map fun d => 2 ^ d % p) ++
      [false])) (rowTB U) := by
  have hr0 : (p - Tf (Bf p (fun i => ws i ++ [t i]) a') p t a') % p < p := Nat.mod_lt _ (by omega)
  have hlen : (ListEval.unary p ++ ListEval.unary ((p - Tf (Bf p (fun i => ws i ++ [t i]) a') p t a') % p)).length ≤
      2 * (p + 1) := by simp [ListEval.unary]; omega
  have d1 := rowA_spec cap R Pay Dg hPD a' ha cD S m zs ws t rest G p U σ hst hs hc hzs hws hm hGa hp hDs hDh hA hG hP
    hz hcU hmU hGU hpU (by rw [La_prefix]; simp only [List.length_append] at hlen ⊢; omega) haU hU
  have d2 := rowB_spec cap R Dg p τ U hp σ (La (Bf p (fun i => ws i ++ [t i]) a') p ws (ListEval.unary p ++
      ListEval.unary ((p - Tf (Bf p (fun i => ws i ++ [t i]) a') p t a') % p)) a') hDh hP hT hz hpU hτU
    (by rw [La_prefix]; simp only [List.length_append] at hlen ⊢; omega) hU
  refine WExec.cast cap (WExec.seq d1 d2) ?_ (by unfold rowTB; omega)
  rw [La_prefix, List.append_assoc]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
