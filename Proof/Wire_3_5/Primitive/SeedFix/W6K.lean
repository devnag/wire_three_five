import Proof.Wire_3_5.Primitive.SeedFix.W6J

/-! # W6, part 11: one candidate of the prime rows

P3:2551-2553 (row:prime: the primes `p ≤ cutoff`, "a polynomial-size set of polynomially bounded primes"; the prime rows
are listed in increasing order, `Joins.primesList`, port `17` = `Data.unaryList (primesList cut)`). One candidate `x ≥ 2`
of the listing loop: count its divisors (`tdPre`), and on a prime append `1^x 0` to stream `sPr`, count it (`r58`) and
add it to the prime sum (`r59`); then the next candidate:
* `pSt σ0 L g` (stream `sPr` holding `L`, head at its end, registers `g`), `appendO_pSt`, `RegRun.onP`;
* **`emitP_exec`** (a prime appended); **`pBody_exec`**: from `pSt σ0 L g` with `r21 = x` to
  `pSt σ0 (L ++ pw x) (pg g x L)` (`pw x = 1^x 0` on a prime, `[]` otherwise).

Paper quantities of the main types: the prime rows' next entry `1^x 0` (on a prime `x`) and the prime count and sum. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ)

/-- Stream `sPr` holding `L` (head at its end), registers `g`, everything else as `σ0`. -/
def pSt (σ0 : WL) (L : List Bool) (g : Fin 80 → ℕ) : WL :=
  ⟨Function.update σ0.sh sPr L.length, Function.update σ0.st sPr L, g, σ0.cell⟩

theorem appendO_pSt (σ0 : WL) (L u : List Bool) (g : Fin 80 → ℕ) :
    WriteNat.appendO (pSt σ0 L g) sPr 74 u = pSt σ0 (L ++ u) (Function.update g 74 (g 74 + u.length)) := by
  apply WState.eq
  · funext j
    by_cases hj : j = sPr
    · subst hj; simp [pSt]
    · simp [pSt, Function.update_apply, hj]
  · funext j
    by_cases hj : j = sPr
    · subst hj; simp [pSt]
    · simp [pSt, Function.update_apply, hj]
  · simp [pSt]
  · simp [pSt]

theorem RegRun.onP {P : WP} {g g' : Fin 80 → ℕ} {n : ℕ} (h : RegRun cap P g g' n) (σ0 : WL) (L : List Bool) :
    WExec cap P (pSt σ0 L g) (pSt σ0 L g') n := h _ rfl

theorem reps_true (x : ℕ) : FiltRec.reps x [true] = List.replicate x true := by
  induction x with
  | zero => rfl
  | succ k ih => rw [FiltRec.reps_succ, ih, List.replicate_succ']

/-! ## A prime appended -/

/-- `1^x 0` appended to `sPr` (`r21 = x`), `r58 += 1`, `r59 += x`. -/
def emitP : WP :=
  .seq (Emit.repRegW sPr 74 21 34 33 [true]) (.seq (Emit.emitW sPr 74 [false]) (.seq (.inc 58) (ParseNat.addTo 21 59 33)))

theorem emitP_exec (σ0 : WL) (L : List Bool) (g : Fin 80 → ℕ) (x : ℕ) (hx : g 21 = x) (h74 : g 74 = L.length)
    (z33 : g 33 = 0) (z34 : g 34 = 0) (b1 : L.length + x + 1 ≤ cap) (b2 : g 58 + 1 ≤ cap) (b3 : g 59 + x ≤ cap) :
    WExec cap emitP (pSt σ0 L g) (pSt σ0 (L ++ (List.replicate x true ++ [false]))
      (Function.update (Function.update (Function.update g 74 (L.length + (x + 1))) 58 (g 58 + 1)) 59 (g 59 + x)))
      (5 * (opU cap + 1)) := by
  have hU := lin_le_opU cap
  have h1 := Emit.repRegW_spec cap sPr 74 21 34 33 (by decide) (by decide) (by decide) (by decide) [true] (pSt σ0 L g)
    z34 z33 (by simp [pSt]) (by show g 21 ≤ cap; omega)
    (by show g 74 + g 21 * [true].length ≤ cap; simp only [List.length_singleton, Nat.mul_one]; omega)
  have h1' : WExec cap (Emit.repRegW sPr 74 21 34 33 [true]) (pSt σ0 L g)
      (pSt σ0 (L ++ List.replicate x true) (Function.update g 74 (L.length + x))) (30 * x + 5) := by
    refine WExec.cast cap h1 ?_ ?_
    · show WriteNat.appendO _ _ _ (FiltRec.reps (g 21) [true]) = _
      rw [hx, reps_true, appendO_pSt, h74, List.length_replicate]
    · show 18 * g 21 + 3 + 1 + (g 21 * (8 * [true].length + 4) + 1) ≤ _
      simp only [List.length_singleton, Nat.mul_one, Nat.reduceAdd]
      omega
  have h2 := Emit.emitW_spec cap sPr 74 [false] (pSt σ0 (L ++ List.replicate x true) (Function.update g 74 (L.length + x)))
    (by simp [pSt]) (by show Function.update g 74 (L.length + x) 74 + [false].length ≤ cap; simp only [Function.update_self, List.length_singleton]; omega)
  rw [appendO_pSt] at h2
  have h3 := RegRun.onP cap (inc_rr cap 58 (Function.update (Function.update g 74 (L.length + x)) 74
      (Function.update g 74 (L.length + x) 74 + [false].length)) (g 58 + 1) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega))
    σ0 (L ++ List.replicate x true ++ [false])
  have h4 := RegRun.onP cap (addTo_rr cap 21 59 33 (by decide) (by decide) (by decide)
      (Function.update (Function.update (Function.update g 74 (L.length + x)) 74
        (Function.update g 74 (L.length + x) 74 + [false].length)) 58 (g 58 + 1)) (g 59 + x)
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hx]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z33]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega))
    σ0 (L ++ List.replicate x true ++ [false])
  refine WExec.cast cap (WExec.seq h1' (WExec.seq h2 (WExec.seq h3 h4))) ?_ ?_
  · rw [List.append_assoc]
    congr 1
    funext r
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, List.length_singleton]
    split_ifs <;> subst_vars <;> simp_all <;> omega
  · simp only [List.length_singleton]
    omega

/-! ## One candidate -/

def pBody : WP := .seq tdPre (.seq (.ifr 24 (WM.clear 24) emitP) (.inc 21))

/-- The word a candidate appends: `1^x 0` on a prime. -/
def pw (x : ℕ) : List Bool := if Nat.Prime x then List.replicate x true ++ [false] else []

/-- The registers after a candidate. -/
def pg (g : Fin 80 → ℕ) (x : ℕ) (L : List Bool) : Fin 80 → ℕ :=
  Function.update (Function.update (Function.update (Function.update g 74 (L.length + (pw x).length)) 58
    (g 58 + if Nat.Prime x then 1 else 0)) 59 (g 59 + if Nat.Prime x then x else 0)) 21 (x + 1)

theorem pBody_exec (σ0 : WL) (L : List Bool) (g : Fin 80 → ℕ) (x : ℕ) (hx : g 21 = x) (h2x : 2 ≤ x)
    (h74 : g 74 = L.length) (z22 : g 22 = 0) (z23 : g 23 = 0) (z24 : g 24 = 0) (z25 : g 25 = 0) (z26 : g 26 = 0) (z27 : g 27 = 0) (z28 : g 28 = 0) (z29 : g 29 = 0) (z30 : g 30 = 0) (z31 : g 31 = 0) (z33 : g 33 = 0) (z34 : g 34 = 0) (bx : x + 1 ≤ cap) (b1 : L.length + x + 1 ≤ cap)
    (b2 : g 58 + 1 ≤ cap) (b3 : g 59 + x ≤ cap) :
    WExec cap pBody (pSt σ0 L g) (pSt σ0 (L ++ pw x) (pg g x L))
      (x * (8 * (opU cap + 1) + 4) + 14 * (opU cap + 1)) := by
  have hU := lin_le_opU cap
  have hc := cntDiv_le x x
  have t := RegRun.onP cap (tdPre_rr cap g x hx h2x z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 z33 bx) σ0 L
  by_cases hp : Nat.Prime x
  · have h0 : cntDiv x x = 0 := (prime_iff_cntDiv x h2x).mp hp
    have e := emitP_exec cap σ0 L (Function.update g 24 (cntDiv x x)) x (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hx]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h74])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z33]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z34]) b1 (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
    have i := RegRun.onP cap (inc_rr cap 21 (Function.update (Function.update (Function.update
        (Function.update g 24 (cntDiv x x)) 74 (L.length + (x + 1))) 58 (Function.update g 24 (cntDiv x x) 58 + 1)) 59
        (Function.update g 24 (cntDiv x x) 59 + x)) (x + 1) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hx]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hx]; omega))
      σ0 (L ++ (List.replicate x true ++ [false]))
    refine WExec.cast cap (WExec.seq t (WExec.seq (WExec.ifrF (by show Function.update g 24 (cntDiv x x) 24 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h0]) e) i)) ?_ ?_
    · simp only [pw, pg, if_pos hp]
      congr 1
      funext r
      simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, List.length_append, List.length_replicate, List.length_singleton]
      split_ifs <;> subst_vars <;> simp_all
    · omega
  · have h0 : cntDiv x x ≠ 0 := fun h => hp ((prime_iff_cntDiv x h2x).mpr h)
    have c := RegRun.onP cap (clear_rr cap 24 (Function.update g 24 (cntDiv x x)) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)) σ0 L
    have i := RegRun.onP cap (inc_rr cap 21 (Function.update (Function.update g 24 (cntDiv x x)) 24 0) (x + 1)
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hx]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hx]; omega)) σ0 L
    refine WExec.cast cap (WExec.seq t (WExec.seq (WExec.ifrT (by show Function.update g 24 (cntDiv x x) 24 ≠ 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact h0) c) i)) ?_ ?_
    · simp only [pw, pg, if_neg hp, List.append_nil]
      congr 1
      funext r
      simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, List.length_nil, Nat.add_zero]
      split_ifs <;> subst_vars <;> simp_all
    · omega

end NearCubicWires.WireExponent3_5.PrimT.W6
