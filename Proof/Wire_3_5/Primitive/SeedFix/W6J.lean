import Proof.Wire_3_5.Primitive.SeedFix.W6I

/-! # W6, part 10: trial division (the primality test of the prime rows)

P3:2551-2553 (row:prime: the prime rows run over "a polynomial-size set of polynomially bounded primes", the primes
`p ≤ cutoff`). The numbers machine lists the primes by trial division on its unary registers: for a candidate `x ≥ 2`
it counts the divisors `d ∈ [2, x)` (`cntDiv x x`), which is `0` exactly when `x` is prime (`prime_iff_cntDiv`):
* `dec_rr`, `skip_rr`, `RegRun.ifr`, **`RegRun.loop`** (the counted loop on a register run, from `wloop`);
* **`tdBody_rr`** (one divisor: `divW`, then the count on a zero remainder), **`tdLoop_rr`**, **`tdPre_rr`**
  (`r24 := cntDiv x x` from `r21 = x`, scratch `22 … 33` at `0` and restored).

Paper quantity of the main type: the primality of the candidate (`cntDiv x x = 0 ↔ x prime`). -/

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

/-! ## More register runs -/

theorem dec_rr (r : Fin 80) (f : Fin 80 → ℕ) (v : ℕ) (hv : f r - 1 = v) (h : f r ≤ cap) :
    RegRun cap (.dec r) f (Function.update f r v) (opU cap) := fun σ hσ => by
  subst hv
  have e := WExec.dec (cap := cap) r σ (by rw [hσ]; exact h)
  rw [setv_mk, hσ] at e
  exact WExec.mono e (by have := lin_le_opU cap; omega)

theorem skip_rr (f : Fin 80 → ℕ) : RegRun cap .skip f f 0 := fun σ hσ => by
  obtain ⟨sh, st, val, cell⟩ := σ
  simp only at hσ
  subst hσ
  exact WExec.skip (cap := cap) _

theorem RegRun.ifr (r : Fin 80) {P Q : WP} {f g : Fin 80 → ℕ} {n : ℕ} (hT : f r ≠ 0 → RegRun cap P f g n)
    (hF : f r = 0 → RegRun cap Q f g n) : RegRun cap (.ifr r P Q) f g (n + 1) := fun σ hσ => by
  by_cases h : f r = 0
  · exact WExec.ifrF (by rw [hσ]; exact h) (hF h σ hσ)
  · exact WExec.ifrT (by rw [hσ]; exact h) (hT h σ hσ)

/-- **The counted loop on a register run** (`wloop`): `while K ≠ 0 { K--; body }` along the register files `g k`. -/
theorem RegRun.loop (K : Fin 80) (body : WP) (c n : ℕ) (g : ℕ → Fin 80 → ℕ) (hK : ∀ k ≤ n, g k K = n - k)
    (hcap : n ≤ cap) (hbody : ∀ k < n, RegRun cap body (Function.update (g k) K (n - k - 1)) (g (k + 1)) c) :
    RegRun cap (.whr K (.seq (.dec K) body)) (g 0) (g n) (n * (c + 4) + 1) := fun σ hσ => by
  have h := UnionMachine.Round.wloop cap K body c n (fun k => ⟨σ.sh, σ.st, g k, σ.cell⟩) (fun k hk => hK k hk) hcap
    (fun k hk => hbody k hk _ rfl)
  have e : (⟨σ.sh, σ.st, g 0, σ.cell⟩ : WL) = σ := by rw [← hσ]
  rw [e] at h
  exact h

/-! ## Counting divisors -/

/-- The divisors of `x` in `[2, m)`. -/
def cntDiv (x m : ℕ) : ℕ := ((Finset.Ico 2 m).filter (fun d => d ∣ x)).card

theorem cntDiv_two (x : ℕ) : cntDiv x 2 = 0 := by simp [cntDiv]

theorem cntDiv_succ (x m : ℕ) (hm : 2 ≤ m) : cntDiv x (m + 1) = cntDiv x m + if x % m = 0 then 1 else 0 := by
  unfold cntDiv
  rw [Nat.Ico_succ_right_eq_insert_Ico hm, Finset.filter_insert]
  by_cases h : x % m = 0
  · have hd : m ∣ x := Nat.dvd_of_mod_eq_zero h
    rw [if_pos hd, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · have hd : ¬ m ∣ x := fun hd => h (Nat.mod_eq_zero_of_dvd hd)
    rw [if_neg hd, if_neg h, Nat.add_zero]

theorem cntDiv_le (x m : ℕ) : cntDiv x m ≤ m := by
  unfold cntDiv
  calc ((Finset.Ico 2 m).filter (fun d => d ∣ x)).card ≤ (Finset.Ico 2 m).card := Finset.card_filter_le _ _
    _ = m - 2 := Nat.card_Ico 2 m
    _ ≤ m := Nat.sub_le m 2

/-- **Trial division decides primality**: for `x ≥ 2`, `x` is prime iff it has no divisor in `[2, x)`. -/
theorem prime_iff_cntDiv (x : ℕ) (hx : 2 ≤ x) : Nat.Prime x ↔ cntDiv x x = 0 := by
  rw [Nat.prime_def_lt', cntDiv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro ⟨-, h⟩ d hd
    rw [Finset.mem_Ico] at hd
    exact h d hd.1 hd.2
  · intro h
    exact ⟨hx, fun m h2 hlt => h (Finset.mem_Ico.mpr ⟨h2, hlt⟩)⟩

/-! ## One divisor -/

def Rdv : Fin 9 ↪ Fin 80 := ⟨![25, 22, 26, 27, 28, 29, 30, 31, 32], by decide⟩

/-- `r24 += [x mod d = 0]`, `r22 := d + 1` (`r21 = x`, `r22 = d`). -/
def tdBody : WP :=
  .seq (wcopyR 21 25 33) (.seq (UnaryArith.divW Rdv) (.seq (.ifr 25 .skip (.inc 24))
    (.seq (WM.clear 25) (.seq (WM.clear 26) (.inc 22)))))

theorem tdBody_rr (f : Fin 80 → ℕ) (x d z : ℕ) (hx : f 21 = x) (hd : f 22 = d) (hz : f 24 = z) (hd1 : 1 ≤ d)
    (z25 : f 25 = 0) (z26 : f 26 = 0) (z27 : f 27 = 0) (z28 : f 28 = 0) (z29 : f 29 = 0) (z30 : f 30 = 0)
    (z31 : f 31 = 0) (z33 : f 33 = 0) (bx : x ≤ cap) (bd : d + 1 ≤ cap) (bz : z + 1 ≤ cap) :
    RegRun cap tdBody f (Function.update (Function.update f 24 (z + if x % d = 0 then 1 else 0)) 22 (d + 1))
      (8 * (opU cap + 1)) := by
  have hU := lin_le_opU cap
  have hxd : x % d ≤ x := Nat.mod_le x d
  have hqd : x / d ≤ x := Nat.div_le_self x d
  have c1 := wcopy_rr cap 21 25 33 (by decide) (by decide) (by decide) f x hx z25 z33 (by rw [hx]; exact bx)
  have c2 := div_rr cap Rdv 25 22 26 27 28 29 30 31 rfl rfl rfl rfl rfl rfl rfl rfl (Function.update f 25 x) (x % d) (x / d)
    (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hd]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hd, z26]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hd]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z27]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z28])
    (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z29]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z30]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z31]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact bx) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hd]; omega)
    (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z26]; exact bx) (by omega)
  have c3 : RegRun cap (.ifr 25 .skip (.inc 24))
      (Function.update (Function.update (Function.update f 25 x) 25 (x % d)) 26 (x / d))
      (Function.update (Function.update (Function.update (Function.update f 25 x) 25 (x % d)) 26 (x / d)) 24
        (z + if x % d = 0 then 1 else 0)) (opU cap + 1) := by
    refine RegRun.ifr cap 25 (fun h => ?_) (fun h => ?_)
    · have h' : x % d ≠ 0 := by simpa only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add] using h
      refine ((skip_rr cap _).congr cap ?_).mono cap (Nat.zero_le _)
      rw [if_neg h', Nat.add_zero]
      funext r
      simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
      split_ifs <;> subst_vars <;> simp_all
    · have h' : x % d = 0 := by simpa only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add] using h
      rw [if_pos h']
      exact inc_rr cap 24 _ (z + 1) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hz]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hz]; omega)
  have c4 := clear_rr cap 25 (Function.update (Function.update (Function.update (Function.update f 25 x) 25 (x % d)) 26 (x / d)) 24
        (z + if x % d = 0 then 1 else 0)) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
  have c5 := clear_rr cap 26 (Function.update (Function.update (Function.update (Function.update (Function.update f 25 x) 25 (x % d)) 26 (x / d)) 24
        (z + if x % d = 0 then 1 else 0)) 25 0) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
  have c6 := inc_rr cap 22 (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update f 25 x) 25 (x % d)) 26 (x / d)) 24 (z + if x % d = 0 then 1 else 0)) 25 0) 26 0) (d + 1)
    (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hd]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hd]; omega)
  refine ((c1.seq cap (c2.seq cap (c3.seq cap (c4.seq cap (c5.seq cap c6))))).congr cap ?_).mono cap (by omega)
  funext r
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
  split_ifs <;> subst_vars <;> simp_all

/-! ## The divisor loop -/

/-- The register files of the divisor loop: `r23 = n − j`, `r24 = cntDiv x (j+2)`, `r22 = j + 2`. -/
def tdG (f : Fin 80 → ℕ) (x n j : ℕ) : Fin 80 → ℕ :=
  Function.update (Function.update (Function.update f 23 (n - j)) 24 (cntDiv x (j + 2))) 22 (j + 2)

def tdLoop : WP := .whr 23 (.seq (.dec 23) tdBody)

theorem tdLoop_rr (f : Fin 80 → ℕ) (x : ℕ) (hx : f 21 = x) (h2x : 2 ≤ x)
    (z25 : f 25 = 0) (z26 : f 26 = 0) (z27 : f 27 = 0) (z28 : f 28 = 0) (z29 : f 29 = 0) (z30 : f 30 = 0)
    (z31 : f 31 = 0) (z33 : f 33 = 0) (bx : x + 1 ≤ cap) :
    RegRun cap tdLoop (tdG f x (x - 2) 0) (tdG f x (x - 2) (x - 2)) ((x - 2) * (8 * (opU cap + 1) + 4) + 1) := by
  refine RegRun.loop cap 23 tdBody _ (x - 2) (tdG f x (x - 2)) (fun k hk => by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by omega)
    (fun j hj => ?_)
  have hc := cntDiv_le x (j + 2)
  have hb := tdBody_rr cap (Function.update (tdG f x (x - 2) j) 23 (x - 2 - j - 1)) x (j + 2) (cntDiv x (j + 2))
    (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, hx]) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by omega)
    (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z25]) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z26]) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z27]) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z28])
    (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z29]) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z30]) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z31]) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z33])
    (by omega) (by omega) (by omega)
  refine hb.congr cap ?_
  rw [← cntDiv_succ x (j + 2) (by omega)]
  unfold tdG
  have e : x - 2 - j - 1 = x - 2 - (j + 1) := by omega
  rw [e]
  funext r
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
  split_ifs <;> subst_vars <;> simp_all

/-! ## The divisor count of the candidate -/

/-- `r24 := cntDiv x x` from `r21 = x` (scratch `22 … 33` at `0` and restored). -/
def tdPre : WP :=
  .seq (wcopyR 21 23 33) (.seq (.dec 23) (.seq (.dec 23) (.seq (StarNums.incN 22 2) (.seq tdLoop (WM.clear 22)))))

theorem tdPre_rr (f : Fin 80 → ℕ) (x : ℕ) (hx : f 21 = x) (h2x : 2 ≤ x) (z22 : f 22 = 0) (z23 : f 23 = 0)
    (z24 : f 24 = 0) (z25 : f 25 = 0) (z26 : f 26 = 0) (z27 : f 27 = 0) (z28 : f 28 = 0) (z29 : f 29 = 0)
    (z30 : f 30 = 0) (z31 : f 31 = 0) (z33 : f 33 = 0) (bx : x + 1 ≤ cap) :
    RegRun cap tdPre f (Function.update f 24 (cntDiv x x)) (x * (8 * (opU cap + 1) + 4) + 6 * (opU cap + 1)) := by
  have hU := lin_le_opU cap
  have c1 := wcopy_rr cap 21 23 33 (by decide) (by decide) (by decide) f x hx z23 z33 (by rw [hx]; omega)
  have c2 := dec_rr cap 23 (Function.update f 23 x) (x - 1) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
  have c3 := dec_rr cap 23 (Function.update (Function.update f 23 x) 23 (x - 1)) (x - 2) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
  have c4 := incN_rr cap 22 2 (Function.update (Function.update (Function.update f 23 x) 23 (x - 1)) 23 (x - 2)) 2
    (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z22]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z22]; omega)
  have e0 : Function.update (Function.update (Function.update (Function.update f 23 x) 23 (x - 1)) 23 (x - 2)) 22 2 =
      tdG f x (x - 2) 0 := by
    unfold tdG
    rw [cntDiv_two, Nat.sub_zero, Nat.zero_add]
    funext r
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
    split_ifs <;> subst_vars <;> simp_all
  have c5 := tdLoop_rr cap f x hx h2x z25 z26 z27 z28 z29 z30 z31 z33 bx
  rw [← e0] at c5
  have c6 := clear_rr cap 22 (tdG f x (x - 2) (x - 2)) (by unfold tdG; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
  have hx2 : x - 2 + 2 = x := by omega
  refine ((c1.seq cap (c2.seq cap (c3.seq cap (c4.seq cap (c5.seq cap c6))))).congr cap ?_).mono cap ?_
  · unfold tdG
    rw [hx2, Nat.sub_self]
    funext r
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
    split_ifs <;> subst_vars <;> simp_all
  · have hx' : (x - 2) * (8 * (opU cap + 1) + 4) ≤ x * (8 * (opU cap + 1) + 4) := Nat.mul_le_mul_right _ (Nat.sub_le x 2)
    omega

end NearCubicWires.WireExponent3_5.PrimT.W6
