import Proof.Wire_3_5.FinalPass.DigsDig3

/-! # `DigsW`'s body, part 7: one circuit's term of the stack base (P3:2543-2551)

The stack base is `base = 1 + Σ_i ‖child_i‖` with `‖child‖ = Σ_k |w_k| + |t|` (`EqRead.baseOf_eq`,
`childMagnitude_eq`). `cBodyBW` on circuit `i`'s payload: to the selected child, then over its `S + 1` integers
(weights, then the target) `Bm := (Bm + |z| mod p) mod p` (`bBodyW` = `absW2W` + `addLoopW`, with `R 24 = p − Bm`),
back to the start. `bfold` is the running residue. Main declarations: `bfold`, `bfold_take`, `bBody_spec`,
`bInts_spec`, **`cBodyB_spec`**. Paper quantity: `(1 + Σ_{j ≤ i} ‖child_j‖) mod p`, the stack base modulo `p`. -/

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

/-- The running residue: `x`, then `(acc + |z| mod p) mod p` per integer. -/
def bfold (p x : ℕ) (zs : List ℤ) : ℕ := zs.foldl (fun acc z => (acc + z.natAbs % p) % p) x

theorem bfold_take (p x : ℕ) (zs : List ℤ) (k : ℕ) (hk : k < zs.length) :
    bfold p x (zs.take (k + 1)) = (bfold p x (zs.take k) + zs[k].natAbs % p) % p := by
  unfold bfold
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem bfold_lt (p x : ℕ) (hp : 0 < p) (hx : x < p) : ∀ zs : List ℤ, bfold p x zs < p
  | [] => hx
  | z :: zs => by
    unfold bfold; rw [List.foldl_cons]
    exact bfold_lt p _ hp (Nat.mod_lt _ hp) zs

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- One integer: `Bm := (Bm + |z| mod p) mod p`. -/
def bBodyW (E : Fin (ns + 1)) : WM ns nr := .seq (absW2W E (R 14) (Rg R)) (addLoopW (R 23) (R 24) (R 5))

theorem bBody_spec (E : Fin (ns + 1)) (z : ℤ) (c rest : List Bool) (j p x : ℕ) (hp : 1 ≤ p) (hpc : p ≤ cap)
    (hx : x < p) (τ : WState ns nr) (hst : τ.st E = frame c) (hs : τ.sh E = 2 * j + 1) (hpj : τ.val (R 14) = j)
    (hd : c.drop j = intWord z ++ rest) (hP : τ.val (R 2) = p) (h23 : τ.val (R 23) = x) (h24 : τ.val (R 24) = p - x)
    (hz : Zs R τ coreL) (hjc : j + (intWord z).length ≤ cap) :
    WExec cap (bBodyW R E) τ
      (at2 ((τ.setv (R 23) ((x + z.natAbs % p) % p)).setv (R 24) (p - (x + z.natAbs % p) % p)) E (R 14)
        (j + (intWord z).length)) (modCost2 (natBitLength z.natAbs) p + 1 + (p * (7 * p + 12) + 1)) := by
  have hpos : 0 < p := by omega
  have d1 := absW2_spec cap E (R 14) (Rg R) (Rg_ne_Pc R) z c rest j p hp hpc τ hst hs hpj hd (by simp [hP])
    (core_zero R _ hz) hjc
  rw [Rg1] at d1
  have hk : z.natAbs % p < p := Nat.mod_lt _ hpos
  have d2 := addLoop_spec cap (R 23) (R 24) (R 5) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) p hpc (z.natAbs % p) (at2 (τ.setv (R 5) (z.natAbs % p)) E (R 14)
      (j + (intWord z).length)) x (by simp [at2]) (by omega) (by simp [at2, h23]) (by simp [at2, h24]) hx
  refine WExec.cast cap (WExec.seq d1 d2) ?_ (by
    have : z.natAbs % p * (7 * p + 12) ≤ p * (7 * p + 12) := Nat.mul_le_mul_right _ hk.le
    omega)
  have h5 := hz 5 (by decide)
  clear d1 d2 hz
  refine WState.eq ?_ ?_ ?_ ?_
  · wst_sh
  · wst_st
  · funext y
    by_cases y1 : y = R 5
    · rw [y1]; simp_all [at2, Function.update_apply]
    by_cases y2 : y = R 23
    · rw [y2]; simp_all [at2, Function.update_apply]
    by_cases y3 : y = R 24
    · rw [y3]; simp_all [at2, Function.update_apply]
    by_cases y4 : y = R 14
    · rw [y4]; simp_all [at2, Function.update_apply]
    simp_all [at2, Function.update_apply]
  · rfl

/-- The base loop's state: reading position `j`, countdown `k`, running residue `b`. -/
def bSt (τ : WState ns nr) (E : Fin (ns + 1)) (p j k b : ℕ) : WState ns nr :=
  at2 (((τ.setv (R 20) k).setv (R 23) b).setv (R 24) (p - b)) E (R 14) j

/-- The integers: `R 20` counted down, one term each. -/
def bIntsW (E : Fin (ns + 1)) : WM ns nr := countW (R 20) (bBodyW R E)

theorem bInts_spec (E : Fin (ns + 1)) (zs : List ℤ) (Lm : ℕ) (hLm : ∀ z ∈ zs, natBitLength z.natAbs ≤ Lm)
    (c rest : List Bool) (j0 p x : ℕ) (hp : 1 ≤ p) (hpc : p ≤ cap) (hx : x < p) (τ : WState ns nr)
    (hst : τ.st E = frame c) (hd : c.drop j0 = zs.flatMap intWord ++ rest) (hP : τ.val (R 2) = p)
    (hz : Zs R τ coreL) (hjc : j0 + (zs.flatMap intWord).length ≤ cap) (hn : zs.length ≤ cap) :
    WExec cap (bIntsW R E) (bSt R τ E p j0 zs.length x)
      (bSt R τ E p (j0 + (zs.flatMap intWord).length) 0 (bfold p x zs))
      (zs.length * (modCost2 Lm p + 1 + (p * (7 * p + 12) + 1) + 4) + 1) := by
  have hpos : 0 < p := by omega
  have hF := count_spec cap (R 20) (bBodyW R E) zs.length (modCost2 Lm p + 1 + (p * (7 * p + 12) + 1)) hn
    (fun k => bSt R τ E p (j0 + ((zs.take k).flatMap intWord).length) (zs.length - k) (bfold p x (zs.take k)))
    (fun k _ => by simp [bSt, at2])
    (fun k hk => by
      have hsplit := fm_split zs k
      have hdk := fm_drop zs k hk
      have htk := fm_take zs k hk
      have hlen : ((zs.take k).flatMap intWord).length + (intWord zs[k]).length ≤ (zs.flatMap intWord).length := by
        rw [hsplit, hdk]; simp
      have hbl := bfold_lt p x hpos hx (zs.take k)
      have d := bBody_spec cap R E zs[k] c ((zs.drop (k + 1)).flatMap intWord ++ rest)
        (j0 + ((zs.take k).flatMap intWord).length) p (bfold p x (zs.take k)) hp hpc hbl
        ((bSt R τ E p (j0 + ((zs.take k).flatMap intWord).length) (zs.length - k) (bfold p x (zs.take k))).setv (R 20)
          (zs.length - k - 1))
        (by simp [bSt, at2, hst]) (by simp [bSt, at2]) (by simp [bSt, at2])
        (by rw [← List.drop_drop, hd, hsplit, List.append_assoc, List.drop_left, hdk, List.append_assoc])
        (by simp [bSt, at2, hP]) (by simp [bSt, at2]) (by simp [bSt, at2])
        (fun r hr => by
          have h20 : r ≠ 20 := by rintro rfl; revert hr; decide
          have h23 : r ≠ 23 := by rintro rfl; revert hr; decide
          have h24 : r ≠ 24 := by rintro rfl; revert hr; decide
          have h14 : r ≠ 14 := by rintro rfl; revert hr; decide
          have := hz r hr
          simp [bSt, at2, Function.update_apply, R.injective.ne h20, R.injective.ne h23, R.injective.ne h24,
            R.injective.ne h14, this])
        (by omega)
      refine WExec.cast cap d ?_ (by
        have h1 := hLm zs[k] (List.getElem_mem hk)
        unfold modCost2 coreCost
        have : natBitLength zs[k].natAbs * (bitCost2 p + 2) ≤ Lm * (bitCost2 p + 2) := Nat.mul_le_mul_right _ h1
        omega)
      rw [bfold_take p x zs k hk, htk, show zs.length - (k + 1) = zs.length - k - 1 by omega, ← Nat.add_assoc]
      unfold bSt; clear d hsplit hdk htk hlen hbl hz
      refine WState.eq ?_ ?_ ?_ ?_
      · wst_sh
      · wst_st
      · funext y
        by_cases y1 : y = R 20
        · rw [y1]; simp_all [at2, Function.update_apply]
        by_cases y2 : y = R 23
        · rw [y2]; simp_all [at2, Function.update_apply]
        by_cases y3 : y = R 24
        · rw [y3]; simp_all [at2, Function.update_apply]
        by_cases y4 : y = R 14
        · rw [y4]; simp_all [at2, Function.update_apply]
        simp_all [at2, Function.update_apply]
      · rfl)
  have e0 : bSt R τ E p (j0 + ((zs.take 0).flatMap intWord).length) (zs.length - 0) (bfold p x (zs.take 0)) =
      bSt R τ E p j0 zs.length x := by simp [bfold]
  rw [e0, Nat.sub_self, List.take_length] at hF
  exact hF

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
