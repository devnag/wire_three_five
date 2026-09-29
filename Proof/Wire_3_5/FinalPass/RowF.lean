import Proof.Wire_3_5.FinalPass.RowChain3
import Proof.Wire_3_5.FinalPass.TermThrEval

/-! # `RowW`, part 6: the digit weights and the unary head (P3:2596-2599)

The digit section of stage 8's row word is `1 1^{w_d} 0` per digit `d < τ₀`, `w_d = 2^d mod p` (`Term.digWord`,
`Term.thrWeights`). `dwBodyW` appends one (`true`, then `1^W 0`) and doubles `W` modulo `p`; `dwLoopW` runs it `τ₀`
times. `unPW` appends `1^p 0`; `unR0W` appends `1^{(p − T) mod p} 0` from `R 41 = T`, `R 42 = p − T`. Main
declarations: `dwBody_spec`, `dwSt`, **`dwLoop_spec`**, `unP_spec`, **`unR0_spec`**. Paper quantities: the digit
weights `2^d mod p` and the head `p`, `r₀` of row `(g, p)`. -/

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

theorem pow_dbl (p k : ℕ) : (2 ^ k % p + 2 ^ k % p) % p = 2 ^ (k + 1) % p := by
  have h : 2 ^ k % p + 2 ^ k % p ≡ 2 ^ k + 2 ^ k [MOD p] := Nat.ModEq.add (Nat.mod_modEq _ _) (Nat.mod_modEq _ _)
  rw [show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring] at h
  exact h

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- One digit weight: `true`, `1^W 0`, then `W := 2W mod p`. -/
def dwBodyW (Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (emitBitW Dg (R 34) true) (.seq (Hash4.wcopyR (R 43) (R 33) (R 39)) (.seq (unW Dg (R 34) (R 33))
    (addModW (R 43) (R 44) (R 43) (R 39) (R 40))))

/-- One digit weight's bound. -/
def dwCost (p : ℕ) : ℕ := 7 + 1 + (18 * p + 3 + 1 + (11 * p + 9 + 1 + (18 * p + 3 + 1 + (p * (7 * p + 12) + 1))))

theorem dwBody_spec (Dg : Fin (ns + 1)) (p W : ℕ) (hpc : p ≤ cap) (hW : W < p) (τ : WState ns nr) (l : List Bool)
    (hst : τ.st Dg = l) (hsh : τ.sh Dg = l.length) (hlw : τ.val (R 34) = l.length) (h43 : τ.val (R 43) = W)
    (h44 : τ.val (R 44) = p - W) (h33 : τ.val (R 33) = 0) (h39 : τ.val (R 39) = 0) (h40 : τ.val (R 40) = 0)
    (hlc : l.length + p + 2 ≤ cap) :
    WExec cap (dwBodyW R Dg) τ
      (outAt ((τ.setv (R 43) ((W + W) % p)).setv (R 44) (p - (W + W) % p)) Dg (R 34) (l ++ (true :: ListEval.unary W)))
      (dwCost p) := by
  have d1 := emitBit_spec cap Dg (R 34) true τ l hst hsh hlw (by omega)
  have d2 := Hash4.wcopyR_spec cap (R 43) (R 33) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (outAt τ Dg (R 34) (l ++ [true])) (by simp [outAt, h33]) (by simp [outAt, h39])
    (by simp [outAt, h43]; omega)
  rw [show (outAt τ Dg (R 34) (l ++ [true])).val (R 43) = W by simp [outAt, h43]] at d2
  have d3 := unW_spec cap Dg (R 34) (R 33) (R.injective.ne (by decide)) W ((outAt τ Dg (R 34) (l ++ [true])).setv (R 33) W)
    (l ++ [true]) (by simp) (by simp [outAt]) (by simp [outAt]) (by simp [outAt]) (by simp; omega)
  have e3 : outAt (((outAt τ Dg (R 34) (l ++ [true])).setv (R 33) W).setv (R 33) 0) Dg (R 34) (l ++ [true] ++
      ListEval.unary W) = outAt τ Dg (R 34) (l ++ (true :: ListEval.unary W)) := by
    rw [wsetv_setv, ← outAt_setv _ _ _ _ (R 33) (R.injective.ne (by decide)), outAt_outAt,
      ThrRead.setv_eq_self τ (R 33) 0 h33, List.append_assoc]; rfl
  rw [e3] at d3
  have d4 := addMod_spec cap (R 43) (R 44) (R 43) (R 39) (R 40) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) p hpc (outAt τ Dg (R 34) (l ++ (true :: ListEval.unary W)))
    W W (by simp [outAt, h39]) (by simp [outAt, h40]) (by simp [outAt, h43]) (by omega) (by simp [outAt, h43])
    (by simp [outAt, h44]) hW
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) ?_ (by
    unfold dwCost
    have : W * (7 * p + 12) ≤ p * (7 * p + 12) := Nat.mul_le_mul_right _ hW.le
    omega)
  rw [← outAt_setv _ _ _ _ (R 43) (R.injective.ne (by decide)), ← outAt_setv _ _ _ _ (R 44) (R.injective.ne (by decide)),
    ← outAt_setv _ _ _ _ (R 39) (R.injective.ne (by decide)), ThrRead.setv_eq_self _ (R 39) 0 (by simp [h39])]

/-- The digit weights loop's state. -/
def dwSt (σ : WState ns nr) (Dg : Fin (ns + 1)) (τ p : ℕ) (l : List Bool) (k : ℕ) : WState ns nr :=
  outAt (((σ.setv (R 35) (τ - k)).setv (R 43) (2 ^ k % p)).setv (R 44) (p - 2 ^ k % p)) Dg (R 34)
    (l ++ Term.digWord ((List.range k).map fun d => 2 ^ d % p))

/-- The digit weights. -/
def dwLoopW (Dg : Fin (ns + 1)) : WM ns nr := countW (R 35) (dwBodyW R Dg)

theorem digWord_len_le (p : ℕ) (hp : 1 ≤ p) :
    ∀ k, (Term.digWord ((List.range k).map fun d => 2 ^ d % p)).length ≤ k * (p + 1)
  | 0 => by simp [Term.digWord]
  | k + 1 => by
    have ih := digWord_len_le p hp k
    have hm : 2 ^ k % p < p := Nat.mod_lt _ (by omega)
    have e : Term.digWord ((List.range (k + 1)).map fun d => 2 ^ d % p) =
        Term.digWord ((List.range k).map fun d => 2 ^ d % p) ++ (true :: ListEval.unary (2 ^ k % p)) := by
      simp only [List.range_succ, List.map_append, Term.digWord, List.flatMap_append, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [e, List.length_append, List.length_cons, ListEval.unary, List.length_append, List.length_replicate,
      List.length_singleton]
    nlinarith

theorem dwLoop_spec (Dg : Fin (ns + 1)) (τ p : ℕ) (hp : 2 ≤ p) (hpc : p ≤ cap) (hτ : τ ≤ cap) (σ : WState ns nr)
    (l : List Bool) (h33 : σ.val (R 33) = 0) (h39 : σ.val (R 39) = 0) (h40 : σ.val (R 40) = 0)
    (hlc : l.length + τ * (p + 1) + p + 2 ≤ cap) :
    WExec cap (dwLoopW R Dg) (dwSt R σ Dg τ p l 0) (dwSt R σ Dg τ p l τ) (τ * (dwCost p + 4) + 1) := by
  refine count_spec cap (R 35) (dwBodyW R Dg) τ (dwCost p) hτ (dwSt R σ Dg τ p l) (fun k _ => by simp [dwSt, outAt])
    (fun k hk => ?_)
  have hm : 2 ^ k % p < p := Nat.mod_lt _ (by omega)
  have hlen := digWord_len_le p (by omega) k
  have dx := dwBody_spec cap R Dg p (2 ^ k % p) hpc hm ((dwSt R σ Dg τ p l k).setv (R 35) (τ - k - 1))
    (l ++ Term.digWord ((List.range k).map fun d => 2 ^ d % p)) (by simp [dwSt]) (by simp [dwSt])
    (by simp [dwSt, outAt]) (by simp [dwSt, outAt]) (by simp [dwSt, outAt]) (by simp [dwSt, outAt, h33])
    (by simp [dwSt, outAt, h39]) (by simp [dwSt, outAt, h40])
    (by simp only [List.length_append]; have : k * (p + 1) ≤ τ * (p + 1) := Nat.mul_le_mul_right _ hk.le; omega)
  refine WExec.cast cap dx ?_ le_rfl
  unfold dwSt
  rw [← outAt_setv _ _ _ _ (R 35) (R.injective.ne (by decide)), ← outAt_setv _ _ _ _ (R 43) (R.injective.ne (by decide)),
    ← outAt_setv _ _ _ _ (R 44) (R.injective.ne (by decide)), outAt_outAt,
    chain3b σ (R 35) (R 43) (R 44) (R.injective.ne (by decide)) (R.injective.ne (by decide))
      (R.injective.ne (by decide)), pow_dbl p k, show τ - (k + 1) = τ - k - 1 by omega]
  congr 1
  simp only [List.range_succ, List.map_append, Term.digWord, List.flatMap_append, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- `1^p 0`. -/
def unPW (Dg : Fin (ns + 1)) : WM ns nr := .seq (Hash4.wcopyR (R 2) (R 33) (R 39)) (unW Dg (R 34) (R 33))

theorem unP_spec (Dg : Fin (ns + 1)) (p : ℕ) (τ : WState ns nr) (l : List Bool) (hP : τ.val (R 2) = p)
    (hst : τ.st Dg = l) (hsh : τ.sh Dg = l.length) (hlw : τ.val (R 34) = l.length) (h33 : τ.val (R 33) = 0)
    (h39 : τ.val (R 39) = 0) (hlc : l.length + p + 1 ≤ cap) :
    WExec cap (unPW R Dg) τ (outAt τ Dg (R 34) (l ++ ListEval.unary p)) (18 * p + 3 + 1 + (11 * p + 9)) := by
  have d1 := Hash4.wcopyR_spec cap (R 2) (R 33) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) τ h33 h39 (by omega)
  rw [hP] at d1
  have d2 := unW_spec cap Dg (R 34) (R 33) (R.injective.ne (by decide)) p (τ.setv (R 33) p) l (by simp)
    (by simp [hst]) (by simp [hsh]) (by simp [hlw]) hlc
  refine WExec.cast cap (WExec.seq d1 d2) ?_ le_rfl
  rw [wsetv_setv, ThrRead.setv_eq_self τ (R 33) 0 h33]

/-- `1^{(p − T) mod p} 0` from `T` in `R 41` and `p − T` in `R 42`. -/
def unR0W (Dg : Fin (ns + 1)) : WM ns nr :=
  .ifr (R 41) (.seq (Hash4.wcopyR (R 42) (R 33) (R 39)) (unW Dg (R 34) (R 33))) (emitBitW Dg (R 34) false)

theorem unR0_spec (Dg : Fin (ns + 1)) (p T : ℕ) (hT : T < p) (τ : WState ns nr) (l : List Bool)
    (h41 : τ.val (R 41) = T) (h42 : τ.val (R 42) = p - T) (hst : τ.st Dg = l) (hsh : τ.sh Dg = l.length)
    (hlw : τ.val (R 34) = l.length) (h33 : τ.val (R 33) = 0) (h39 : τ.val (R 39) = 0) (hlc : l.length + p + 1 ≤ cap) :
    WExec cap (unR0W R Dg) τ (outAt τ Dg (R 34) (l ++ ListEval.unary ((p - T) % p))) (18 * p + 3 + 1 + (11 * p + 9) + 1) := by
  by_cases h0 : T = 0
  · have d := emitBit_spec cap Dg (R 34) false τ l hst hsh hlw (by omega)
    have e : ListEval.unary ((p - T) % p) = [false] := by
      rw [h0, Nat.sub_zero, Nat.mod_self]; rfl
    rw [e]
    exact WExec.mono (WExec.ifrF (by rw [h41, h0]) d) (by omega)
  · have d1 := Hash4.wcopyR_spec cap (R 42) (R 33) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
      (R.injective.ne (by decide)) τ h33 h39 (by omega)
    rw [h42] at d1
    have d2 := unW_spec cap Dg (R 34) (R 33) (R.injective.ne (by decide)) (p - T) (τ.setv (R 33) (p - T)) l (by simp)
      (by simp [hst]) (by simp [hsh]) (by simp [hlw]) (by omega)
    rw [wsetv_setv, ThrRead.setv_eq_self τ (R 33) 0 h33] at d2
    rw [Nat.mod_eq_of_lt (by omega : p - T < p)]
    exact WExec.mono (WExec.ifrT (by rw [h41]; exact h0) (WExec.seq d1 d2)) (by omega)

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
