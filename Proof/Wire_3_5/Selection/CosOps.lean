import Proof.Wire_3_5.Selection.CosTab

/-! # C1.5: the coset loop's small moves (P3:1356-1362)

Paper: "Sum its exact count with the rational population weights, over gates and rows" (P3:1356-1357); "Repeated
labelled occurrences are charged with their weights; they need not be deduplicated" (P3:1361-1362). A population's
gate indices are read one by one from the population table; an index `i < #gates` is turned into a unary count
(`toU`: count `J` up to the index word by C6's `incB`/`ltB`), which the fetch consumes. Also: a stream's head back to
`0` by `k ≥` its position backward moves (`rewS`), a register copied into a zero register (`copyR`), a unary run
`1^m 0` read into a register (`readUn`). Main declarations: **`rewS_spec`**, **`copyR_spec`**, **`readUn_spec`**,
**`toU_spec`**. Paper quantity: a population's gate occurrence as a gate index. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)

variable {ns nr : ℕ}

/-! ## A head back to the start -/

/-- `k` backward moves of stream `i` (counted by `K`, scratch `T`). -/
def rewS (i : Fin (ns + 1)) (K T : Fin nr) : WM ns nr := cloop K T (.bwd i)

theorem rewS_spec (cap : ℕ) (i : Fin (ns + 1)) (K T : Fin nr) (hKT : K ≠ T) (σ : WState ns nr) (k : ℕ)
    (hK : σ.val K = k) (hT : σ.val T = 0) (hk : k ≤ cap) (hp : σ.sh i ≤ k) :
    WExec cap (rewS i K T) σ (σ.seth i 0) (k * (1 + 8) + 1 + 1 + (7 * k + 1)) := by
  have h := Point.cloopM cap K T hKT (.bwd i) (fun σ' j => σ'.seth i (σ.sh i - j)) (fun σ' j v w => by
      simp only [wseth_setv]) σ k 1 hK hT hk (by
      intro j _ v w
      have := WExec.bwd (cap := cap) i (((σ.setv K v).setv T w).seth i (σ.sh i - j))
      refine WExec.cast cap this ?_ le_rfl
      simp only [WState.seth_sh, Function.update_self, wseth_seth]
      congr 1)
  have e0 : σ.seth i (σ.sh i - 0) = σ := WState.eq (by funext j; by_cases hj : j = i <;> simp [hj]) rfl rfl rfl
  have e1 : σ.sh i - k = 0 := by omega
  rw [e0, e1] at h
  exact h

/-! ## A register copied -/

/-- `D := D + K` (counted by `K`, scratch `T`). -/
def copyR (K T D : Fin nr) : WM ns nr := cloop K T (.inc D)

theorem copyR_spec (cap : ℕ) (K T D : Fin nr) (hKT : K ≠ T) (hKD : K ≠ D) (hTD : T ≠ D) (σ : WState ns nr) (k : ℕ)
    (hK : σ.val K = k) (hT : σ.val T = 0) (hD : σ.val D = 0) (hk : k ≤ cap) :
    WExec cap (copyR K T D) σ (σ.setv D k) (k * (3 + 8) + 1 + 1 + (7 * k + 1)) := by
  have h := Point.cloopM cap K T hKT (.inc D) (fun σ' j => σ'.setv D j) (fun σ' j v w => by
      rw [wsetv_comm _ _ _ (Ne.symm hKD), wsetv_comm _ _ _ (Ne.symm hTD)])
    σ k 3 hK hT hk (by
      intro j hj v w
      have := WExec.inc (cap := cap) D (((σ.setv K v).setv T w).setv D j) (by simp; omega)
      refine WExec.cast cap this ?_ le_rfl
      simp [wsetv_setv])
  have e0 : σ.setv D 0 = σ := by rw [← hD, wsetv_same]
  rw [e0] at h
  exact h

/-! ## A unary run -/

/-- Read the run `1^m 0` at the head of `I` into `D` (the head moves past the `0`). -/
def readUn (I : Fin (ns + 1)) (D : Fin nr) : WM ns nr := .seq (.whs I (.seq (.fwd I) (.inc D))) (.fwd I)

theorem readUn_loop (cap : ℕ) (I : Fin (ns + 1)) (D : Fin nr) (σ : WState ns nr) (p m : ℕ)
    (hones : ∀ j < m, readTapeBit (σ.st I) (p + j) = true) (hend : readTapeBit (σ.st I) (p + m) = false)
    (hm : m ≤ cap) : ∀ t ≤ m,
      WExec cap (.whs I (.seq (.fwd I) (.inc D))) ((σ.seth I (p + t)).setv D t)
        ((σ.seth I (p + m)).setv D m) ((m - t) * 7 + 1)
  | t, ht => by
    by_cases htm : t = m
    · subst htm
      refine WExec.cast cap (WExec.whsF ?_) rfl (by omega)
      simp [wbit, hend]
    · have hb : wbit ((σ.seth I (p + t)).setv D t) I = true := by simp [wbit, hones t (by omega)]
      have h1 := WExec.fwd (cap := cap) I ((σ.seth I (p + t)).setv D t)
      have h2 := WExec.inc (cap := cap) D (((σ.seth I (p + t)).setv D t).seth I
        (((σ.seth I (p + t)).setv D t).sh I + 1)) (by simp; omega)
      have ih := readUn_loop cap I D σ p m hones hend hm (t + 1) (by omega)
      have e : (((σ.seth I (p + t)).setv D t).seth I (((σ.seth I (p + t)).setv D t).sh I + 1)).setv D
          ((((σ.seth I (p + t)).setv D t).seth I (((σ.seth I (p + t)).setv D t).sh I + 1)).val D + 1) =
          (σ.seth I (p + (t + 1))).setv D (t + 1) := by
        apply WState.eq
        · funext j; by_cases hj : j = I <;> simp [hj]; omega
        · rfl
        · funext j; by_cases hj : j = D <;> simp [hj]
        · rfl
      rw [e] at h2
      refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) ih) rfl ?_
      have : m - t = (m - (t + 1)) + 1 := by omega
      rw [this]; ring_nf; omega

theorem readUn_spec (cap : ℕ) (I : Fin (ns + 1)) (D : Fin nr) (σ : WState ns nr) (m : ℕ)
    (hones : ∀ j < m, readTapeBit (σ.st I) (σ.sh I + j) = true) (hend : readTapeBit (σ.st I) (σ.sh I + m) = false)
    (hD : σ.val D = 0) (hm : m ≤ cap) :
    WExec cap (readUn I D) σ ((σ.seth I (σ.sh I + m + 1)).setv D m) (m * 7 + 1 + 1 + 1) := by
  have h := readUn_loop cap I D σ (σ.sh I) m hones hend hm 0 (by omega)
  have e0 : (σ.seth I (σ.sh I + 0)).setv D 0 = σ := by
    apply WState.eq
    · funext j; by_cases hj : j = I <;> simp [hj]
    · rfl
    · funext j; by_cases hj : j = D <;> simp [hj, hD]
    · rfl
  rw [e0, Nat.sub_zero] at h
  have h2 := WExec.fwd (cap := cap) I ((σ.seth I (σ.sh I + m)).setv D m)
  refine WExec.cast cap (WExec.seq h h2) ?_ le_rfl
  apply WState.eq
  · funext j; by_cases hj : j = I <;> simp [hj]
  · rfl
  · rfl
  · rfl

/-! ## An index word as a unary count -/

/-- `J := 0`, then count `J` and `GI` up while `J < IX`. Streams `J = S 46`, `IX = S 44`; registers `F₀ = Q 50`,
`GI = Q 54`, `F = Q 61`, `R = Q 62`. -/
def toU (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) : WM ns nr :=
  .seq (zeroB (S 46) (S 44) (Q 61) (Q 62))
    (.seq (ltB (S 46) (S 44) (Q 50) (Q 62))
      (.whr (Q 50) (.seq (.dec (Q 50)) (.seq (incB (S 46) (S 44) (Q 61) (Q 62))
        (.seq (.inc (Q 54)) (ltB (S 46) (S 44) (Q 50) (Q 62)))))))

/-- The counting state after `t` rounds. -/
def uSt (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) (σ : WState ns nr) (W i t : ℕ) : WState ns nr :=
  ((σ.sets (S 46) (frame (binary W t))).setv (Q 54) t).setv (Q 50) (decide (t < i)).toNat

/-- One round's cost. -/
def uRound (W : ℕ) : ℕ := 1 + 1 + (41 * W + 7 + 1 + (3 + 1 + (41 * W + 3)))


/-- The count's cost. -/
def toUCost (W i : ℕ) : ℕ := 41 * W + 3 + 1 + (41 * W + 3 + 1 + (i * (uRound W + 2) + 1))

section U
variable (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr) (hQ : Function.Injective Q)
variable (cap W : ℕ)
include hS hQ

theorem toU_round (σ : WState ns nr) (i t : ℕ) (ht : t < i) (hi : i < 2 ^ W) (hIX : NumOn σ (S 44) W i)
    (h46 : σ.sh (S 46) = 0) (q61 : σ.val (Q 61) = 0) (q62 : σ.val (Q 62) = 0) (hc : i ≤ cap)
    (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (.seq (.dec (Q 50)) (.seq (incB (S 46) (S 44) (Q 61) (Q 62)) (.seq (.inc (Q 54))
      (ltB (S 46) (S 44) (Q 50) (Q 62))))) (uSt S Q σ W i t) (uSt S Q σ W i (t + 1)) (uRound W) := by
  have hJX : S 46 ≠ S 44 := hS.ne (by decide)
  have q50_54 : Q 50 ≠ Q 54 := hQ.ne (by decide)
  have q50_61 : Q 50 ≠ Q 61 := hQ.ne (by decide)
  have q50_62 : Q 50 ≠ Q 62 := hQ.ne (by decide)
  have q54_61 : Q 54 ≠ Q 61 := hQ.ne (by decide)
  have q54_62 : Q 54 ≠ Q 62 := hQ.ne (by decide)
  have q61_62 : Q 61 ≠ Q 62 := hQ.ne (by decide)
  have hF1 : (uSt S Q σ W i t).val (Q 50) = 1 := by simp [uSt, ht]
  have d1 := WExec.dec (cap := cap) (Q 50) (uSt S Q σ W i t) (by rw [hF1]; omega)
  rw [hF1] at d1
  set σ1 := (uSt S Q σ W i t).setv (Q 50) (1 - 1) with hσ1
  have d2 := incB_spec cap W (A := S 46) (B := S 44) (F := Q 61) (R := Q 62) hJX q61_62 σ1 t i
    ⟨by simp [hσ1, uSt], by simp [hσ1, uSt, h46]⟩ ⟨by simp [hσ1, uSt, Ne.symm hJX, hIX.1], by simp [hσ1, uSt, hIX.2]⟩
    (by simp [hσ1, uSt, Ne.symm q50_61, Ne.symm q54_61, q61])
    (by simp [hσ1, uSt, Ne.symm q50_62, Ne.symm q54_62, q62]) (by omega) hcap
  set σ2 := σ1.sets (S 46) (frame (binary W (t + 1))) with hσ2
  have hG2 : σ2.val (Q 54) = t := by simp [hσ2, hσ1, uSt, Function.update_apply, Ne.symm q50_54]
  have d3 := WExec.inc (cap := cap) (Q 54) σ2 (by rw [hG2]; omega)
  rw [hG2] at d3
  set σ3 := σ2.setv (Q 54) (t + 1) with hσ3
  have d4 := ltB_spec cap W (A := S 46) (B := S 44) (F := Q 50) (R := Q 62) hJX q50_62 σ3 (t + 1) i
    ⟨by simp [hσ3, hσ2], by simp [hσ3, hσ2, hσ1, uSt, h46]⟩
    ⟨by simp [hσ3, hσ2, hσ1, uSt, Ne.symm hJX, hIX.1], by simp [hσ3, hσ2, hσ1, uSt, hIX.2]⟩
    (by simp [hσ3, hσ2, hσ1, q50_54]) (by simp [hσ3, hσ2, hσ1, uSt, Ne.symm q50_62, Ne.symm q54_62, q62])
    (by omega) hi hcap
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) ?_ (by unfold uRound; omega)
  apply WState.eq
  · simp [hσ3, hσ2, hσ1, uSt]
  · simp [hσ3, hσ2, hσ1, uSt]
  · funext r
    by_cases h50 : r = Q 50
    · subst h50; simp [hσ3, hσ2, hσ1, uSt]
    · by_cases h54 : r = Q 54
      · subst h54; simp [hσ3, hσ2, hσ1, uSt, Ne.symm q50_54]
      · simp [hσ3, hσ2, hσ1, uSt, Function.update_apply, h50, h54]
  · simp [hσ3, hσ2, hσ1, uSt]

theorem toU_loop (σ : WState ns nr) (i : ℕ) (hi : i < 2 ^ W) (hIX : NumOn σ (S 44) W i) (h46 : σ.sh (S 46) = 0)
    (q61 : σ.val (Q 61) = 0) (q62 : σ.val (Q 62) = 0) (hc : i ≤ cap) (hcap : 2 * W + 1 ≤ cap) :
    ∀ m t, t + m = i →
      WExec cap (.whr (Q 50) (.seq (.dec (Q 50)) (.seq (incB (S 46) (S 44) (Q 61) (Q 62)) (.seq (.inc (Q 54))
        (ltB (S 46) (S 44) (Q 50) (Q 62)))))) (uSt S Q σ W i t) (uSt S Q σ W i i) (m * (uRound W + 2) + 1)
  | 0, t, h => by
    have ht : t = i := by omega
    subst ht
    refine WExec.cast cap (WExec.whrF ?_) rfl (by omega)
    simp [uSt]
  | m + 1, t, h => by
    have ht : t < i := by omega
    have r := toU_round S hS Q hQ cap W σ i t ht hi hIX h46 q61 q62 hc hcap
    have ih := toU_loop σ i hi hIX h46 q61 q62 hc hcap m (t + 1) (by omega)
    refine WExec.cast cap (WExec.whrT ?_ r ih) rfl (by ring_nf; omega)
    simp [uSt, ht]

/-- **The index as a unary count**: `J := i`, `GI := i` (from `GI = 0`, `F₀ = 0`). -/
theorem toU_spec (σ : WState ns nr) (j0 i : ℕ) (hJ : NumOn σ (S 46) W j0) (hIX : NumOn σ (S 44) W i)
    (hi : i < 2 ^ W) (q50 : σ.val (Q 50) = 0) (q54 : σ.val (Q 54) = 0) (q61 : σ.val (Q 61) = 0)
    (q62 : σ.val (Q 62) = 0) (hc : i ≤ cap) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (toU S Q) σ ((σ.sets (S 46) (frame (binary W i))).setv (Q 54) i) (toUCost W i) := by
  have hJX : S 46 ≠ S 44 := hS.ne (by decide)
  have q50_62 : Q 50 ≠ Q 62 := hQ.ne (by decide)
  have q61_62 : Q 61 ≠ Q 62 := hQ.ne (by decide)
  have z := zeroB_spec cap W (A := S 46) (B := S 44) (F := Q 61) (R := Q 62) hJX q61_62 σ j0 i hJ hIX q61 q62 hcap
  have l := ltB_spec cap W (A := S 46) (B := S 44) (F := Q 50) (R := Q 62) hJX q50_62 (σ.sets (S 46)
    (frame (binary W 0))) 0 i ⟨by simp, by simp [hJ.2]⟩ ⟨by simp [Ne.symm hJX, hIX.1], by simp [hIX.2]⟩
    (by simp [q50]) (by simp [q62]) (by omega) hi hcap
  have e0 : (σ.sets (S 46) (frame (binary W 0))).setv (Q 50) (decide (0 < i)).toNat = uSt S Q σ W i 0 := by
    unfold uSt
    congr 1
    rw [Gate.wsetv_zero _ _ (by simp [q54])]
  rw [e0] at l
  have lp := toU_loop S hS Q hQ cap W σ i hi hIX hJ.2 q61 q62 hc hcap i 0 (by omega)
  have e1 : uSt S Q σ W i i = (σ.sets (S 46) (frame (binary W i))).setv (Q 54) i := by
    unfold uSt
    rw [show (decide (i < i)).toNat = 0 by simp]
    exact Gate.wsetv_zero _ _ (by simp [hQ.ne (show (50 : Fin 64) ≠ 54 by decide), q50])
  rw [e1] at lp
  unfold toU toUCost
  exact WExec.seq z (WExec.seq l lp)

end U

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
