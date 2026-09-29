import Proof.Wire_3_5.FinalPass.FreeGen5

/-! # The free numbers, v2, part 1: `freeW`'s exact exit state and the constant powers

"Their coefficients and targets have `O(ℓ+log(f+2))` bits" (alg:disjoint, P3:1596-1615: the pool children's bits are
the pool gates' own weight bits, `poly(n)`), so the compiler's `h` and `pr` are polynomial in `n`, and "`Q' = Q+m−1`"
with `2^Q > J` (P3:1886-1890) is `O(k+L)`. The v2 program runs FreeGen's `freeW` at `dQ = dH = dP = 0` and then
rewrites `Q'`, `h`, `pr`; this part gives the pieces:
* **`freeW_exec`**: `freeW κ` ends in `freeOut κ x σ` (FreeGen4's run, with its exit state named), `freeOut_val`;
* `powLoop e S`, **`powLoop_spec`**: `S0 := S0·S1^e` by `e` products (a program by recursion on the constant `e`).
Paper quantities of the main types: the free numbers' exit registers and the powers `(n+1)^e`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.SymQM NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- **`freeW κ` ends in `freeOut κ x σ`** (FreeGen4's run with the exit state named). -/
theorem freeW_exec (κ : FreeK) (cap : ℕ) (σ : WState (LNS 0) LNR) (x : FreeIn) (hR : FreeRegs σ x)
    (hF : ∀ q : Fin LNR, 130 ≤ q.val → q.val < 137 → σ.val q = 0)
    (hS : ∀ q : Fin LNR, 177 ≤ q.val → q.val < 200 → σ.val q = 0) (hc : need κ x ≤ cap) :
    WExec cap (freeW κ) σ (freeOut κ x σ) (200 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hn : σ.val (Gall 30) = x.n := hR.1
  have hkh : σ.val (Gall 31) = x.kh := hR.2.1
  have hnc : σ.val (Gall 32) = x.nc := hR.2.2.2.2.2.1
  have ha : σ.val (Gall 33) = x.a := hR.2.2.2.2.1
  have hM : σ.val (Gall 34) = x.M := hR.2.2.2.2.2.2.1
  have hz0 : ∀ k : Fin 35, k.val < 30 → σ.val (Gall k) = 0 := by
    intro k hk
    rcases Gall_range k hk with h | h
    · exact hF _ h.1 h.2
    · exact hS _ h.1 h.2
  unfold need at hc
  generalize hP : 2 ^ (κ.dC * (β x * β x) + 1) = P at hc
  have hg4 : β x * β x ≤ β x * β x * (β x * β x) + 1 := by
    rcases Nat.eq_zero_or_pos (β x * β x) with h | h
    · omega
    · have := Nat.le_mul_of_pos_left (β x * β x) h; omega
  unfold freeW
  refine seqD cap _ 30 (betaW_spec cap (eB.trans Gall) σ x.n (by simp [hn]) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 5 (sqW_spec cap (eS1.trans Gall) _ (β x) (by simp [β]) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 5 (sqW_spec cap (eS2.trans Gall) _ (β x * β x) (by simp) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 5 (mulW_spec cap (eM3.trans Gall) _ (β x * β x * (β x * β x)) (β x * β x) (by simp) (by simp)
    (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 5 (cmulW_spec cap κ.dT (eT.trans Gall) _ (β x * β x) (by simp) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega)
    (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 5 (cmulW_spec cap κ.dQ (eQ.trans Gall) _ (β x * β x) (by simp) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega)
    (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 5 (cmulW_spec cap κ.dH (eH.trans Gall) _ (β x * β x) (by simp) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega)
    (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 5 (cmulW_spec cap κ.dP (eP.trans Gall) _ (β x * β x * (β x * β x) * (β x * β x)) (by simp)
    (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 5 (cmulW_spec cap κ.dC (eC.trans Gall) _ (β x * β x) (by simp) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega)
    (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (pow2v cap (eW2.trans Gall) (κ.dC * (β x * β x)) _ (by simp) (by simp [hz0]) (by simp [hz0])
    (by simp [hz0]) (by rw [hP]; omega)) (by omega) (by omega) ?_
  refine seqD cap _ 16 (wlW_spec cap (eL.trans Gall) _ (β x) (by simp [β]) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Gall 31) (Gall 22) (Gall 26) (by simp) (by simp) (by simp) x.kh _ (by simp [hkh])
    (by simp [hz0]) (by simp [hz0]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Gall 32) (Gall 23) (Gall 26) (by simp) (by simp) (by simp) x.nc _ (by simp [hnc])
    (by simp [hz0]) (by simp [hz0]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Gall 33) (Gall 24) (Gall 26) (by simp) (by simp) (by simp) x.a _ (by simp [ha])
    (by simp [hz0]) (by simp [hz0]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Gall 34) (Gall 25) (Gall 26) (by simp) (by simp) (by simp) x.M _ (by simp [hM])
    (by simp [hz0]) (by simp [hz0]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 40 (mW_spec cap κ.mA κ.mB κ.mC κ.mD κ.mF κ.mE (eMm.trans Gall) _ x.nc x.a
    (2 * ((β x + 5) / 2 / 2) + 1) x.M (by simp) (by simp) (by simp) (by simp)
    (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by rw [W_eq]; omega)) (by omega) (by omega) ?_
  exact endD cap _ 30 (rhoW_spec cap κ.dA κ.dR (eR.trans Gall) _ x.n x.kh (β x) (β x * β x) (by simp [hn]) (by simp)
    (by simp [β]) (by simp) (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [hz0]) (by omega)) rfl (by omega)
    (by omega)

/-- `freeOut` off the registers it sets is the entry state. -/
theorem freeOut_val (κ : FreeK) (x : FreeIn) (σ : WState (LNS 0) LNR) (k : Fin 35)
    (hk : k ∉ ({8, 17, 18, 19, 0, 2, 3, 5, 20, 1, 21, 22, 23, 24, 25, 4, 6} : Finset (Fin 35))) :
    (freeOut κ x σ).val (Gall k) = σ.val (Gall k) := by
  have hne : ∀ j : Fin 35, j ∈ ({8, 17, 18, 19, 0, 2, 3, 5, 20, 1, 21, 22, 23, 24, 25, 4, 6} : Finset (Fin 35)) →
      Gall k ≠ Gall j := fun j hj h => hk (Gall.injective h ▸ hj)
  simp only [freeOut, WState.setv_val, Function.update_apply]
  simp [hne _ (by decide : (8 : Fin 35) ∈ _), hne _ (by decide : (17 : Fin 35) ∈ _), hne _ (by decide : (18 : Fin 35) ∈ _),
    hne _ (by decide : (19 : Fin 35) ∈ _), hne _ (by decide : (0 : Fin 35) ∈ _), hne _ (by decide : (2 : Fin 35) ∈ _),
    hne _ (by decide : (3 : Fin 35) ∈ _), hne _ (by decide : (5 : Fin 35) ∈ _), hne _ (by decide : (20 : Fin 35) ∈ _),
    hne _ (by decide : (1 : Fin 35) ∈ _), hne _ (by decide : (21 : Fin 35) ∈ _), hne _ (by decide : (22 : Fin 35) ∈ _),
    hne _ (by decide : (23 : Fin 35) ∈ _), hne _ (by decide : (24 : Fin 35) ∈ _), hne _ (by decide : (25 : Fin 35) ∈ _),
    hne _ (by decide : (4 : Fin 35) ∈ _), hne _ (by decide : (6 : Fin 35) ∈ _)]

theorem freeOut_beta (κ : FreeK) (x : FreeIn) (σ : WState (LNS 0) LNR) : (freeOut κ x σ).val (Gall 8) = β x := by
  simp [freeOut, Function.update_apply]

theorem freeOut_fb (κ : FreeK) (x : FreeIn) (σ : WState (LNS 0) LNR) (j : Fin 7) :
    (freeOut κ x σ).val (FB j) = freeVal κ x j := by
  fin_cases j <;> simp [freeOut, freeVal, W_eq, Nat.sub_sub] <;> rfl

/-! ## Constant powers -/

variable {ns nr : ℕ} (cap : ℕ)

/-- `S0 := S0·S1^e` (`e` products `mulByW`). -/
def powLoop (S : Fin 5 ↪ Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | e + 1 => .seq (powLoop S e) (mulByW S)

theorem powLoop_spec (S : Fin 5 ↪ Fin nr) (x y : ℕ) (hy : y ≤ cap) :
    ∀ (e : ℕ) (σ : WState ns nr), σ.val (S 0) = x → σ.val (S 1) = y → σ.val (S 2) = 0 → σ.val (S 3) = 0 →
      σ.val (S 4) = 0 → x * y ^ e ≤ cap → (∀ j ≤ e, x * y ^ j ≤ cap) →
      WExec cap (powLoop S e) σ (σ.setv (S 0) (x * y ^ e)) (e * (4 * UnaryPow.sq cap))
  | 0, σ, h0, _, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.skip σ) ?_ (by omega)
    rw [pow_zero, Nat.mul_one, ← h0]
    exact (wsetv_same σ (S 0)).symm
  | e + 1, σ, h0, h1, h2, h3, h4, hc, hj => by
    have hsq := UnaryPow.sq_ge cap
    have hne : ∀ {i j : Fin 5}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
    have ih := powLoop_spec S x y hy e σ h0 h1 h2 h3 h4 (hj e (by omega)) (fun j hj' => hj j (by omega))
    have h2' := mulBy1 cap S (x * y ^ e) y (σ.setv (S 0) (x * y ^ e)) (by simp)
      (by simp [hne (show (1 : Fin 5) ≠ 0 by decide), h1]) (by simp [hne (show (2 : Fin 5) ≠ 0 by decide), h2])
      (by simp [hne (show (3 : Fin 5) ≠ 0 by decide), h3]) (by simp [hne (show (4 : Fin 5) ≠ 0 by decide), h4])
      (by rw [Nat.mul_assoc, ← pow_succ]; exact hc) (hj e (by omega)) hy
    refine WExec.cast cap (WExec.seq ih h2') ?_ ?_
    · rw [wsetv_setv, Nat.mul_assoc, ← pow_succ]
    · rw [Nat.add_mul, Nat.one_mul]; omega

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

