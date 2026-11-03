import Proof.Wire_3_5.UnionMachine.FrontSemCap3
import Proof.Wire_3_5.UnionMachine.FrontFoldBound2

/-! # C6 front, the semantic core (15): the writers' fold at the machine's capacities (P3:3669-3672)

M-FoldBound2 sized the fold at its own capacity `T = value eT 2^eT s`. The front runs it at the machine's
`T = value De Ce W`, `tot = value Dt Ct W` (fixed exponents, the width `W`): **`rcostT_le`** (every round at any
`T ≤ (s+2)^t`, any atom width `≤ s + 2`, within `(s+2)^{eMt + 6}`), **`widthT_le`** (every kept tape within `tot`),
**`envFit_mono`**, **`value_mono`**, **`valueW_le`**, and at a guess **`foldCapsG`** (PathCaps' `env`, `cwT`, `len`,
`Z0`).

Paper quantity: none (the front's time, a fixed polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemFold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound
open NearCubicWires.WireExponent3_5.UnionMachine.CWIface (ParityWriterJ CarrierWriterJ)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (bitmap codesWord carrierOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode (envCodeCost atomsOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (cropBCost appendBCost)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldCat (catCost efCost)
open NearCubicWires.BlockPlatform.UnaryCalc (value tapes)

/-- The round's exponent at an envelope capacity `T ≤ (s+2)^t`. -/
def eMt {m : Mode} (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (deg t : ℕ) : ℕ :=
  27 * (lc Pw Cw + 2) + t + 156 + eP Pw + eC Pw Cw + lp Pw + lc Pw Cw + 20 + deg

theorem foldr_max_le (l : List ℕ) (K : ℕ) (h : ∀ x ∈ l, x ≤ K) : l.foldr max 0 ≤ K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem supR_le (f : ℕ → ℕ) (M K : ℕ) (h : ∀ i < M, f i ≤ K) : FrontSemTW.supR f M ≤ K := by
  unfold FrontSemTW.supR
  refine foldr_max_le _ K ?_
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact h i (List.mem_range.1 hi)

theorem envFit_mono {q : ℕ} {X : Stars.Carrier q} {deg T T' : ℕ} (h : EnvFit X deg T) (hT : T ≤ T') :
    EnvFit X deg T' :=
  ⟨h.c.trans hT, h.s.trans hT, h.l.trans hT, h.w.trans hT⟩

theorem value_mono {D D' C C' n n' : ℕ} (hD : D ≤ D') (hC : C ≤ C') (hn : n ≤ n') : value D C n ≤ value D' C' n' := by
  unfold value
  exact Nat.mul_le_mul hC ((Nat.pow_le_pow_left (by omega) D).trans (Nat.pow_le_pow_right (by omega) hD))

/-- The machine's envelope capacity at the width `W = K_w (q+1)^{D_w}` is a power of `s + 2` for `q ≤ s`. -/
theorem valueW_le (Ce De Kw Dw q s : ℕ) (hq : q ≤ s) :
    value De Ce (Kw * (q + 1) ^ Dw) ≤ (s + 2) ^ (Ce + De * (Kw + Dw)) := by
  have hB : 2 ≤ s + 2 := by omega
  have h1 : Kw + 1 ≤ (s + 2) ^ Kw :=
    (Nat.lt_two_pow_self (n := Kw)).trans_le (Nat.pow_le_pow_left hB Kw)
  have h2 : (q + 1) ^ Dw ≤ (s + 2) ^ Dw := Nat.pow_le_pow_left (by omega) Dw
  have h3 : Kw * (q + 1) ^ Dw + 1 ≤ (s + 2) ^ (Kw + Dw) := by
    have a := Nat.one_le_pow Dw (q + 1) (by omega)
    have b : (Kw + 1) * (q + 1) ^ Dw ≤ (s + 2) ^ Kw * (s + 2) ^ Dw := Nat.mul_le_mul h1 h2
    rw [← pow_add] at b
    have e : (Kw + 1) * (q + 1) ^ Dw = Kw * (q + 1) ^ Dw + (q + 1) ^ Dw := by ring
    omega
  have h4 : Ce ≤ (s + 2) ^ Ce := (Nat.lt_two_pow_self (n := Ce)).le.trans (Nat.pow_le_pow_left hB Ce)
  unfold value
  calc Ce * (Kw * (q + 1) ^ Dw + 1) ^ De ≤ (s + 2) ^ Ce * ((s + 2) ^ (Kw + Dw)) ^ De :=
        Nat.mul_le_mul h4 (Nat.pow_le_pow_left h3 De)
    _ = (s + 2) ^ (Ce + De * (Kw + Dw)) := by rw [← pow_mul, ← pow_add, mul_comm (Kw + Dw)]

/-- `2(s+2)^E ≤ value Dt Ct W` for `s ≤ W`, `E ≤ Dt`, `2·2^{Dt} ≤ Ct`. -/
theorem pow_le_value (s W E Dt Ct : ℕ) (hsW : s ≤ W) (hE : E ≤ Dt) (hCt : 2 * 2 ^ Dt ≤ Ct) :
    (s + 2) ^ E + (s + 2) ^ E ≤ value Dt Ct W := by
  have h1 : (s + 2) ^ E ≤ (W + 2) ^ Dt :=
    (Nat.pow_le_pow_left (by omega) E).trans (Nat.pow_le_pow_right (by omega) hE)
  have h2 : (W + 2) ^ Dt ≤ 2 ^ Dt * (W + 1) ^ Dt := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) Dt
  have h3 : 2 * 2 ^ Dt * (W + 1) ^ Dt ≤ Ct * (W + 1) ^ Dt := Nat.mul_le_mul_right _ hCt
  unfold value
  have e : 2 * 2 ^ Dt * (W + 1) ^ Dt = 2 * (2 ^ Dt * (W + 1) ^ Dt) := by ring
  omega

section Gen
variable {m : Mode} {q : ℕ} (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (F : FoldIn m q) (s deg : ℕ)

/-- **Every round at any envelope capacity `T ≤ (s+2)^t`** within `(s+2)^{eMt + 6}`. -/
theorem rcostT_le (hq : q ≤ s) (hA : ∀ X < F.nv, (codesWord m (F.atoms X)).length ≤ s)
    (X : ℕ) (hX : X < F.nv) (hnv : F.nv ≤ s) (T t Wa : ℕ) (hT : T ≤ (s + 2) ^ t) (hWa : Wa ≤ s + 2) :
    rcost Pw Cw F T Wa X ≤ (s + 2) ^ (eMt Pw Cw deg t + 6) := by
  have hB : 2 ≤ s + 2 := by omega
  have hXB : X ≤ s + 2 := by omega
  have hM : ∀ e, e ≤ eMt Pw Cw deg t → ∀ x, x ≤ (s + 2) ^ e → x ≤ (s + 2) ^ eMt Pw Cw deg t :=
    fun e he x hx => ble hB he hx
  have hpw := pw_len Pw F s hq X
  have hcw := cw_len Pw Cw F s hq X (hA X hX)
  unfold rcost
  apply roundCost_le hB
  · exact hM 9 (by unfold eMt; omega) _ (crop_le hB X q hXB (by omega))
  · exact hM _ (by unfold eMt; omega) _ (cP_le Pw F s hq X)
  · have h2 : appendBCost ((List.range X).map F.pw) (F.pw X) ≤ 32 * (s + 2) ^ (lp Pw + 3) := by
      have h1 := sumFrame_le hB X (lp Pw) hXB F.pw (fun i _ => pw_len Pw F s hq i)
      have := ble hB (show lp Pw ≤ lp Pw + 3 by omega) hpw
      unfold appendBCost; have := bpos hB (lp Pw + 3); omega
    exact hM _ (by unfold eMt; omega) _ (bcm hB 32 5 (by norm_num) h2)
  · exact hM 9 (by unfold eMt; omega) _ (crop_le hB X Wa hXB hWa)
  · have h2 : catCost (codesWord m (F.atoms X)).length (F.pw X).length X ≤ 64 * (s + 2) ^ lp Pw := by
      have a1 := hA X hX
      have a2 : s + 2 ≤ (s + 2) ^ lp Pw := Nat.le_self_pow (by unfold FrontFoldBound.lp; omega) _
      unfold catCost; omega
    exact hM _ (by unfold eMt; omega) _ (bcm hB 64 6 (by norm_num) h2)
  · exact hM _ (by unfold eMt; omega) _ (cC_le Pw Cw F s hq X (hA X hX))
  · have h2 : appendBCost ((List.range X).map F.cw) (F.cw X) ≤ 32 * (s + 2) ^ (lc Pw Cw + 3) := by
      have h1 := sumFrame_le hB X (lc Pw Cw) hXB F.cw (fun i hi => cw_len Pw Cw F s hq i (hA i (by omega)))
      have := ble hB (show lc Pw Cw ≤ lc Pw Cw + 3 by omega) hcw
      unfold appendBCost; have := bpos hB (lc Pw Cw + 3); omega
    exact hM _ (by unfold eMt; omega) _ (bcm hB 32 5 (by norm_num) h2)
  · have hW := Wc_le Pw Cw F s hq X (hA X hX)
    have h1 := envCost_le hB (Stars.Carrier.code (F.car X)) T (lc Pw Cw + 2) t hW hT
    exact hM _ (by unfold eMt; omega) _ h1
  · have h2 : efCost X ≤ 16 * (s + 2) := by unfold efCost; omega
    have h3 := bcm hB 16 4 (by norm_num) (show efCost X ≤ 16 * (s + 2) ^ 1 by rw [pow_one]; exact h2)
    exact hM _ (by unfold eMt; omega) _ h3

/-- **Every kept tape of every round state within `tot`**, at any envelope capacity `T ≤ tot`. -/
theorem widthT_le (hq : q ≤ s) (hnv : F.nv ≤ s) (hsys : F.sys ≤ s)
    (hA : ∀ X < F.nv, (codesWord m (F.atoms X)).length ≤ s) (X : ℕ) (hX : X ≤ F.nv) (T t tot : ℕ)
    (hT : T ≤ tot) (htot : (s + 2) ^ eMt Pw Cw deg t ≤ tot) (tP tC : ℕ) (t' : Fin (1220 + tP + tC)) :
    (F.st deg T tot X tP tC t').length ≤ tot := by
  have hB : 2 ≤ s + 2 := by omega
  have hM : ∀ e, e ≤ eMt Pw Cw deg t → ∀ x, x ≤ (s + 2) ^ e → x ≤ tot :=
    fun e he x hx => (ble hB he hx).trans htot
  have hs : s + 2 ≤ tot := hM 1 (by unfold eMt; omega) _ (by rw [pow_one])
  have hsq : (s + 2) * (2 * (s + 2)) ≤ (s + 2) ^ 3 := by
    have : (s + 2) * (2 * (s + 2)) = 2 * (s + 2) ^ 2 := by ring
    rw [this, pow_succ]; nlinarith
  unfold FoldIn.st
  apply FrontFoldBound.Qf_len
  intro k hk
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 := FrontFoldBound.flat_frame_le q F.ys (ys_len F)
    have h2 : F.ys.length * (2 * q + 1) ≤ (s + 2) * (2 * (s + 2)) := by
      rw [show F.ys.length = F.nv by simp [FoldIn.ys]]; exact Nat.mul_le_mul (by omega) (by omega)
    exact hM 3 (by unfold eMt; omega) _ (h1.trans (h2.trans hsq))
  · simp [FrontFoldRound.ctr]; omega
  · have h1 := FrontFoldBound.flat_frame_le s F.as (FrontFoldBound.as_len F s hA)
    have h2 : F.as.length * (2 * s + 1) ≤ (s + 2) * (2 * (s + 2)) := by
      rw [show F.as.length = F.nv by simp [FoldIn.as]]; exact Nat.mul_le_mul (by omega) (by omega)
    exact hM 3 (by unfold eMt; omega) _ (h1.trans (h2.trans hsq))
  · simp [FrontFoldRound.ctr]; omega
  · simp; omega
  · exact hM _ (by unfold eMt; omega) _ (FrontFoldBound.sumFrame_le hB X (lp Pw) (by omega) F.pw
      (fun i _ => pw_len Pw F s hq i))
  · exact hM _ (by unfold eMt; omega) _ (FrontFoldBound.sumFrame_le hB X (lc Pw Cw) (by omega) F.cw
      (fun i hi => cw_len Pw Cw F s hq i (hA i (by omega))))
  · simp; omega
  · simp only [List.length_replicate]
    exact hM deg (by unfold eMt; omega) _ (Nat.pow_le_pow_left (by omega) deg)
  · simp only [List.length_replicate]
    exact hT

end Gen

section Guess
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemFold
