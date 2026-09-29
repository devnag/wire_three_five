import Proof.Wire_3_5.Primitive.SeedFix.TS4K

/-! # thrStage4U, part 15: the v4 stage's time bound `cost3`, polynomial

P3:3071-3091 ("the preprocessing … runs in time polynomial in `n`") and P3:3114-3115: the v4 stage's time `cost3G` (the
prep, W6's numbers machine, PA's first three phases, the hash writer, the collection, the reset) is `PolyBounded` in
`K + n + L + W`, the degree `DcG l` fixed by the literals, the coefficient `CcG l c_r` by `c_r`:

* `emitsCost_le`, `qh_le` (the hash writer within `19W + 4`);
* `Dw`, `Cw`, `Ct`, `DcG`, `CcG`; **`cost3G`**; `numsM_le`, **`cost3G_le`**.

Paper quantities of the main type: the v4 data stage's step count. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.ThrData NearCubicWires.SupplierPipeline
open NearCubicWires.ValidatorPolynomialDomination

theorem emitsCost_le : ∀ cs : List ℕ, emitsCost cs ≤ 19 * (unaryList cs).length
  | [] => by simp [emitsCost, unaryList]
  | c :: cs => by
    have ih := emitsCost_le cs
    have e : (unaryList (c :: cs)).length = c + 1 + (unaryList cs).length := by
      rw [unaryList_cons]; simp; omega
    simp only [emitsCost]
    rw [e]
    omega

theorem qh_le (cs : List ℕ) (W : ℕ) (h : 2 * (unaryList cs).length ≤ 2 * W) : qhCost cs ≤ 19 * W + 4 := by
  have := emitsCost_le cs
  unfold qhCost; omega

variable (l : Literals)

/-- W6's time degree and coefficient (`numsCost_poly` at `D = 1`). -/
noncomputable def Dw : ℕ := (W6.tf (W6.litAlg l)).Dc + 18
noncomputable def Cw : ℕ := 2 * (W6.tf (W6.litAlg l)).Cc + 2 * 10000000000000000000000000000000000000000 + 128000 * 1 + 60

/-- PA's data stage coefficient and degree (`thrCost2_le`). -/
noncomputable def Ct : ℕ := 40 * ThrData.cTT + 80 * ThrData.cX + 70100

/-- The v4 stage's time degree (the literals only). -/
noncomputable def DcG : ℕ := Dp l + (PrimAsm.CallIndexR.capZR l + 26) * Dw l + ThrData.dD + 1

/-- The v4 stage's time coefficient. -/
noncomputable def CcG (cr : ℕ) : ℕ :=
  (4 * Kp l cr + 2 * (Cw l * (PrimAsm.CallIndexR.capK cr + 2) ^ Dw l) + 2 * Ct + 61) * 3 ^ DcG l

/-- **The v4 stage's time** (the hash writer at its bound `19W + 4`). -/
noncomputable def cost3G (cr : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (L W : ℕ) : ℕ :=
  2 * ((((2 * p0StageCost n cr (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) (ReqBridge.thrCodes Cs).length
      (carriers.map Stars.Carrier.code).length W W + 2) + 1 +
    (2 * W6.numsT (W6.litAlg l) 1 (n + (W + (n + 1) ^ 26) + capTOf cr n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)) + 3) + 1 +
    preCost a' Cs carriers L W) + 1 + (19 * W + 4)) + 1 +
    collectTailCost (carriers.map (·.length)) (PrimT.ThrTab.tupleG Cs).length) + 2 + 1

theorem numsM_le (cr n W M : ℕ) (hM : n + W + 3 ≤ M) :
    2 * W6.numsT (W6.litAlg l) 1 (n + (W + (n + 1) ^ 26) + capTOf cr n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)) + 3 ≤
      Cw l * (PrimAsm.CallIndexR.capK cr + 2) ^ Dw l * M ^ ((PrimAsm.CallIndexR.capZR l + 26) * Dw l) := by
  have hp := W6.numsCost_poly (W6.litAlg l) 1 (n + (W + (n + 1) ^ 26) + capTOf cr n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l))
  unfold PolyBounded at hp
  have ecap : capTOf cr n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) = capTL l cr n := rfl
  rw [ecap] at hp ⊢
  have hz := capZR_pos l
  have hc : capTL l cr n ≤ PrimAsm.CallIndexR.capK cr * M ^ PrimAsm.CallIndexR.capZR l :=
    (capTL_le l cr n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = M ^ (PrimAsm.CallIndexR.capZR l + 26) := ⟨_, rfl⟩
  have hM1 : M ≤ Z := by rw [hZ]; exact Nat.le_self_pow (by omega) _
  have h26 : (n + 1) ^ 26 ≤ Z := by
    rw [hZ]; exact (Nat.pow_le_pow_left (show n + 1 ≤ M by omega) 26).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hcZ : PrimAsm.CallIndexR.capK cr * M ^ PrimAsm.CallIndexR.capZR l ≤ PrimAsm.CallIndexR.capK cr * Z :=
    Nat.mul_le_mul_left _ (by rw [hZ]; exact Nat.pow_le_pow_right (by omega) (by omega))
  have hm : n + (W + (n + 1) ^ 26) + capTL l cr n + 1 ≤ (PrimAsm.CallIndexR.capK cr + 2) * Z := by
    have e : (PrimAsm.CallIndexR.capK cr + 2) * Z = PrimAsm.CallIndexR.capK cr * Z + 2 * Z := by ring
    omega
  have hpw := Nat.pow_le_pow_left hm ((W6.tf (W6.litAlg l)).Dc + 18)
  rw [mul_pow, hZ, ← pow_mul] at hpw
  unfold Cw Dw
  calc _ ≤ (2 * (W6.tf (W6.litAlg l)).Cc + 2 * 10000000000000000000000000000000000000000 + 128000 * 1 + 60) *
        (n + (W + (n + 1) ^ 26) + capTL l cr n + 1) ^ ((W6.tf (W6.litAlg l)).Dc + 18) := hp
    _ ≤ (2 * (W6.tf (W6.litAlg l)).Cc + 2 * 10000000000000000000000000000000000000000 + 128000 * 1 + 60) *
        ((PrimAsm.CallIndexR.capK cr + 2) ^ ((W6.tf (W6.litAlg l)).Dc + 18) *
          M ^ ((PrimAsm.CallIndexR.capZR l + 26) * ((W6.tf (W6.litAlg l)).Dc + 18))) := Nat.mul_le_mul_left _ hpw
    _ = _ := by ring

/-- **The v4 stage's time is polynomial** in `K + n + L + W`. -/
theorem cost3G_le (cr : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (L W K : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (hK : ∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ K)
    (hKX : ∀ X ∈ carriers, natBitLength X.code ≤ K) (h2 : 2 ≤ n + L) :
    PolyBounded (cost3G l cr Cs carriers L W) (K + n + L + W) (CcG l cr) (DcG l) := by
  unfold PolyBounded
  obtain ⟨M, hMd⟩ : ∃ M, M = K + n + L + W := ⟨_, rfl⟩
  have hcl : (ReqBridge.thrCodes Cs).length = a' := by simp [ReqBridge.thrCodes]
  have hml : (carriers.map Stars.Carrier.code).length = carriers.length := List.length_map _
  have fP := p0Stage_le l cr n W (ReqBridge.thrCodes Cs).length (carriers.map Stars.Carrier.code).length (by omega) (by omega)
  have fW := numsM_le l cr n W (M + 3) (by omega)
  have fT := ThrData.thrCost2_le Cs carriers L W K ha hk hL hLX hK hKX h2
  unfold PolyBounded at fT
  rw [← hMd] at fT
  have eCore : ThrData.thrCoreCost2 a' Cs carriers L W = preCost a' Cs carriers L W + 1 +
      collectCostT2 (carriers.map (·.length)) (PrimT.ThrTab.tupleG Cs).length := by
    unfold ThrData.thrCoreCost2 preCost; ring
  have eCol : collectTailCost (carriers.map (·.length)) (PrimT.ThrTab.tupleG Cs).length + 4 =
      collectCostT2 (carriers.map (·.length)) (PrimT.ThrTab.tupleG Cs).length := by
    unfold collectTailCost collectCostT2; ring
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = (M + 3) ^ DcG l := ⟨_, rfl⟩
  have Y1 : 1 ≤ Y := hYd ▸ Nat.one_le_pow _ _ (by omega)
  have yP : (n + W + 3) ^ Dp l ≤ Y := by
    rw [hYd]; exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by unfold DcG; omega))
  have yW : (M + 3) ^ ((PrimAsm.CallIndexR.capZR l + 26) * Dw l) ≤ Y := by
    rw [hYd]; exact Nat.pow_le_pow_right (by omega) (by unfold DcG; omega)
  have yT : (M + 1) ^ ThrData.dD ≤ Y := by
    rw [hYd]; exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by unfold DcG; omega))
  have yQ : W + 1 ≤ Y := by
    rw [hYd]; exact (show W + 1 ≤ M + 3 by omega).trans (Nat.le_self_pow (by unfold DcG; omega) _)
  have fP' := fP.trans (Nat.mul_le_mul_left (Kp l cr) yP)
  have fW' := fW.trans (Nat.mul_le_mul_left (Cw l * (PrimAsm.CallIndexR.capK cr + 2) ^ Dw l) yW)
  have fT' := fT.trans (Nat.mul_le_mul_left (40 * ThrData.cTT + 80 * ThrData.cX + 70100) yT)
  have eY : (M + 3) ^ DcG l ≤ 3 ^ DcG l * (M + 1) ^ DcG l := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have hfin : cost3G l cr Cs carriers L W ≤
      (4 * Kp l cr + 2 * (Cw l * (PrimAsm.CallIndexR.capK cr + 2) ^ Dw l) + 2 * Ct + 61) * Y := by
    clear yP yW yT eY fP fW fT hYd hMd
    unfold cost3G
    have e : (4 * Kp l cr + 2 * (Cw l * (PrimAsm.CallIndexR.capK cr + 2) ^ Dw l) + 2 * Ct + 61) * Y =
        4 * (Kp l cr * Y) + 2 * (Cw l * (PrimAsm.CallIndexR.capK cr + 2) ^ Dw l * Y) + 2 * (Ct * Y) + 61 * Y := by ring
    rw [e]
    unfold Ct
    omega
  have hY : Y ≤ 3 ^ DcG l * (M + 1) ^ DcG l := by rw [hYd]; exact eY
  have hfin2 := hfin.trans (Nat.mul_le_mul_left
    (4 * Kp l cr + 2 * (Cw l * (PrimAsm.CallIndexR.capK cr + 2) ^ Dw l) + 2 * Ct + 61) hY)
  have eC : (4 * Kp l cr + 2 * (Cw l * (PrimAsm.CallIndexR.capK cr + 2) ^ Dw l) + 2 * Ct + 61) *
      (3 ^ DcG l * (M + 1) ^ DcG l) = CcG l cr * (M + 1) ^ DcG l := by unfold CcG; ring
  rw [eC] at hfin2
  subst hMd
  exact hfin2

end NearCubicWires.WireExponent3_5.PrimT.TS4
