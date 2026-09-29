import Proof.Wire_3_5.FinalPass.ThrSz4
import Proof.Wire_3_5.Primitive.Writers.BudgetIface

/-! # The THR word-size lemma, part 1: the call, its cap, its numbers, its table and payloads

At a THR call of `callInputs l F …` (`kOf`): the THR cap `capOfT` (PA's `CallIndexR.cap_leR`: `≤ capK c_r·2^{capZR l}
·(n+1)^{capZR l}`, **`cap_kn`**, the exponent from `l` only), the call's THR numbers `valsOf` (W6's `thrNumVals`,
every entry among `hashNums`, **`mem_nums`**), the gate table word **`w0_le`** (`≤ 2253·(n+1)^79`) and a payload
word **`pay_le'`** (`≤ (11 + 2·2^{algX l})·(n+1)^{26 + algX l}`, `payOf_le`, `CallIndex.scb_le`). Paper quantity:
the call's words, polynomial in `n` (P3:3069-3072, 3176-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrSz
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm

section Pieces
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
  (hs : (Plan.callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- The call. -/
noncomputable abbrev kOf : Seams.ThrCall :=
  Seams.thrCallOf (Plan.callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers translation

/-- The THR cap of the call. -/
noncomputable abbrev capOfT : ℕ := ((gate0 l F).budget kclk coef A a ha).capOf .thr n

/-- The call's THR numbers (W6's `thrNumVals`). -/
noncomputable abbrev valsOf : PrimThrW.Joins.ThrNumVals :=
  PrimThrW.Joins.thrNumVals ((Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
    (Plan.callInputs l F kclk coef A a ha).D carriers.length (capOfT l F kclk coef A a ha n)

theorem cap_kn : capOfT l F kclk coef A a ha n ≤
    (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) * (n + 1) ^ CallIndexR.capZR l := by
  have h := CallIndexR.cap_leR l F.cr .thr n
  have h2 : (n + 2) ^ CallIndexR.capZR l ≤ 2 ^ CallIndexR.capZR l * (n + 1) ^ CallIndexR.capZR l := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  calc capOfT l F kclk coef A a ha n ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l := h
    _ ≤ CallIndexR.capK F.cr * (2 ^ CallIndexR.capZR l * (n + 1) ^ CallIndexR.capZR l) := Nat.mul_le_mul_left _ h2
    _ = _ := by ring

theorem mem_nums (i : Fin 14) :
    (valsOf l F kclk coef A a ha n hs Cs carriers).get i ∈
      ThrData.hashNums ((Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (Plan.callInputs l F kclk coef A a ha).D (capOfT l F kclk coef A a ha n) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))

/-- The table word. -/
theorem w0_le (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 0).length ≤ 2253 * (n + 1) ^ 79 := by
  rw [ThrPt.thrWords_table]
  split_ifs
  · exact Nat.zero_le _
  · exact table_kn ha' Cs hd

/-- A payload word. -/
theorem pay_le' (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (j : Fin 4) :
    (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) ⟨j.val + 1, by omega⟩).length ≤
      (11 + 2 * 2 ^ CallIndex.algX l) * (n + 1) ^ (26 + CallIndex.algX l) := by
  rw [ThrPt.thrWords_pay]
  split_ifs with hj
  · show (PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨j.val, hj⟩)).length ≤ _
    have h1 := payOf_le (gate0 l F).alg (Cs ⟨j.val, hj⟩) ((n + 1) ^ 26) (hd _)
    have h2 := CallIndex.scb_le l n
    have h3 : (n + 2) ^ CallIndex.algX l ≤ 2 ^ CallIndex.algX l * (n + 1) ^ CallIndex.algX l := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    have hN : 1 ≤ n + 1 := by omega
    have e1 : (n + 1) ^ 26 ≤ (n + 1) ^ (26 + CallIndex.algX l) := Nat.pow_le_pow_right hN (by omega)
    have e2 : (n + 1) ^ CallIndex.algX l ≤ (n + 1) ^ (26 + CallIndex.algX l) := Nat.pow_le_pow_right hN (by omega)
    have e3 : 1 ≤ (n + 1) ^ (26 + CallIndex.algX l) := Nat.one_le_pow _ _ hN
    have e4 : 2 ^ CallIndex.algX l * (n + 1) ^ CallIndex.algX l ≤
        2 ^ CallIndex.algX l * (n + 1) ^ (26 + CallIndex.algX l) := Nat.mul_le_mul_left _ e2
    have hg : (gate0 l F).alg = Endpoint.gateAlg l := rfl
    rw [hg] at h1 ⊢
    have e : (11 + 2 * 2 ^ CallIndex.algX l) * (n + 1) ^ (26 + CallIndex.algX l) =
        11 * (n + 1) ^ (26 + CallIndex.algX l) + 2 * (2 ^ CallIndex.algX l * (n + 1) ^ (26 + CallIndex.algX l)) := by
      ring
    rw [e]
    omega
  · exact Nat.zero_le _

end Pieces

end NearCubicWires.WireExponent3_5.FinalPass.ThrSz
