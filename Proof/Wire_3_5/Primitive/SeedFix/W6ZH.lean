import Proof.Wire_3_5.Primitive.SeedFix.W6ZG

/-! # W6, part 34: the numbers machine's time is polynomial in the count

P3:3071-3091 ("the preprocessing … runs in time polynomial in `n`") and P3:2543-2558, 2150-2157, 2220-2231 (the THR
numbers, the modulus search, the EW stage): with `N^{48D+700} ≤ 2V+2`, the body's step count `bodyB` is at most
`(10^{40} + 64000·D)·(V+1)^{18}`:
* `progCost_le` (proof 1's program: `≤ 3000(W+1)^6 + T_tail`, base `loopsCost_le`), `costC_le`, `costE_le`;
* `pcC_le`, `pcE_le` (the two programs at the THR request, `≤ 10^{20}(V+1)^6`);
* `opU_le`, `ewBound_le`, `sc_le` (the modulus search, S5's `searchCost_le`), `cut_term_le`, `dexp_term_le`;
* **`bodyB_le`**.

Paper quantities of the main type: the body's step count, the count `V`, the target exponent `D`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.PacketsMeta NearCubicWires.PacketsMeta.Lev NearCubicWires.PacketsMeta.Setup
open NearCubicWires.PacketsMeta.Tail NearCubicWires.PacketsMeta.Prog NearCubicWires.PacketsMeta.Spec
open NearCubicWires.PacketsMeta.Bounds
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

theorem metaW_eq (ds : List CD) : PrimThrW.W6Meta.metaW (twOf ds) = 32 * (12 + (twOf ds).length) := by
  unfold PrimThrW.W6Meta.metaW; rw [PrimThrW.W6Meta.nw0_len]

/-- **Proof 1's program at a top word**: `≤ 3000(W+1)^6` plus its tail. -/
theorem progCost_le (ds : List CD) (nT : ℕ) :
    PrimThrW.W6Meta.progCost (twOf ds) ds nT ≤ 3000 * (PrimThrW.W6Meta.metaW (twOf ds) + 1) ^ 6 + nT := by
  have hW := metaW_eq ds
  have hpay : ∀ c : Fin 4, (pay (dOf ds c)).length ≤ PrimThrW.W6Meta.metaW (twOf ds) := by
    intro c
    by_cases hc : c.val < ds.length
    · rw [PacketsMeta.Setup.dOf_lt _ c hc]; have := PacketsMeta.Setup.pay_le_tw ds c.val hc; omega
    · rw [PacketsMeta.Setup.dOf_ge _ c (by omega), PacketsMeta.Bounds.pay_pad_len]; omega
  have hl := PacketsMeta.Bounds.loopsCost_le (PrimThrW.W6Meta.metaW (twOf ds)) (by omega) (dOf ds) hpay
  have hp : PrimThrW.W6Meta.metaW (twOf ds) + 1 ≤ (PrimThrW.W6Meta.metaW (twOf ds) + 1) ^ 6 :=
    Nat.le_self_pow (by norm_num) _
  unfold PrimThrW.W6Meta.progCost PacketsMeta.Prog.hdrCost PacketsMeta.Prog.thrCost PacketsMeta.Setup.extCost
  simp only [PrimThrW.W6Meta.nw0_len, PacketsMeta.Bounds.pay_pad_len]
  omega

theorem costC_le (W C U : ℕ) (hW : W + 1 ≤ 417 * U) (hC : C ≤ 2 * U) (hU : 1 ≤ U) :
    PrimThrW.W6Meta.costC W C ≤ 6000 * U ^ 2 := by
  unfold PrimThrW.W6Meta.costC
  have p := Nat.mul_le_mul (show C + 1 ≤ 3 * U by omega)
    (show (2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2 ≤ 1675 * U by omega)
  have e : 3 * U * (1675 * U) = 5025 * U ^ 2 := by ring
  have hU2 : U ≤ U ^ 2 := Nat.le_self_pow (by norm_num) U
  omega

theorem costE_le (W F U : ℕ) (hW : W + 1 ≤ 417 * U) (hE : Nat.clog 2 (F + 1) ≤ 2 * U) (hU : 1 ≤ U) :
    PrimThrW.W6Meta.costE W F ≤ 20000 * U ^ 2 := by
  have hc := costC_le W (Nat.clog 2 (F + 1)) U hW hE hU
  unfold PrimThrW.W6Meta.costE
  have p := Nat.mul_le_mul (show Nat.clog 2 (F + 1) + 1 ≤ 3 * U by omega)
    (show (2 * W + 3) + ((2 * W + 3) + 1 + (2 * W + 3)) + 2 ≤ 2508 * U by omega)
  have e : 3 * U * (2508 * U) = 7524 * U ^ 2 := by ring
  have hU2 : U ≤ U ^ 2 := Nat.le_self_pow (by norm_num) U
  omega

variable (alg : DecompositionAlgorithm)

theorem pcC_le (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (U : ℕ) (hU : 1 ≤ U)
    (htw : (twOf (dsOf alg (Primitive.thrRequest P Cs))).length ≤ U) (hC : Cv (dsOf alg (Primitive.thrRequest P Cs)) ≤ 2 * U) : pcC alg P Cs ≤ 100000000000000000000 * U ^ 6 := by
  unfold pcC
  generalize (dsOf alg (Primitive.thrRequest P Cs)) = ds at htw hC ⊢
  have h1 := progCost_le ds (PrimThrW.W6Meta.costC (PrimThrW.W6Meta.metaW (twOf ds)) (Cv ds))
  have hW := metaW_eq ds
  generalize PrimThrW.W6Meta.metaW (twOf ds) = W at h1 hW ⊢
  have hW1 : W + 1 ≤ 417 * U := by omega
  have h6 : (W + 1) ^ 6 ≤ 5257948522194369 * U ^ 6 := by
    calc (W + 1) ^ 6 ≤ (417 * U) ^ 6 := Nat.pow_le_pow_left hW1 6
      _ = 5257948522194369 * U ^ 6 := by rw [mul_pow]; norm_num
  have hc := costC_le W (Cv ds) U hW1 hC hU
  have hU2 : U ^ 2 ≤ U ^ 6 := Nat.pow_le_pow_right hU (by norm_num)
  have hU6 : 1 ≤ U ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

theorem pcE_le (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (U : ℕ) (hU : 1 ≤ U)
    (htw : (twOf (dsOf alg (Primitive.thrRequest P Cs))).length ≤ U) (hE : Nat.clog 2 (Fv (dsOf alg (Primitive.thrRequest P Cs)) + 1) ≤ 2 * U) : pcE alg P Cs ≤ 100000000000000000000 * U ^ 6 := by
  unfold pcE
  generalize (dsOf alg (Primitive.thrRequest P Cs)) = ds at htw hE ⊢
  have h1 := progCost_le ds (PrimThrW.W6Meta.costE (PrimThrW.W6Meta.metaW (twOf ds)) (Fv ds))
  have hW := metaW_eq ds
  generalize PrimThrW.W6Meta.metaW (twOf ds) = W at h1 hW ⊢
  have hW1 : W + 1 ≤ 417 * U := by omega
  have h6 : (W + 1) ^ 6 ≤ 5257948522194369 * U ^ 6 := by
    calc (W + 1) ^ 6 ≤ (417 * U) ^ 6 := Nat.pow_le_pow_left hW1 6
      _ = 5257948522194369 * U ^ 6 := by rw [mul_pow]; norm_num
  have hc := costE_le W (Fv ds) U hW1 hE hU
  have hU2 : U ^ 2 ≤ U ^ 6 := Nat.pow_le_pow_right hU (by norm_num)
  have hU6 : 1 ≤ U ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

theorem opU_le (V : ℕ) : opU (2 * V + 2) ≤ 64000 * (V + 1) ^ 2 := by
  unfold opU UnaryPow.sq
  have h : (2 * V + 2 + 2) * (2 * V + 2 + 2) ≤ (4 * (V + 1)) * (4 * (V + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : 20 * (200 * (2 * V + 2 + 2) * (2 * V + 2 + 2)) = 4000 * ((2 * V + 2 + 2) * (2 * V + 2 + 2)) := by ring
  have e2 : 4 * (V + 1) * (4 * (V + 1)) = 16 * (V + 1) ^ 2 := by ring
  omega

theorem ewBound_le (x U : ℕ) (hx : x + 1 ≤ 9 * U) : UnionMachine.EwSize.ewBound x ≤ 200000000000000000000000000000000000000 * U ^ 18 := by
  unfold UnionMachine.EwSize.ewBound
  calc 10 ^ 21 * (x + 1) ^ 18 ≤ 10 ^ 21 * (9 * U) ^ 18 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 18)
    _ = 10 ^ 21 * 9 ^ 18 * U ^ 18 := by ring
    _ ≤ 200000000000000000000000000000000000000 * U ^ 18 := Nat.mul_le_mul_right _ (by norm_num)

theorem sc_le (l U : ℕ) (hU : 1 ≤ U) (h : 2 ^ (l + 1) ≤ 2 * U) :
    GF2.searchCost l ≤ 200 * U ^ 3 ∧ 2 * (l + 2) * (40 * 2 ^ l + 40) ≤ 480 * U ^ 2 := by
  have e0 : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
  have h2l : 2 ^ l ≤ U := by omega
  have hl : l < 2 ^ l := Nat.lt_two_pow_self
  refine ⟨?_, ?_⟩
  · have h1 := GF2.searchCost_le l U hU (by omega)
    have p1 : 2 ^ (2 * l) ≤ U ^ 2 := by
      calc 2 ^ (2 * l) = (2 ^ l) ^ 2 := by rw [← pow_mul, mul_comm]
        _ ≤ U ^ 2 := Nat.pow_le_pow_left h2l 2
    have p2 : 2 ^ (2 * l) * U ^ 1 ≤ U ^ 2 * U ^ 1 := Nat.mul_le_mul_right _ p1
    have e : U ^ 2 * U ^ 1 = U ^ 3 := by ring
    omega
  · have a := Nat.mul_le_mul (show 2 * (l + 2) ≤ 6 * U by omega) (show 40 * 2 ^ l + 40 ≤ 80 * U by omega)
    have e : 6 * U * (80 * U) = 480 * U ^ 2 := by ring
    omega

theorem cut_term_le (ct O U : ℕ) (hU : 1 ≤ U) (hct : ct ≤ 2 * U) (hO : O ≤ 64000 * U ^ 2) :
    ct * (ct * (8 * (O + 1) + 4) + 14 * (O + 1) + 4) ≤ 3840084 * U ^ 4 := by
  have hU2 : 1 ≤ U ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hU3 : 1 ≤ U ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hU23 : U ^ 2 ≤ U ^ 3 := Nat.pow_le_pow_right hU (by norm_num)
  have a1 : 8 * (O + 1) + 4 ≤ 512012 * U ^ 2 := by omega
  have a2 := Nat.mul_le_mul hct a1
  have e2 : 2 * U * (512012 * U ^ 2) = 1024024 * U ^ 3 := by ring
  have a3 : ct * (8 * (O + 1) + 4) + 14 * (O + 1) + 4 ≤ 1920042 * U ^ 3 := by omega
  have a4 := Nat.mul_le_mul hct a3
  have e4 : 2 * U * (1920042 * U ^ 3) = 3840084 * U ^ 4 := by ring
  omega

theorem dexp_term_le (D O U : ℕ) (hU : 1 ≤ U) (hO : O ≤ 64000 * U ^ 2) :
    (D + 1) * O ≤ 64000 * (D * U ^ 18) + 64000 * U ^ 18 := by
  have h := Nat.mul_le_mul_left (D + 1) hO
  have h2 : U ^ 2 ≤ U ^ 18 := Nat.pow_le_pow_right hU (by norm_num)
  have h3 := Nat.mul_le_mul_left D h2
  have e : (D + 1) * (64000 * U ^ 2) = 64000 * (D * U ^ 2) + 64000 * U ^ 2 := by ring
  omega

/-- **The body's step count is polynomial in the count** `V`. -/
theorem bodyB_le (Dexp : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (ncar capT V : ℕ) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hnc : ncar ≤ 2)
    (hV : (thrN alg P capT) ^ (48 * Dexp + 700) ≤ 2 * V + 2) :
    bodyB alg Dexp P Cs ncar capT V ≤ 10000000000000000000000000000000000000000 * (V + 1) ^ 18 + 64000 * (Dexp * (V + 1) ^ 18) := by
  have hN := thrN16 alg P capT
  have tb := (thr_basic alg P Cs capT ha hd)
  have cp : ∀ {x e : ℕ}, x ≤ (thrN alg P capT) ^ e → e ≤ 48 * Dexp + 700 → x ≤ 2 * V + 2 :=
    fun hx he => (pw_mono (by omega) hx he).trans hV
  have hU : 1 ≤ V + 1 := by omega
  have sg : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG ≤ 2 * V + 2 := cp (vb_nG alg Dexp P Cs ncar capT ha hd) (by omega)
  have sE : familyMagnitudeExponent (Primitive.thrRealize P Cs alg) ≤ 2 * V + 2 := cp tb.2.1 (by omega)
  have sct : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut ≤ 2 * (V + 1) := cp (vb_cut alg Dexp P Cs ncar capT ha hd) (by omega)
  have s2l : 2 ^ ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 1) ≤ 2 * (V + 1) := cp (vb_2ell alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  have sM : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M ≤ 2 * V + 2 := cp (vb_M alg Dexp P Cs ncar capT ha hd) (by omega)
  have sA : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A ≤ 2 * V + 2 := cp (vb_A alg Dexp P Cs ncar capT ha hd) (by omega)
  have sB : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs ≤ 2 * V + 2 := cp (vb_Bs alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  have sK : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den ≤ 2 * V + 2 := cp (vb_den alg Dexp P Cs ncar capT ha hd) (by omega)
  have spay : 2 * (payF alg Cs 0 ++ payF alg Cs 1 ++ payF alg Cs 2 ++ payF alg Cs 3).length + 4 ≤ 2 * V + 2 :=
    cp (pw_two hN tb.2.2.2.2.1) (by omega)
  have etw := congrArg List.length (payF_cat alg P Cs ha)
  have eC := PrimThrW.W6Meta.Cv_thr alg P Cs ha
  have eE := PrimThrW.W6Meta.E_thr alg P Cs ha
  have eG := v_nG alg Dexp P Cs ncar capT
  have hPC := pcC_le alg P Cs (V + 1) hU (by omega) (by omega)
  have hPE := pcE_le alg P Cs (V + 1) hU (by omega) (by omega)
  have hO := opU_le V
  have hEW := ewBound_le ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den) (V + 1) (by omega)
  have hsc := sc_le (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 (V + 1) hU s2l
  have hct := cut_term_le (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut (opU (2 * V + 2)) (V + 1) hU sct hO
  have hdx := dexp_term_le Dexp (opU (2 * V + 2)) (V + 1) hU hO
  have q2 : (V + 1) ^ 2 ≤ (V + 1) ^ 18 := Nat.pow_le_pow_right hU (by norm_num)
  have q3 : (V + 1) ^ 3 ≤ (V + 1) ^ 18 := Nat.pow_le_pow_right hU (by norm_num)
  have q4 : (V + 1) ^ 4 ≤ (V + 1) ^ 18 := Nat.pow_le_pow_right hU (by norm_num)
  have q6 : (V + 1) ^ 6 ≤ (V + 1) ^ 18 := Nat.pow_le_pow_right hU (by norm_num)
  have q1 : V + 1 ≤ (V + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q0 : 1 ≤ (V + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsc1 := hsc.1
  have hsc2 := hsc.2
  unfold bodyB
  omega

end NearCubicWires.WireExponent3_5.PrimT.W6
