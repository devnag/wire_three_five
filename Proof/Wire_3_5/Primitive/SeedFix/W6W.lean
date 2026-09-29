import Proof.Wire_3_5.Primitive.SeedFix.W6V

/-! # W6, part 23: the fill's state and the request's words

P3:2543-2558 (the THR call's request and its circuits' payloads): the word state after the front end and the fill
(`σ1`, W6C) holds the framed request word on `sReq`, `1^V` on `sCnt`, `1^{ncar}`, `1^{cap_T}`, the payloads and the
native words, everything else blank; the request word starts with `n` and `a'` (`Data.enc_reqW`); circuit `i`'s payload
starts with `|supp(topᵢ)|`; their sum is `|thrOccs|` (the fixed hash's `M`):
* `σ1_*` (the state's streams, heads, registers, cell), **`req_form`**, `payF_frame`, `payF_nil`, **`payF_sz`**,
  **`M_sum`** (`|thrOccs| = Σᵢ |supp(topᵢ)|` in `p1_spec`'s guarded form).

Paper quantities of the main types: the request's `n`, `a'` and the payloads' support sizes (their sum `M`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

variable (alg : DecompositionAlgorithm) (w : List Bool) (ncar capT V : ℕ) {n a' : ℕ}
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)


theorem σ1_st (s : Fin 192) : (σ1 alg w ncar capT V Cs).st s =
    if s = sAUX then List.replicate (2 * V + 3) false else fIn w ncar capT V (payF alg Cs) (natF Cs) s := rfl

theorem σ1_req : (σ1 alg w ncar capT V Cs).st sReq = frame w := by
  rw [σ1_st, if_neg (by decide)]; simp [fIn, sReq]

theorem σ1_cnt : (σ1 alg w ncar capT V Cs).st sCnt = List.replicate V true := by
  rw [σ1_st, if_neg (by decide)]; simp [fIn, sCnt]

theorem σ1_nc : (σ1 alg w ncar capT V Cs).st sNc = List.replicate ncar true := by
  rw [σ1_st, if_neg (by decide)]; simp [fIn, sNc]

theorem σ1_cap : (σ1 alg w ncar capT V Cs).st sCap = List.replicate capT true := by
  rw [σ1_st, if_neg (by decide)]; simp [fIn, sCap]

theorem σ1_pay (j : Fin 4) : (σ1 alg w ncar capT V Cs).st (sPay j) = payF alg Cs j := by
  rw [σ1_st, if_neg (fun h => by have := congrArg Fin.val h; simp [sPay, sAUX] at this; omega)]
  unfold fIn
  have hv : (sPay j).val = 22 + j.val := rfl
  have hj := j.isLt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp [hv])

theorem σ1_blank (s : Fin 192) (hs : 30 ≤ s.val ∨ (5 ≤ s.val ∧ s.val < 22)) : (σ1 alg w ncar capT V Cs).st s = [] := by
  rw [σ1_st, if_neg (fun h => by rw [h] at hs; simp [sAUX] at hs)]
  unfold fIn
  split_ifs <;> first | rfl | omega

/-- **The request word**: `n`, the THR mark, `a'`, then the rest. -/
theorem req_form (codes : List ℕ) (tl : List Bool) :
    frame (Data.reqW n true (ReqBridge.thrCodes Cs) codes tl) =
      frameP (natWord n) ++ ([true, true] ++ (frameP (natWord a') ++
        (ParseNat.enc true ((ReqBridge.thrCodes Cs).flatMap natWord) ++ (ParseNat.enc true (natWord codes.length) ++
          (ParseNat.enc true (codes.flatMap natWord) ++ (ParseNat.enc true tl ++ [false])))))) := by
  rw [Data.enc_reqW, show (ReqBridge.thrCodes Cs).length = a' from List.length_ofFn]
  rfl

theorem payF_nil (j : Fin 4) (h : a' ≤ j.val) : payF alg Cs j = [] := by
  unfold payF; rw [dif_neg (by omega)]

theorem payF_frame (j : Fin 4) (h : j.val < a') : ∃ y, payF alg Cs j = frame y := by
  unfold payF PrimThrW.TopFront.payOf; rw [dif_pos h]; exact ⟨_, rfl⟩

/-- Circuit `j`'s support size (`0` past `a'`). -/
def szOf (j : Fin 4) : ℕ := if h : j.val < a' then (Cs ⟨j.val, h⟩).top.support.card else 0

theorem payF_sz (j : Fin 4) (h : j.val < a') : ∃ r, payF alg Cs j = frameP (natWord (szOf Cs j)) ++ r := by
  unfold payF PrimThrW.TopFront.payOf szOf
  rw [dif_pos h, dif_pos h, frame_eq_frameP, frameP_app, List.append_assoc]
  exact ⟨_, rfl⟩

/-- **`M = |thrOccs|`** in `p1_spec`'s guarded form. -/
theorem M_sum (P : StarParams) (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (ha : a' ≤ 4) :
    (Primitive.thrOccs P Cs).length = (if (0 : Fin 4).val < a' then szOf Cs 0 else 0) +
      (if (1 : Fin 4).val < a' then szOf Cs 1 else 0) + (if (2 : Fin 4).val < a' then szOf Cs 2 else 0) +
      (if (3 : Fin 4).val < a' then szOf Cs 3 else 0) := by
  show (SupplierEstimator.thresholdFourfoldOccurrences (Primitive.thrRequest P Cs)).length = _
  unfold SupplierEstimator.thresholdFourfoldOccurrences Primitive.thrRequest szOf
  simp only [List.length_flatMap, SupplierEstimator.thresholdCircuitOccurrences, List.length_ofFn]
  interval_cases a' <;> simp [List.ofFn_succ, Fin.sum_univ_succ] <;> ring

end NearCubicWires.WireExponent3_5.PrimT.W6
