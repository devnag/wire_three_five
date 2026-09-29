import Proof.Wire_3_5.Primitive.Writers.SBParse
import Proof.Wire_3_5.Primitive.Writers.SBNumsA

/-! # SB, part 16: the request's `n` and mode bit, read and rewound

On S4's small-number register file (`SBNums.NRB`): measure the framed request (`93`), copy the length (`94`, via `95`),
rewind, read `n` into `16` (`ParseNat.readNatM`, scratch `27 … 30`), read the mode bit into `60`, rewind.

* `parseW`, `parseCost`, `mode_bit`, **`parse_spec`**: from `frame (Data.reqW n mb codes cc tl)` (head `0`) and those
  registers at `0`: `16 = n`, `60 = [mb]`, the head back at `0`, every other register and every stream unchanged.

Paper quantity of the main type: the request's `n` and class mode (`PrimRequest.word`, P3:3068-3084). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBParse
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SBNums

variable {ns : ℕ} (cap : ℕ)

/-- Measure, rewind, read `n`, read the mode bit, rewind. -/
def parseW (I : Fin (ns + 1)) : WM ns NRB :=
  .seq (measureW I (93 : Fin NRB)) (.seq (FinalPass.Hash4.wcopyR 93 94 95) (.seq (WM.rewind I 93)
    (.seq (readNatM true I 27 28 16 29 30) (.seq (.fwd I) (.seq (.ifs I (.inc 60) .skip) (WM.rewind I 94))))))

def parseCost (w n : ℕ) : ℕ :=
  (w * 13 + 1) + 1 + (UnaryPow.sq cap + 1 + ((5 * (2 * w) + 1) + 1 +
    ((natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 + (1 + 1 + (4 + 1 + (5 * (2 * w) + 1))))))

theorem mode_bit (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) :
    readTapeBit (frame (Data.reqW n mb codes cc tl)) (2 * (RepairRepresentation.natWord n).length + 1) = mb := by
  rw [Data.enc_reqW]
  simp only [ParseNat.enc, ↓reduceIte, Streaming.marks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hl : (List.flatMap (fun b => [true, b]) (RepairRepresentation.natWord n)).length =
      2 * (RepairRepresentation.natWord n).length := by
    simp [List.length_flatMap]; ring
  simp only [readTapeBit]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl,
    show 2 * (RepairRepresentation.natWord n).length + 1 - 2 * (RepairRepresentation.natWord n).length = 1 by omega]
  simp

theorem parse_spec (I : Fin (ns + 1)) (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (σ : WState ns NRB)
    (hst : σ.st I = frame (Data.reqW n mb codes cc tl)) (hsh : σ.sh I = 0)
    (z93 : σ.val 93 = 0) (z94 : σ.val 94 = 0) (z95 : σ.val 95 = 0) (z27 : σ.val 27 = 0) (z28 : σ.val 28 = 0)
    (z16 : σ.val 16 = 0) (z29 : σ.val 29 = 0) (z30 : σ.val 30 = 0) (z60 : σ.val 60 = 0)
    (hc : 2 * (Data.reqW n mb codes cc tl).length ≤ cap) (hcn : 2 ^ (natBitLength n + 1) ≤ cap) :
    WExec cap (parseW I) σ ((σ.setv 16 n).setv 60 (if mb then 1 else 0))
      (parseCost cap (Data.reqW n mb codes cc tl).length n) := by
  set w := Data.reqW n mb codes cc tl with hw
  have hwl : (RepairRepresentation.natWord n).length + 1 ≤ w.length := by simp [hw, Data.reqW]
  have hsq := UnaryPow.sq_ge cap
  -- 1: measure
  have e1 := measure_spec cap I (93 : Fin NRB) w σ hst hsh z93 (by omega)
  set σ1 := (σ.seth I (2 * w.length)).setv 93 (2 * w.length) with hσ1
  -- 2: copy the length
  have e2 := SparseNum.copy1 cap (93 : Fin NRB) 94 95 (by decide) (by decide) (by decide) (2 * w.length) σ1
    (by simp [hσ1]) (by simp [hσ1, Function.update_apply, z94]) (by simp [hσ1, Function.update_apply, z95]) (by omega)
  set σ2 := σ1.setv 94 (2 * w.length) with hσ2
  -- 3: rewind
  have e3 := wrewind_spec cap I (93 : Fin NRB) (2 * w.length) σ2 (by simp [hσ2, hσ1, Function.update_apply])
    (by simp [hσ2, hσ1, Function.update_apply]; omega)
  set σ3 := (σ2.setv 93 0).seth I (σ2.sh I - 2 * w.length) with hσ3
  have sh3 : σ3.sh I = 0 := by simp [hσ3, hσ2, hσ1]
  have st3 : σ3.st I = [] ++ ParseNat.enc true (RepairRepresentation.natWord n) ++
      (ParseNat.enc true [mb] ++ (ParseNat.enc true (RepairRepresentation.natWord codes.length) ++
        (ParseNat.enc true (codes.flatMap RepairRepresentation.natWord) ++
          (ParseNat.enc true (RepairRepresentation.natWord cc.length) ++
            (ParseNat.enc true (cc.flatMap RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false])))))) := by
    simp only [hσ3, hσ2, hσ1, WState.seth_st, WState.setv_st, hst, hw, Data.enc_reqW, List.nil_append]
  -- 4: `n` into `16`
  have e4 := readNatM_spec cap true I (27 : Fin NRB) 28 16 29 30 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n [] _ σ3 st3 (by simpa using sh3)
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, z27]) (by simp [hσ3, hσ2, hσ1, Function.update_apply, z28])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, z29]) (by simp [hσ3, hσ2, hσ1, Function.update_apply, z30])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, z16]; omega)
  set σ4 := (σ3.seth I (([] : List Bool).length + stp true * (RepairRepresentation.natWord n).length)).setv 16
    (σ3.val 16 + n) with hσ4
  -- 5: the mode bit's cell
  have e5 := WExec.fwd (cap := cap) I σ4
  set σ5 := σ4.seth I (σ4.sh I + 1) with hσ5
  have hsh5 : σ5.sh I = 2 * (RepairRepresentation.natWord n).length + 1 := by
    simp [hσ5, hσ4, stp]
  have hbit : wbit σ5 I = mb := by
    unfold wbit
    rw [hsh5]
    simp only [hσ5, hσ4, hσ3, hσ2, hσ1, WState.seth_st, WState.setv_st, hst]
    exact mode_bit n mb codes cc tl
  -- 6: the mode bit into `60`
  have e6 : WExec cap (.ifs I (.inc (60 : Fin NRB)) .skip) σ5 (σ5.setv 60 (if mb then 1 else 0)) 4 := by
    cases hm : mb
    · have e := WExec.ifsF (cap := cap) (i := I) (P := .inc 60) (Q := .skip) (by rw [hbit, hm]) (WExec.skip σ5)
      have e' : σ5.setv 60 (if false = true then 1 else 0) = σ5 := by
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show (0 : ℕ) = σ5.val 60 by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, z60], wsetv_same]
      rw [e']
      exact WExec.mono e (by omega)
    · have ei := WExec.inc (cap := cap) (60 : Fin NRB) σ5 (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, z60]; omega)
      have e := WExec.ifsT (cap := cap) (i := I) (P := .inc 60) (Q := .skip) (by rw [hbit, hm]) ei
      have e' : σ5.setv 60 (σ5.val 60 + 1) = σ5.setv 60 (if true = true then 1 else 0) := by
        simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, z60]
      rw [e'] at e
      exact e
  set σ6 := σ5.setv 60 (if mb then 1 else 0) with hσ6
  -- 7: rewind
  have e7 := wrewind_spec cap I (94 : Fin NRB) (2 * w.length) σ6 (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, Function.update_apply])
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, Function.update_apply]; omega)
  have hsh6 : σ6.sh I = 2 * (RepairRepresentation.natWord n).length + 1 := by
    rw [hσ6, WState.setv_sh]; exact hsh5
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7)))))) ?_
    (by unfold parseCost; omega)
  apply WState.eq
  · funext j
    by_cases hj : j = I
    · subst hj
      simp only [WState.seth_sh, Function.update_self, WState.setv_sh]
      rw [hsh6, hsh]
      omega
    · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hj]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
  · funext j
    simp only [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]

end NearCubicWires.WireExponent3_5.PrimAsm.SBParse
