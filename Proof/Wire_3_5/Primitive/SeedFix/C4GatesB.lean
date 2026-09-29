import Proof.Wire_3_5.Primitive.SeedFix.C4GatesG

/-! # G1, the gate converter, part 4: one gate (P3:1655-1664)

One table gate `true :: pairW h (−θ) ++ (weights).flatMap (pairW h)` becomes, on the gate scratch `S`, its native word
framed once more (`quad (tabGW g) ++ [T, F]`, `tabGW g = natWord n ++ (weights).flatMap intWord ++ intWord (θ − 1)`,
C3a's native word of the pool gate `suppG g`): the threshold's word first on its own scratch `TS`, then the arity's
word, the weights' words, the threshold's word copied back (**`gateB_spec`**, **`gate_content`**).

Paper quantity of the main type: the gate's native word `tabGW g` (C3a's `nativeWord (suppG g)`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Gates
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

/-! ## One gate -/

/-- `σ` with `w` appended to the threshold scratch, its counter unchanged. -/
def appTS (σ : CS) (w : List Bool) : CS := (σ.sets sTS (σ.st sTS ++ w)).seth sTS (σ.sh sTS + w.length)

/-- **One gate** (after its marker): the threshold's word on `TS`, then the gate's native word on `S`: the arity's
word, the weights' words, the threshold's word, the frame's end. -/
def gateB (T : Fin 12) : CW :=
  .seq (tPair T) (.seq copyNQ (.seq (FinalPass.Hash4.wcopyR rN rK rT) (.seq (wLoop T)
    (.seq copyTS (.seq (PrimAsm.Emit.emitW sS rOs [true, false]) (.inc rCNT))))))

/-- The gate's step bound. -/
def gateCost (h n : ℕ) : ℕ := (n + 2) * (pairCost h + 100) + 300 * (natBitLength n + 1) + 500 * h + 800

/-- The gate's native word, framed once more, is what the gate body appends. -/
theorem gate_content {n : ℕ} (g : NormalizedThresholdGate n) :
    Streaming.marks (Streaming.marks (natWord n)) ++ quad ((List.ofFn g.weight).flatMap intWord) ++
      quad (intWord (g.threshold - 1)) ++ [true, false] = quad (tabGW g) ++ [true, false] := by
  rw [marks_marks, tabGW_eq, quad_append, quad_append]

theorem gateB_spec (cap : ℕ) (hcap : 1 ≤ cap) (j : Fin 6) (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n)
    (pre rest : List Bool) (σ : CS) (hh : 1 ≤ h) (hw : ∀ i, (g.weight i).natAbs < 2 ^ h)
    (ht : (g.threshold - 1).natAbs + 1 < 2 ^ h) (ht' : g.threshold.natAbs < 2 ^ h)
    (hst : σ.st (tbl j) = pre ++ (pairW h (-g.threshold) ++ ((List.ofFn g.weight).flatMap (pairW h) ++ rest)))
    (hsh : σ.sh (tbl j) = pre.length)
    (hL : σ.val rL = 0) (hL2 : σ.val rL2 = 0) (hZ : σ.val rZ = 0) (hF : σ.val rF = 0) (hH : σ.val rH = 0)
    (hX : σ.val rX = 0) (hT : σ.val rT = 0) (hK : σ.val rK = 0) (hOt : σ.val rOt = 0)
    (hNQ : σ.st sNQ = Streaming.marks (natWord n)) (hNQh : σ.sh sNQ = 0)
    (hq : σ.val rOq = (Streaming.marks (natWord n)).length) (hN : σ.val rN = n)
    (hS : σ.sh sS = (σ.st sS).length) (hTS : σ.sh sTS = (σ.st sTS).length)
    (hcS : σ.val rOs + (8 * h + 8) * (n + 2) + 8 * natBitLength n + 8 ≤ cap) (hc2 : 2 * h + 2 ≤ cap)
    (hcn : n + 4 * natBitLength n + 4 ≤ cap) (hcC : σ.val rCNT < cap) :
    WExec cap (gateB (tbl j)) σ
      (((PrimAsm.WriteNat.appendO (appTS σ (quad (intWord (g.threshold - 1)))) sS rOs
        (quad (tabGW g) ++ [true, false])).setv rCNT (σ.val rCNT + 1)).seth (tbl j)
        (pre.length + (pairW h (-g.threshold)).length + ((List.ofFn g.weight).flatMap (pairW h)).length))
      (gateCost h n) := by
  have hne : tbl j ≠ sS := tbl_ne j sS (by decide)
  have hneT : tbl j ≠ sTS := tbl_ne j sTS (by decide)
  have hneQ : tbl j ≠ sNQ := tbl_ne j sNQ (by decide)
  set wt := quad (intWord (g.threshold - 1)) with hwt
  have hwtl : wt.length ≤ 8 * h + 8 := by
    rw [hwt, quad_length, intWord_length']
    have := CompilerMachine.Pool.natBitLength_le (g.threshold - 1).natAbs h hh (by omega)
    omega
  have hnq : (Streaming.marks (natWord n)).length = 4 * natBitLength n + 2 := by
    rw [Streaming.marks_length, natWord_length']; ring
  have hmm : (Streaming.marks (Streaming.marks (natWord n))).length = 8 * natBitLength n + 4 := by
    rw [Streaming.marks_length, hnq]; ring
  have hws : ∀ w ∈ List.ofFn g.weight, w.natAbs < 2 ^ h := by
    intro w hw'; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw'; exact hw i
  have hlen : (List.ofFn g.weight).length = n := List.length_ofFn
  have hwsl : (quad ((List.ofFn g.weight).flatMap intWord)).length ≤ n * (8 * h + 8) := by
    rw [quad_length]; have := flatMap_intWord_le h hh _ hws; rw [hlen] at this
    have e : n * (8 * h + 8) = 4 * (n * (2 * h + 2)) := by ring
    omega
  set A := n * (8 * h + 8) with hA
  have hM : (8 * h + 8) * (n + 2) = A + 16 * h + 16 := by rw [hA]; ring
  rw [hM] at hcS
  have h8 : 8 * h + 8 ≤ cap := by omega
  -- 1: the threshold's word on TS
  have s1 := tPair_spec cap hcap j h g.threshold pre ((List.ofFn g.weight).flatMap (pairW h) ++ rest) σ hh ht ht'
    hst hsh hL hL2 hZ hF hH hX hTS (by rw [hOt]; omega) hc2
  set p1 := pre.length + (pairW h (-g.threshold)).length with hp1
  set σ1 := (PrimAsm.WriteNat.appendO σ sTS rOt wt).seth (tbl j) p1 with hσ1
  -- 2: the arity's word on S
  have s2 := copyNQ_spec cap (Streaming.marks (natWord n)) σ1
    (by simp [σ1, Function.update_apply, hneQ.symm, hNQ, show sNQ ≠ sTS by decide])
    (by simp [σ1, Function.update_apply, hneQ.symm, hNQh, show sNQ ≠ sTS by decide])
    (by simp +decide [σ1, Function.update_apply, hq]) (by simp +decide [σ1, Function.update_apply, hX])
    (by simp +decide [σ1, Function.update_apply, hT]) (by simp +decide [σ1, Function.update_apply, hne.symm, hS])
    (by simp +decide [σ1, Function.update_apply]; omega) (by rw [hnq]; omega)
  set σ2 := PrimAsm.WriteNat.appendO σ1 sS rOs (Streaming.marks (Streaming.marks (natWord n))) with hσ2
  -- 3: K := n
  have s3 := FinalPass.Hash4.wcopyR_spec cap rN rK rT (by decide) (by decide) (by decide) σ2
    (by simp +decide [σ2, σ1, Function.update_apply, hK]) (by simp +decide [σ2, σ1, Function.update_apply, hT])
    (by simp +decide [σ2, σ1, Function.update_apply, hN]; omega)
  have hσ2N : σ2.val rN = n := by simp +decide [σ2, σ1, Function.update_apply, hN]
  rw [hσ2N] at s3
  set σ3 := σ2.setv rK n with hσ3
  -- 4: the weights' words on S
  have hv3 : σ3.val rOs = σ.val rOs + (Streaming.marks (Streaming.marks (natWord n))).length := by
    simp only [σ3, σ2, σ1, WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply,
      if_neg (show rOs ≠ rK by decide), if_pos rfl, if_neg (show rOs ≠ rOt by decide), ite_true]
  have s4 := wLoop_spec cap hcap j h hh (List.ofFn g.weight) (pre ++ pairW h (-g.threshold)) rest σ3 hws
    (by simp [σ3, σ2, σ1, Function.update_apply, hne, hneT, hst, List.append_assoc])
    (by simp [σ3, σ2, σ1, Function.update_apply, hne, hneT, hp1])
    (by simp [σ3, hlen])
    (by simp +decide [σ3, σ2, σ1, Function.update_apply, hL]) (by simp +decide [σ3, σ2, σ1, Function.update_apply, hL2])
    (by simp +decide [σ3, σ2, σ1, Function.update_apply, hZ]) (by simp +decide [σ3, σ2, σ1, Function.update_apply, hF])
    (by simp +decide [σ3, σ2, σ1, Function.update_apply, hH]) (by simp +decide [σ3, σ2, σ1, Function.update_apply, hX])
    (by simp +decide [σ3, σ2, σ1, Function.update_apply, hne.symm, hS])
    (by rw [hv3, hmm, hlen, show (8 * h + 8) * n = A by rw [hA]; ring]; omega) hc2 (by rw [hlen]; omega)
  set p2 := (pre ++ pairW h (-g.threshold)).length + ((List.ofFn g.weight).flatMap (pairW h)).length with hp2
  set σ4 := ((PrimAsm.WriteNat.appendO σ3 sS rOs (quad ((List.ofFn g.weight).flatMap intWord))).seth (tbl j) p2).setv
    rK 0 with hσ4
  have hv4 : σ4.val rOs = σ3.val rOs + (quad ((List.ofFn g.weight).flatMap intWord)).length := by
    simp only [σ4, WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply,
      if_neg (show rOs ≠ rK by decide), if_pos rfl, ite_true]
  -- 5: the threshold's word copied onto S
  have s5 := copyTS_spec cap (σ.st sTS) wt σ4
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hneT.symm, show sTS ≠ sS by decide])
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hneT.symm, show sTS ≠ sS by decide, hTS])
    (by simp +decide [σ4, σ3, σ2, σ1, Function.update_apply, hOt])
    (by simp +decide [σ4, σ3, σ2, σ1, Function.update_apply, hX])
    (by simp +decide [σ4, σ3, σ2, σ1, Function.update_apply, hT])
    (by simp +decide [σ4, σ3, σ2, σ1, Function.update_apply, hne.symm, hS] <;> omega)
    (by rw [hv4, hv3, hmm]; omega) (by omega)
  set σ5 := (PrimAsm.WriteNat.appendO σ4 sS rOs wt).setv rOt 0 with hσ5
  have hv5 : σ5.val rOs = σ4.val rOs + wt.length := by
    simp only [σ5, WState.setv_val, PrimAsm.WriteNat.appendO_val, Function.update_apply,
      if_neg (show rOs ≠ rOt by decide), if_pos rfl, ite_true]
  -- 6: the frame's end, the count
  have s6 := PrimAsm.Emit.emitW_spec cap sS rOs [true, false] σ5
    (by simp +decide [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne.symm, hS]; omega)
    (by rw [hv5, hv4, hv3, hmm]; simp only [List.length_cons, List.length_nil]; omega)
  set σ6 := PrimAsm.WriteNat.appendO σ5 sS rOs [true, false] with hσ6
  have s7 := WExec.inc (cap := cap) rCNT σ6 (by simp +decide [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; exact hcC)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))))
    ?_ ?_
  · have hc := gate_content g
    have hcl := congrArg List.length hc
    simp only [List.length_append] at hcl
    apply WState.eq
    · funext i
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, appTS, WState.setv_sh, WState.seth_sh, WState.sets_sh,
        PrimAsm.WriteNat.appendO_sh, Function.update_apply]
      by_cases h1 : i = tbl j
      · subst h1; simp [hne, hneT, hp2, hp1] <;> omega
      · by_cases h2 : i = sS
        · subst h2; simp +decide [h1, hwt] at hcl ⊢; omega
        · by_cases h3 : i = sTS
          · subst h3; simp +decide [h1]
          · simp [h1, h2, h3]
    · funext i
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, appTS, WState.setv_st, WState.seth_st, WState.sets_st,
        PrimAsm.WriteNat.appendO_st, Function.update_apply]
      by_cases h2 : i = sS
      · subst h2; simp +decide [← hc, List.append_assoc, hwt]
      · by_cases h3 : i = sTS
        · subst h3; simp +decide
        · simp [h2, h3]
    · funext r
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, appTS, WState.setv_val, WState.seth_val, WState.sets_val,
        PrimAsm.WriteNat.appendO_val, Function.update_apply]
      by_cases h1 : r = rCNT
      · subst h1; simp +decide
      · by_cases h2 : r = rOs
        · subst h2; simp +decide [hwt] at hcl ⊢; omega
        · by_cases h3 : r = rOt
          · subst h3; simp +decide [hOt]
          · by_cases h4 : r = rK
            · subst h4; simp +decide [hK]
            · simp [h1, h2, h3, h4]
    · rfl
  · unfold gateCost
    have : 70 * (Streaming.marks (natWord n)).length ≤ 280 * natBitLength n + 140 := by rw [hnq]; omega
    simp only [hlen, List.length_cons, List.length_nil]
    have e1 : n * (pairCost h + 4) = n * pairCost h + 4 * n := by ring
    have e2 : (n + 2) * (pairCost h + 100) = n * pairCost h + 100 * n + 2 * pairCost h + 200 := by ring
    omega

end NearCubicWires.WireExponent3_5.PrimT.C4Gates
