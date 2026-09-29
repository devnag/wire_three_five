import Proof.Wire_3_5.Primitive.SeedFix.S3Circ
import Proof.Wire_3_5.Primitive.SeedFix.S3Filt
import Proof.Wire_3_5.Primitive.SeedFix.CarMask
import Proof.Wire_3_5.FinalPass.ThrPtLiftR

/-! # S4 (the seeds phase), part 2: one carrier's factor of the mask at a sampled point (P3:2019-2025, 3074-3080)

"Write `M(e,x)` for their product" (P3:3078-3080): the call's mask at the point `x = c+u+v` is, over the named
carriers `X`, the regular filter `F_e` of the residual vector `Z_X(x)` (`maskBits`). By `Corner.maskBits_point` each
factor is stage 7 (`filterBits`, which is `tabEval` on the seed's table, `Filt.filterBits_eq_tab`) of stage 3's `+`
population of the doubled gates' corner word (stage 2).

On the evaluator layout (`SM = WM 13 32`), **`maskOne`**: stage 2 on the carrier's mask table (`cwS`), the `+`
population (`popP`), stage 7 with the bit in a register (`main7K`, lifted: **`m7S_spec`**; its streams the
population `sZ`, the seed's table on `sFT`, the threshold on `sT5`; its registers `7 … 13`), the population blanked
(`blankP`), the bit moved into register `26`. **`maskOne_spec`**: register `26` gains `tabEval thr tbl Z⁺`, the corner
word stays on `sX`, the accumulators hold some binary values, everything else as it was. **`maskOne_carrier`**: at a
carrier's mask table, the seed's table `filterTable FP e |maskGates X|` and the threshold `majorityThreshold`, the
bit is the carrier's factor `filterBits FP e (popBits true (cornerWord …))` of `maskBits_point`.

Paper quantity of the main type: one carrier's factor of the mask `M(e,x)` at a sampled point. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.SupplierWalk (majorityThreshold)

/-! ## Stage 7 on the layout -/

/-- Stage 7's streams: the population (`sZ`), the seed's table (on `sFT`), the threshold (on `sT5`). -/
def fs7 : Fin 3 → Fin 14 := ![7, 12, 10]

/-- Stage 7's registers: `7 … 13`. -/
def fr7 (i : Fin 7) : Fin 32 := ⟨i.val + 7, by omega⟩

theorem fs7_inj : Function.Injective fs7 := by decide

theorem fr7_inj : Function.Injective fr7 := fun a b h => Fin.ext (by
  have := congrArg Fin.val h
  simp only [fr7] at this
  omega)

/-- **Stage 7 on the layout**: the filter bit into register `9`. -/
def m7S : SM := main7K.liftR fs7 fr7

theorem m7S_spec (cap : ℕ) (Z : List Bool) (tbl : List (List (List Bool))) (thr : ℕ) (ω : SS)
    (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ Z.length) (hcap : capOf7 Z.length tbl thr ≤ cap)
    (hZ : ω.st sZ = frame Z) (hT : ω.st sFT = tableWord tbl) (hH : ω.st sT5 = ListEval.unary thr)
    (hsh : ∀ i, ω.sh (fs7 i) = 0) (hr : ∀ i, ω.val (fr7 i) = 0) :
    WExec cap m7S ω (ω.setv 9 (tabEval thr tbl Z).toNat) (cost7 (tableWord tbl).length thr) := by
  have h := main7K_spec cap Z tbl thr ω.cell hlen hcap
  have hL : LiftRelR fs7 fr7 (streams7 Z tbl thr) ω (S7 0 0 0 0 0 0 0 ω.cell) := by
    refine ⟨fun i => ?_, fun i p => ?_, fun r => ?_, rfl⟩
    · rw [hsh i]
      fin_cases i <;> rfl
    · fin_cases i
      · show readTapeBit (ω.st sZ) p = _
        rw [hZ]
        rfl
      · show readTapeBit (ω.st sFT) p = _
        rw [hT]
        rfl
      · show readTapeBit (ω.st sT5) p = _
        rw [hH]
        rfl
    · rw [hr r]
      fin_cases r <;> rfl
  have e := ThrPt.RExec.liftR_upd (streams7 Z tbl thr) cap cap le_rfl fs7_inj fr7_inj h ω hL
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · funext j
    by_cases hj : ∃ i, fs7 i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [ThrPt.updR_sh_in fs7_inj, WState.setv_sh, hsh i]
      fin_cases i <;> rfl
    · rw [ThrPt.updR_sh_out _ _ j (fun i e => hj ⟨i, e⟩), WState.setv_sh]
  · rfl
  · funext q
    by_cases hq : ∃ r, fr7 r = q
    · obtain ⟨r, rfl⟩ := hq
      rw [ThrPt.updR_val_in fr7_inj, WState.setv_val]
      by_cases h2 : r = 2
      · subst h2
        rw [show fr7 2 = 9 from rfl, Function.update_self]
        rfl
      · have hne : fr7 r ≠ 9 := fun e => h2 (fr7_inj (e.trans (rfl : (9 : Fin 32) = fr7 2)))
        rw [Function.update_of_ne hne, hr r]
        fin_cases r <;> first | rfl | exact absurd rfl h2
    · have hne : q ≠ 9 := fun e => hq ⟨2, e.symm⟩
      rw [ThrPt.updR_val_out _ _ q (fun r e => hq ⟨r, e⟩), WState.setv_val, Function.update_of_ne hne]
  · rfl

/-! ## One carrier's mask bit -/

/-- **One carrier's mask bit into register `26`**: stage 2, the `+` population, stage 7, the population blanked,
the bit moved. -/
def maskOne : SM := .seq cwS (.seq popP (.seq m7S (.seq blankP (WM.move 9 26))))

/-- Its steps: stage 2, two passes, stage 7, the move of one bit. -/
def mkCost (h n g W thr : ℕ) : ℕ :=
  cwCost h n g + 1 + (passCost g + 1 + (cost7 W thr + 1 + (passCost g + 1 + 8)))

/-- The capacity one carrier's mask needs (stage 2's, the passes', stage 7's). -/
structure MkCap (cap h n g : ℕ) (tbl : List (List (List Bool))) (thr : ℕ) : Prop where
  one : 1 ≤ cap
  hh : 2 * h ≤ cap
  nn : 2 * n ≤ cap
  kk : g * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ cap
  oo : 8 * g ≤ cap
  f7 : capOf7 g tbl thr ≤ cap

theorem maskOne_spec (cap h : ℕ) {n : ℕ} (G : List (NormalizedThresholdGate n)) (c u v : BitInput n)
    (tbl : List (List (List Bool))) (thr A B : ℕ) (ys : List Bool) (ω : SS)
    (hG : ω.st sG = gatesW h G) (hC : ω.st sC = frame (List.ofFn c)) (hU : ω.st sU = frame (List.ofFn u))
    (hV : ω.st sV = frame (List.ofFn v)) (hpos : ω.st sPos = frameP (binary h A) ++ [false])
    (hneg : ω.st sNeg = frameP (binary h B) ++ [false]) (hX : ω.st sX = ys ++ [false])
    (hys : ys.length = 8 * G.length) (hZ : ω.st sZ = List.replicate (2 * G.length + 1) false)
    (hSp : ω.st sSp = [true]) (hT : ω.st sFT = tableWord tbl) (hH : ω.st sT5 = ListEval.unary thr)
    (hsh : ∀ i, ω.sh i = 0) (hr : ∀ q : Fin 32, q.val < 14 → ω.val q = 0)
    (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ G.length) (hcap : MkCap cap h n G.length tbl thr)
    (h26 : ω.val 26 + 1 ≤ cap)
    (hov : ∀ g ∈ G, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) :
    ∃ ω' A' B', WExec cap maskOne ω ω' (mkCost h n G.length (tableWord tbl).length thr) ∧
      ω'.st sX = frameP (cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ [false] ∧
      ω'.st sPos = frameP (binary h A') ++ [false] ∧ ω'.st sNeg = frameP (binary h B') ++ [false] ∧
      (∀ i, i ≠ sPos → i ≠ sNeg → i ≠ sX → ω'.st i = ω.st i) ∧ ω'.sh = ω.sh ∧
      ω'.val = Function.update ω.val 26 (ω.val 26 +
        (tabEval thr tbl (popBits true (cornerWord (G.map NormalizedThresholdGate.eval) c u v))).toNat) ∧
      ω'.cell = ω.cell := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcap
  generalize hXdef : cornerWord (G.map NormalizedThresholdGate.eval) c u v = X
  have hXl : X.length = 4 * G.length := by rw [← hXdef, cornerWord_length, List.length_map]
  have hpl : (popBits true X).length = G.length := popBits_length true G.length X hXl
  have hb1 : (tabEval thr tbl (popBits true X)).toNat ≤ 1 := by
    cases tabEval thr tbl (popBits true X) <;> simp
  -- stage 2
  obtain ⟨ω1, A1, B1, e1, x1, p1, n1, o1, h1, v1, k1⟩ := cwS_spec cap h G c u v ω A B [] [] [] [] [false] [false] []
    ys (by rw [hsh sG, hG, List.drop_zero, List.append_nil]) (by rw [hsh sG, hG, gatesW_length]; omega)
    (by rw [hC, frame_eq_frameP]) (by rw [hU, frame_eq_frameP]) (by rw [hV, frame_eq_frameP]) (by rw [hpos])
    (by rw [hneg]) (by rw [hX]) hys (fun i _ _ => hsh i) (fun q hq => hr q (by omega)) c1 c2 c3 c4 c5 hov
  rw [hXdef] at x1
  -- the + population
  have hw1 : wbit ω1 sSp = true := by
    unfold wbit
    rw [o1 sSp (by decide) (by decide) (by decide), h1 sSp, hSp, hsh sSp]
    rfl
  have e2 := pop_spec cap sX sZ sSp (0 : Fin 32) (by decide) (by decide) (by decide) true G.length X []
    (List.replicate (2 * G.length + 1) false) ω1 hXl x1 (by rw [h1, hsh])
    (by rw [o1 sZ (by decide) (by decide) (by decide), hZ]) (by rw [h1, hsh]) (by simp) hw1
    (by rw [v1, hr 0 (by decide)]) (by omega)
  have hZp : frameP (popBits true X) ++ (List.replicate (2 * G.length + 1) false).drop (2 * G.length) =
      frame (popBits true X) := by
    rw [List.drop_replicate, show 2 * G.length + 1 - 2 * G.length = 1 by omega, frame_eq_frameP]
    rfl
  rw [hZp] at e2
  obtain ⟨ω2, hω2⟩ : ∃ y, y = ω1.sets sZ (frame (popBits true X)) := ⟨_, rfl⟩
  rw [← hω2] at e2
  -- stage 7
  have e3 := m7S_spec cap (popBits true X) tbl thr ω2 (by rw [hpl]; exact hlen) (by rw [hpl]; exact c6)
    (by rw [hω2]; simp)
    (by
      rw [hω2]
      simp only [WState.sets_st]
      rw [Function.update_of_ne (by decide), o1 sFT (by decide) (by decide) (by decide), hT])
    (by
      rw [hω2]
      simp only [WState.sets_st]
      rw [Function.update_of_ne (by decide), o1 sT5 (by decide) (by decide) (by decide), hH])
    (fun i => by rw [hω2]; simp only [WState.sets_sh]; rw [h1, hsh])
    (fun i => by
      rw [hω2]
      simp only [WState.sets_val]
      rw [v1]
      have := i.isLt
      exact hr _ (by simp only [fr7]; omega))
  obtain ⟨ω3, hω3⟩ : ∃ y, y = ω2.setv 9 (tabEval thr tbl (popBits true X)).toNat := ⟨_, rfl⟩
  rw [← hω3] at e3
  -- blank the population
  have hw3 : wbit ω3 sSp = true := by
    unfold wbit
    rw [hω3, hω2]
    simp only [WState.setv_st, WState.setv_sh, WState.sets_st, WState.sets_sh]
    rw [Function.update_of_ne (by decide), o1 sSp (by decide) (by decide) (by decide), h1 sSp, hSp, hsh sSp]
    rfl
  have e4 := blank_spec cap sX sZ sSp (0 : Fin 32) (by decide) (by decide) (by decide) true G.length X []
    (frame (popBits true X)) ω3 hXl
    (by
      rw [hω3, hω2]
      simp only [WState.setv_st, WState.sets_st]
      rw [Function.update_of_ne (by decide), x1])
    (by rw [hω3, hω2]; simp only [WState.setv_sh, WState.sets_sh]; rw [h1, hsh])
    (by rw [hω3, hω2]; simp)
    (by rw [hω3, hω2]; simp only [WState.setv_sh, WState.sets_sh]; rw [h1, hsh])
    (by rw [frame_eq_frameP]; simp [hpl]) hw3
    (by
      rw [hω3, hω2]
      simp only [WState.setv_val, WState.sets_val]
      rw [Function.update_of_ne (by decide), v1, hr 0 (by decide)])
    (by omega)
  have hZb : List.replicate (2 * G.length) false ++ (frame (popBits true X)).drop (2 * G.length) =
      List.replicate (2 * G.length + 1) false := by
    rw [frame_eq_frameP, List.drop_append_of_le_length (by simp [hpl]),
      List.drop_eq_nil_of_le (by simp [hpl]), List.nil_append, ← List.replicate_succ']
  rw [hZb] at e4
  obtain ⟨ω4, hω4⟩ : ∃ y, y = ω3.sets sZ (List.replicate (2 * G.length + 1) false) := ⟨_, rfl⟩
  rw [← hω4] at e4
  -- the bit into 26
  have v49 : ω4.val 9 = (tabEval thr tbl (popBits true X)).toNat := by
    rw [hω4, hω3]
    simp
  have v426 : ω4.val 26 = ω.val 26 := by
    rw [hω4, hω3, hω2]
    simp only [WState.sets_val, WState.setv_val]
    rw [Function.update_of_ne (by decide), v1]
  have e5 := wmove_spec cap (9 : Fin 32) 26 (by decide) _ ω4 v49 (by rw [v49]; omega) (by rw [v49, v426]; omega)
  refine ⟨_, A1, B1, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · unfold mkCost
    omega
  · simp only [WState.setv_st]
    rw [hω4]
    simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), hω3]
    simp only [WState.setv_st]
    rw [hω2]
    simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), x1]
  · simp only [WState.setv_st]
    rw [hω4]
    simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), hω3]
    simp only [WState.setv_st]
    rw [hω2]
    simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), p1]
  · simp only [WState.setv_st]
    rw [hω4]
    simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), hω3]
    simp only [WState.setv_st]
    rw [hω2]
    simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), n1]
  · intro i i1 i2 i3
    simp only [WState.setv_st]
    rw [hω4]
    simp only [WState.sets_st]
    by_cases hi : i = sZ
    · subst hi
      rw [Function.update_self, hZ]
    · rw [Function.update_of_ne hi, hω3]
      simp only [WState.setv_st]
      rw [hω2]
      simp only [WState.sets_st]
      rw [Function.update_of_ne hi, o1 i i1 i2 i3]
  · funext i
    simp only [WState.setv_sh]
    rw [hω4, hω3, hω2]
    simp only [WState.sets_sh, WState.setv_sh]
    exact h1 i
  · funext q
    simp only [WState.setv_val]
    by_cases hq26 : q = 26
    · subst hq26
      rw [Function.update_self, Function.update_self, v426, v49]
    · rw [Function.update_of_ne hq26, Function.update_of_ne hq26]
      by_cases hq9 : q = 9
      · subst hq9
        rw [Function.update_self, hr 9 (by decide)]
      · rw [Function.update_of_ne hq9, hω4, hω3]
        simp only [WState.sets_val, WState.setv_val]
        rw [Function.update_of_ne hq9, hω2]
        simp only [WState.sets_val]
        exact v1 q
  · simp only [WState.setv_cell]
    rw [hω4, hω3, hω2]
    simp only [WState.sets_cell, WState.setv_cell]
    exact k1

/-! ## The carrier's factor -/

/-- **The bit at the seed's table is the carrier's factor**: stage 7 at `filterTable FP e |maskGates X|` and the
majority threshold is the regular filter `filterBits FP e` of the population (`Filt.filterBits_eq_tab`). -/
theorem mask_tab (FP : GapParams) (e : GapSeed FP) {n : ℕ} (X : Stars.Carrier n) (c u v : BitInput n) :
    tabEval (majorityThreshold FP.walkLen) (filterTable FP e (maskGates X).length)
        (popBits true (cornerWord ((maskGates X).map NormalizedThresholdGate.eval) c u v)) =
      filterBits FP e (popBits true (cornerWord ((maskGates X).map NormalizedThresholdGate.eval) c u v)) := by
  rw [filterBits_eq_tab, popBits_length true (maskGates X).length _ (by rw [cornerWord_length, List.length_map])]

/-- **One carrier's factor of the mask into register `26`** (`maskOne` at the carrier's mask table
`gatesW (tabH X) (maskGates X)`, the seed's table and the majority threshold). -/
theorem maskOne_carrier (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (X : Stars.Carrier n)
    (c u v : BitInput n) (A B : ℕ) (ys : List Bool) (ω : SS)
    (hG : ω.st sG = gatesW (PrimT.tabH X) (maskGates X)) (hC : ω.st sC = frame (List.ofFn c))
    (hU : ω.st sU = frame (List.ofFn u)) (hV : ω.st sV = frame (List.ofFn v))
    (hpos : ω.st sPos = frameP (binary (PrimT.tabH X) A) ++ [false])
    (hneg : ω.st sNeg = frameP (binary (PrimT.tabH X) B) ++ [false]) (hX : ω.st sX = ys ++ [false])
    (hys : ys.length = 8 * (maskGates X).length)
    (hZ : ω.st sZ = List.replicate (2 * (maskGates X).length + 1) false) (hSp : ω.st sSp = [true])
    (hT : ω.st sFT = tableWord (filterTable FP e (maskGates X).length))
    (hH : ω.st sT5 = ListEval.unary (majorityThreshold FP.walkLen))
    (hsh : ∀ i, ω.sh i = 0) (hr : ∀ q : Fin 32, q.val < 14 → ω.val q = 0)
    (hcap : MkCap cap (PrimT.tabH X) n (maskGates X).length (filterTable FP e (maskGates X).length)
      (majorityThreshold FP.walkLen))
    (h26 : ω.val 26 + 1 ≤ cap) :
    ∃ ω' A' B', WExec cap maskOne ω ω' (mkCost (PrimT.tabH X) n (maskGates X).length
        (tableWord (filterTable FP e (maskGates X).length)).length (majorityThreshold FP.walkLen)) ∧
      ω'.st sX = frameP (cornerWord ((maskGates X).map NormalizedThresholdGate.eval) c u v) ++ [false] ∧
      ω'.st sPos = frameP (binary (PrimT.tabH X) A') ++ [false] ∧
      ω'.st sNeg = frameP (binary (PrimT.tabH X) B') ++ [false] ∧
      (∀ i, i ≠ sPos → i ≠ sNeg → i ≠ sX → ω'.st i = ω.st i) ∧ ω'.sh = ω.sh ∧
      ω'.val = Function.update ω.val 26 (ω.val 26 +
        (filterBits FP e (popBits true (cornerWord ((maskGates X).map NormalizedThresholdGate.eval) c u v))).toNat) ∧
      ω'.cell = ω.cell := by
  obtain ⟨ω', A', B', e1, x1, p1, n1, o1, h1, v1, k1⟩ := maskOne_spec cap (PrimT.tabH X) (maskGates X) c u v
    (filterTable FP e (maskGates X).length) (majorityThreshold FP.walkLen) A B ys ω hG hC hU hV hpos hneg hX hys hZ
    hSp hT hH hsh hr (fun vs hv cs hc => (filterTable_lengths FP e _ vs hv cs hc).le) hcap h26
    (PrimT.CarMask.mask_hov X)
  exact ⟨ω', A', B', e1, x1, p1, n1, o1, h1, by rw [v1, mask_tab], k1⟩

end NearCubicWires.WireExponent3_5.FinalPass.Sd
