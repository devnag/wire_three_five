import Proof.Wire_3_5.Compiler.MachinePoolRun

/-! # C3a, the pool builder: `pool_run` with its cost (P3:1596-1664, 1905-1906)

Paper: alg:pullback (P3:1624-1664) and "Construction is polynomial in the explicit output size" (alg:disjoint,
P3:1614). MC6's `pool_run` states the pool builder's run with its cost under an existential; the class bound
of C3a's machine obligation needs the cost itself. **`pool_run_cost`** is the same run (same proof) with the explicit
cost `poolCost`: phase A (the normalization, `2·normCost + 2`), phase B (every flip pattern's dense children,
`2·(|flips|·(flipCost + 2) + 1) + 2`), phase C (the terminator, `1`) and phase D (the children table,
`|flips|·(tflipCost + 2) + 1`), with the three bridges. The paper quantity is the construction cost of C3a's two
words. Main declarations: `poolCost`, **`pool_run_cost`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

variable (a : DecompositionAlgorithm)

/-- The pool builder's cost: phases A–D with their bridges (`nL`, `nR` the side counts, `G` the children, `F` the flip
patterns, `W` the labels, `c` the gates). -/
def poolCost (h Q Wc V n width nL nR G F W c : ℕ) : ℕ :=
  (2 * normCost h n G + 2) + 1 + ((2 * (F * (flipCost h n width nL nR G + 2) + 1) + 2) + 1 +
    (1 + 1 + (F * (tflipCost n Q W Wc V c + 2) + 1)))

/-- **The pool builder with its cost**: MC6's `pool_run` with the cost `poolCost`. -/
theorem pool_run_cost (h Q Wc V : ℕ) (h1 : 1 ≤ h) (hW1 : 1 ≤ Wc) {n : ℕ} (hn : 1 ≤ n) (gates : List (SupportedNormalizedGate n))
    (side : List Bool) (width : ℕ) (flips : List (List Bool)) (hs : side.length = n)
    (hfl : ∀ f ∈ flips, f.length = n) (hL : nLeft side n ≤ width) (hR : nRight side n ≤ width)
    (postG postC tS sZL sZR staleF MR FR RP RN OL OR PA NA TM NM OUT TB : List Bool)
    (x0 capK cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 : ℕ)
    (hok : ∀ e ∈ GS a gates, ∀ z ∈ List.ofFn e.weight ++ [e.target], CoefOk h capK cap z)
    (hcs : ∀ v ∈ counts a gates, v < 2 ^ Wc ∧ v ≤ V ∧ natBitLength v ≤ capK)
    (hc1 : 2 * h + 1 ≤ cap) (hcF : 2 * n + 1 ≤ cap)
    (hcT1 : 2 * (Q + flips.length * (counts a gates).sum + 1) + 1 ≤ cap) (hcT2 : 2 * Wc + 2 ≤ cap)
    (hcT3 : 3 * Wc + 2 ≤ cap)
    (hcN2 : innerCost h n ≤ capN2) (hcN7 : normCost h n (GS a gates).length ≤ capN7) (hcC2 : cloopCost h n ≤ capC2)
    (hcC3 : appCost h (2 * nLeft side n) (2 * (width - nLeft side n)) (2 * nRight side n)
      (2 * (width - nRight side n)) ≤ capC3)
    (hcC4 : kidsCost h n width (nLeft side n) (nRight side n) (GS a gates).length ≤ capC4)
    (hcF8 : flips.length * (flipCost h n width (nLeft side n) (nRight side n) (GS a gates).length + 2) + 1 ≤ capF8)
    (hc5 : gatesCost Q (flips.length * (counts a gates).sum) Wc V (counts a gates).length ≤ cap5) :
    ∃ tout : RT, tout.out = overlay ((poolRecs a h gates side width flips).flatMap frame ++ [false]) OUT ∧
      tout.tb = overlay ((childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream) TB ∧
      Step poolM (poolCost h Q Wc V n width (nLeft side n) (nRight side n) (GS a gates).length flips.length
        (flips.length * (counts a gates).sum) (counts a gates).length) (rH 0 0 0 0 0)
        (rA (rtPool ((GS a gates).flatMap exactWord ++ postG) (false :: List.replicate capK true) MR (frame (binary h 0))
          NM (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false)
          (List.replicate (GS a gates).length true) (frame side ++ tS) FR RP RN OL OR PA NA TM
          (List.replicate capC2 false) (streamTape (zeroRecs h (width - nLeft side n)) sZL)
          (streamTape (zeroRecs h (width - nRight side n)) sZR) OUT (List.replicate capC3 false)
          (List.replicate capC4 false) (streamTape flips staleF) ((counts a gates).flatMap natWord ++ false :: postC)
          (frame (binary Wc x0)) (frame (binary Wc 0)) (frame (binary Wc x0)) [false] [true]
          (frame (entC Q (flips.length * (counts a gates).sum) 0)) (frame (shiftMask Q (flips.length * (counts a gates).sum)))
          (frame (entC Q (flips.length * (counts a gates).sum) 0)) TB (List.replicate cap5 false)
          (List.replicate capN7 false) (List.replicate capF8 false)))
        (rH ((GS a gates).flatMap exactWord).length (GS a gates).length
          ((poolRecs a h gates side width flips).flatMap frame ++ [false]).length (flips.flatMap frame).length
          ((childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream).length)
        (rA tout) := by
  set gs := GS a gates
  set W := flips.length * (counts a gates).sum
  set t0 := rtPool (gs.flatMap exactWord ++ postG) (false :: List.replicate capK true) MR (frame (binary h 0))
    NM (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false)
    (List.replicate gs.length true) (frame side ++ tS) FR RP RN OL OR PA NA TM
    (List.replicate capC2 false) (streamTape (zeroRecs h (width - nLeft side n)) sZL)
    (streamTape (zeroRecs h (width - nRight side n)) sZR) OUT (List.replicate capC3 false)
    (List.replicate capC4 false) (streamTape flips staleF) ((counts a gates).flatMap natWord ++ false :: postC)
    (frame (binary Wc x0)) (frame (binary Wc 0)) (frame (binary Wc x0)) [false] [true]
    (frame (entC Q W 0)) (frame (shiftMask Q W)) (frame (entC Q W 0)) TB (List.replicate cap5 false)
    (List.replicate capN7 false) (List.replicate capF8 false)
  have sA := pA_step h h1 gs postG t0 capK cap capN2 capN7 hok hc1 hcN2 hcN7
  set x1 := (t0.inA (gs.flatMap exactWord ++ postG) (false :: List.replicate capK true) (frame (binary h 0))
    (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false) (List.replicate gs.length true)
    (List.replicate capN7 false)).outA (mrKids h MR gs) (overlay (normTape h gs) NM)
  have sB := pB_step h h1 hn gs side width flips hs hfl hL hR (NM.drop (normTape h gs).length) tS sZL sZR staleF x1
    (gs.flatMap exactWord).length gs.length cap capC2 capC3 capC4 capF8 hc1 hcF hcC2 hcC3 hcC4 hcF8
  rw [normTape_overlay] at sB
  set E' := flips.flatMap (fun f => gs.flatMap (denseRecs h side f width))
  set st' := flips.foldl (fnext h gs side width) x1.fst
  set x2 := (x1.inB (overlay (normTape h gs) NM) (frame side ++ tS) (frame (binary h 0))
    (streamTape (zeroRecs h (width - nLeft side n)) sZL) (streamTape (zeroRecs h (width - nRight side n)) sZR)
    (List.replicate cap false) (List.replicate capC2 false) (List.replicate capC3 false)
    (List.replicate capC4 false) (streamTape flips staleF) (List.replicate capF8 false)).outB st' (overlay (E'.flatMap frame) OUT)
  have sC := pC_step (gs.flatMap exactWord).length gs.length 0 0 (E'.flatMap frame) OUT x2
  set x3 := x2.outC (overlay (E'.flatMap frame ++ [false]) OUT)
  have sD := pD_step Q W Wc V n (counts a gates) flips postC staleF x3 (gs.flatMap exactWord).length gs.length
    (E'.flatMap frame ++ [false]).length x0 capK cap cap5 hW1 hfl hn hcs hcT1 hcT2 hcT3 hc5
  set gst := flips.foldl (fun st _ => (counts a gates).foldl (gnext Q W) st) ⟨0, x0, []⟩
  have j := sA.seq (sB.seq (sC.seq sD))
  have hE : (E'.flatMap frame ++ [false]).length = ((poolRecs a h gates side width flips).flatMap frame ++ [false]).length := by
    rw [poolRecs_eq]
  have ht := table_eq a Q gates side width flips [] x0
  simp only [List.nil_append] at ht
  have hT : gst.tbl.length = ((childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream).length := by
    rw [ht]
  rw [hE, hT] at j
  refine ⟨_, ?_, ?_, j⟩
  · show overlay (E'.flatMap frame ++ [false]) OUT = _
    rw [poolRecs_eq]
  · show overlay gst.tbl TB = _
    rw [ht]

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
