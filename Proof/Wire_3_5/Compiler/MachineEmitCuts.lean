import Proof.Wire_3_5.Compiler.MachineEmitCut

/-! # C3.7 emit: the two successor cuts' weights and thresholds (P3:1728-1731)

Paper: "Replace an equality by the two successor cuts `1[E_i=0] = 1[E_i≥0] − 1[E_i≥1]`" (P3:1728-1731). The first cut
writes the `nf = 2w` signed weights and the threshold `T` (**`cut0_step`**); the second writes the same weights and
`T + 1` (**`cut1_step`**). The stack and driver heads return to cell `0` (a masked reset), so the two cuts read the
same stack. The paper quantity of the main theorems is the request's word of each cut's fields before its
coefficient: `fieldsWord W bs (nf + 1)` for the first cut, `fieldsWord W bs nf ++ frame (sm (fz nf + 1))` for the
second.

Layout: the field layout (0 `S1`, 1 `TZ`, 2 `RP`, 3 `RN`, 4 `RD`, 5 `CMP`, 6 `OUT`, 7 `LOG`, 8 `CW`, 9 `RP1`) and the
reset log 10. Main declarations: `cutSel`, `cut0Raw`, `cut1Raw`, `cut0M`, `cut1M`, `cutH`, `cutA`, `cut0Cost`,
`cut1Cost`, **`cut0_step`**, **`cut1_step`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (signMagnitude)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The heads a cut returns to cell `0`: the stack and the driver. -/
def cutSel : Fin 10 → Bool := ![true, false, false, false, false, false, false, false, true, false]

noncomputable def cut0Raw := Composition.machine (StreamController.machine fieldBodyM 8) pair0M
noncomputable def cut1Raw := Composition.machine (StreamController.machine fieldBodyM 8) pair1M
/-- **The first cut's fields** (weights and `T`), heads of the stack and driver reset. -/
noncomputable def cut0M := MaskedReset.machine cut0Raw cutSel
/-- **The successor cut's fields** (weights and `T + 1`), heads of the stack and driver reset. -/
noncomputable def cut1M := MaskedReset.machine cut1Raw cutSel

/-- The cut layout's heads (only the output cursor is not at cell `0`). -/
def cutH (o : ℕ) : Fin 11 → ℕ := ![0, 0, 0, 0, 0, 0, o, 0, 0, 0, 0]

/-- The cut layout's tapes. -/
def cutA (S1 TZ RP RN RD O LG CW RP1 LG2 : List Bool) : Fin 11 → List Bool :=
  ![S1, TZ, RP, RN, RD, [false], O, LG, CW, RP1, LG2]

def cut0Cost (W L nf : ℕ) : ℕ := nf * (fieldCost W L + 2) + 1 + 1 + (padCost W L + 1 + padCost W L + 1 + normCost W)
def cut1Cost (W L nf : ℕ) : ℕ :=
  nf * (fieldCost W L + 2) + 1 + 1 + (padCost W L + 1 + padCost W L + 1 + ((2 * (2 * W + 1) + 2) + 1 + normCost W))

/-- **The first cut**: the output gets the `nf` weights and the threshold, `fieldsWord W bs (nf + 1)`. -/
theorem cut0_step (W L nf : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L)
    (hnf : 2 * nf + 1 < bs.length) (stale tz RP RN RD out BW post RP1 : List Bool) (hpost : readTapeBit post 0 = false)
    (cap cap2 : ℕ) (hcap1 : 2 * W + 1 ≤ cap) (hcap2 : 2 * L + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hc : cut0Cost W L nf ≤ cap2) :
    Step cut0M (2 * cut0Cost W L nf + 2) (cutH out.length)
      (cutA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) RP RN RD (overlay out BW)
        (List.replicate cap false) (List.replicate nf true ++ post) RP1 (List.replicate cap2 false))
      (cutH (out ++ fieldsWord W bs (nf + 1)).length)
      (cutA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) (regAt W RP (fx bs) (nf + 1))
        (regAt W RN (fy bs) (nf + 1)) (regAt W RD (fun q => (fz bs q).natAbs) (nf + 1))
        (overlay (out ++ fieldsWord W bs (nf + 1)) BW) (List.replicate cap false) (List.replicate nf true ++ post) RP1
        (List.replicate cap2 false)) := by
  have lp := field_loop W L nf hLW bs hbs (by omega) stale tz RP RN RD out BW post RP1 hpost cap hcap1 hcap2
  have pr := pair0_step W L hLW bs hbs nf hnf stale tz (regAt W RP (fx bs) nf) (regAt W RN (fy bs) nf)
    (regAt W RD (fun q => (fz bs q).natAbs) nf) (out ++ fieldsWord W bs nf) BW (List.replicate nf true ++ post) RP1
    nf cap hcap1 hcap2
  rw [regAt_succ W RP (fx bs) nf, regAt_succ W RN (fy bs) nf] at pr
  have e3 : overlay (frame (binary W (fz bs nf).natAbs)) (regAt W RD (fun q => (fz bs q).natAbs) nf) =
      regAt W RD (fun q => (fz bs q).natAbs) (nf + 1) := regAt_succ W RD (fun q => (fz bs q).natAbs) nf
  rw [e3, List.append_assoc, ← fieldsWord_succ] at pr
  have j := lp.seq pr
  have hm := j.mask cutSel (by intro i hi; fin_cases i <;> simp_all [cutSel, fdH]) (cap := cap2) (by unfold cut0Cost at hc; omega)
  unfold cut0Cost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

/-- **The successor cut**: the output gets the `nf` weights and the threshold plus one. -/
theorem cut1_step (W L nf : ℕ) (hLW : L < W) (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = L)
    (hnf : 2 * nf + 1 < bs.length) (stale tz RP RN RD out BW post RP1 : List Bool) (hpost : readTapeBit post 0 = false)
    (cap cap2 : ℕ) (hcap1 : 2 * W + 1 ≤ cap) (hcap2 : 2 * L + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hc : cut1Cost W L nf ≤ cap2) :
    Step cut1M (2 * cut1Cost W L nf + 2) (cutH out.length)
      (cutA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) RP RN RD (overlay out BW)
        (List.replicate cap false) (List.replicate nf true ++ post) RP1 (List.replicate cap2 false))
      (cutH (out ++ (fieldsWord W bs nf ++ frame (signMagnitude W (fz bs nf + 1)))).length)
      (cutA (streamTape (bs.map (true :: ·)) stale) (frame (List.replicate W false) ++ tz) (regAt W RP (fx bs) (nf + 1))
        (regAt W RN (fy bs) (nf + 1))
        (overlay (frame (binary W (fz bs nf + 1).natAbs)) (regAt W RD (fun q => (fz bs q).natAbs) nf))
        (overlay (out ++ (fieldsWord W bs nf ++ frame (signMagnitude W (fz bs nf + 1)))) BW) (List.replicate cap false)
        (List.replicate nf true ++ post) (overlay (frame (binary W (fx bs nf + 1))) RP1)
        (List.replicate cap2 false)) := by
  have lp := field_loop W L nf hLW bs hbs (by omega) stale tz RP RN RD out BW post RP1 hpost cap hcap1 hcap2
  have pr := pair1_step W L hLW bs hbs nf hnf stale tz (regAt W RP (fx bs) nf) (regAt W RN (fy bs) nf)
    (regAt W RD (fun q => (fz bs q).natAbs) nf) (out ++ fieldsWord W bs nf) BW (List.replicate nf true ++ post) RP1
    nf cap hcap1 hcap2
  rw [regAt_succ W RP (fx bs) nf, regAt_succ W RN (fy bs) nf, List.append_assoc] at pr
  have j := lp.seq pr
  have hm := j.mask cutSel (by intro i hi; fin_cases i <;> simp_all [cutSel, fdH]) (cap := cap2) (by unfold cut1Cost at hc; omega)
  unfold cut1Cost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl


end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
