import Proof.Wire_3_5.Selection.GatePre1

/-! # C1.4: the gate routine's words and record copies (P3:1339-1358)

Paper: "Enumerate each half's score vectors" (P3:1344-1345). The routine's scratch words start empty or at their
working length with any contents; `zw` writes a width-`n` zero word over either (`zw_spec`). The weight tables are
built record by record from the gate record `GA` (C1.4's `gateRec`: each weight's sign cell and framed magnitude):
`skipRec` passes one record, `copyRec neg` copies one, its sign xor `neg` (the left table negates). Main declarations:
**`zw_spec`**, **`skipRec_rst`**, **`copyRec_rst`**. Paper quantity: none (the machine's words and tables). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-! ## Zero words -/

/-- **Write a width-`N` zero word** on `Z` (over its old contents), head and counter `CZ` back to `0`. -/
def zw (Z : Fin (ns + 1)) (CZ N T : Fin nr) : WM ns nr :=
  .seq (emitPairsN Z CZ N T false) (.seq (emitB Z CZ false) (WM.rewind Z CZ))

theorem zw_spec (cap : ℕ) (σ : WState ns nr) {A Z : Fin (ns + 1)} {CA CZ N T : Fin nr} (hAZ : A ≠ Z) (hC : CA ≠ CZ)
    (hNT : N ≠ T) (hN1 : N ≠ CA) (hN2 : N ≠ CZ) (hT1 : T ≠ CA) (hT2 : T ≠ CZ) (n : ℕ)
    (hA : σ.sh A = 0) (hCA : σ.val CA = 0) (hZ : σ.sh Z = 0) (hCZ : σ.val CZ = 0) (hN : σ.val N = n) (hT : σ.val T = 0)
    (hlen : (σ.st Z).length ≤ 2 * n + 1) (hcap : 2 * n + 2 ≤ cap) :
    WExec cap (zw Z CZ N T) σ (σ.sets Z (frame (binary n 0))) (n * (15 + 8) + 1 + 1 + (7 * n + 1) + 1 + (5 * (2 * n) + 14)) := by
  have h1 := emitPairs_rst cap σ (σ.st Z) hAZ hC N T hNT hN1 hN2 hT1 hT2 false n 0 [] hN hT (by omega) (by simp; omega)
  rw [rst_kst σ (σ.st Z) hAZ hC hA hCA, rst_kst σ (σ.st Z) hAZ hC hA hCA, kst_nil σ Z CZ hZ hCZ, List.nil_append] at h1
  have h2 := kst_end cap σ hAZ hC hA hCA hZ hCZ (σ.st Z) (frameP (List.replicate n false)) (by simp; omega)
  have e : overlay (frameP (List.replicate n false) ++ [false]) (σ.st Z) = frame (binary n 0) := by
    rw [overlay_full _ _ (by simp; omega), frame_eq_frameP, binary_zero_rep]
  rw [e] at h2
  unfold zw
  exact WExec.cast cap (WExec.seq h1 h2) rfl (by simp)

/-! ## Records of the gate record -/

/-- Skip one record (the sign cell, the framed magnitude). -/
def skipRec (A : Fin (ns + 1)) (CA : Fin nr) : WM ns nr := .seq (WM.fwdC A CA) (skipRest A CA)

/-- Copy one record, its sign xor `neg`. -/
def copyRec (neg : Bool) (A B : Fin (ns + 1)) (CA CB : Fin nr) : WM ns nr :=
  .seq (.ifs A (emitB B CB (!neg)) (emitB B CB neg)) (.seq (WM.fwdC A CA) (.seq (.whs A (copyPair A B CA CB))
    (.seq (emitB B CB false) (WM.fwdC A CA))))

section Rec
variable (cap : ℕ) (σ0 : WState ns nr) {A B : Fin (ns + 1)} {CA CB : Fin nr} (L : List Bool)
variable (hAB : A ≠ B) (hC : CA ≠ CB)
include hAB hC

theorem skipRec_rst (W : ℕ) (r : Bool × ℕ) (pre post out : List Bool) (hA : σ0.st A = pre ++ recBits W r ++ post)
    (hcap : pre.length + 2 * W + 2 < cap) :
    WExec cap (skipRec A CA) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L (pre.length + (2 * W + 2)) out) (13 * W + 13) := by
  have f := fwdA_rst cap σ0 L hAB hC pre.length out (by omega)
  have hA' : σ0.st A = (pre ++ [r.1]) ++ frameP (binary W r.2) ++ false :: post := by
    rw [hA]; simp [recBits, frame_eq_frameP]
  have h := skipRest_rst cap σ0 L hAB hC (binary W r.2) (pre ++ [r.1]) out post hA' (by simp; omega)
  simp only [List.length_append, List.length_singleton, binary_length] at h
  unfold skipRec
  exact WExec.cast cap (WExec.seq f h) (by congr 1; omega) (by omega)

theorem copyRec_rst (neg : Bool) (W : ℕ) (r : Bool × ℕ) (pre post out : List Bool)
    (hA : σ0.st A = pre ++ recBits W r ++ post) (hcap : pre.length + 2 * W + 2 < cap)
    (hq : out.length + 2 * W + 2 < cap) :
    WExec cap (copyRec neg A B CA CB) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L (pre.length + (2 * W + 2)) (out ++ recBits W (xor r.1 neg, r.2))) (40 * W + 40) := by
  have hbit : wbit (rst σ0 A B CA CB L pre.length out) A = r.1 := by
    rw [rst_bitA σ0 L hAB hC, hA, List.append_assoc, rd_app0]; simp [recBits]; rfl
  have e1 : WExec cap (.ifs A (emitB B CB (!neg)) (emitB B CB neg)) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L pre.length (out ++ [xor r.1 neg])) 8 := by
    cases h : r.1
    · rw [h] at hbit
      have := emitB_rst cap σ0 L hAB hC pre.length out neg (by omega)
      simpa using WExec.ifsF hbit this
    · rw [h] at hbit
      have := emitB_rst cap σ0 L hAB hC pre.length out (!neg) (by omega)
      simpa using WExec.ifsT hbit this
  have f1 := fwdA_rst cap σ0 L hAB hC pre.length (out ++ [xor r.1 neg]) (by omega)
  have hA' : σ0.st A = (pre ++ [r.1]) ++ frameP (binary W r.2) ++ false :: post := by
    rw [hA]; simp [recBits, frame_eq_frameP]
  have c := copyLoop_rst cap σ0 L hAB hC (binary W r.2) (pre ++ [r.1]) (out ++ [xor r.1 neg]) post hA'
    (by simp; omega) (by simp; omega)
  simp only [List.length_append, List.length_singleton, binary_length] at c
  have e2 := emitB_rst cap σ0 L hAB hC (pre.length + 1 + 2 * W) (out ++ [xor r.1 neg] ++ frameP (binary W r.2)) false
    (by simp; omega)
  have f2 := fwdA_rst cap σ0 L hAB hC (pre.length + 1 + 2 * W) (out ++ [xor r.1 neg] ++ frameP (binary W r.2) ++ [false])
    (by omega)
  unfold copyRec
  refine WExec.cast cap (WExec.seq e1 (WExec.seq f1 (WExec.seq c (WExec.seq e2 f2)))) ?_ (by omega)
  congr 1
  · omega
  · simp [recBits, frame_eq_frameP]

end Rec

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
