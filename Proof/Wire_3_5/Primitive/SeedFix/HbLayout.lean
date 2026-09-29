import Proof.Wire_3_5.Primitive.SeedFix.HashRefM
import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Proof.Wire_3_5.Primitive.Writers.Emit

/-! # C4.Hb, machine part 1: the word layer's layout and the masked word step (`filt:soft`, P3:2253-2290)

The Hb machine prints, cell by cell of its odometer, the terms of `hashTermsM` (HashRefM): "After fixing `p`, Gaussian
elimination finds its conditional probability" (P3:2268-2269) is the elimination block (`elimX_run`), docked between
two word programs of C5's register language `WM` (the cell's validity and constraint records before it; the term and
the odometer's step after it). A word program runs as a `Step` through base's masked reset
(`MaskedReset.machine`): every head returns to cell `0` and the reset's log is blank again at the end
(**`wm_mask`**, from `Step.mask`), so the same program runs again at the next cell.

The layout (`HS := WState 23 40`) names the streams and registers the Hb programs share.

Paper quantity of the main type: the printed words of the cells (through `wm_mask`, the word programs as machine
steps). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## The masked word step -/

/-- **A word program as a reusable `Step`**: from heads at `0` and a blank log of capacity `capL`, the compiled program
under base's masked reset ends with every head at `0` and the log blank again. -/
theorem wm_mask {ns nr : ℕ} (cap capL : ℕ) (P : WM ns nr) (σ τ : WState ns nr) (n : ℕ) (hw : WExec cap P σ τ n)
    (hH : (wenc cap σ).H = fun _ => 0) (hn : n ≤ capL) :
    Step (MaskedReset.machine P.toProg.compile (fun _ => true)) (2 * n + 2) (fun _ => 0)
      (Fin.addCases (wenc cap σ).A (fun _ : Fin 1 => List.replicate capL false)) (fun _ => 0)
      (Fin.addCases (wenc cap τ).A (fun _ : Fin 1 => List.replicate capL false)) := by
  have hs := (WExec.exec cap hw).step
  rw [hH] at hs
  have hm := hs.mask (cap := capL) (fun _ => true) (fun _ _ => rfl) hn
  have e1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (ns + 2 + nr + 1) → ℕ) = fun _ => 0 := by
    funext i; induction i using Fin.addCases <;> simp
  have e2 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc cap τ).H i) (fun _ : Fin 1 => 0) :
      Fin (ns + 2 + nr + 1) → ℕ) = fun _ => 0 := by
    funext i; induction i using Fin.addCases <;> simp
  rw [e1, e2] at hm
  exact hm

theorem wenc_H_zero' {ns nr : ℕ} (cap : ℕ) (σ : WState ns nr) (hs : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) :
    (wenc cap σ).H = fun _ => 0 := by
  funext j; simp only [wenc]; split <;> simp [hs, hv]

/-! ## The layout -/

/-- The Hb word programs' state: 24 streams, 40 registers. -/
abbrev HS := WState 23 40
abbrev HW := WM 23 40

/-- The printed expression's term records (no terminator yet). -/
scoped notation "sOUT" => (0 : Fin 24)
/-- `1^{|OUT|}`. -/
scoped notation "sOLEN" => (1 : Fin 24)
/-- PA's HASH tape. -/
scoped notation "sHT" => (2 : Fin 24)
/-- The populations' records. -/
scoped notation "sPOPS" => (3 : Fin 24)
/-- The cleared weights' framed bits. -/
scoped notation "sWT" => (4 : Fin 24)
/-- The odometer's binary word: the sign bits, then the `ℓ₀`-bit positions. -/
scoped notation "sCTR" => (5 : Fin 24)
/-- The odometer's level, population, aux seed and row counters (`1^v 0^m`). -/
scoped notation "sLAM" => (6 : Fin 24)
scoped notation "sPC" => (7 : Fin 24)
scoped notation "sEC" => (8 : Fin 24)
scoped notation "sQC" => (9 : Fin 24)
/-- The elimination's constraint tape, its flag and its count exponent. -/
scoped notation "sCONS" => (10 : Fin 24)
scoped notation "sGF" => (11 : Fin 24)
scoped notation "sXE" => (12 : Fin 24)
/-- The cell's validity bit and the loop's bit. -/
scoped notation "sVAL" => (13 : Fin 24)
scoped notation "sMORE" => (14 : Fin 24)
/-- The rulers `1^{2t}`, `1^{ℓ₀}`, `1^J`, `1^G`, `1^{N²}`, `1^{nE}`, `1^{|pops|}`. -/
scoped notation "sTT" => (15 : Fin 24)
scoped notation "sLL" => (16 : Fin 24)
scoped notation "sJJ" => (17 : Fin 24)
scoped notation "sGG" => (18 : Fin 24)
scoped notation "sNN" => (19 : Fin 24)
scoped notation "sEE" => (20 : Fin 24)
scoped notation "sPP" => (21 : Fin 24)
/-- Scratch. -/
scoped notation "sS1" => (22 : Fin 24)
scoped notation "sS2" => (23 : Fin 24)

end NearCubicWires.WireExponent3_5.PrimT.HbM
