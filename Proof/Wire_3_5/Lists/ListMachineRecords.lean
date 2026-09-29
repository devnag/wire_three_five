import Proof.Wire_3_5.Lists.ListMachineEncoding
import Proof.Wire_3_5.MachineModel.BlockCopy
import Proof.Wire_3_5.MachineModel.BlockWhile

/-! # C2 machines, part 1: the tape encoding of explicit `𝔽₂` polynomials and the open copy

Realizes the output format of the C2 list machines (P3:1482-1488, "the explicit monomial lists"): the lists the
printer consumes are written on a tape as

* an atom (coordinate) `i` in unary, `atomCode i = 1^i 0`;
* a monomial `m` as the framed word of its atoms' codes, `frame (monoBits m)`;
* a polynomial `p` as its monomial records `true :: frame (monoBits m)`, then `false` (`polyWord p`).

Products only concatenate monomials, and `frame (x ++ y) = Streaming.marks x ++ frame y` (`Streaming.frame_append`), so a product
monomial is the OPEN copy of the first factor (its pairs, without the terminator) followed by the framed copy of the
second. This module gives that open copy as a machine (`CopyOpen`), exact in `2|x|+1` steps, and the one-step record
marker (`Mark`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Rec
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The open copy: the pairs of a framed word, without its terminator -/

namespace CopyOpen

end CopyOpen

/-! ## The full copy that steps past the terminator -/

namespace CopyPast

def action (state : Fin 3) (output : Option Bool) : Action 2 3 :=
  ⟨state, fun i => if i.val = 1 then output else none, fun _ => .right⟩

/-- Tape 0 holds a framed word at its cursor; tape 1 receives the framed word at its cursor. Both heads end one cell
past the terminator. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state scanned => if state.val = 0 then
      (if scanned 0 then some (action 1 (some true)) else some (action 2 (some false)))
    else if state.val = 1 then some (action 0 (some (scanned 0)))
    else none

def config (state : Fin 3) (source : List Bool) (sourceHead : ℕ) (output backing : List Bool) :
    Configuration 2 3 := ⟨state, ![sourceHead, output.length], ![source, overlay output backing]⟩

@[simp] theorem config_cells (state : Fin 3) (source : List Bool) (sourceHead : ℕ) (output backing : List Bool) :
    (config state source sourceHead output backing).tapeCells = source.length + max output.length backing.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]

theorem marker_step (source : List Bool) (h : ℕ) (output backing : List Bool) (hr : readTapeBit source h = true) :
    step machine (config 0 source h output backing) = some (config 1 source (h + 1) (output ++ [true]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem bit_step (source : List Bool) (h : ℕ) (output backing : List Bool) (b : Bool) (hr : readTapeBit source h = b) :
    step machine (config 1 source h output backing) = some (config 0 source (h + 1) (output ++ [b]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem finish_step (source : List Bool) (h : ℕ) (output backing : List Bool) (hr : readTapeBit source h = false) :
    step machine (config 0 source h output backing) = some (config 2 source (h + 1) (output ++ [false]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem copy_prefix (pre w tail output backing : List Bool) :
    Prefix machine ((pre ++ frame w ++ tail).length + (output.length + 2 * w.length + 1) + backing.length)
      (2 * w.length + 1)
      (config 0 (pre ++ frame w ++ tail) pre.length output backing)
      (config 2 (pre ++ frame w ++ tail) (pre.length + 2 * w.length + 1) (output ++ frame w) backing) := by
  induction w generalizing pre output with
  | nil =>
    have hread := Streaming.read_append pre tail false
    have hp := finish_step (pre ++ frame [] ++ tail) pre.length output backing
      (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp; omega) rfl hp ?_
    simpa [frame] using Prefix.refl (p := machine)
      (config 2 (pre ++ frame [] ++ tail) (pre.length + 1) (output ++ [false]) backing) (by simp; omega)
  | cons a w ih =>
    let src := pre ++ frame (a :: w) ++ tail
    let space := src.length + (output.length + 2 * (a :: w).length + 1) + backing.length
    have ht : Prefix machine space (2 * w.length + 1)
        (config 0 src (pre.length + 2) (output ++ [true, a]) backing)
        (config 2 src (pre.length + 2 * (a :: w).length + 1) (output ++ frame (a :: w)) backing) := by
      have hi := ih (pre ++ [true, a]) (output ++ [true, a])
      convert hi using 1 <;> simp [src, space, frame, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    have hread : readTapeBit src pre.length = true := by
      simpa [src, frame, List.append_assoc] using Streaming.read_append pre (a :: frame w ++ tail) true
    have hbit : readTapeBit src (pre.length + 1) = a := by
      simpa [src, frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ tail) a
    have hp := Prefix.step (by simp [space]; omega :
        (config 1 src (pre.length + 1) (output ++ [true]) backing).tapeCells ≤ space)
      rfl (bit_step src (pre.length + 1) (output ++ [true]) backing a hbit)
      (by simpa [List.append_assoc, Nat.add_assoc] using ht)
    have hstart := Prefix.step (by simp [space]; omega :
        (config 0 src pre.length output backing).tapeCells ≤ space)
      rfl (marker_step src pre.length output backing hread) hp
    convert hstart using 1 <;> simp [src, frame, List.append_assoc, Nat.add_assoc, Nat.mul_add]

/-- **The full copy**: `frame w` from the source cursor onto the output cursor; both heads pass the terminator. -/
theorem run (pre w tail output backing : List Bool) :
    Step machine (2 * w.length + 1) ![pre.length, output.length] ![pre ++ frame w ++ tail, overlay output backing]
      ![pre.length + 2 * w.length + 1, (output ++ frame w).length] ![pre ++ frame w ++ tail, overlay (output ++ frame w) backing] := by
  obtain ⟨r, hr, hf, _, _⟩ := (copy_prefix pre w tail output backing).run rfl (by simp [frame_length]; omega)
  refine Step.of_run hr ?_ ?_
  · rw [hf]; rfl
  · rw [hf]; rfl

end CopyPast

/-! ## The record marker: write `true`, step both heads -/

namespace Mark

end Mark

/-! ## Docking helpers -/

theorem dockRun {t u s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (RecoveryRootRound.install slots A tout) := by
  have hf := h.focus slots hi H A
  have e1 : dockH slots H hin = H := by
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [dockH, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [dockH, hp]
      rw [← he]
      exact (hH j).symm
  rwa [e1, RecoveryRootRound.install_existing slots A tin hA] at hf

/-- The masked (head-rewinding) form of a step whose selected heads start at `0`: the log tape is the last. -/
theorem maskRun {t s n cap : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (sel : Fin t → Bool) (hstart : ∀ i, sel i = true → hin i = 0) (hcap : n ≤ cap) :
    Step (MaskedReset.machine p sel) (2 * n + 2) (Fin.addCases hin (fun _ : Fin 1 => 0))
      (Fin.addCases tin (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases (fun i => if sel i then 0 else hout i) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate cap false)) :=
  h.mask sel hstart hcap

/-! ## CopyO as a step -/

/-! ## The inner pass of the product: one monomial `a` against every monomial of `q` -/

namespace ProdInner




end ProdInner

/-! ## Record streams -/

namespace ProdInner

end ProdInner

/-! ## One step right -/

namespace Skip

def machine : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun _ => .right⟩ else none

theorem run (tape : List Bool) (h : ℕ) : Step machine 1 ![h] ![tape] ![h + 1] ![tape] := by
  have hs : step machine ⟨machine.start, ![h], ![tape]⟩ = some ⟨1, ![h + 1], ![tape]⟩ := by
    simp [step, machine]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨r, hr, hf, _⟩ := (RecoveryExecution.Timed.single (p := machine) rfl hs).run rfl
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

end Skip

/-! ## The product `p·q`, unreduced: for each monomial `a` of `p`, the records `a·b`, `b` in `q` -/

namespace ProdOuter




end ProdOuter


end NearCubicWires.WireExponent3_5.ListMachine.Rec
