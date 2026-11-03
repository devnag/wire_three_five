import Proof.Wire_3_5.Foundations.OutMachineDataDockW2
import Proof.Wire_3_5.UnionMachine.NumsA9Base

/-! # The SYM front, part 5: the data stage with the empty slots' gate tables exported

The SYM numbers writer (the gate tables' width `tabH` per circuit) reads every slot's gate-table tape: filled ones
hold `gatesW (tabH G_i) G_i` (part 1) and the empty ones must be blank. X6's `dataDock_stepW'` drops that conjunct of
its raw data stage (`data_step_blankW2`); **`dataDock_stepW3`** keeps it on the dock (X6's docking, one more
conjunct), and **`dataPostW2`** is part 1's `dataPostW` over it, exporting `∀ i, a' ≤ i → (gate tape i) = []`.

Paper quantity of the main type: the SYM call's slices (the circuits' gate tables, blank past the tuple,
P3:3049-3050) on the bank's data tapes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g)
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.NumsA

open NearCubicWires.WireExponent3_5.FinalPass.Out.DataW (data_step_blankW2 scanWord)
open NearCubicWires.WireExponent3_5.PrimT.SymTab (scanSl)
open NearCubicWires.WireExponent3_5.UnionMachine.DataDock
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.PrimAsm.Data

section DockW3
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **`dataDock` with every slot tape exported**: X6's `dataDock_stepW'` plus the unfilled SYM slots' gate-table tapes
blank (`data_step_blankW2`'s conjunct kept on the dock). -/
theorem dataDock_stepW3 {ns nr : ℕ} (cap : ℕ) (tmap : Fin DT → Fin (ns + 1)) (hinj : Function.Injective tmap)
    (σ : WState ns nr) (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2)
    (hcu : 2 * (unaryList (carriers.map (·.length))).length +
      2 * (unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2)
    (hin : ∀ j, σ.st (tmap j) = dataIn (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W j)
    (hh : ∀ j, σ.sh (tmap j) = 0) :
    ∃ tout : Fin DT → List Bool,
      Step (dataDockM (nr := nr) tmap) (2 * coreCost a' Cs carriers L W + 2) (wenc cap σ).H (wenc cap σ).A
        (wenc cap (DockW.updS tmap σ (fun _ => 0) tout)).H (wenc cap (DockW.updS tmap σ (fun _ => 0) tout)).A ∧
      tout iOUT = dataWord (symCounts a' Cs carriers) ∧
      tout iIN = RepairOrdinary.frame (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (iSym i) =
        FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (iCar k) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      (∀ j, (tout j).length ≤ dataB (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W
        Cs carriers) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (iOf (sSym i (scanSl 0))) = scanWord (Cs ⟨i.val, h⟩)) ∧
      (∀ i : Fin 4, a' ≤ i.val → tout (iOf (sSym i (scanSl 0))) = []) ∧
      (∀ i : Fin 4, a' ≤ i.val → tout (iSym i) = []) := by
  obtain ⟨tout0, m, hs, ho, hi, hS, hC, hS0, -, hW, hE⟩ := Out.DataW.data_step_blankW2 a' Cs carriers tl L W ha hk hL hLX h2 hcN
    hcA hcK hcx hcy hcu
  obtain ⟨w, hwd⟩ : ∃ v, v = reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl := ⟨_, rfl⟩
  rw [← hwd] at hs hi hin ⊢
  have e1 : (fun j => σ.sh (tmap j)) = fun _ => 0 := funext hh
  have e2 : (fun j => σ.st (tmap j)) = dataIn w n L W := funext hin
  have hs' : Step dataM (2 * coreCost a' Cs carriers L W + 2) (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j))
      (fun _ => 0) (Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false)) := by
    rw [e1, e2]; exact hs
  refine ⟨Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false), DockW.dockS cap tmap hinj σ hs', ?_, ?_,
    fun i h => ?_, fun k h => ?_, ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_⟩
  · unfold iOUT iOf; beta_reduce; rw [Fin.addCases_left]; exact ho
  · unfold iIN iOf; beta_reduce; rw [Fin.addCases_left]; exact hi
  · unfold iSym iOf; beta_reduce; rw [Fin.addCases_left]; exact hS i h
  · unfold iCar iOf; beta_reduce; rw [Fin.addCases_left]; exact hC k h
  · intro j
    have hl := Shell.Step.len hs j (2 * w.length + n + L + W + 1) (Nat.zero_le _)
      (by have := dataIn_len w n L W j; unfold dataIn at this; exact this)
    unfold dataB
    beta_reduce
    omega
  · unfold iOf; beta_reduce; rw [Fin.addCases_left]; exact hW i h
  · unfold iOf; beta_reduce; rw [Fin.addCases_left]; exact hE i h
  · unfold iSym iOf; beta_reduce; rw [Fin.addCases_left]; exact hS0 i h

end DockW3

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFront
