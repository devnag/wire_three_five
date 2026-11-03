import Proof.Wire_3_5.UnionMachine.NumsA9Base

/-! # SWg, part 1: the data stage's gate tables on NW's bank, the inactive slots fixed

The call words of kind `0` (`PrimT.S3.wordOf k 0 j`, the SYM slots `16 … 19`) are the gate tables
`Corner.gatesW (tabH G_j) G_j` of the bottom gates `G_j = gatesJ k j` (`[]` past the tuple, the word `[false]`). PA's data
stage leaves exactly these tables on its slot tapes `iSym j` for `j < a` and blank tapes past the tuple
(`data_step_blank`); a gate word starts with the marker `true`, so one test fixes the blank ones to `[false]`:

* **`dataDock_step2`** (`DataDock.dataDock_step` with the blank slots kept), `fix1`, **`fix1_spec`**, **`dockG`** (at a
  SYM request, from `PreDock`: the docked run, the tables `if j < a then gatesW … else []`, the request kept, the
  tapes' lengths).

Paper quantities of the main type: the SYM call's bottom gates' tables (P3:3049-3050; `symWords`, kind `0`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g)

section Dock
open NearCubicWires.WireExponent3_5.UnionMachine.DataDock NearCubicWires.WireExponent3_5.PrimAsm.Data
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **`dataDock`, with the blank slots**: `DataDock.dataDock_step` and the slot tapes past the tuple blank. -/
theorem dataDock_step2 {ns nr : ℕ} (cap : ℕ) (tmap : Fin DT → Fin (ns + 1)) (hinj : Function.Injective tmap)
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
      tout iIN = RepairOrdinary.frame (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (iSym i) =
        FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))) ∧
      (∀ i : Fin 4, a' ≤ i.val → tout (iSym i) = []) ∧
      (∀ j, (tout j).length ≤ dataB (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W
        Cs carriers) := by
  obtain ⟨tout0, m, hs, -, hi, hS, -, hSb, -⟩ := data_step_blank a' Cs carriers tl L W ha hk hL hLX h2 hcN hcA hcK
    hcx hcy hcu
  obtain ⟨w, hwd⟩ : ∃ v, v = reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl := ⟨_, rfl⟩
  rw [← hwd] at hs hi hin ⊢
  have e1 : (fun j => σ.sh (tmap j)) = fun _ => 0 := funext hh
  have e2 : (fun j => σ.st (tmap j)) = dataIn w n L W := funext hin
  have hs' : Step dataM (2 * coreCost a' Cs carriers L W + 2) (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j))
      (fun _ => 0) (Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false)) := by
    rw [e1, e2]; exact hs
  refine ⟨Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false), DockW.dockS cap tmap hinj σ hs', ?_,
    fun i h => ?_, fun i h => ?_, ?_⟩
  · unfold iIN iOf; beta_reduce; rw [Fin.addCases_left]; exact hi
  · unfold iSym iOf; beta_reduce; rw [Fin.addCases_left]; exact hS i h
  · unfold iSym iOf; beta_reduce; rw [Fin.addCases_left]; exact hSb i h
  · intro j
    have hl := Shell.Step.len hs j (2 * w.length + n + L + W + 1) (Nat.zero_le _)
      (by have := dataIn_len w n L W j; unfold dataIn at this; exact this)
    unfold dataB
    beta_reduce
    omega

end Dock

section Fix
variable {ns nr : ℕ} (cap : ℕ)

/-- A blank slot tape to `[false]` (a gate word starts with the marker `true`). -/
def fix1 (O : Fin (ns + 1)) : WM ns nr := .ifs O .skip (.wr O false)

theorem fix1_spec (O : Fin (ns + 1)) (σ : WState ns nr) (hh : σ.sh O = 0) (h : ℕ) {n : ℕ}
    (G : List (NormalizedThresholdGate n))
    (hO : σ.st O = FinalPass.Corner.gatesW h G ∨ (σ.st O = [] ∧ G = [])) :
    WExec cap (fix1 O) σ (σ.sets O (FinalPass.Corner.gatesW h G)) 2 := by
  cases G with
  | nil =>
    have hw : FinalPass.Corner.gatesW h ([] : List (NormalizedThresholdGate n)) = [false] := rfl
    have hb : wbit σ O = false := by
      unfold wbit; rw [hh]
      rcases hO with h1 | ⟨h1, -⟩ <;> rw [h1] <;> [rw [hw]; skip] <;> rfl
    have e := WExec.wr (cap := cap) O false σ
    have hst : writeTapeBit (σ.st O) (σ.sh O) false = [false] := by
      rw [hh]; rcases hO with h1 | ⟨h1, -⟩ <;> rw [h1] <;> [rw [hw]; skip] <;> rfl
    rw [hst] at e
    rw [hw]
    exact WExec.ifsF hb e
  | cons g G =>
    have h1 : σ.st O = FinalPass.Corner.gatesW h (g :: G) := by
      rcases hO with h1 | ⟨-, h2⟩
      · exact h1
      · exact absurd h2 (List.cons_ne_nil g G)
    have hb : wbit σ O = true := by
      unfold wbit; rw [hh, h1]; rfl
    rw [← h1, wsets_same]
    exact WExec.mono (WExec.ifsT hb (WExec.skip σ)) (by omega)

end Fix

section Gate

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
