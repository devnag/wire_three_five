import Proof.Wire_3_5.Primitive.Writers.DataBlank
import Proof.Wire_3_5.Primitive.Writers.ShellLayout

/-! # `dataDock` (build once): PA's per-call data stage docked on any word bank's streams

PA's per-call data stage `Data.dataM` (PA.tables; `data_step_blank`) runs on its own raw tapes: from
`frame w` (`w = reqW n false codes carrierCodes tl`, the request's word shape with any tail `tl`, e.g. the final pass's
input `fpIn = word ++ seedWord`), `1^n`, `1^L`, `1^W`, all else blank, it leaves the gate tables
`gatesW (tabH (symGates C_i)) (symGates C_i)` (and the carriers' mask tables) and `dataWord (symCounts …)` (the
carriers' sizes, then the circuits' bottom counts), every head back at `0`. Here it is docked, once, on the streams
`tmap` of ANY word bank `WState ns nr` (PA's `DockW.dockS`: the registers, the cell and the other streams kept):

* `DT`, `dataIn`, `iOf`, `iIN`, `iOUT`, `iSym`, `iCar`, `dataDockM`, `dataB`, **`dataDock_step`**; `nwTmap`,
  `nwTmap_inj` (NW's bank) (the docked run, its
  outputs, and every docked tape's length `≤ 2|w| + n + L + W + 2·coreCost + 4`, PA's `Shell.Step.len`).

Consumers: the NW phase (a) (the bottom counts → the SYM numbers `|E|`, `|FlatSeed|`, `Q`) and the SYM words
writer (the word-0 tables). Paper quantities of the main type: the call's gate tables and bottom counts (P3:3049-3050,
the SYM call's slices). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.DataDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.SupplierPipeline

/-- The data stage's tapes. -/
abbrev DT : ℕ := DS + 2 + DR + 1

/-- The data stage's raw inputs. -/
def dataIn (w : List Bool) (n L W : ℕ) : Fin DT → List Bool :=
  Fin.addCases (rawIn w n L W) (fun _ : Fin 1 => List.replicate 0 false)

/-- The tape of a data stream. -/
def iOf (s : Fin (DS + 1)) : Fin DT := Fin.castAdd 1 (sTape (nr := DR) s)

/-- The request's tape. -/
def iIN : Fin DT := iOf sIN
/-- The output tape (`dataWord`). -/
def iOUT : Fin DT := iOf sOUT
/-- A SYM slot's table tape. -/
def iSym (i : Fin 4) : Fin DT := iOf (sSym i 3)
/-- A carrier slot's table tape. -/
def iCar (k : Fin 2) : Fin DT := iOf (sCar k 3)

/-- **The data stage docked on the streams `tmap`** of a word bank. -/
noncomputable def dataDockM {ns nr : ℕ} (tmap : Fin DT → Fin (ns + 1)) :=
  RecoveryFocus.machine (fun j => sTape (nr := nr) (tmap j)) dataM

/-- The docked tapes' length bound (inputs and steps). -/
noncomputable def dataB (w : List Bool) (n L W : ℕ) {m a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit m)
    (carriers : List (Stars.Carrier m)) : ℕ :=
  2 * w.length + n + L + W + 1 + (2 * coreCost a' Cs carriers L W + 2) + 1

theorem dataIn_len (w : List Bool) (n L W : ℕ) (j : Fin DT) :
    (dataIn w n L W j).length ≤ 2 * w.length + n + L + W + 1 := by
  unfold dataIn
  refine Fin.addCases (fun i => ?_) (fun o => ?_) j
  · rw [Fin.addCases_left]
    unfold rawIn
    split_ifs <;> simp [RepairOrdinary.frame_length] <;> omega
  · rw [Fin.addCases_right]; simp

section Run
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **`dataDock`**: the data stage's run on the streams `tmap` of any word bank, at any capacity. -/
theorem dataDock_step {ns nr : ℕ} (cap : ℕ) (tmap : Fin DT → Fin (ns + 1)) (hinj : Function.Injective tmap)
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
        Cs carriers) := by
  obtain ⟨tout0, m, hs, ho, hi, hS, hC, -, -⟩ := data_step_blank a' Cs carriers tl L W ha hk hL hLX h2 hcN hcA hcK
    hcx hcy hcu
  obtain ⟨w, hwd⟩ : ∃ v, v = reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl := ⟨_, rfl⟩
  rw [← hwd] at hs hi hin ⊢
  have e1 : (fun j => σ.sh (tmap j)) = fun _ => 0 := funext hh
  have e2 : (fun j => σ.st (tmap j)) = dataIn w n L W := funext hin
  have hs' : Step dataM (2 * coreCost a' Cs carriers L W + 2) (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j))
      (fun _ => 0) (Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false)) := by
    rw [e1, e2]; exact hs
  refine ⟨Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false), DockW.dockS cap tmap hinj σ hs', ?_, ?_,
    fun i h => ?_, fun k h => ?_, ?_⟩
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

end Run

/-! ## NW's bank (a twin of the docking, the phase (a)) -/

/-- The data stage's tapes on NW's bank (`WState (LNS x) LNR`, `DT ≤ x`): the request on NW's input stream, every other
tape on the extra stream `161 + j`. -/
def nwTmap (x : ℕ) (hx : DT ≤ x) (sIn : Fin (SymLayout.LNS x + 1)) :
    Fin DT → Fin (SymLayout.LNS x + 1) := fun j =>
  if j = iIN then sIn else ⟨161 + j.val, by have := j.isLt; unfold SymLayout.LNS; omega⟩

theorem nwTmap_inj (x : ℕ) (hx : DT ≤ x) (sIn : Fin (SymLayout.LNS x + 1)) (hs : sIn.val < 161) :
    Function.Injective (nwTmap x hx sIn) := by
  intro i j h
  unfold nwTmap at h
  by_cases hi : i = iIN <;> by_cases hj : j = iIN
  · rw [hi, hj]
  · rw [if_pos hi, if_neg hj] at h
    have := congrArg Fin.val h; simp at this; omega
  · rw [if_neg hi, if_pos hj] at h
    have := congrArg Fin.val h; simp at this; omega
  · rw [if_neg hi, if_neg hj] at h
    exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

end NearCubicWires.WireExponent3_5.UnionMachine.DataDock
