import Proof.Packets.SrcMetaRegs
import Proof.Packets.SrcMetaWords
import Proof.CaseAnalysis.RowsEstimatorParityNatural
import Proof.Hierarchy.HierarchyFixedWord

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.MetaAsm
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation NearCubicWires.SourceStart.MetaTM NearCubicWires.SourceStart.Regs
noncomputable section

/-! ## 1. A stage with its scratch block anywhere -/

/-! ## 2. The piece machines as heads-`0` local runs -/

/-! ## 3. Body appends from a list of framed sources -/

/-- One append: `bodyM false` docked on `(src, out)`. -/
def appendM {N : ℕ} (src out : Fin N) : Machine N 3 := RecoveryFocus.machine ![src, out] (bodyM false)

/-- The appends of a list of sources, in order (then a halting machine). -/
def asmM {N : ℕ} (out : Fin N) : List (Fin N) → (st : ℕ) × Machine N st
  | [] => ⟨1, CloseoutRowsOriginalSwitch.stop N⟩
  | j :: js => ⟨3 + (asmM out js).1, Composition.machine (appendM j out) (asmM out js).2⟩

/-- Its cost. -/
def asmCost {N : ℕ} (w : Fin N → List Bool) : List (Fin N) → ℕ
  | [] => 0
  | j :: js => (2*(w j).length+1) + 1 + asmCost w js

/-! ## 4. The two phases -/

/-- The Field copier appending `frame [] = [false]` from `term` onto `out`. -/
def termM {N : ℕ} (term out : Fin N) : Machine N 3 :=
  RecoveryFocus.machine ![term, out] RepairSource.ProjectionNormalization.Field.machine

/-- Phase A's inner machine on `Fin (m + 2)`: sources `0..m-1`, output `m`, terminator `m+1`. -/
def innerA (m : ℕ) : (st : ℕ) × Machine (m + 2) st :=
  ⟨_, Composition.machine (asmM (⟨m, by omega⟩ : Fin (m+2)) ((List.finRange m).map (Fin.castAdd 2))).2
    (termM (⟨m+1, by omega⟩ : Fin (m+2)) ⟨m, by omega⟩)⟩

/-- Phase A's cost. -/
def costA (m : ℕ) (w : Fin m → List Bool) : ℕ :=
  2*(asmCost (fun i : Fin (m+2) => if h : i.val < m then w ⟨i.val, h⟩ else []) ((List.finRange m).map (Fin.castAdd 2)) + 1 +
    (2*0+1)) + 2

/-- Phase B's inner machine on `Fin 3`: `0` the source `frame v`, `1` the terminator, `2` the output. -/
def innerB : (st : ℕ) × Machine 3 st :=
  ⟨_, Composition.machine (RecoveryFocus.machine (![0, 2] : Fin 2 → Fin 3) (bodyM true)) (termM (1 : Fin 3) 2)⟩

end
end NearCubicWires.SourceStart.MetaAsm

