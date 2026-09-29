import Proof.Rows.ClosureOffsetSourceGateReusable
import Proof.Rows.Plan

/-! Eight retained words physically produce the whole reusable gate bank.
The computed source and assignment occur only in this small palette; none of
the evaluator's copied masters or padded scratch tapes is supplied for free. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ45bee56da9f34d5a_CellGatePalette
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open NearCubicWires.RepairRepresentation
noncomputable section

def entryChoice : Nat→Option (Fin 8)
  | 0=>some 0 | 9=>some 2 | 13=>some 3 | 14=>some 3
  | 39=>some 1 | 40=>some 4 | 42=>some 5 | 46=>some 6 | _=>none
def gateChoice (i : Fin 98) : Option (Fin 8) :=
  if h : i.val<48 then entryChoice i.val
  else if h' : i.val<95 then entryChoice (HardwireReusable.work ⟨i.val-48,by omega⟩).val
  else if i=96 then some 7 else none
def target (i : Fin 97) : Fin 98 := if h:i.val<34 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
def choice (i : Fin 97) := gateChoice (target i)
def words (source assignment : List Bool) (q w C R : Nat) : Fin 8→List Bool :=
  ![source,assignment,List.replicate w true,frame (SignedSortKey.binary w 0),
    List.replicate C true,CompareMachine.word q,CompareMachine.word 0,List.replicate R true]
def gates (i : Fin 98) : Fin 108 :=
  if h:i=34 then 107 else if h':i.val<34 then ⟨8+i.val,by omega⟩ else ⟨7+i.val,by omega⟩

def heads (out : List Bool) (pos : Nat) : Fin 108→Nat :=
  fun i=>if i=107 then out.length else if i=49 ∨ i=53 then pos else 0
def cold (palette : Fin 8→List Bool) (U : Nat) (out : List Bool) : Fin 108→List Bool :=
  Fin.addCases (motive:=fun _=>List Bool) (NativeFanout.reusableInput (m:=97) palette U) (fun _ : Fin 1=>out)
def fanout := TapeEmbedding.machine 1 (NativeFanout.machine choice)


end
end PCJ45bee56da9f34d5a_CellGatePalette
