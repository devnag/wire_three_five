import Proof.SourceAssembly.SourcePoolMasters
import Proof.SourceAssembly.SourcePoolInitialize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolProduced
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
noncomputable section

def slots (i : Fin 145) : Fin 229:=if h:i.val<9 then
  (PCJ6e421fabe2aa4155_SourcePoolMasters.fields ⟨i.val,h⟩).castAdd 145
  else if i=141 then 51 else i.natAdd 84
theorem slots_inj : Function.Injective slots:=by decide
def first:=TapeEmbedding.machine 145 PCJ6e421fabe2aa4155_SourcePoolMasters.machine
def last:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourcePoolInitialize.machine
def machine:=Composition.machine first last
def input {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 229→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (PCJ6e421fabe2aa4155_SourcePoolMasters.input live B N source) (fun _ : Fin 145=>[])
def budget (B q N : Nat):=PCJ6e421fabe2aa4155_SourcePoolMasters.budget B q N+1+
  PCJ6e421fabe2aa4155_SourcePoolInitialize.budget B q N

theorem input_shape (D : Fin 9→List Bool) (P : Nat) (i : Fin 145) :
    Fin.addCases (motive:=fun _=>List Bool) (NativeFanout.input (m:=132) D P) (fun _ : Fin 2=>[]) i=
    if h:i.val<9 then D ⟨i.val,h⟩ else if i=141 then List.replicate P true else [] := by
  fin_cases i <;>rfl

end
end PCJ6e421fabe2aa4155_SourcePoolProduced
