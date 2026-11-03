import Proof.SourceAssembly.SourceRequestCurContract

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurWriter
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp
noncomputable section

inductive Wr where
  | c (d : Fin 128) (w : List Bool)
  | cp (a d : Fin 128) (n : Nat)

/-- A write's machine shape (the copy's value `n` is data, not part of the machine). -/
inductive WrS where
  | c (d : Fin 128) (w : List Bool)
  | cp (a d : Fin 128)

def Wr.shape : Wr → WrS
  | .c d w => .c d w
  | .cp a d _ => .cp a d

def WrS.mach : WrS → (Σ s, Machine 128 s)
  | .c d w => ⟨_, constM w d 5⟩
  | .cp a d => ⟨_, copyM a d 5⟩

def chainM : List WrS → (Σ s, Machine 128 s)
  | [] => ⟨_, CloseoutRowsOriginalSwitch.stop 128⟩
  | x :: xs => ⟨_, Composition.machine x.mach.2 (chainM xs).2⟩

end
end NearCubicWires.SourceRequest.CurWriter

