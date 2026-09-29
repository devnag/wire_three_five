import Proof.Rows.CellGatePalette
import Proof.Rows.HeaderRewind
import Proof.Rows.ResidueProductBounds
import Proof.Rows.TopChildCursor

/-! A reusable physical modular-product emitter. Resident short masters are
copied into the product worker, the computed residue is appended in framed
stream order, and all worker tapes are rewound and erased. The append prefix
is never rescanned and never enters the scratch reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueScaleCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence SignedSortKey
noncomputable section

def palette (a b p w : Nat):=PCJ45bee56da9f34d5a_ResidueProductReady.input (2*w+1) a p w (2*w+2)
  (PCJ45bee56da9f34d5a_ResidueProductBounds.resetCap w) (binary w b)
def cold (P : Fin 31→List Bool) (U : Nat) (out : List Bool) : Fin 65→List Bool:=
  Fin.addCases (m:=64) (n:=1) (motive:=fun _=>List Bool) (NativeFanout.reusableInput (m:=31) P U) (fun _=>out)

end
end PCJ45bee56da9f34d5a_ResidueScaleCell
