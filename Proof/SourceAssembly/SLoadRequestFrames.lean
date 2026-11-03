import Proof.SourceAssembly.SLoadMaskFrame

/-! Deliverable 2, first piece: the suffix's framing pass on an actual request.

`Ready`'s second conjunct quantifies over an ARBITRARY compatible final bank
`B` of the supplied mask producer and promises only `B 4`. This module frames
that promised word and concatenates it with the four retained request fields,
proving that the resulting scratch word is literally `Request.input a r`, the
argument of the packet program's own input representation. No private tape of
the mask worker is read. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.RequestFrames
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The fixed framing program: one raw framer and five frame appenders. -/
noncomputable def machine {U : Nat} (mskOut drv frm sN sS sI sT out log : Fin U) : Machine U 25 :=
  Composition.machine (MaskFrame.machine mskOut drv frm log)
    (Frames.machine sN sS frm sI sT out log)

/-- Fuel for the framing pass, in the physical word lengths. -/
def cost (q n s i t : Nat) : Nat := 4 * q + 4 + 1 + Frames.cost n s q i t


end
end SLoad.RequestFrames
