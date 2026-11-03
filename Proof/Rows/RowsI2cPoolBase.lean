import Proof.SourceAssembly.PoolDonorCompatible
import Proof.MachineModel.UWalkUnary
import Proof.MachineModel.ClockJoin
import Proof.MachineModel.ClockNormalize
import Proof.PCP.ProjectionDimensionPower
import Proof.PCP.ProjectionDimensionTemplate
import Proof.PCP.ProjectionDimensionPolynomial
import Proof.MachineModel.OrdinarySelectiveReset
import Proof.MachineModel.ClockUnaryProduct
import Proof.PCP.PCPSerializerCapacityPower
import Proof.MachineModel.ClockUnarySum
import Proof.MachineModel.ClockScalarFields
import Proof.Supplier.EquationNaturalHeader
import Proof.Supplier.RowCachedEquationMeaning
import Proof.Hierarchy.HierarchyFixedWord

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section
/- Helpers copied from source-reuse-20260922: PCJ6e421fabe2aa4155_SourceLog (clock_step, dock_zero, install_blank),
PCJ6e421fabe2aa4155_SourceLiveCount (product_step, unary_pad), PCJ6e421fabe2aa4155_SourceCacheBudget (occurrence_eq, loop_eq),
PCJ6e421fabe2aa4155_SourcePoolAdmissions (magnitude). Proofs unchanged. -/
namespace RowsConstruction.I2c.Log
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
noncomputable section

theorem clock_step {t s F : Nat} {p : Machine t s} {I O : Fin t→List Bool}
    (h : ClockJoin.ReadyRun p F I O) : Step p F (fun _=>0) I (fun _=>0) O := by
  obtain ⟨r,hr,rt,rh,rs⟩:=h
  exact ⟨r,hr,funext rh,rt,rs⟩

theorem dock_zero {t u s F : Nat} {p : Machine t s} {I O : Fin t→List Bool}
    (h : Step p F (fun _=>0) I (fun _=>0) O) (slots : Fin t→Fin u)
    (hi : Function.Injective slots) (A : Fin u→List Bool) (ha : ∀i,A (slots i)=I i) :
    Step (RecoveryFocus.machine slots p) F (fun _=>0) A (fun _=>0) (install slots A O) := by
  have hz : dockH slots (fun _=>0) (fun _=>0)=(fun _ : Fin u=>0) := by
    funext i;cases hp:RecoveryFocus.pick slots i <;>simp [dockH,hp]
  exact (h.dock slots hi (fun _=>0) A (fun _=>rfl) ha).congr hz rfl

theorem install_blank {t u cut old : Nat} (slots : Fin t→Fin u) (A : Fin u→List Bool)
    (O : Fin t→List Bool) (ho:old≤cut) (hs:∀j,(slots j).val<cut)
    (ha:∀i,old≤ i.val→A i=[]) : ∀i,cut≤ i.val→install slots A O i=[] := by
  intro i hi
  rw [install_other slots A O i (by intro j he;have hj:=hs j;rw [he] at hj;omega)]
  exact ha i (ho.trans hi)

end
end RowsConstruction.I2c.Log

namespace RowsConstruction.I2c.LiveCount
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
noncomputable section

end
end RowsConstruction.I2c.LiveCount

namespace RowsConstruction.I2c.CacheBudget
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation P1Closure

end RowsConstruction.I2c.CacheBudget

namespace RowsConstruction.I2c.PoolAdmissions
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound SupplierPipeline SupplierEstimator CompilerSemantics RepairSource.VerifierDecoding
noncomputable section

end
end RowsConstruction.I2c.PoolAdmissions
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolDrivers.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolDrivers
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open RowsConstruction.I2c.Log (clock_step dock_zero install_blank)
noncomputable section



end
end RowsConstruction.I2c.PoolDrivers
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolScalars.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolScalars
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.ProjectionNormalization
open RowsConstruction.I2c.Log (clock_step dock_zero install_blank)
noncomputable section



end
end RowsConstruction.I2c.PoolScalars
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolCapacity.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolCapacity
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
noncomputable section

end
end RowsConstruction.I2c.PoolCapacity
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolPreparation.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolPreparation
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open RowsConstruction.I2c.Log (clock_step dock_zero install_blank)
noncomputable section

-- The input dimension is20; the unused slot42 remains blank.


end
end RowsConstruction.I2c.PoolPreparation
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolHeader.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolHeader
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open RowsConstruction.I2c.Log (clock_step dock_zero install_blank)
noncomputable section


end
end RowsConstruction.I2c.PoolHeader
end

