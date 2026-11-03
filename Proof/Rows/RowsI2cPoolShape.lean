import Proof.Rows.RowsI2cPoolBase

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolSeedShape.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolSeedShape
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
noncomputable section

end
end RowsConstruction.I2c.PoolSeedShape
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolSeedFanout.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolSeedFanout
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
noncomputable section


theorem pad_pad (C D : Nat) (bits : List Bool) (h:C≤D) :
    ZeroPadding.pad D (ZeroPadding.pad C bits)=ZeroPadding.pad D bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc]
  rw [←List.replicate_add]
  congr 2
  omega

end
end RowsConstruction.I2c.PoolSeedFanout
end

