import Proof.Rows.RowsI2cPoolShape
import Proof.MachineModel.NativeFanout
import Proof.Circuits.DecompositionCountPosition
import Proof.PCP.PCPPQueryField

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolBank.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolBank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open RowsConstruction.I2c.PoolSeedFanout (pad_pad)
noncomputable section



attribute [local irreducible] PoolEntry.input

end
end RowsConstruction.I2c.PoolBank
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolAllocate.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolAllocate
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open RowsConstruction.I2c.PoolBank
noncomputable section


end
end RowsConstruction.I2c.PoolAllocate
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolBoot.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolBoot
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
noncomputable section


end
end RowsConstruction.I2c.PoolBoot
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolInitialize.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolInitialize
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open RowsConstruction.I2c.PoolBank
noncomputable section


end
end RowsConstruction.I2c.PoolInitialize
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolMasters.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolMasters
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open RowsConstruction.I2c.Log (dock_zero)
noncomputable section


end
end RowsConstruction.I2c.PoolMasters
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolProduced.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolProduced
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
noncomputable section


end
end RowsConstruction.I2c.PoolProduced
end

