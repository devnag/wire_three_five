import Proof.MachineModel.ClosureRadixFamily
import Proof.MachineModel.NativeWidth
import Proof.MachineModel.NativeAllocation
import Proof.MachineModel.NativeMeasured
import Proof.MachineModel.NativeMaster
import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.CaseAnalysis.RowsSourceMeaning
import Proof.MachineModel.BankFields
import Proof.MachineModel.BankMetadata
import Proof.MachineModel.BankCountLayout
import Proof.Hierarchy.HierarchyAllocation
import Proof.MachineModel.BankConsumer
import Proof.MachineModel.BankOptional
import Proof.MachineModel.BankCountNative
import Proof.MachineModel.BankCountConsumer
import Proof.MachineModel.BankCountRaw
import Proof.MachineModel.BankCountPositive
import Proof.MachineModel.BankCountZero
import Proof.MachineModel.BankCountBranch
import Proof.MachineModel.BankCountOptional
import Proof.MachineModel.NativeFanout
import Proof.CaseAnalysis.RowsBankFields
import Proof.MachineModel.NativeFanoutLayout
import Proof.MachineModel.NativeTemplateExact
import Proof.MachineModel.NativeBankInputs
import Proof.MachineModel.NativeBankPosition
import Proof.CaseAnalysis.RowsEstimatorBankCycle
import Proof.MachineModel.NativeRound
import Proof.MachineModel.NativeState
import Proof.MachineModel.NativeFamily

/-! The complete measured-cache run produces the final p=base+Q word and
signed-field driver, retaining every shared cache/dimension field. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeWidth
open NearCubicWires.ExtIncidence.NativeWidth
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q : ℕ):=P1CompactRowTupleFixedCapacity.width gs Q+Q

end NearCubicWires.ExtIncidence.P1CompactNativeWidth

/-! The same measured native cache supplies p and the exact coefficient
allocation F. No width or capacity word is an input to this whole run. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeAllocation
open NearCubicWires.ExtIncidence.NativeAllocation
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q : ℕ):=
  P1CompactRowCommonBounds.capacity gs (gs.length*Q) (P1CompactNativeWidth.width gs Q)

end NearCubicWires.ExtIncidence.P1CompactNativeAllocation

/-! One measured cache supplies the actual p, F, and full preparation C.
Only the mode's short w and Q are additional inputs to this whole run. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeMeasured
open NearCubicWires.ExtIncidence.NativeMeasured
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ):=
  P1CompactCloseoutRowsPreparationBounds.capacity n (P1CompactNativeWidth.width gs Q) (P1CompactNativeAllocation.capacity gs Q) w gs.length Q

end NearCubicWires.ExtIncidence.P1CompactNativeMeasured

/-! All fifteen distinct source words for native initialization are outputs
of one fixed ordinary run over the same measured cache. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeMaster
open NearCubicWires.ExtIncidence.NativeMaster
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def words {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) : Fin 15→List Bool:=
  ![exactListWord gs,List.replicate (P1Radix.bits gs) true,
    List.replicate (RowCachedCoordinateBounds.inner (P1Radix.bits gs)) true,
    UnaryTemplate.tape n,
    List.replicate (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)) true,
    CompareMachine.word (P1CompactNativeWidth.width gs Q+1),List.replicate (P1CompactNativeAllocation.capacity gs Q) true,
    CompareMachine.word (n+1),UnaryTemplate.tape gs.length,frame (SignedSortKey.binary w 0),
    CompareMachine.word w,CompareMachine.word 1,List.replicate w true,
    List.replicate (P1CompactNativeWidth.width gs Q) true,CompareMachine.word Q]

end NearCubicWires.ExtIncidence.P1CompactNativeMaster

/-! The complete executed outer loop uses the same strict paper load as
the signed cuts. This bounds the actual driver and loop, not an assumed
original-source packet generator or the narrower internal-syntax Tprep. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsFamilyBudget
open NearCubicWires.RepairOrdinary.CloseoutRowsFamilyBudget
open CloseoutRowsSourceDigits P1CompactCloseoutRowsSourceLoad P1CompactCloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsFamilyBudget

/-! The actual canonical support becomes the existing native incidence ABI.
Only repeated variables inside one conjunction are collapsed; distinct
monomial occurrences, including equal resulting masks, remain separate. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSourceMeaning
open NearCubicWires.RepairOrdinary.CloseoutRowsSourceMeaning
open SupplierPrinter CloseoutRowsSourceDigits P1CompactCloseoutRowsCacheInput RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSourceMeaning

/-! Exact existing native-bank projections consumed by the physical incidence
dock. These are field identities, not producers for the remaining metadata. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankFields
open NearCubicWires.ExtIncidence.BankFields
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactBankFields

/-! The actual incidence table and two copies of its last row index are the
only row-dependent native inputs. Common false backing erases the dependence
of the two scratch extents on the number of monomial occurrences. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankMetadata
open NearCubicWires.ExtIncidence.BankMetadata
open LocalBitMultitape RepairOrdinary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactBankMetadata

/-! Dock the actual count converter into the existing native bank. Shared
ports are count115, width109, fields52/107 and driver104/log105. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 18→Fin 128:=
  ![115,116,117,118,119,120,121,122,123,124,109,52,125,126,127,107,104,105]
noncomputable def machine:=RecoveryFocus.machine slots CountIndexClean.machine

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Exact field replacement by the count-conversion run: private scratch is
restored, and only count115 and the two native index words change. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Physical raw incidence production, paid cursor return, and the EXISTING
polynomial consumer. All other native fields are explicit caller-produced
inputs. The separate zero-polynomial branch is not supplied here. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankConsumer
open NearCubicWires.ExtIncidence.BankConsumer
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true



end NearCubicWires.ExtIncidence.P1CompactBankConsumer

/-! One actual raw stream runs through the positive or empty bank entry.
The caller supplies the existing native ports; no separate marker, count pass
or serialized polynomial packet is required. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankOptional
open NearCubicWires.ExtIncidence.BankOptional
open LocalBitMultitape RepairOrdinary P1CompactBankConsumer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

end
end NearCubicWires.ExtIncidence.P1CompactBankOptional

/-! Discharge the native worker's row-dependent input from the actual table
and counted index. Every other native input is the same empty-row template. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 113) : Fin 128:=i.castAdd 15

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Execute count metadata and the original polynomial worker on the same
actual incidence table. No last-index word is supplied to this consumer. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def consumer:=RecoveryFocus.machine old P1CompactCloseoutRowsBankPolynomial.machine
noncomputable def counted:=Composition.machine machine consumer
def budget (C Q w M : ℕ):=CountIndexClean.budget C w M+1+P1CompactCloseoutRowsBankPolynomial.budget Q C

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The original incidence printer runs in the count-metadata bank. Its
actual count and table are retained; the twelve new private tapes are idle. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawOld (i : Fin 116) : Fin 128:=i.castAdd 12
noncomputable def raw:=RecoveryFocus.machine rawOld BankExecution.machine


end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Exact ambient state after the original raw incidence pass. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The raw pass physically supplies the converter count and preserves the
empty native template, the same width and every private scratch field. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! One positive raw polynomial now produces its actual incidence table,
count and both binary index fields before calling the original worker. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def positive:=Composition.machine raw counted
def positiveBudget (B C Q w : ℕ) (ms : List (List ℕ)):=
  BankExecution.budget B C ms+1+budget C Q w ms.length

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The existing zero-polynomial worker uses the same enlarged bank and
leaves every private converter tape untouched. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def zero:=RecoveryFocus.machine rawOld BankZero.machine

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Dispatch on the original raw stream marker in the same count bank. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def idle : Machine 128 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def dispatch {s t : ℕ} (yes : Machine 128 s) (no : Machine 128 t):=
  CloseoutWitness.HeaderSwitch.machine idle yes no (fun _=>true) (fun cells=>cells 113)
def optional:=dispatch positive zero

end
end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Every original raw polynomial, including the empty polynomial, executes
without a supplied row count or either last-index field. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def optionalBudget (B C Q w : ℕ) (ms : List (List ℕ)):=
  max (positiveBudget B C Q w ms) (BankZero.budget B C)+2

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The fifteen measured source words are exactly the static native inputs.
Only the table and counted last-index fields remain for incidence to fill. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeTemplate
open NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.ExtIncidence.P1CompactNativeTemplate

/-! Native input correspondence is proved through small tape projections;
no concrete ordinary controller is expanded by the field simplifier. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeTemplate
open NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.ExtIncidence.P1CompactNativeTemplate

/-! Remaining coefficient/template ports complete the exact static payload. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeTemplate
open NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.ExtIncidence.P1CompactNativeTemplate

/-! Every distributed metadata word fits the actual measured native C.
The coefficient width, mode width and original arity remain distinct. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeMaster
open NearCubicWires.ExtIncidence.NativeMaster
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactNativeMaster

/-! Observed bits and the proved common extent identify the exact native
input lists, so false backing never becomes a prepared-word assumption. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeTemplate
open NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactNativeTemplate

/-! The physically initialized bank supplies all native, count-conversion
and raw-incidence inputs, without an input row count or last-index word. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeBankInputs
open NearCubicWires.ExtIncidence.NativeBankInputs
open LocalBitMultitape RepairOrdinary NativeInitializedPorts NativeFanoutLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactNativeBankInputs

/-! The existing zero-polynomial worker uses the same enlarged bank and
leaves every private converter tape untouched. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! One positive raw polynomial now produces its actual incidence table,
count and both binary index fields before calling the original worker. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! Every original raw polynomial, including the empty polynomial, executes
without a supplied row count or either last-index field. -/
namespace NearCubicWires.ExtIncidence.P1CompactBankCount
open NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactBankCount

/-! The completed optional worker has the literal all-blank reload bank. -/
namespace NearCubicWires.ExtIncidence.P1CompactEstimatorBankCycle
open NearCubicWires.ExtIncidence.EstimatorBankCycle
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.P1CompactEstimatorBankCycle

/-! One actual reusable native call preserves every ambient port outside its bank. -/
namespace NearCubicWires.ExtIncidence.P1CompactEstimatorBankCycle
open NearCubicWires.ExtIncidence.EstimatorBankCycle
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last:=RecoveryFocus.machine bank P1CompactBankCount.optional
noncomputable def machine:=Composition.machine NativeBankPosition.machine last
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) (ms : List (List ℕ)):=
  1+1+P1CompactBankCount.optionalBudget gs.length (P1CompactNativeMeasured.capacity gs Q w) Q w ms

end NearCubicWires.ExtIncidence.P1CompactEstimatorBankCycle

/-! The actual polynomial worker and one retained-metadata reload return
the reusable entry bank, ready for the next original raw polynomial. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeRound
open NearCubicWires.ExtIncidence.NativeRound
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine P1CompactEstimatorBankCycle.machine NativeFanoutLayout.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) (ms : List (List ℕ)):=
  P1CompactEstimatorBankCycle.budget gs Q w ms+1+(2*P1CompactNativeMeasured.capacity gs Q w+4)

end NearCubicWires.ExtIncidence.P1CompactNativeRound

/-! Canonical reusable states change only the source and append positions.
Every other ambient tape is the same actual initialized workspace. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeState
open NearCubicWires.ExtIncidence.NativeState
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def heads (H : Fin 277→ℕ) (pos : ℕ) (out : List Bool):=
  dockH bank H (extraH pos out)
noncomputable def tapes (A : Fin 277→List Bool) (data : Fin 15→List Bool)
    (C : ℕ) (source out : List Bool):=install bank A (word data C source out)

end NearCubicWires.ExtIncidence.P1CompactNativeState

/-! The original raw polynomial family executes with one retained native
bank and one literal outer driver, including empty polynomials/families. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeFamily
open NearCubicWires.ExtIncidence.NativeFamily
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawWord {B : ℕ} (ms : List (List (Fin B))):=stream (rawIndices ms)
def emit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (Q w : ℕ)
    (ms : List (List (Fin gs.length))):=
  (P1CompactCloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
    (MatrixScoreBatch.cutWord (P1CompactNativeWidth.width gs Q))
def cost {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) :
    List (List (List (Fin gs.length)))→ℕ
  | []=>0
  | ms::ps=>max (P1CompactNativeRound.budget gs Q w (rawIndices ms)) (cost gs Q w ps)

noncomputable def machine:=P1CompactCloseoutRowsDegreeLoop.machine P1CompactNativeRound.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))):=ps.length*(cost gs Q w ps+3)+3
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))) (pre tail : List Bool)
    (H : Fin 277→ℕ) (A : Fin 277→List Bool) (j : ℕ) (out : List Bool):=
    (⟨P1CompactNativeRound.machine.start,
      P1CompactNativeState.heads H (pre.length+((ps.take j).flatMap rawWord).length) out,
      P1CompactNativeState.tapes A (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w)
        (pre++ps.flatMap rawWord++tail) out⟩ : Configuration 277 _)

end NearCubicWires.ExtIncidence.P1CompactNativeFamily

namespace NearCubicWires.ExtIncidence
end NearCubicWires.ExtIncidence
