import Proof.Assembly.BankFamilyBankInitializer
import Proof.Assembly.Dispatch
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.defProp false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairRepresentation RepairSource.VerifierDecoding
open PCJ1fef9807c6954e94_Native
namespace PCJd35087fe899b4422_
attribute [local irreducible] P1TopDownPaidPayload.tapes

noncomputable def slot (g : PCJ515eaa990d75455b_FamilyInit.PrefixCode) (k : Fin 17) : Fin (PCJf990607ff5714139_Generator.tapes g.printer (7+g.scratch)) := by
 unfold PCJf990607ff5714139_Generator.tapes
 exact Fin.natAdd (r_tapes g.printer) ⟨k.val,by have h:=k.isLt;omega⟩
noncomputable def family (g : PCJ515eaa990d75455b_FamilyInit.PrefixCode) (k : Fin (r_tapes g.printer)) :
 Fin (PCJf990607ff5714139_Generator.tapes g.printer (7+g.scratch)) := by
 unfold PCJf990607ff5714139_Generator.tapes
 exact k.castAdd (10+(7+g.scratch))

@[simp] theorem slot_val (g : PCJ515eaa990d75455b_FamilyInit.PrefixCode) (k : Fin 17) :
 (slot g k).val=r_tapes g.printer+k.val := rfl
@[simp] theorem family_val (g : PCJ515eaa990d75455b_FamilyInit.PrefixCode) (k : Fin (r_tapes g.printer)) :
 (family g k).val=k.val := rfl





end PCJd35087fe899b4422_
