import Proof.CaseAnalysis.ScheduleCoreWidth
import Proof.CaseAnalysis.WitnessCoefficientPolicy

/-! One policy from the actual retained cache arity and actual clause-bit
count. The cache template stays at head one. Existing width arithmetic with
copies=1 supplies q0, then the exact coefficient-bit policy is produced once. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CorePolicy
open LocalBitMultitape RecoveryRootRound RepairSource
open CloseoutSchedule ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev W (D : ℕ):=Width.tapes D
def tapes (D : ℕ):=W D+26
def templateSlots (D : ℕ) (i : Fin 5) : Fin (tapes D):=⟨i.val,by dsimp [tapes,W,Width.tapes,Clause.tapes];omega⟩
def widthSlots (D : ℕ) (i : Fin (W D)) : Fin (tapes D):=
  ⟨if i.val=0 then 1 else 5+i.val,by dsimp only [tapes];split_ifs <;> omega⟩
def q0Slot (D : ℕ):=widthSlots D (Width.outputSlot D)
def clauseSlot (D : ℕ) : Fin (tapes D):=⟨5,by dsimp [tapes,W,Width.tapes,Clause.tapes];omega⟩
def policySlots (D : ℕ) (i : Fin 21) : Fin (tapes D):=
  if i.val=0 then q0Slot D else if i.val=16 then clauseSlot D
  else ⟨W D+5+i.val,by dsimp only [tapes];omega⟩
def capSlot (D : ℕ):=policySlots D 19
def template (D : ℕ):=RecoveryFocus.machine (templateSlots D) PCPPNativeTemplateRaw.machine
def width (D : ℕ):=RecoveryFocus.machine (widthSlots D) (Width.machine D 1)
def policy (D copies : ℕ) (delta : ℚ):=RecoveryFocus.machine (policySlots D) (CoefficientBits.machine delta copies)
def first (D : ℕ):=Composition.machine (template D) (width D)
def machine (D copies : ℕ) (delta : ℚ):=Composition.machine (first D) (policy D copies delta)
def q0 (D core : ℕ):=core+CloseoutLanguage.clauseWidth D core+1
def budget (D copies core cb : ℕ) (delta : ℚ):=
  (4*core+16)+1+Width.budget D 1 core+1+CoefficientBits.budget delta copies (q0 D core) cb


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.CorePolicy
