import Proof.Packets.BudgetFamilyAt
import Proof.SourceAssembly.SourcePhaseCoeff

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceSteps
noncomputable section

section select
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)

def rBsel : Nat :=
  max (CloseoutFinalC10ModeNativeSchedule.selected sources p 0).exponent
    (SourceBudget.betaE (decompositionOf sources) p.clauseDegree + 3)

def onsetR (k : Nat) : Nat :=
  max (CloseoutFinalC10ModeNativeSchedule.selected sources p k).onset
    (max (C10PartsSchedule.partsOnset sources k (rBsel sources p) p.clauseDegree)
      (max (CloseoutWitnessPolicy.inputCutoff sources)
        (2 ^ (2 * SourceBudget.betaC (decompositionOf sources) p.clauseDegree + 10))))

def selR (k : Nat) : CloseoutFinalC10ModeNativeSchedule.Selection sources p k where
  exponent := rBsel sources p
  onset := onsetR sources p k
  parts_le := (le_max_left _ _).trans (le_max_right _ _)
  cutoff_le := (CloseoutFinalC10ModeNativeSchedule.selected sources p k).cutoff_le.trans (le_max_left _ _)
  cap_le := fun N hN => by
    have h := (CloseoutFinalC10ModeNativeSchedule.selected sources p k).cap_le N ((le_max_left _ _).trans hN)
    refine h.trans ?_
    unfold C10PartsSchedule.widthPower
    exact Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)

end select

end
end NearCubicWires.SourceSteps
end
