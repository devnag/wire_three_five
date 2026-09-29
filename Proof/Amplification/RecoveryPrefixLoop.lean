import Proof.Amplification.RecoveryOracleRepeat
import Proof.Amplification.RecoveryPrefixBodyReady
import Proof.Amplification.RecoveryPrefixCanonical

/-! Whole bounded execution of the existing oracle repeater. Generic trace
boundaries keep the prefix body's large finite graph opaque. The physical
capacity and native fields remain obligations of the subsequent cold caller. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixLoop
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
open RecoveryPrefixBody RecoveryPrefix RecoveryQuery VerifierDecoding.RepeatMachine
open CanonicalSATSelfReduction CanonicalRecoveryLanguage CanonicalBinary TseitinCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem cfg_restart {t s : Nat} (body : Machine t s) (data : Configuration t s)
    (total head : Nat) (hh : ∀ i,data.heads i=0) :
    cfg 0 data total head = cfg 0 (initialConfiguration body data.tapes) total head := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [cfg,controlConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases_left] using hh j
    · simp only [cfg,controlConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases_right]
  · rfl

/-- Native data and zero heads; the added physical driver is at pos+1. -/
noncomputable def boundary (p : OrdinaryOracleProgram) (phase : Fin 5)
    (total pos : Nat) (data : Fin p.base.tapeCount→List Bool) :
    (RecoveryOracleRepeat.program p).Config :=
  cfg phase (initialConfiguration p.base.machine data) total (pos+1)

/-- An interval of actual iterations, without the final driver reset. -/
def Interval (o : Nat→Bool) (p : OrdinaryOracleProgram) (total pos count budget : Nat)
    (input output : Fin p.base.tapeCount→List Bool) : Prop :=
  ∃ cost ≤ budget, OrdinaryOracleTrace o (RecoveryOracleRepeat.program p) cost
    (boundary p 0 total pos input) (boundary p 0 total (pos+count) output)

/-- Full physical repetition including its retained driver rewind and halt. -/
def Run (o : Nat→Bool) (p : OrdinaryOracleProgram) (total budget : Nat)
    (input output : Fin p.base.tapeCount→List Bool) : Prop :=
  ∃ cost ≤ budget, OrdinaryOracleTrace o (RecoveryOracleRepeat.program p) cost
    (boundary p 0 total 0 input) (boundary p 3 total 0 output) ∧
    (RecoveryOracleRepeat.program p).base.machine.halted (boundary p 3 total 0 output).control=true

theorem interval (o : Nat→Bool) (p : OrdinaryOracleProgram) (total bodyBudget : Nat)
    (I : Nat→(Fin p.base.tapeCount→List Bool)→Prop)
    (body : ∀ pos<total,∀ input,I pos input →
      ∃ cost ≤ bodyBudget,∃ final : p.Config,
        OrdinaryOracleTrace o p cost (initialConfiguration p.base.machine input) final ∧
        p.base.machine.halted final.control=true ∧ (∀ i,final.heads i=0) ∧ I (pos+1) final.tapes)
    (remaining : Nat) : ∀ pos,pos+remaining≤total →
      ∀ input,I pos input → ∃ output,
        Interval o p total pos remaining (remaining*(bodyBudget+2)) input output ∧
        I (pos+remaining) output := by
  induction remaining with
  | zero =>
    intro pos _ input hi
    exact ⟨input,⟨0,by omega,.refl _⟩,hi⟩
  | succ remaining ih =>
    intro pos hpos input hi
    obtain ⟨bodyCost,hbodyCost,after,hbody,hhalt,hheads,hafter⟩ := body pos (by omega) input hi
    have hcall := RecoveryOracleRepeat.iteration total pos (by omega) rfl hbody hhalt
    rw [cfg_restart p.base.machine after total (pos+2) hheads] at hcall
    obtain ⟨output,⟨tailCost,htailCost,htail⟩,hout⟩ := ih (pos+1) (by omega) after.tapes hafter
    refine ⟨output,⟨bodyCost+2+tailCost,?_,?_⟩,?_⟩
    · calc
        bodyCost+2+tailCost ≤ (bodyBudget+2)+remaining*(bodyBudget+2) := by omega
        _ = (remaining+1)*(bodyBudget+2) := by simp only [Nat.add_mul,Nat.one_mul]; omega
    · simpa only [boundary,Nat.add_assoc,Nat.add_comm remaining 1] using trans hcall htail
    · simpa only [Nat.add_assoc,Nat.add_comm remaining 1] using hout

theorem whole (o : Nat→Bool) (p : OrdinaryOracleProgram) (total bodyBudget : Nat)
    (I : Nat→(Fin p.base.tapeCount→List Bool)→Prop)
    (body : ∀ pos<total,∀ input,I pos input →
      ∃ cost ≤ bodyBudget,∃ final : p.Config,
        OrdinaryOracleTrace o p cost (initialConfiguration p.base.machine input) final ∧
        p.base.machine.halted final.control=true ∧ (∀ i,final.heads i=0) ∧ I (pos+1) final.tapes)
    (input : Fin p.base.tapeCount→List Bool) (hi : I 0 input) :
    ∃ output,Run o p total (total*(bodyBudget+3)+3) input output ∧ I total output := by
  obtain ⟨output,⟨cost,hcost,htrace⟩,hout⟩ := interval o p total bodyBudget I body total 0 (by omega) input hi
  simp only [Nat.zero_add] at hout htrace
  have hexhaust := RecoveryOracleRepeat.exhaust_trace o p (initialConfiguration p.base.machine output) total
  change OrdinaryOracleTrace o (RecoveryOracleRepeat.program p) (total+3)
    (boundary p 0 total total output) (boundary p 3 total 0 output) at hexhaust
  refine ⟨output,⟨cost+(total+3),?_,trans htrace hexhaust,?_⟩,hout⟩
  · calc
      cost+(total+3) ≤ total*(bodyBudget+2)+(total+3) := by omega
      _ = total*(bodyBudget+3)+3 := by simp only [Nat.mul_add]; omega
  · simp [boundary,RecoveryOracleRepeat.program,machine,cfg,controlConfig,phaseCode]

private theorem search_succ (flat : Bool) (payload n : Nat) (xs : List Bool) :
    search flat payload (n+1) xs=nextPrefix flat payload (search flat payload n xs) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => exact ih (nextPrefix flat payload xs)

end NearCubicWires.RepairSource.RecoveryPrefixLoop
