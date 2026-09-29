import Proof.PCP.PCPPQuerySourceCall

/-! The physical support parser returns the literal selected support mask
from the same source PCPP object. The index driver is the actual unary
template produced by the query entry, including its trailing zero. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupport
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mask {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (i : Fin p.systematicBits) : List Bool :=
  List.ofFn fun j : Fin r.arity => decide (j∈p.systematicSupport i)
def supportRows {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) := List.ofFn (mask r p)
def clauseTail {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) :=
  natListWord ((List.ofFn fun i : Fin (2^p.clauseBits) =>
    [literalIndex (p.clauses i).left,literalIndex (p.clauses i).right]).flatten)
def headerBits {n0 : ℕ} {r : PCPPRequest n0} (p : PointwisePCPP r.circuit) :=
  PCPPQueryField.fourBits 3 p.systematicBits p.auxiliaryBits p.clauseBits

theorem output_word {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) :
    pcppOutput r p=headerBits p++(supportRows r p).flatten++clauseTail r p := by
  simp [pcppOutput,headerBits,supportRows,clauseTail,natListWord,
    PCPPQueryField.fourBits,PCPPQueryField.pairBits,PCPPQueryField.fieldBits,List.append_assoc]
  rfl

noncomputable def ready (source : List Bool) (arity index : ℕ) :=
  (⟨machine.start,![0,0,0,1,0,1],![source,[],[],UnaryTemplate.tape arity,[],UnaryTemplate.tape index]⟩ :
    Configuration 6 (16+(Fintype.card (RepeatMachine.Control 5)+5)))
def capacity (index : ℕ) : Fin 6→ℕ := fun i => if i=5 then index+2 else 0

theorem template_pad (index : ℕ) : ZeroPadding.pad (index+2) (CompareMachine.word index)=UnaryTemplate.tape index := by
  simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem ready_eq (source : List Bool) (arity index : ℕ) :
    ZeroPadding.config (capacity index) (entry source arity index)=ready source arity index := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,entry,ready,capacity,template_pad]

end NearCubicWires.RepairOrdinary.PCPPQuerySupport
