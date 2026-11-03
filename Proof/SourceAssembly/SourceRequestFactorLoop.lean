import Proof.SourceAssembly.SourceRequestFields

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.Fields
noncomputable section

section
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- The three segments of one factor slot (`none` = absent factor). -/
def segN (mode : Bool) (o : Option (C10TotalDecode.Atom pcpp)) : List Bool := (o.map (natSeg mode)).getD []
def segS (mode : Bool) (o : Option (C10TotalDecode.Atom pcpp)) : List Bool := (o.map (supSeg mode)).getD []
def segT (a : DecompositionAlgorithm) (mode : Bool) (o : Option (C10TotalDecode.Atom pcpp)) : List Bool :=
  (o.map (topSeg a mode)).getD []

/-- **The per-factor producer contract** (the per-kind producers' deliverable type). -/
structure FactorProducer (mode : Bool) (a : DecompositionAlgorithm) (pcpp : PointwisePCPP circuit) where
  t : Nat
  s : Nat
  machine : Machine t s
  d : Nat
  descSlots : Fin d → Fin t
  descInjective : Function.Injective descSlots
  outN : Fin t
  outS : Fin t
  outT : Fin t
  hNS : outN ≠ outS
  hNT : outN ≠ outT
  hST : outS ≠ outT
  /-- the slot's descriptor bank, written by factor selection -/
  Desc : Option (C10TotalDecode.Atom pcpp) → Fin d → List Bool
  /-- admission precondition on the slot's factor -/
  Ok : Option (C10TotalDecode.Atom pcpp) → Prop
  cost : Option (C10TotalDecode.Atom pcpp) → Nat
  /-- the blank backing the producer needs -/
  need : Option (C10TotalDecode.Atom pcpp) → Nat
  run : ∀ (o : Option (C10TotalDecode.Atom pcpp)) (R : Nat), Ok o → need o ≤ R →
    ∃ A' : Fin t → List Bool,
      Step machine (cost o) (fun _ => 0)
        (install descSlots (fun _ => List.replicate R false) (fun k => ZeroPadding.pad R (Desc o k)))
        (fun _ => 0) A' ∧
      A' outN = ZeroPadding.pad R (RepairOrdinary.frame (segN mode o)) ∧
      A' outS = ZeroPadding.pad R (RepairOrdinary.frame (segS mode o)) ∧
      A' outT = ZeroPadding.pad R (RepairOrdinary.frame (segT a mode o))


/-! ## The composed factor loop -/

variable {mode : Bool} {a : DecompositionAlgorithm} (P : FactorProducer mode a pcpp)

theorem slot_lt (i : Fin 4) (j : Fin P.t) : 19 + i.val * P.t + j.val < 19 + 4 * P.t := by
  have hi := i.isLt
  have hj := j.isLt
  have h := Nat.mul_le_mul_right P.t (show i.val + 1 ≤ 4 by omega)
  rw [Nat.succ_mul] at h
  omega

/-- Slot `i`'s producer tape `j`. -/
def cslot (i : Fin 4) (j : Fin P.t) : Fin (19 + 4 * P.t) := ⟨19 + i.val * P.t + j.val, slot_lt P i j⟩

/-- The Fields machine's tapes: header `0`, slot segments on the four producers' output tapes, pass
privates on `1..18`. -/
def fslot (j : Fin 31) : Fin (19 + 4 * P.t) :=
  if h0 : j.val = 0 then ⟨0, by omega⟩
  else if h1 : j.val < 5 then cslot P ⟨j.val - 1, by omega⟩ P.outN
  else if h2 : j.val < 9 then cslot P ⟨j.val - 5, by omega⟩ P.outS
  else if h3 : j.val < 13 then cslot P ⟨j.val - 9, by omega⟩ P.outT
  else ⟨j.val - 12, by omega⟩

/-- The factor loop: the per-factor producer in slots `0..3`, then the three field passes. -/
def machine :=
  Composition.machine (RecoveryFocus.machine (cslot P 0) P.machine)
    (Composition.machine (RecoveryFocus.machine (cslot P 1) P.machine)
      (Composition.machine (RecoveryFocus.machine (cslot P 2) P.machine)
        (Composition.machine (RecoveryFocus.machine (cslot P 3) P.machine)
          (RecoveryFocus.machine (fslot P) Fields.machine))))

def cost (L target : Nat) (atoms : List (C10TotalDecode.Atom pcpp)) : Nat :=
  P.cost atoms[0]? + 1 + (P.cost atoms[1]? + 1 + (P.cost atoms[2]? + 1 + (P.cost atoms[3]? + 1 +
    Fields.cost (header mode q L target atoms.length) (nSlots mode atoms) (sSlots mode atoms)
      (tSlots a mode atoms))))

/-- The site's monomial list. -/
abbrev monomials (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) :=
  (CloseoutFinalC10SupplierCalls.siteCalls ph pcpp coordinate C10TotalDecode.Atom.systematic ci).monomials

def factorsAt (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (m : Nat) :
    List (C10TotalDecode.Atom pcpp) :=
  match (monomials coordinate ph ci)[m]? with
  | some mo => mo.factors
  | none => []

theorem factorsAt_le (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (m : Nat) :
    (factorsAt coordinate ph ci m).length ≤ 4 := by
  unfold factorsAt
  split
  · rename_i mo _
    exact mo.degree_le
  · exact Nat.zero_le 4

end


end
end NearCubicWires.SourceRequest.FactorLoop
