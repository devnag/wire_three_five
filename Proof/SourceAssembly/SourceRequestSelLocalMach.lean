import Proof.SourceAssembly.SourceRequestSelBackThrRun

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open PCJ6e421fabe2aa4155_SourceLiteralSupport (value)
noncomputable section

/-! ## The `36 ↔ 39` swap and front A's dock -/

/-- The swap on values. -/
def swv (k : Nat) : Nat := if k = 36 then 39 else if k = 39 then 36 else k

theorem swv_ne (k : Nat) (h1 : k ≠ 36) (h2 : k ≠ 39) : swv k = k := by
  simp only [swv, if_neg h1, if_neg h2]

theorem swv_lt (k : Nat) (h : k < NF) : swv k < NF := by
  by_cases h1 : k = 36
  · subst h1; decide
  · by_cases h2 : k = 39
    · subst h2; decide
    · rw [swv_ne k h1 h2]; exact h

def sw (z : Fin NF) : Fin NF := ⟨swv z.val, swv_lt z.val z.isLt⟩

/-- Front A's dock: the fixed ports, `36` and `39` exchanged. -/
def us {t : Nat} (z : Fin NF) : Fin (NF + (19 + 4 * t)) := up (sw z)

/-! ## The request-free back docks (THR) -/

/-- The THR producer's tape count, with no request data. -/
abbrev tT (da : RepairRepresentation.DecompositionAlgorithm) : Nat := 3864 + 2 * ThrOriginal.Tn da

theorem slotT_lt (da : RepairRepresentation.DecompositionAlgorithm) (i : Fin 4) (j : Fin (tT da)) :
    19 + i.val * tT da + j.val < 19 + 4 * tT da := by
  have hi := i.isLt
  have hj := j.isLt
  have h := Nat.mul_le_mul_right (tT da) (show i.val + 1 ≤ 4 by omega)
  rw [Nat.succ_mul] at h
  omega

def loT (da : RepairRepresentation.DecompositionAlgorithm) (k : Nat) (h : k < NF) : Fin (NF + (19 + 4 * tT da)) :=
  Fin.castAdd _ ⟨k, h⟩
def rgT (da : RepairRepresentation.DecompositionAlgorithm) (x : Fin (19 + 4 * tT da)) : Fin (NF + (19 + 4 * tT da)) :=
  Fin.natAdd NF x
def cslotT (da : RepairRepresentation.DecompositionAlgorithm) (i : Fin 4) (j : Fin (tT da)) : Fin (19 + 4 * tT da) :=
  ⟨19 + i.val * tT da + j.val, slotT_lt da i j⟩

/-- `SelBack.slB` at the THR producer, request-free. -/
def slBT (da : RepairRepresentation.DecompositionAlgorithm) (i : Fin 4) (j : Fin 1121) : Fin (NF + (19 + 4 * tT da)) :=
  if h17 : j.val < 17 then loT da (inPort i.val j.val) (by have := inPort_lt i.val i.isLt j.val h17; unfold NF; omega)
  else if h33 : j.val < 33 then rgT da (cslotT da i (ThrSwitch.descSlots da ⟨j.val - 17, by omega⟩))
  else if j.val = 33 then loT da (1400 + i.val) (by have := i.isLt; unfold NF; omega)
  else loT da (1500 + 1100 * i.val + (j.val - 34)) (by have := i.isLt; have := j.isLt; unfold NF; omega)

/-- `SelBack.hdSl` at the THR producer, request-free. -/
def hdSlT (da : RepairRepresentation.DecompositionAlgorithm) (j : Fin 35) : Fin (NF + (19 + 4 * tT da)) :=
  if j.val = 0 then loT da 1222 (by decide)
  else if j.val < 5 then loT da (24 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val = 5 then loT da 31 (by decide)
  else if j.val = 6 then loT da 43 (by decide)
  else if j.val = 7 then rgT da ⟨0, by omega⟩
  else loT da (6000 + j.val) (by have := j.isLt; unfold NF; omega)

/-- `SelBack.cfSl` at the THR producer, request-free. -/
def cfSlT (da : RepairRepresentation.DecompositionAlgorithm) (j : Fin 245) : Fin (NF + (19 + 4 * tT da)) :=
  if j.val < 4 then loT da (1400 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val < 8 then loT da (1207 + 4 * (j.val - 4)) (by have := j.isLt; unfold NF; omega)
  else if j.val = 8 then loT da 1223 (by decide)
  else if j.val = 9 then loT da 32 (by decide)
  else if j.val = 10 then loT da 39 (by decide)
  else if j.val < 14 then loT da (23 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val = 14 then loT da 44 (by decide)
  else loT da (6100 + j.val) (by have := j.isLt; unfold NF; omega)

/-! ## The packed pieces and the fixed machine -/

def pA : Σ s, Machine NF s := ⟨_, frontA⟩
def pB (ph : Phase) : Σ s, Machine NF s := ⟨_, frontB ph⟩
def p4 (da : RepairRepresentation.DecompositionAlgorithm) : Σ s, Machine (NF + (19 + 4 * tT da)) s :=
  ⟨_, SourceFactorSel.Slots4.fourM (slBT da)⟩
def pH : Σ s, Machine 35 s := ⟨_, SourceFactorSel.HdrBlock.hdrM⟩
def pC : Σ s, Machine 245 s := ⟨_, SourceFactorSel.CoefR.coefRM⟩

/-- **The back machine (THR)**: four slots ; header block ; coefficient stage. -/
def backP (da : RepairRepresentation.DecompositionAlgorithm) :=
  Composition.machine (p4 da).2
    (Composition.machine (RecoveryFocus.machine (hdSlT da) pH.2) (RecoveryFocus.machine (cfSlT da) pC.2))

/-- **FactorSelection's machine on the local universe (THR, phase `ph`)**: ONE fixed machine per `(da, ph)`. -/
def selThrM (ph : Phase) (da : RepairRepresentation.DecompositionAlgorithm) :=
  Composition.machine (RecoveryFocus.machine (us (t := tT da)) pA.2)
  (Composition.machine (RecoveryFocus.machine (up (t := tT da)) (pB ph).2) (backP da))

/-! ## Site data: the two literals' term lists and atoms -/

section site
variable {n0 : Nat} {circuit : BooleanCircuit n0}

/-- The queried clause's two coordinate term lists (`false` = left). -/
def Tof {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (ci : Fin (2 ^ pcpp.clauseBits)) : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
  | false => (coordinate (literalIndex (pcpp.clauses ci).left)).monomials
  | true => (coordinate (literalIndex (pcpp.clauses ci).right)).monomials

end site

/-! ## The entry predicate and the cost -/

/-- The cursor record of call `m` at the queried clause. -/
abbrev sigmaOf (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (ph : Phase) (m : Nat) : Option Sel :=
  selAt ph (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
    (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
    (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
    (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
    (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length m

/-- **The run's cost** (THR): front A + front B + back. `Rc`-free. -/
def selThrCost (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (ph : Phase) (L target cwid cw D b m : Nat) : Nat :=
  costA a r ci + 1 +
  (costB ph bits (literalIndex ((a.output r).clauses ci).left).val (literalIndex ((a.output r).clauses ci).right).val
      (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
      (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
      (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
      (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length + 1 +
    backThrCost (Tof coordinate ci) bits (literalIndex ((a.output r).clauses ci).left).val
      (literalIndex ((a.output r).clauses ci).right).val (sigmaOf a r ci coordinate ph m) cwid cw D r.arity L target
      (FactorLoop.factorsAt coordinate ph ci m).length (2 ^ (a.output r).clauseBits) b)

end
end NearCubicWires.SourceRequest.SelLocal

