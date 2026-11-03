import Proof.SourceAssembly.SourceRequestSelLocalMach
import Proof.Packets.SelBackSymRun

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

/-- The SYM producer's tape count. -/
abbrev tS : Nat := 3778

theorem slotS_lt (i : Fin 4) (j : Fin tS) : 19 + i.val * tS + j.val < 19 + 4 * tS := by
  have hi := i.isLt
  have hj := j.isLt
  have h := Nat.mul_le_mul_right tS (show i.val + 1 ≤ 4 by omega)
  rw [Nat.succ_mul] at h
  omega

def loS (k : Nat) (h : k < NF) : Fin (NF + (19 + 4 * tS)) := Fin.castAdd _ ⟨k, h⟩
def rgS (x : Fin (19 + 4 * tS)) : Fin (NF + (19 + 4 * tS)) := Fin.natAdd NF x
def cslotS (i : Fin 4) (j : Fin tS) : Fin (19 + 4 * tS) := ⟨19 + i.val * tS + j.val, slotS_lt i j⟩

/-- `SelBack.slB` at the SYM producer, request-free. -/
def slBS (i : Fin 4) (j : Fin 1121) : Fin (NF + (19 + 4 * tS)) :=
  if h17 : j.val < 17 then loS (inPort i.val j.val) (by have := inPort_lt i.val i.isLt j.val h17; unfold NF; omega)
  else if h33 : j.val < 33 then rgS (cslotS i (SymSwitch.descSlots ⟨j.val - 17, by omega⟩))
  else if j.val = 33 then loS (1400 + i.val) (by have := i.isLt; unfold NF; omega)
  else loS (1500 + 1100 * i.val + (j.val - 34)) (by have := i.isLt; have := j.isLt; unfold NF; omega)

/-- `SelBack.hdSl` at the SYM producer. -/
def hdSlS (j : Fin 35) : Fin (NF + (19 + 4 * tS)) :=
  if j.val = 0 then loS 1222 (by decide)
  else if j.val < 5 then loS (24 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val = 5 then loS 31 (by decide)
  else if j.val = 6 then loS 43 (by decide)
  else if j.val = 7 then rgS ⟨0, by omega⟩
  else loS (6000 + j.val) (by have := j.isLt; unfold NF; omega)

/-- `SelBack.cfSl` at the SYM producer. -/
def cfSlS (j : Fin 245) : Fin (NF + (19 + 4 * tS)) :=
  if j.val < 4 then loS (1400 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val < 8 then loS (1207 + 4 * (j.val - 4)) (by have := j.isLt; unfold NF; omega)
  else if j.val = 8 then loS 1223 (by decide)
  else if j.val = 9 then loS 32 (by decide)
  else if j.val = 10 then loS 39 (by decide)
  else if j.val < 14 then loS (23 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val = 14 then loS 44 (by decide)
  else loS (6100 + j.val) (by have := j.isLt; unfold NF; omega)

def p4S : Σ s, Machine (NF + (19 + 4 * tS)) s := ⟨_, SourceFactorSel.Slots4.fourM slBS⟩

/-- **The back machine (SYM)**: four slots ; header block ; coefficient stage. -/
def backPS :=
  Composition.machine p4S.2
    (Composition.machine (RecoveryFocus.machine hdSlS pH.2) (RecoveryFocus.machine cfSlS pC.2))

/-- **FactorSelection's machine on the local universe (SYM, phase `ph`)**: ONE fixed machine per phase. -/
def selSymM (ph : Phase) :=
  Composition.machine (RecoveryFocus.machine (us (t := tS)) pA.2)
  (Composition.machine (RecoveryFocus.machine (up (t := tS)) (pB ph).2) backPS)

/-- **The run's cost** (SYM): front A + front B + back. `Rc`-free. -/
def selSymCost (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
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
    SelBackSym.backSymCost (Tof coordinate ci) bits (literalIndex ((a.output r).clauses ci).left).val
      (literalIndex ((a.output r).clauses ci).right).val (sigmaOf a r ci coordinate ph m) cwid cw D r.arity L target
      (FactorLoop.factorsAt coordinate ph ci m).length (2 ^ (a.output r).clauseBits) b)

end
end NearCubicWires.SourceRequest.SelLocal

