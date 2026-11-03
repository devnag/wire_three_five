import Proof.SourceAssembly.SourceFactorSelDesc
import Proof.SourceAssembly.SourceRequestSymSwitch

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Modes
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierPipeline SourceInterfaces
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest
open PCJ6e421fabe2aa4155_SourceSymmetricMeaning (bitmap)
open Desc (Kind gdesc)
noncomputable section

section
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- A slot's kind in the branch mode (`false` THR, `true` SYM); an atom of the other mode is not admitted
(`ThrSwitch.ok` / `SymSwitch.ok` are `False` there) and gets no descriptor. -/
def kindOf (mode : Bool) : Option (C10TotalDecode.Atom pcpp) → Kind
  | none => .absent
  | some (.systematic _) => .sys
  | some (.threshold _) => if mode then .absent else .orig
  | some (.symmetric _) => if mode then .orig else .absent

/-- A systematic slot's support bitmap. -/
def bmOf : Option (C10TotalDecode.Atom pcpp) → List Bool
  | some (.systematic idx) => bitmap (pcpp.systematicSupport idx)
  | _ => []

def bitsOf (mode : Bool) (L : Nat) : Option (C10TotalDecode.Atom pcpp) → List Bool
  | some (.threshold c) => if mode then [] else ThrSwitch.codeBits L c
  | some (.symmetric c) => if mode then SymOriginal.symCodeBits L c else []
  | _ => []

theorem thr_descAt (P W L : Nat) (o : Option (C10TotalDecode.Atom pcpp)) (n : Nat) :
    ThrSwitch.descAt P W L o n = gdesc (UnaryTemplate.tape q) (List.replicate P true)
      (List.replicate W true) (List.replicate L true) (bmOf o) (bitsOf false L o) (kindOf false o) n := by
  rcases o with _ | (idx | c | c)
  · rfl
  · by_cases hn : n < 16
    · interval_cases n <;> simp [ThrSwitch.descAt, ThrSwitch.sysDescAt, gdesc, kindOf, bmOf]
    · simp [ThrSwitch.descAt, gdesc, kindOf, show ¬ n < 4 by omega, show n ≠ 14 by omega,
        show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
  · rfl
  · by_cases hn : n < 16
    · interval_cases n <;> simp [ThrSwitch.descAt, ThrSwitch.origDescAt, ThrOriginal.thrAt,
        ThrOriginal.posVal, gdesc, kindOf, bitsOf]
    · simp [ThrSwitch.descAt, gdesc, kindOf, show ¬ n < 4 by omega, show ¬ n < 14 by omega,
        show n ≠ 15 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
        show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
        show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega]

theorem sym_descAt (P W L : Nat) (o : Option (C10TotalDecode.Atom pcpp)) (n : Nat) :
    SymSwitch.descAt P W L o n = gdesc (UnaryTemplate.tape q) (List.replicate P true)
      (List.replicate W true) (List.replicate L true) (bmOf o) (bitsOf true L o) (kindOf true o) n := by
  rcases o with _ | (idx | c | c)
  · rfl
  · by_cases hn : n < 16
    · interval_cases n <;> simp [SymSwitch.descAt, ThrSwitch.sysDescAt, gdesc, kindOf, bmOf]
    · simp [SymSwitch.descAt, gdesc, kindOf, show ¬ n < 4 by omega, show n ≠ 14 by omega,
        show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
  · by_cases hn : n < 16
    · interval_cases n <;> simp [SymSwitch.descAt, ThrSwitch.origDescAt, ThrOriginal.thrAt,
        ThrOriginal.posVal, gdesc, kindOf, bitsOf]
    · simp [SymSwitch.descAt, gdesc, kindOf, show ¬ n < 4 by omega, show ¬ n < 14 by omega,
        show n ≠ 15 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
        show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
        show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega]
  · rfl

/-! ## The docked writer, per mode -/

theorem tape_length (q : Nat) : (UnaryTemplate.tape q).length = q + 2 := by
  simp [UnaryTemplate.tape]

/-! ## The loop-region entry from its ports (generic in the producer) -/

end


end
end NearCubicWires.SourceFactorSel.Modes
