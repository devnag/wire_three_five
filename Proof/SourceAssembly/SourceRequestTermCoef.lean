import Proof.SourceAssembly.SourceRequestTermSegC
import Proof.CaseAnalysis.RowsIntegerFields
import Proof.CaseAnalysis.WitnessNat
import Proof.CaseAnalysis.WitnessCoefficientRecord

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermCoef
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg

/-! ## Layout on `Fin 543`
`0` the coefficient code; `1 + i` pair parser (149); `150` log; `151 + i` integer fields (203); `354` log;
`355 + i` natural decoder (178); `533` log; `534` resident `1^cw`; `535..537` / `538..540` the two normalizers' tapes 2–4;
`541` the record; `542` its rewind log. -/

def pS (i : Fin 149) : Fin 543 := ⟨1 + i.val, by omega⟩
def iS (i : Fin 203) : Fin 543 := ⟨151 + i.val, by omega⟩
def dS (i : Fin 178) : Fin 543 := ⟨355 + i.val, by omega⟩
def c1S : Fin 3 → Fin 543 := ![0, 2, 150]
def c3S : Fin 3 → Fin 543 := ![39, 151, 354]
def c5S : Fin 3 → Fin 543 := ![79, 355, 533]
def n1S : Fin 5 → Fin 543 := ![534, 345, 535, 536, 537]
def n2S : Fin 5 → Fin 543 := ![534, 529, 538, 539, 540]
def rS : Fin 6 → Fin 543 := ![168, 535, 538, 541, 537, 542]


/-- The CoefficientRecord stage with its rewind log. -/
noncomputable def recordMachine := Rewind.machine CloseoutWitness.CoefficientRecord.machine

noncomputable def machine :=
  Composition.machine
   (Composition.machine
    (Composition.machine
     (Composition.machine
      (Composition.machine
       (Composition.machine
        (Composition.machine
         (Composition.machine (RecoveryFocus.machine c1S copyMachine)
          (RecoveryFocus.machine pS CloseoutWitness.PairHeader.machine))
         (RecoveryFocus.machine c3S copyMachine))
        (RecoveryFocus.machine iS CloseoutRowsIntegerFields.machine))
       (RecoveryFocus.machine c5S copyMachine))
      (RecoveryFocus.machine dS CloseoutWitness.NatCold.machine))
     (RecoveryFocus.machine n1S ClockNormalize.machine))
    (RecoveryFocus.machine n2S ClockNormalize.machine))
   (RecoveryFocus.machine rS recordMachine)

/-- The integer and natural code words of the coefficient code. -/
noncomputable def intW (a : List Bool) : List Bool := CloseoutWitness.PairHeader.codeWord a 0
noncomputable def natW (a : List Bool) : List Bool := CloseoutWitness.PairHeader.codeWord a 1
noncomputable def nb (a : List Bool) (cw : Nat) : List Bool :=
  ClockNormalize.resize cw (CloseoutWitness.BitFields.payload (RecoveryFixedUnpair.rightWord (intW a)))
noncomputable def db (a : List Bool) (cw : Nat) : List Bool :=
  ClockNormalize.resize cw (CloseoutWitness.BitFields.payload (natW a))

noncomputable def cost (a : List Bool) (cw : Nat) : Nat :=
  ((((((((2 * (2 * a.length + 1) + 2) + 1 + CloseoutWitness.PairHeader.budget a) + 1 +
    (2 * (2 * (intW a).length + 1) + 2)) + 1 + CloseoutRowsIntegerFields.budget (intW a)) + 1 +
    (2 * (2 * (natW a).length + 1) + 2)) + 1 + CloseoutWitness.NatCold.budget (natW a)) + 1 +
    (4 * cw + 4)) + 1 + (4 * cw + 4)) + 1 +
    (2 * CloseoutWitness.CoefficientRecord.budget (nb a cw) (db a cw) + 2)

/-! ## The word is the compact coefficient record -/

end NearCubicWires.SourceRequest.TermCoef

