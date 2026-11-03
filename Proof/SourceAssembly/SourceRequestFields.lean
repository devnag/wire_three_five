import Proof.SourceAssembly.SourceRequestSegments
import Proof.SourceAssembly.SourceRequestFieldPass

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.Fields
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

/-! ## 1. A pass at uniform backing `R` -/

/-! ## 2. Three docked passes on `Fin 31` -/

def natSlots : Fin 11 → Fin 31 := ![0, 1, 2, 3, 4, 13, 14, 15, 16, 17, 18]
def supSlots : Fin 10 → Fin 31 := ![5, 6, 7, 8, 19, 20, 21, 22, 23, 24]
def topSlots : Fin 10 → Fin 31 := ![9, 10, 11, 12, 25, 26, 27, 28, 29, 30]


def machine :=
  Composition.machine (RecoveryFocus.machine natSlots (FieldPass.machine 5))
    (Composition.machine (RecoveryFocus.machine supSlots (FieldPass.machine 4))
      (RecoveryFocus.machine topSlots (FieldPass.machine 4)))

def wN (hdr : List Bool) (ns : Fin 4 → List Bool) : Fin 5 → List Bool := ![hdr, ns 0, ns 1, ns 2, ns 3]

def cost (hdr : List Bool) (ns ss ts : Fin 4 → List Bool) : Nat :=
  FieldPass.cost 5 (wN hdr ns) + 1 + (FieldPass.cost 4 ss + 1 + FieldPass.cost 4 ts)

/-! ## 3. At the request of one monomial -/

section request
open NearCubicWires.SourceRequest
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- The four native / support / TOP slot segments of a `≤ 4`-factor monomial. -/
def nSlots (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) : Fin 4 → List Bool :=
  fun i => slotSeg (natSeg mode) atoms i.val
def sSlots (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) : Fin 4 → List Bool :=
  fun i => slotSeg (supSeg mode) atoms i.val
def tSlots (a : DecompositionAlgorithm) (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) :
    Fin 4 → List Bool :=
  fun i => slotSeg (topSeg a mode) atoms i.val

end request


end
end NearCubicWires.SourceRequest.Fields
