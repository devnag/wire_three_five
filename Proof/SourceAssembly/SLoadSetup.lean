import Proof.SourceAssembly.SLoadMaskReady

/-! Deliverable 2, the `setupLoad` machine.

`SLoad.RowInput` reduced the second conjunct of `MaskFamilyCode.Prepared` to
two produced words, two structure aliases and a zero backing. Both produced
words are `RepairOrdinary.frame` of a bare word:

* `rowPublicInput … rowRequestPort = frame (r.input a)`;
* `rowPublicInput … rowCapsPort = rowMetadataWord w degree C caps`, which is by
  definition `frame (natListWord [w,degree,C] ++ caps.word)`.

So `setupLoad` is TWO calls of the raw framer this loader family already uses
(`SLoad.MaskFrame.machine`, the docked `AppendFrameKernel`), each driven by a
retained unary length word onto a zero-backed destination slot. Ten states,
eight slots, no request in scope, and the exit bank differs from the entry bank
at exactly the two destination slots — so the two aliases and the 440-plus
blank header tapes are carried through untouched and no clearing scan is paid.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Setup
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The setup loader: two paid framings on one ambient layout. -/
noncomputable def machine {U : Nat} (s1 d1 t1 l1 s2 d2 t2 l2 : Fin U) :=
  Composition.machine (MaskFrame.machine s1 d1 t1 l1) (MaskFrame.machine s2 d2 t2 l2)

/-- Fuel for the setup loader, in the two physical word lengths. -/
def cost (n1 n2 : Nat) : Nat := (4 * n1 + 4) + 1 + (4 * n2 + 4)

/-- The bare metadata bits the caps port's word frames. -/
def metaBits (w degree C : Nat) (caps : RowCaps) : List Bool :=
  natListWord [w, degree, C] ++ caps.word

theorem meta_frame (w degree C : Nat) (caps : RowCaps) :
    rowMetadataWord w degree C caps = frame (metaBits w degree C caps) := rfl


/-! ### Two of `Prepared`'s remaining obligations are already clauses of
`RowCaps.Good` — citations, not work. -/



end
end SLoad.Setup
