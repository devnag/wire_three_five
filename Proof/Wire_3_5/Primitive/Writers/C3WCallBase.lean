import Proof.Wire_3_5.Primitive.Writers.C3WFieldsB

/-! # C3 request writer, part 16: the run at a call

Paper quantities: the fields `preW`, `postW` of the call's request (P3:1886-1906, 1636-1664). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.PrimAsm.C3Asm NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairRepresentation (natWord)

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (EG : Envelope) (cG kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The gate field's rest after the gate count. -/
def gyrOf {n : ℕ} (gates : List (NormalizedThresholdGate n)) : List Bool :=
  frame (List.replicate n true) ++ (gates.map PrimT.C4Geo.suppG).flatMap fun g => frame (RepairOrdinary.CloseoutRowsCircuitBottom.nativeWord g)

theorem gateField_eq {n : ℕ} (gates : List (NormalizedThresholdGate n)) :
    PrimT.C4Geo.gateField gates = frame (natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates) := by
  unfold PrimT.C4Geo.gateField ExtDecompositionBatch.segment gyrOf
  rw [List.append_assoc]

/-- The call's steps before the teardown. -/
noncomputable def callCost (P5 : Wr5) (Dv Cv : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm)
    (P : StarParams) (σ : P.Translation) (gates : List (NormalizedThresholdGate P.n)) (w : List Bool)
    (h Q m pr BG BS BF : ℕ) : ℕ :=
  P5.runCost Dv Cv (Ua := C3a.Lay.U alg) w P.n h Q m pr BG BS BS BF BS (PrimT.C4Geo.width P)
    (gates.map PrimT.C4Geo.suppG).length (PrimT.C4Geo.width P) (PrimT.C4Geo.cols P).length
    ((PrimT.C4Geo.flips P σ).flatMap frame).length (PrimT.C4Geo.flips P σ).length
    (natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates).length (PrimT.C4Geo.side P).length
    (C3a.Lay.c3aCost alg (PrimT.C4Geo.poolReq P σ gates h Q 0))
    ((poolRecs alg h (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side P) (PrimT.C4Geo.width P)
      (PrimT.C4Geo.flips P σ)).flatMap frame).length
    (atomsStream (childTable Q (shapeOf (densePool alg (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side P)
      (PrimT.C4Geo.width P) (PrimT.C4Geo.flips P σ))))).length
    ((childTable Q (shapeOf (densePool alg (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side P)
      (PrimT.C4Geo.width P) (PrimT.C4Geo.flips P σ)))).map List.length).sum
    (natWord (PrimT.C4Geo.width P) ++ (PrimT.C4Geo.cols P).flatMap
      fun x => frame (RepairOrdinary.SignedSortKey.binary (PrimT.C4Geo.width P) x)).length

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.C3Field
