import Proof.Wire_3_5.Primitive.Writers.C3WFields
import Proof.Wire_3_5.Primitive.SeedFix.FlipsPack

/-! # C3 request writer, part 15: the writer at a call

The generic run (`Wr5.c3_run`) at a call of the gate's family: the five writers (the gate field's writer, the geometry
writers `sideAt`, `widthAt`, `colsAt`, the flips machine at its own steps), C3a′ (`c3aM`, `c3a_run`) on the call's
pool request, and the fields `preW`, `postW` of the call's request.

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

variable (a : RepairRepresentation.DecompositionAlgorithm)

/-! ## The fields of the call's request -/

theorem preW_eq (P : StarParams) (σ : P.Translation) (gates : List (NormalizedThresholdGate P.n)) (h Q m pr : ℕ) :
    PrimT.C3ReqIface.preW a (PrimT.C3ReqIface.r0 P σ gates h Q 0 m 0 pr 0) =
      [List.replicate Q true,
        List.replicate ((childTable Q (shapeOf (densePool a (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side P)
          (PrimT.C4Geo.width P) (PrimT.C4Geo.flips P σ)))).map List.length).sum true,
        List.replicate m true, List.replicate h true, List.replicate (pr + 1) true,
        List.replicate (PrimT.C4Geo.width P) true,
        (poolRecs a h (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side P) (PrimT.C4Geo.width P)
          (PrimT.C4Geo.flips P σ)).flatMap frame,
        atomsStream (childTable Q (shapeOf (densePool a (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side P)
          (PrimT.C4Geo.width P) (PrimT.C4Geo.flips P σ))))].flatMap frame := by
  rw [sum_childTable, ← tableTape_eq]
  rfl

theorem postW_eq (P : StarParams) (σ : P.Translation) (gates : List (NormalizedThresholdGate P.n)) (h Q m pr : ℕ) :
    PrimT.C3ReqIface.postW a (PrimT.C3ReqIface.r0 P σ gates h Q 0 m 0 pr 0) =
      [frame (natWord (PrimT.C4Geo.cols P).length ++ natWord (pr + 1)),
        frame (natWord (PrimT.C4Geo.width P) ++ (PrimT.C4Geo.cols P).flatMap
          fun x => frame (RepairOrdinary.SignedSortKey.binary (PrimT.C4Geo.width P) x))].flatMap frame := by
  rw [PrimT.C4Geo.cols_length]
  rfl

/-! ## The machines -/

/-- The flips machine as a writer stage (`FlipsPack.flipsAt`'s machine, run at its own steps). -/
noncomputable def flipsStage (cr : ℕ) : WriterIface.WriterStage :=
  PrimT.C4GateSym.mkStage (GeoFront.geoM (PrimT.Flips.flipsW cr) PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv cr))
    (GeoFront.gInP PrimT.FlipsPack.flD) (GeoFront.gOutP PrimT.FlipsPack.flD) (GeoFront.gInP_ne_out PrimT.FlipsPack.flD)

/-- C3a′'s input tape. -/
def c3aIn : Fin (C3a.Lay.U a) := ⟨0, by unfold C3a.Lay.U; omega⟩

theorem c3aIn_ne : c3aIn a ≠ C3a.Word.c3aOut a := by
  intro e
  have := congrArg Fin.val e
  simp [c3aIn, C3a.Word.c3aOut] at this

end NearCubicWires.WireExponent3_5.PrimAsm.C3Field
