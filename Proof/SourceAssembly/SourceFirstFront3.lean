import Proof.SourceAssembly.SourceFirstCore3
import Proof.SourceAssembly.SourceRefillSeam3

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- The first prologue's second clear: the cursor template `rsT 2` and the loop counter `cnt`, then the resident
driver `scr 11` and log `scr 12`. -/
def clrCur {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)
    (cnt : Fin V) : Fin (2+1+1) → Fin V :=
  ![d.rsT e hV 2, cnt, d.scr hV 11, d.scr hV 12]

/-- **The first prologue's front**: the refill clear on `clr2`, the second clear on `clrCur`, then E6 (query copy to
`q284`, cache tape `c15` erased) on the cache's own driver/log `c17/c18`. -/
def firstFront {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt2 se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    (cnt c15 q284 c17 c18 : Fin V) :=
  Composition.machine
    (RecoveryFocus.machine (Dims.clr2 e.ext1 hV) (PCJ6e421fabe2aa4155_SourceClear.machine (d.tcl2 se.extra sp.extra gW)))
    (Composition.machine (RecoveryFocus.machine (clrCur e.ext1 hV cnt) (PCJ6e421fabe2aa4155_SourceClear.machine 2))
      (Prologue.restoreMachine c15 q284 c17 c18))

def firstPro3 {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt3 se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    {si : Nat} (initM : Machine V si) {s7 : Nat} (g7M : Machine V s7) (cnt c15 q284 c17 c18 : Fin V) :=
  Composition.machine initM
    (Composition.machine
      (RecoveryFocus.machine (Dims.clrZ e hV) (PCJ6e421fabe2aa4155_SourceClear.machine (71 + se.extra + sp.extra)))
      (Composition.machine (firstFront se sp e.ext2 hV cnt c15 q284 c17 c18) (firstCore se sp e.ext2 hV g7M cnt)))

section front

end front

end
end NearCubicWires.SourceConstruction.Rest
end
