import Proof.SourceAssembly.SourceRefillJoin

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
namespace NearCubicWires.SourceConstruction
noncomputable section

namespace Dims
variable (d : Dims)

/-- The rest layout with the twelve high residents of decisions 41 and 47. -/
structure RestExt3 (eX pX gW : Nat) : Prop where
  ext2 : d.RestExt2 eX pX gW
  hres3 : 19 + restPc eX pX gW + 22 ≤ d.res

/-- The lower per-call block: the tapes of the back half (frame input, metadata stages, F6, slope, cursor, `nT`). -/
def InZ (eX pX v : Nat) : Prop := d.B + 19 ≤ v ∧ v < d.B + 19 + 71 + eX + pX

/-- The ten FactorSelection residents `hrT 0..9`. -/
def HiRes (eX pX gW v : Nat) : Prop :=
  d.B + 29 + restPc eX pX gW ≤ v ∧ v < d.B + 29 + restPc eX pX gW + 10

variable {d} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- A high resident. -/
def hrT (i : Fin 12) : Fin V :=
  ⟨d.B + 29 + restPc eX pX gW + i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres3; unfold B U G prepT; omega) hV⟩

/-- The outer clear set `Z`, then the driver `hrT 10`, then the log `hrT 11`, by value. -/
def clrZV (eX pX gW i : Nat) : Nat :=
  if i < 71 + eX + pX then d.B + 19 + i
  else if i = 71 + eX + pX then d.B + 29 + restPc eX pX gW + 10
  else d.B + 29 + restPc eX pX gW + 11

/-- The outer clear's slot map. -/
def clrZ : Fin (71 + eX + pX + 1 + 1) → Fin V := fun i =>
  ⟨d.clrZV eX pX gW i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres3
    simp only [clrZV, restPc, B, U, G, prepT] at *
    split_ifs <;> omega) hV⟩

/-! ### value facts -/

end Dims

namespace Rest

/-- **The refill prologue of the window repair**: the outer clear of `Z` (driver `hrT 10 = 1^Rk`, log
`hrT 11 = 0^(Rk+2)`), then the verified refill prologue `refillPro = clear (clr2) ; rest ; refresh`. ONE fixed machine. -/
def refillPro3 {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt3 se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) :=
  Composition.machine
    (RecoveryFocus.machine (Dims.clrZ e hV) (PCJ6e421fabe2aa4155_SourceClear.machine (71 + se.extra + sp.extra)))
    (refillPro se sp e.ext2 hV g7M)

def srcK3 {d : SourceConstruction.Dims} {eX pX gW : Nat} {V : Nat} (cacheT : Fin 19 → Fin V) (x : Fin V) : Prop :=
  x.val = 1 ∨ x.val = 284 ∨ (∃ i, cacheT i = x) ∨ d.HiRes eX pX gW x.val

end Rest
end
end NearCubicWires.SourceConstruction
end
