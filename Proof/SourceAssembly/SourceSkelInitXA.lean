import Proof.SourceAssembly.SourceSkelInitX
import Proof.SourceAssembly.SourceSkelInitAll
import Proof.SourceAssembly.SourceSkelInitC

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

/-! ## 1. The extended resident map -/

/-- **The whole init's resident map with the extension.** -/
def valAllX (mode : Bool) (L q Rc DD CD Dcw Ccw CL DL b : Nat) (MB : List Bool) : Nat → Option (List Bool) := fun i =>
  if i = 16 then some (ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L)))
  else if i = 17 then some (ZeroPadding.pad Rc (frame MB))
  else if i = 18 then some (ZeroPadding.pad Rc (frame (List.replicate MB.length true)))
  else if i = 19 then some (ZeroPadding.pad Rc (List.replicate b true))
  else valAll mode L q Rc DD CD Dcw Ccw CL DL i

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-! ## 2. `hlong` and `InvC` at the init's exit, generic in the resident map -/

/-! ## 3. The meta stage's contract (POOL-9) and the extended init -/

def MetaRun (NR NE : Nat) (L cS cR q b Rc Vv CP CW CL DP DW DL : Nat) (mode : Bool) (tg : Nat) (MB : List Bool)
    (u : Nat) {sM : Nat} (M : Machine T sM) (mcost wM : Nat) : Prop :=
  u + wM ≤ NE ∧
  ∀ (val : Nat → Option (List Bool)) (H H' : Fin T → ℕ) (A A' : Fin T → List Bool),
    InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A' →
    val 14 = some (ZeroPadding.pad Rc (frame (List.replicate q true))) →
    val 15 = some (ZeroPadding.pad Rc (frame (List.replicate (normalizedLiveCount q L) true))) →
    val 16 = some (ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L))) →
    val 17 = none → val 18 = none →
    ∃ A'', Step M mcost H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun j => if j = 17 then some (ZeroPadding.pad Rc (frame MB))
          else if j = 18 then some (ZeroPadding.pad Rc (frame (List.replicate MB.length true))) else val j)
        (u + wM) H A H' A''

end
end NearCubicWires.SourceSkeleton.InitS
end

