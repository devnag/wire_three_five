import Proof.SourceAssembly.SourceSkelInitMove
import Proof.SourceAssembly.SourceInitHeader
import Proof.SourceAssembly.SourceResidentPorts

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

/-- The strip base `B + 29 + Pc` (S's `hrT 0`). -/
abbrev sb (d : Dims) (eX pX gW : Nat) : Nat := d.B + 29 + restPc eX pX gW

def KeptS (d : Dims) (eX pX gW X NS NR : Nat) (v : Nat) : Prop :=
  v = d.scrV 11 ∨ v = d.scrV 12 ∨ (d.B + 14 ≤ v ∧ v < d.B + 19) ∨
  (d.B + 19 + restPc eX pX gW ≤ v ∧ v < sb d eX pX gW + 8) ∨ (d.F + d.rt + 3 ≤ v ∧ v < d.F + d.rt + 13) ∨
  (sb d eX pX gW + NR ≤ v ∧ v < sb d eX pX gW + NR + X) ∨
  (d.B + 64 + restPc eX pX gW + X ≤ v ∧ v < d.B + 64 + restPc eX pX gW + X + NS)

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

include pl hh in
/-- S's `RestExt3` holds on the init's placement. -/
theorem ext3 : d.RestExt3 eX pX gW := ⟨pl.ext2, by have := hh.hres; omega⟩

include pl hh in
/-- The strip and the moved block fit in the universe. -/
theorem room (NR : Nat) (hNR : NR ≤ 32) : sb d eX pX gW + 3 + X + NR ≤ T := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pl.zlay hh
  unfold ZB at e1 e2
  unfold sb; omega

/-- Its cost (unchanged by the relocation). -/
def initSCost (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b : Nat) : Nat :=
  pl.init2Cost L C cVc cS cR q b + 1 + Place.headCost DP CP DW CW DL CL mode L target q (Once.Rc eR L C q)

/-- **The exit on S's port map.** -/
structure InitOutS (NR : Nat) (L cS cR q b Rc Vv CP CW CL DP DW DL : Nat) (mode : Bool) (tg : Nat)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (H' : Fin T → ℕ) (A' : Fin T → List Bool) : Prop where
  drv : A' (d.scr pl.hT 11) = List.replicate Rc true ∧ H' (d.scr pl.hT 11) = 0
  log : A' (d.scr pl.hT 12) = List.replicate (Rc+2) false ∧ H' (d.scr pl.hT 12) = 0
  rew1 : A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = List.replicate Vv true ∧
    H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = 0
  rew2 : A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = List.replicate Vv false ∧
    H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = 0
  master : ∀ i, A' (Dims.mT pl.ext2 pl.hT i) = masterW L cS cR q b Rc Vv i ∧ H' (Dims.mT pl.ext2 pl.hT i) = 0
  target : ∀ i, A' (Dims.rfT pl.ext2 pl.hT i) = masterW L cS cR q b Rc Vv i ∧ H' (Dims.rfT pl.ext2 pl.hT i) = 0
  big : A' (Dims.rsT pl.ext.rest pl.hT 0) = ZeroPadding.pad Rc (List.replicate (Mb L q) true) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 0) = 0
  small : A' (Dims.rsT pl.ext.rest pl.hT 1) = ZeroPadding.pad Rc (List.replicate (InitPost.Ms L q) true) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 1) = 0
  curT : A' (Dims.rsT pl.ext.rest pl.hT 2) = ZeroPadding.pad Rc (UnaryTemplate.tape 0) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 2) = 0
  wres : A' (Dims.rsT pl.ext.rest pl.hT 3) = ZeroPadding.pad Rc (List.replicate b true) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 3) = 0
  qres : A' (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 4) = 0
  enc3 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 3) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 3) ∧
    H' (Dims.encT (d := d) pl.hT 3) = 0
  enc7 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 6) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 7) ∧
    H' (Dims.encT (d := d) pl.hT 6) = 0
  enc8 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 7) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 8) ∧
    H' (Dims.encT (d := d) pl.hT 7) = 0
  enc9 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 8) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 9) ∧
    H' (Dims.encT (d := d) pl.hT 8) = 0
  enc10 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 9) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 10) ∧
    H' (Dims.encT (d := d) pl.hT 9) = 0
  app2 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A' (Dims.encT (d := d) pl.hT 10) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 2) ∧
    H' (Dims.encT (d := d) pl.hT 10) = 0
  app4 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A' (Dims.encT (d := d) pl.hT 11) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 4) ∧
    H' (Dims.encT (d := d) pl.hT 11) = 0
  app5 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A' (Dims.encT (d := d) pl.hT 12) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 5) ∧
    H' (Dims.encT (d := d) pl.hT 12) = 0
  encOld : ∀ kk : Fin 13, (kk.val = 4 ∨ kk.val = 5) →
    A' (Dims.encT (d := d) pl.hT kk) = List.replicate Rc false ∧ H' (Dims.encT (d := d) pl.hT kk) = 0
  
  z0 : A' (Dims.hrT (ext3 pl hh) pl.hT 0) = ZeroPadding.pad Rc (UnaryTemplate.tape q) ∧
    H' (Dims.hrT (ext3 pl hh) pl.hT 0) = 0
  z1 : A' (Dims.hrT (ext3 pl hh) pl.hT 1) = ZeroPadding.pad Rc (List.replicate (CP*(q+1)^DP) true) ∧
    H' (Dims.hrT (ext3 pl hh) pl.hT 1) = 0
  z2 : A' (Dims.hrT (ext3 pl hh) pl.hT 2) = ZeroPadding.pad Rc (List.replicate (CW*(q+1)^DW) true) ∧
    H' (Dims.hrT (ext3 pl hh) pl.hT 2) = 0
  z3 : A' (Dims.hrT (ext3 pl hh) pl.hT 3) = ZeroPadding.pad Rc (List.replicate (CL*(q+1)^DL) true) ∧
    H' (Dims.hrT (ext3 pl hh) pl.hT 3) = 0
  z4 : A' (Dims.hrT (ext3 pl hh) pl.hT 4) = ZeroPadding.pad Rc (SourceFactorSel.Nat.tagWord mode) ∧
    H' (Dims.hrT (ext3 pl hh) pl.hT 4) = 0
  z5 : A' (Dims.hrT (ext3 pl hh) pl.hT 5) = ZeroPadding.pad Rc (frame (natWord q)) ∧
    H' (Dims.hrT (ext3 pl hh) pl.hT 5) = 0
  z6 : A' (Dims.hrT (ext3 pl hh) pl.hT 6) = ZeroPadding.pad Rc (frame (natWord L)) ∧
    H' (Dims.hrT (ext3 pl hh) pl.hT 6) = 0
  z7 : A' (Dims.hrT (ext3 pl hh) pl.hT 7) = ZeroPadding.pad Rc (frame (natWord tg)) ∧
    H' (Dims.hrT (ext3 pl hh) pl.hT 7) = 0
  /-- Every other tape of `[F, U)` (the strip `hrT 8 ..` included) is blank at `Rc`, head 0. -/
  blank : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → ¬ KeptS d eX pX gW X NS NR x.val →
    A' x = List.replicate Rc false ∧ H' x = 0
  /-- The moved init workspace. -/
  junk : ∀ x : Fin T, sb d eX pX gW + NR ≤ x.val → x.val < sb d eX pX gW + NR + X → Rc ≤ (A' x).length ∧ H' x = 0
  /-- The header scratch (not moved). -/
  scr : ∀ x : Fin T, d.B + 64 + restPc eX pX gW + X ≤ x.val → x.val < d.B + 64 + restPc eX pX gW + X + NS →
    Rc ≤ (A' x).length ∧ H' x = 0
  below : ∀ x : Fin T, x.val < d.F → (x.val < 278 ∨ 284 ≤ x.val) → A' x = A x ∧ H' x = H x
  low : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 → H' x = 0
  above : ∀ x : Fin T, d.U ≤ x.val → A' x = A x ∧ H' x = H x

/-! ## The run -/

end
end NearCubicWires.SourceSkeleton.InitS
end
