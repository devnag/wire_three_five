import Proof.SourceAssembly.SourceSkelInitS

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

/-- The extension scratch base: right after SI's header scratch. -/
abbrev eb (d : Dims) (eX pX gW X NS : Nat) : Nat := d.B + 64 + restPc eX pX gW + X + NS

/-- The layout fact for the extension scratch of size `NE`. -/
structure ResExt (d : Dims) (eX pX gW X NS NE : Nat) : Prop where
  hres : 64 + restPc eX pX gW + X + NS + NE ≤ d.res

/-- A strip slot's content: a written resident, or blank at `Rc`. -/
def slotVal (Rc : Nat) (val : Nat → Option (List Bool)) (i : Nat) : List Bool :=
  match val i with
  | some w => w
  | none => List.replicate Rc false

theorem slotVal_none (Rc : Nat) (val : Nat → Option (List Bool)) (i : Nat) (h : val i = none) :
    slotVal Rc val i = List.replicate Rc false := by
  unfold slotVal; rw [h]

theorem slotVal_some (Rc : Nat) (val : Nat → Option (List Bool)) (i : Nat) (w : List Bool) (h : val i = some w) :
    slotVal Rc val i = w := by
  unfold slotVal; rw [h]

/-! ## 1. Generic docked stages on the universe (by tape value) -/

section docks
variable {T : Nat}

/-- The polynomial run's dock: input `inp`, output `out`, workspace `e + j`. -/
def polyDkV (inp out e D : Nat) (j : Nat) : Nat :=
  if j = 0 then inp else if j = 3 + 2*D then out else e + j

/-- The dock (block `[e, e+14+2D)`). -/
def polyDk (inp out : Fin T) (e D : Nat) (h : e + 14 + 2*D ≤ T) : Fin (BlockPlatform.UnaryCalc.tapes D) → Fin T :=
  fun j => ⟨polyDkV inp.val out.val e D j.val, by
    have hj := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at hj
    unfold polyDkV; split_ifs
    · exact inp.isLt
    · exact out.isLt
    · omega⟩

/-- The polynomial stage `C·(n+1)^D` from `inp` onto `out`. -/
def polyAtM (inp out : Fin T) (e D C : Nat) (h : e + 14 + 2*D ≤ T) :=
  RecoveryFocus.machine (polyDk inp out e D h) (PCPSerializerCapacity.Power.machine D C)

/-- The copier's dock. -/
def copyAtM (src b0 drv log : Fin T) :=
  RecoveryFocus.machine (![src, b0, drv, log] : Fin 4 → Fin T) ClockUnarySum.machine

end docks

/-! ## 2. The invariant over the strip and the extension scratch -/

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-- **The init's running exit** after `initS` and any number of resident stages. -/
structure InitInv (NR NE : Nat) (L cS cR q b Rc Vv CP CW CL DP DW DL : Nat) (mode : Bool) (tg : Nat)
    (val : Nat → Option (List Bool)) (u : Nat)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (H' : Fin T → ℕ) (A' : Fin T → List Bool) : Prop where
  /-- Off the written strip and the extension scratch, the bank is `InitOutS`'s. -/
  base : ∃ (H1 : Fin T → ℕ) (A1 : Fin T → List Bool),
    InitOutS pl hh NR L cS cR q b Rc Vv CP CW CL DP DW DL mode tg H A H1 A1 ∧
    ∀ x : Fin T, ¬ (sb d eX pX gW + 8 ≤ x.val ∧ x.val < sb d eX pX gW + NR) →
      ¬ (eb d eX pX gW X NS ≤ x.val ∧ x.val < eb d eX pX gW X NS + NE) → A' x = A1 x ∧ H' x = H1 x
  /-- The strip slots `8 .. NR-1`: their residents (or blank), heads 0. -/
  strip : ∀ x : Fin T, sb d eX pX gW + 8 ≤ x.val → x.val < sb d eX pX gW + NR →
    A' x = slotVal Rc val (x.val - sb d eX pX gW) ∧ H' x = 0
  /-- The used extension scratch. -/
  used : ∀ x : Fin T, eb d eX pX gW X NS ≤ x.val → x.val < eb d eX pX gW X NS + u → Rc ≤ (A' x).length ∧ H' x = 0
  /-- The fresh extension scratch. -/
  fresh : ∀ x : Fin T, eb d eX pX gW X NS + u ≤ x.val → x.val < eb d eX pX gW X NS + NE →
    A' x = List.replicate Rc false ∧ H' x = 0

include pl in
/-- The extension scratch fits in the universe. -/
theorem ext_lt {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (k : Nat) (hk : k < NE) : eb d eX pX gW X NS + k < T := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have := hE.hres; have := pl.hT
  unfold eb; omega

include pl hh in
/-- A strip tape fits in the universe. -/
theorem strip_lt (i : Nat) (hi : i < 32) : sb d eX pX gW + i < T := by
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := pl.zlay hh
  unfold ZB at z1 z2; unfold sb; omega

/-- An extension tape. -/
def extT {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (k : Nat) (hk : k < NE) : Fin T :=
  ⟨eb d eX pX gW X NS + k, ext_lt pl hE k hk⟩

/-- A strip tape. -/
def stripT (i : Nat) (hi : i < 32) : Fin T := ⟨sb d eX pX gW + i, strip_lt pl hh i hi⟩

/-- The fixed part of the bank under the invariant (for stage inputs). -/
theorem fixedOf {NR NE : Nat} {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A') :
    (A' (d.scr pl.hT 11) = List.replicate Rc true ∧ H' (d.scr pl.hT 11) = 0) ∧
    (A' (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 4) = 0) := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  have e11 := hag (d.scr pl.hT 11) (by show ¬ (_ ≤ d.scrV 11 ∧ _); unfold sb; omega)
    (by show ¬ (_ ≤ d.scrV 11 ∧ _); unfold eb; omega)
  have e4 := hag (Dims.rsT pl.ext.rest pl.hT 4)
    (by show ¬ (_ ≤ d.B + 19 + restPc eX pX gW + 4 ∧ _); unfold sb; omega)
    (by show ¬ (_ ≤ d.B + 19 + restPc eX pX gW + 4 ∧ _); unfold eb; omega)
  rw [e11.1, e11.2, e4.1, e4.2]
  exact ⟨ho.drv, ho.qres⟩

/-- S's outer-clear capacity. -/
abbrev Rk (Rc : Nat) : Nat := 16 * (Rc + 1)

/-- **The `Rk` stage**: `1^(16(Rc+1))` from `scr 11` onto the extension tape `u`, then the copier onto `hrT 10` (log `hrT 11`),
blank `b0 = ` extension tape `u+17`; workspace `[u+1, u+17)`. -/
def rkM {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (u : Nat) (hu : u + 18 ≤ NE) :=
  Composition.machine
    (polyAtM (d.scr pl.hT 11) (extT pl hE u (by omega)) (eb d eX pX gW X NS + u + 1) 1 16 (by
      have := ext_lt pl hE (u + 17) (by omega); omega))
    (copyAtM (extT pl hE u (by omega)) (extT pl hE (u + 17) (by omega)) (stripT pl hh 10 (by decide))
      (stripT pl hh 11 (by decide)))

def rkCost (Rc : Nat) : Nat := PCPSerializerCapacity.Power.budget 1 16 Rc + 1 + (2 * Rk Rc + 6)

/-- The `D` stage: `pad Rc 1^(CD(q+1)^DD)` from `rsT 4` onto `hrD` (strip slot 12), workspace `[u, u+14+2DD)`. -/
def dM {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (u DD CD : Nat) (hu : u + 14 + 2*DD ≤ NE) :=
  polyAtM (Dims.rsT pl.ext.rest pl.hT 4) (stripT pl hh 12 (by decide)) (eb d eX pX gW X NS + u) DD CD (by
    have := ext_lt pl hE (u + 13 + 2*DD) (by omega); omega)

/-! ## 4. The init with these residents -/

/-- The resident map of `initRMachine`. -/
def valR (Rc DD CD q : Nat) : Nat → Option (List Bool) := fun i =>
  if i = 12 then some (ZeroPadding.pad Rc (List.replicate (CD*(q+1)^DD) true))
  else if i = 10 then some (List.replicate (Rk Rc) true)
  else if i = 11 then some (List.replicate (Rk Rc + 2) false) else none

def initRCost (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD : Nat) : Nat :=
  initSCost pl L C cVc cS cR DP CP DW CW DL CL mode target q b + 1 + rkCost (Once.Rc eR L C q) + 1 +
    PCPSerializerCapacity.Power.budget DD CD q

end
end NearCubicWires.SourceSkeleton.InitS
end
