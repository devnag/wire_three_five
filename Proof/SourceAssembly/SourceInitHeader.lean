import Proof.SourceAssembly.SourceInitMasters
import Proof.SourceAssembly.SourceFactorSelNat

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
namespace NearCubicWires.SourceConstruction.InitRun
noncomputable section

/-! ## 1. Local stages -/

/-! ## 2. The resident block and the header scratch -/

def ZB (d : Dims) (eX pX gW X : Nat) : Nat := JB d eX pX gW + X

/-- The header scratch size for the three cap degrees: template log, the natWord block, three poly blocks. -/
def nsOf (DP DW DL : Nat) : Nat := 23 + (14 + 2*DP) + (14 + 2*DW) + (14 + 2*DL)

/-- The layout fact: room for the init workspace, 32 residents and the header scratch. -/
structure HeadExt (d : Dims) (eX pX gW X NS : Nat) : Prop where
  hres : 64 + restPc eX pX gW + X + NS ≤ d.res

/-- `rsT 4`'s value (the resident `1^q`). -/
abbrev r4V (d : Dims) (eX pX gW : Nat) : Nat := d.B + 19 + restPc eX pX gW + 4

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

include pl in
theorem zlay {NS : Nat} (hh : HeadExt d eX pX gW X NS) :
    ZB d eX pX gW X = d.B + 32 + restPc eX pX gW + X ∧ ZB d eX pX gW X + 32 + NS ≤ d.U ∧ d.U ≤ T ∧
    d.scrV 11 + 2 = d.B ∧ d.scrV 12 + 1 = d.B ∧ JB d eX pX gW = d.B + 32 + restPc eX pX gW := by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have := hh.hres
  exact ⟨by unfold ZB; omega, by unfold ZB; omega, pl.hT, h11, h12, hJB⟩

include pl in
/-- A resident. -/
def zT {NS : Nat} (hh : HeadExt d eX pX gW X NS) (i : Fin 32) : Fin T :=
  ⟨ZB d eX pX gW X + i.val, by
    obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
    have := i.isLt
    omega⟩

/-! ### The docks, by value -/

def tV (d : Dims) (eX pX gW X : Nat) (j : Nat) : Nat :=
  if j = 0 then r4V d eX pX gW else if j = 1 then ZB d eX pX gW X else ZB d eX pX gW X + 32

include pl in
def tdk {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 1 ≤ NS) : Fin 3 → Fin T := fun j =>
  ⟨tV d eX pX gW X j.val, by
    obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
    unfold tV r4V; split_ifs <;> omega⟩

def pV (d : Dims) (eX pX gW X D o i : Nat) (j : Nat) : Nat :=
  if j = 0 then r4V d eX pX gW else if j = 3 + 2*D then ZB d eX pX gW X + i else ZB d eX pX gW X + 32 + o + j

include pl in
def pdk {NS : Nat} (hh : HeadExt d eX pX gW X NS) (D o i : Nat) (hi : i < 32) (ho : o + (14 + 2*D) ≤ NS) :
    Fin (BlockPlatform.UnaryCalc.tapes D) → Fin T := fun j =>
  ⟨pV d eX pX gW X D o i j.val, by
    obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
    have hj := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at hj
    unfold pV r4V; split_ifs <;> omega⟩

def nV (d : Dims) (eX pX gW X : Nat) (j : Nat) : Nat :=
  if j = 20 then ZB d eX pX gW X + 5 else if j < 22 then ZB d eX pX gW X + 33 + j
  else if j = 22 then r4V d eX pX gW else if j = 23 then d.scrV 11 else d.scrV 12

include pl in
def ndk {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) : Fin 25 → Fin T := fun j =>
  ⟨nV d eX pX gW X j.val, by
    obtain ⟨e1, e2, e3, e4, e5, _⟩ := pl.zlay hh
    have hj := j.isLt
    unfold nV r4V; split_ifs <;> omega⟩

/-! ### The machines -/

include pl in
def tmplM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 1 ≤ NS) :=
  RecoveryFocus.machine (pl.tdk hh hN) (DimensionTemplate.machine false)

include pl in
def polyM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (D C o i : Nat) (hi : i < 32) (ho : o + (14 + 2*D) ≤ NS) :=
  RecoveryFocus.machine (pl.pdk hh D o i hi ho) (PCPSerializerCapacity.Power.machine D C)

include pl in
def natSM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) :=
  RecoveryFocus.machine (pl.ndk hh hN) SourceFactorSel.Nat.natM

include pl in
def wordM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (k : Fin 32) (w : List Bool) :=
  RecoveryFocus.machine (![pl.zT hh k, d.scr pl.hT 12] : Fin 2 → Fin T) (HierarchyFixedWord.machine w)

/-! ## 3. Stage runs on the source layout (stated by tape values) -/

/-! ## 4. The header machine -/

theorem ns_facts {NS DP DW DL : Nat} (hN : nsOf DP DW DL ≤ NS) :
    1 ≤ NS ∧ 23 ≤ NS ∧ 23 + (14 + 2*DP) ≤ NS ∧ 23 + (14 + 2*DP) + (14 + 2*DW) ≤ NS ∧
    23 + (14 + 2*DP) + (14 + 2*DW) + (14 + 2*DL) ≤ NS := by
  unfold nsOf at hN; omega

include pl in
/-- The first quarter: template ; the cap `P`. -/
def headA1M {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW DL : Nat) (hN : nsOf DP DW DL ≤ NS) :=
  Composition.machine (pl.tmplM hh (ns_facts hN).1) (pl.polyM hh DP CP 23 1 (by decide) (ns_facts hN).2.2.1)

include pl in
/-- The second quarter: the caps `W`, `Ld`. -/
def headA2M {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) :=
  Composition.machine (pl.polyM hh DW CW (23 + (14 + 2*DP)) 2 (by decide) (ns_facts hN).2.2.2.1)
    (pl.polyM hh DL CL (23 + (14 + 2*DP) + (14 + 2*DW)) 3 (by decide) (ns_facts hN).2.2.2.2)

include pl in
/-- The first half: template ; the three caps. -/
def headAM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) :=
  Composition.machine (pl.headA1M hh DP CP DW DL hN) (pl.headA2M hh DP DW CW DL CL hN)

include pl in
/-- The second half: tag ; `natWord q` ; `natWord L` ; `natWord target`. -/
def headBM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) (mode : Bool) (L target : Nat) :=
  Composition.machine (pl.wordM hh 4 (SourceFactorSel.Nat.tagWord mode))
  (Composition.machine (pl.natSM hh hN)
  (Composition.machine (pl.wordM hh 6 (frame (natWord L))) (pl.wordM hh 7 (frame (natWord target)))))

include pl in
/-- **The header machine** (ONE fixed machine per `(layout, caps, mode, L, target)`). -/
def headM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS)
    (mode : Bool) (L target : Nat) :=
  Composition.machine (pl.headAM hh DP CP DW CW DL CL hN) (pl.headBM hh (ns_facts hN).2.1 mode L target)

def costA (DP CP DW CW DL CL q : Nat) : Nat :=
  ((2*q+8) + 1 + PCPSerializerCapacity.Power.budget DP CP q) + 1 +
    (PCPSerializerCapacity.Power.budget DW CW q + 1 + PCPSerializerCapacity.Power.budget DL CL q)

def costB (mode : Bool) (L target q Rc : Nat) : Nat :=
  (2 * (SourceFactorSel.Nat.tagWord mode).length + 2) + 1 + (SourceFactorSel.Nat.natCost q Rc + 1 +
    ((2 * (frame (natWord L)).length + 2) + 1 + (2 * (frame (natWord target)).length + 2)))

/-- Its cost (SMALL: a fixed polynomial in `q`, plus the `O(Rc)` natWord copy). -/
def headCost (DP CP DW CW DL CL : Nat) (mode : Bool) (L target q Rc : Nat) : Nat :=
  costA DP CP DW CW DL CL q + 1 + costB mode L target q Rc

end Place

namespace Place

end Place

end
end NearCubicWires.SourceConstruction.InitRun
end
