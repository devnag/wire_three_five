import Proof.Wire_3_5.Primitive.Writers.Enum
import Proof.Wire_3_5.Primitive.SeedFix.WalkBankIface
import Proof.Wire_3_5.FinalPass.FiltTabCopy

/-! # X1, part (a): a filter seed's copy over the walk bank's side, and its index word

"Pad the base seed to an even number of bits and use the explicit powered Margulis walk [...] the seed consists of the
initial base seed and `O(t)` edge-label bits" (P3:2083-2087, 2098-2100). The filter's seeds are walk samples over the
base size `P.baseSize` (`GapSeed P`), enumerated by base's executable `positiveWalkSampleFinEquiv`
(`Enum.gapSeedEquiv`); the walk bank (`WalkBankIface`) runs over the side `2^r`, `r = wOf fieldBits labelBits · 128`.
The two sides are equal (**`baseSize_eq`**, the audit J5), so a seed is read over the bank's side unchanged
(**`seedCopy`**): the same vertices (**`seedCopy_vertex`**, `UnitReady.FiltReady.hvert`) and, for the seed of index
`g`, the index word `binary (160·n + 2r) g` (**`seedIndex_cast`**; `n = 2(errExp/4)`, the walk length `n + 1`).

Paper quantity of the main type: the seed's index word (the walk sample's start vertex and edge labels). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SeedIdx
open NearCubicWires NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.WireExponent3_5.Filters

/-- A walk sample over the side `N`, read over an equal side `M`. -/
def mwsCast {N M : ℕ} (h : N = M) [NeZero N] [NeZero M] {t : ℕ} (e : MargulisWalkSample N t) :
    MargulisWalkSample M t := by
  subst h
  exact e

/-- The cast keeps the index. -/
theorem idx_mwsCast {N M : ℕ} (h : N = M) [NeZero N] [NeZero M] (n : ℕ) (e : MargulisWalkSample N (n + 1)) :
    (positiveWalkSampleFinEquiv M n (mwsCast h e)).val = (positiveWalkSampleFinEquiv N n e).val := by
  subst h
  rfl

/-- The cast keeps the vertices. -/
theorem mwsCast_vertex {N M : ℕ} (h : N = M) [NeZero N] [NeZero M] {t : ℕ} (e : MargulisWalkSample N t) (i : Fin t) :
    ((mwsCast h e).vertex i).1.val = (e.vertex i).1.val ∧ ((mwsCast h e).vertex i).2.val = (e.vertex i).2.val := by
  subst h
  exact ⟨rfl, rfl⟩

/-- **The seeds' side is the walk bank's side** (the audit J5). -/
theorem baseSize_eq (P : GapParams) : P.baseSize = 2 ^ (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128) := by
  unfold Filters.GapParams.baseSize Filters.GapParams.copySize FinalPass.Filt.wOf
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_mul]
  congr 1
  omega

/-- **A filter seed over the walk bank's side** `2^r`, `r = wOf fieldBits labelBits · 128`. -/
def seedCopy (P : GapParams) (e : GapSeed P) :
    MargulisWalkSample (2 ^ (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1) :=
  mwsCast (baseSize_eq P) e

/-- **The copy has the seed's vertices** (`FiltReady.hvert`). -/
theorem seedCopy_vertex (P : GapParams) (e : GapSeed P) (i : Fin (2 * (P.errExp / 4) + 1)) :
    ((seedCopy P e).vertex i).1.val = (e.vertex i).1.val ∧ ((seedCopy P e).vertex i).2.val = (e.vertex i).2.val :=
  mwsCast_vertex (baseSize_eq P) e i

/-- **The index word of the seed of index `g`** at any side `2^r` equal to the base size. -/
theorem seedIndex_castR (P : GapParams) (r : ℕ) (h : P.baseSize = 2 ^ r) (g : ℕ) (hg : g < Fintype.card (GapSeed P)) :
    PrimT.WalkBank.seedIndexWord r (2 * (P.errExp / 4)) (mwsCast h ((PrimAsm.Enum.gapSeedEquiv P).symm ⟨g, hg⟩)) =
      RepairOrdinary.SignedSortKey.binary (160 * (2 * (P.errExp / 4)) + 2 * r) g := by
  unfold PrimT.WalkBank.seedIndexWord
  rw [idx_mwsCast]
  have e : (positiveWalkSampleFinEquiv P.baseSize (2 * (P.errExp / 4))
      ((PrimAsm.Enum.gapSeedEquiv P).symm ⟨g, hg⟩)).val = g := by
    show ((PrimAsm.Enum.gapSeedEquiv P) ((PrimAsm.Enum.gapSeedEquiv P).symm ⟨g, hg⟩)).val = g
    rw [Equiv.apply_symm_apply]
  rw [e]

/-- **The index word of the seed of index `g`** over the walk bank's side (X1 (a)). -/
theorem seedIndex_cast (P : GapParams) (g : ℕ) (hg : g < Fintype.card (GapSeed P)) :
    PrimT.WalkBank.seedIndexWord (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4))
        (seedCopy P ((PrimAsm.Enum.gapSeedEquiv P).symm ⟨g, hg⟩)) =
      RepairOrdinary.SignedSortKey.binary
        (160 * (2 * (P.errExp / 4)) + 2 * (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128)) g :=
  seedIndex_castR P _ (baseSize_eq P) g hg

end NearCubicWires.WireExponent3_5.UnionMachine.SeedIdx
