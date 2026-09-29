import Proof.Wire_3_5.Selection.CosOps
import Proof.Wire_3_5.UnionMachine.RegRatStep

/-! # C1.5: the coset loop's standing state and one gate call (P3:1356-1360)

Paper: "Sum its exact count with the rational population weights, over gates and rows. There are 2^k candidate
cosets" (P3:1356-1358). Inside the coset loop the machine keeps a standing state `Base` at the coset counter `N`: the
gate table and the population table, the gate count, the key offset `2^V`, the coset word `NS = N`, the gate
routine's shape registers and its scratch (empty or at its working lengths, as C1.4's `GateReady` asks), the loop's
constants (`n + 1`, `#pops`, the table's length) and its scratch registers at `0`. **`gate_call`**: from `Base`, with
gate `i`'s record in `GA`, the gate routine (C1.4's `gateW_spec`) adds the gate's row count at the coset to `TX` and
keeps `Base`. Main declarations: `gG`, `gR`, `popRec`, `popTable`, `Base`, `Base.sets`, `Base.setv`, `Base.seth31`,
**`gate_call`**. Paper quantity: a gate's exact row count at a candidate coset. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

/-! ## The gate routine's maps -/

/-- The gate routine's streams: the loop's first 28. -/
def gG (S : Fin 50 → Fin (ns + 1)) : Fin 28 → Fin (ns + 1) := fun i => S ⟨i.val, by omega⟩

/-- The gate routine's registers: the loop's first 48. -/
def gR (Q : Fin 64 → Fin nr) : Fin 48 → Fin nr := fun i => Q ⟨i.val, by omega⟩

theorem gG_inj (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) : Function.Injective (gG S) := by
  intro a b hab
  have := hS hab
  exact Fin.ext (by simpa using congrArg Fin.val this)

theorem gR_inj (Q : Fin 64 → Fin nr) (hQ : Function.Injective Q) : Function.Injective (gR Q) := by
  intro a b hab
  have := hQ hab
  exact Fin.ext (by simpa using congrArg Fin.val this)

/-! ## The population table -/

/-- A population's record: its index count in unary, its indices, its weight's numerator and denominator. -/
def popRec (W : ℕ) (X : List ℕ × ℚ) : List Bool :=
  List.replicate X.1.length true ++ [false] ++ (X.1.map fun i => frame (binary W i)).flatten ++
    frame (binary W X.2.num.toNat) ++ frame (binary W X.2.den)

/-- **The population table**: every population's record, in the request's order. -/
def popTable (W : ℕ) (R : SelectionReq) : List Bool := (R.pops.map (popRec W)).flatten

/-! ## The standing state -/

/-- **The coset loop's standing state** at the coset counter `N`. -/
structure Base (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) (R : SelectionReq) (h : ParamsOk R) (W V N : ℕ)
    (σ : WState ns nr) : Prop where
  gt : σ.st (S 30) = gateTable W R
  gth : σ.sh (S 30) = 0
  pt : σ.st (S 31) = popTable W R
  ng : NumOn σ (S 32) W R.gates.length
  of : NumOn σ (S 2) W (2 ^ V)
  nsw : NumOn σ (S 0) (R.r * R.s) N
  ga : (σ.st (S 1)).length ≤ (R.n + 1) * (2 * W + 2)
  gah : σ.sh (S 1) = 0
  sc : ∀ j : Fin 28, 4 ≤ j.val →
    (σ.st (gG S j) = [] ∨ (σ.st (gG S j)).length = wlen (starParamsOf R h) W j) ∧ σ.sh (gG S j) = 0
  r0 : σ.val (Q 0) = hh (starParamsOf R h)
  r1 : σ.val (Q 1) = (starParamsOf R h).b
  r2 : σ.val (Q 2) = (starParamsOf R h).s
  r3 : σ.val (Q 3) = fL (starParamsOf R h)
  r4 : σ.val (Q 4) = fR (starParamsOf R h)
  r5 : σ.val (Q 5) = V + 1
  zr : ∀ j : Fin 48, 6 ≤ j.val → σ.val (gR Q j) = 0
  nr1 : σ.val (Q 60) = R.n + 1
  np : σ.val (Q 59) = R.pops.length
  ptl : σ.val (Q 58) = (popTable W R).length
  tmp : ∀ j : Fin 64, (j = 48 ∨ j = 49 ∨ j = 50 ∨ j = 54 ∨ j = 55 ∨ j = 56 ∨ j = 61 ∨ j = 62 ∨ j = 63) →
    σ.val (Q j) = 0

section Base
variable {S : Fin 50 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 64 → Fin nr} (hQ : Function.Injective Q)
variable {R : SelectionReq} {h : ParamsOk R} {W V N : ℕ}
include hS hQ

theorem gG_ne (k : Fin 50) (hk : 28 ≤ k.val ∨ k.val < 4) (j : Fin 28) (hj : 4 ≤ j.val) : gG S j ≠ S k := by
  intro e
  have := congrArg Fin.val (hS e)
  simp at this
  omega

/-- A word stream outside the standing state may change. -/
theorem Base.sets {σ : WState ns nr} (b : Base S Q R h W V N σ) (k : Fin 50)
    (hk : k.val = 3 ∨ (28 ≤ k.val ∧ k.val ≠ 30 ∧ k.val ≠ 31 ∧ k.val ≠ 32)) (l : List Bool) :
    Base S Q R h W V N (σ.sets (S k) l) := by
  have ne : ∀ m : Fin 50, (m.val = 0 ∨ m.val = 1 ∨ m.val = 2 ∨ m.val = 30 ∨ m.val = 31 ∨ m.val = 32) → S m ≠ S k :=
    fun m hm e => by have := congrArg Fin.val (hS e); omega
  refine ⟨?_, b.gth, ?_, ?_, ?_, ?_, ?_, b.gah, ?_, b.r0, b.r1, b.r2, b.r3, b.r4, b.r5, b.zr, b.nr1, b.np, b.ptl, b.tmp⟩
  · simp [ne 30 (by decide), b.gt]
  · simp [ne 31 (by decide), b.pt]
  · exact numOn_sets_other _ _ _ _ _ _ (ne 32 (by decide)) b.ng
  · exact numOn_sets_other _ _ _ _ _ _ (ne 2 (by decide)) b.of
  · exact numOn_sets_other _ _ _ _ _ _ (ne 0 (by decide)) b.nsw
  · simp [ne 1 (by decide), b.ga]
  · intro j hj
    have hne := gG_ne hS hQ k (by omega) j hj
    simpa [hne] using b.sc j hj

/-- A loop register outside the standing state may change. -/
theorem Base.setv {σ : WState ns nr} (b : Base S Q R h W V N σ) (k : Fin 64)
    (hk : k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 57) (x : ℕ) : Base S Q R h W V N (σ.setv (Q k) x) := by
  have ne : ∀ m : Fin 64, m ≠ k → Q m ≠ Q k := fun m hm => hQ.ne hm
  have nk : ∀ m : Fin 64, (m.val < 51 ∨ m.val = 54 ∨ m.val = 55 ∨ m.val = 56 ∨ 58 ≤ m.val) → m ≠ k := by
    intro m hm e; subst e; rcases hk with rfl | rfl | rfl | rfl <;> simp at hm
  refine ⟨b.gt, b.gth, b.pt, numOn_setv _ _ _ _ _ _ b.ng, numOn_setv _ _ _ _ _ _ b.of,
    numOn_setv _ _ _ _ _ _ b.nsw, b.ga, b.gah, b.sc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ne 0 (nk 0 (by decide)), b.r0]
  · simp [ne 1 (nk 1 (by decide)), b.r1]
  · simp [ne 2 (nk 2 (by decide)), b.r2]
  · simp [ne 3 (nk 3 (by decide)), b.r3]
  · simp [ne 4 (nk 4 (by decide)), b.r4]
  · simp [ne 5 (nk 5 (by decide)), b.r5]
  · intro j hj
    have : gR Q j ≠ Q k := ne _ (nk _ (by simp; omega))
    simp [this, b.zr j hj]
  · simp [ne 60 (nk 60 (by decide)), b.nr1]
  · simp [ne 59 (nk 59 (by decide)), b.np]
  · simp [ne 58 (nk 58 (by decide)), b.ptl]
  · intro j hj
    have : Q j ≠ Q k := ne _ (nk _ (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    simp [this, b.tmp j hj]

/-- The population table's head may move. -/
theorem Base.seth31 {σ : WState ns nr} (b : Base S Q R h W V N σ) (x : ℕ) :
    Base S Q R h W V N (σ.seth (S 31) x) := by
  have ne : ∀ m : Fin 50, m ≠ 31 → S m ≠ S 31 := fun m hm => hS.ne hm
  refine ⟨b.gt, ?_, b.pt, ⟨b.ng.1, ?_⟩, ⟨b.of.1, ?_⟩, ⟨b.nsw.1, ?_⟩, b.ga, ?_, ?_, b.r0, b.r1, b.r2, b.r3, b.r4,
    b.r5, b.zr, b.nr1, b.np, b.ptl, b.tmp⟩
  · simp [ne 30 (by decide), b.gth]
  · simp [ne 32 (by decide), b.ng.2]
  · simp [ne 2 (by decide), b.of.2]
  · simp [ne 0 (by decide), b.nsw.2]
  · simp [ne 1 (by decide), b.gah]
  · intro j hj
    have hne := gG_ne hS hQ 31 (by decide) j hj
    simpa [hne] using b.sc j hj

end Base

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
