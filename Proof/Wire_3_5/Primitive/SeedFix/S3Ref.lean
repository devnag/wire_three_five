import Proof.Wire_3_5.Primitive.SeedFix.S3Words
import Proof.Wire_3_5.FinalPass.TermRef

/-! # S3, the value: `rsumSym` as the evaluator computes it (P3:3170-3178)

"Evaluate the reported lookups at the sampled pairs" (P3:3046-3048): the SYM per-point sum `rsumSym = Σ_{e'} R̂_{e'}`
over the list seeds, with `R̂_{e'}` over the tuple's circuits the conjunction of stage 8's factor of each circuit's
corner word and the amplified list's reports of its populations. Here:

* **`symRhat_circ`**: `symRhatFast P Cs Pl e' c u v = ⋀_{j < a} circTermT (Cs j) Pl e' c e_L(u) e_R(v)`;
* `circAt` / `circAt_eq`: the factor at circuit `j < 4` of a `SymCall` from its declared gates and top table
  (`gatesJ`, `topJ`), `true` past the tuple; **`rhat4`**: the conjunction over the four guarded slots;
* **`rsum_seeds`**: `rsumSym = Σ_{i < |FlatSeed|} [R̂ at seed i]` in the declared enumeration (`seedOf`).

Paper quantity of the main type: the SYM per-point sum `rsumSym` (the numerator's `Σ R̂`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Term NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall rsumSym)

/-- **One circuit's factor**: stage 8's test of its corner word and its lists' reports at the list seed `el`. -/
def circTermT {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (Pl : FlatListParams) (el : Pl.FlatSeed)
    (c eu ev : BitInput n) : Bool :=
  termOk (cornerWord ((symGates C).map fun g => g.eval) c eu ev) (List.ofFn C.top)
    (flatReportFast Pl el (popBits true (cornerWord ((symGates C).map fun g => g.eval) c eu ev)))
    (flatReportFast Pl el (popBits false (cornerWord ((symGates C).map fun g => g.eval) c eu ev)))

/-- **`R̂` over the circuits' factors.** -/
theorem symRhat_circ (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n)
    (Pl : FlatListParams) (el : Pl.FlatSeed) (c : BitInput P.n) (u v : P.Errors) :
    symRhatFast P Cs Pl el c u v = (List.finRange a).all fun j =>
      circTermT (Cs j) Pl el c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) := by
  rw [symRhatFast_eq_terms]
  refine congrArg (List.finRange a).all (funext fun j => ?_)
  show termOk (cornersOf P Cs c u v j) (List.ofFn (Cs j).top) (flatReportFast Pl el (symZp P Cs c u v j))
    (flatReportFast Pl el (symZm P Cs c u v j)) = _
  rw [symZp_eq_pop, symZm_eq_pop]
  rfl

/-- The factor of slot `j < 4` of a call from its declared gates and top table (`true` past the tuple). -/
def circAt (k : SymCall) (el : k.Pl.FlatSeed) (c eu ev : BitInput k.P.n) (j : Fin 4) : Bool :=
  if j.val < k.a then
    termOk (cornerWord ((gatesJ k j).map fun g => g.eval) c eu ev) (topJ k j)
      (flatReportFast k.Pl el (popBits true (cornerWord ((gatesJ k j).map fun g => g.eval) c eu ev)))
      (flatReportFast k.Pl el (popBits false (cornerWord ((gatesJ k j).map fun g => g.eval) c eu ev)))
  else true

theorem circAt_eq (k : SymCall) (el : k.Pl.FlatSeed) (c eu ev : BitInput k.P.n) (j : Fin 4) (hj : j.val < k.a) :
    circAt k el c eu ev j = circTermT (k.Cs ⟨j.val, hj⟩) k.Pl el c eu ev := by
  unfold circAt circTermT gatesJ topJ
  simp only [if_pos hj, dif_pos hj]

/-- **`R̂` over the four guarded slots.** -/
theorem rhat4 (k : SymCall) (el : k.Pl.FlatSeed) (c : BitInput k.P.n) (u v : k.P.Errors) :
    symRhatFast k.P k.Cs k.Pl el c u v =
      (circAt k el c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) 0 &&
        circAt k el c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) 1 &&
        circAt k el c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) 2 &&
        circAt k el c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) 3) := by
  rw [symRhat_circ]
  have ha := k.ha
  set eu := k.P.errorVector k.P.leftBlock u
  set ev := k.P.errorVector k.P.rightBlock v
  have key : ∀ j : Fin 4, (hj : j.val < k.a) → circAt k el c eu ev j = circTermT (k.Cs ⟨j.val, hj⟩) k.Pl el c eu ev :=
    fun j hj => circAt_eq k el c eu ev j hj
  have past : ∀ j : Fin 4, ¬ j.val < k.a → circAt k el c eu ev j = true := fun j hj => by
    unfold circAt; rw [if_neg hj]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true]
  constructor
  · intro h
    have hs : ∀ i : Fin 4, circAt k el c eu ev i = true := by
      intro i
      by_cases hj : i.val < k.a
      · rw [key i hj]; exact h ⟨i.val, hj⟩
      · rw [past i hj]
    exact ⟨⟨⟨hs 0, hs 1⟩, hs 2⟩, hs 3⟩
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ ⟨j, hj⟩
    have hs : ∀ i : Fin 4, circAt k el c eu ev i = true := by
      intro i; fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    have := hs ⟨j, by omega⟩
    rw [key ⟨j, by omega⟩ hj] at this
    exact this

/-- **`rsumSym` over the declared seed enumeration.** -/
theorem rsum_seeds (k : SymCall) (c : BitInput k.P.n) (u v : k.P.Errors) :
    rsumSym k.P k.Cs k.Pl c u v =
      ∑ i : Fin (Fintype.card k.Pl.FlatSeed), (symRhatFast k.P k.Cs k.Pl (seedOf k i) c u v).toNat := by
  unfold rsumSym seedOf
  exact (Equiv.sum_comp (PrimAsm.Enum.flatSeedEquiv k.Pl).symm (fun el => (symRhatFast k.P k.Cs k.Pl el c u v).toNat)).symm

end NearCubicWires.WireExponent3_5.PrimT.S3
