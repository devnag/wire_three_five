import Proof.Wire_3_5.Primitive.Writers.SymDecRun
import Proof.Wire_3_5.Primitive.Writers.SymDecEnum

/-! # PA (d)-SYM decode, part 15: the call's numbers and the FILTER units' bodies (value level)

The decode computes the call's numbers from its request and counts (`numsVec`, `HVals`); this file identifies them
with the paper's (`Enum`, `SymFlat`) at a SYM call `(I, hs, Cs, carriers)`:

* `cy_sum` (`Σ_i |symGates C_i| = Pl.M`), `stV_eq_nSt` (the padded `Π_j (m_j+1)²` is `nSt`), `fbv_eq_nFlat`,
  `seed_eq_nGap`, **`totV_eq`** (the decode's `TOT` is the SYM tape's unit count `symNT·N²·EU`);
* `pool_length` (`|symPool| = 2Σ|X| + Σ m_i`), `slice_carrier` (a carrier row's slice: offset `fbOff`, length `fbL`);
* **`filt_unit`**: a FILTER unit's request unit `symCallUnit e r 0` is the FILTER bank's body at the enumerated gap
  seed of index `t / Π / |FlatSeed|`.

Paper quantities of the main type: the SYM tape's unit count and its FILTER request units (`SymFlat.symCallUnit`,
P3:3011-3016, 3072-3080). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Enum
open NearCubicWires.WireExponent3_5.PrimAsm.SymDecEnum NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.FinalPass.Corner (maskGates)

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n))

/-- The circuits' bottom counts, as the decode reads them. -/
def cyOf : List ℕ := List.ofFn fun i => (symGates (Cs i)).length

theorem cyOf_length : (cyOf Cs).length = a := by simp [cyOf]

theorem cy_sum : (cyOf Cs).sum = (symListParams I n a Cs carriers).M := by
  unfold cyOf symListParams
  rw [List.sum_ofFn]
  simp [length_symGates]

theorem cy_getD (k : ℕ) : (cyOf Cs).getD k 0 = if h : k < a then (Cs ⟨k, h⟩).bottomCount else 0 := by
  unfold cyOf
  by_cases h : k < a
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa using h)]; simp [length_symGates]
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa using h)]

theorem stV_eq_nSt (ha : a ≤ 4) :
    stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) = nSt I hs Cs := by
  simp only [cy_getD, nSt, symM]
  interval_cases a <;> simp [stV, Fin.prod_univ_succ] <;> ring

theorem fbv_eq_nFlat (capS : ℕ) (hD : I.D = 1) (hcap : B.capOf .sym n = capS) :
    2 ^ FlatNums.fbv (cyOf Cs).sum (bV carriers.length capS) (Ledger.Lq n + 5) = nFlat I Cs carriers := by
  have h1 : bV carriers.length capS = (symListParams I n a Cs carriers).B := by
    unfold bV symListParams; rw [hcap]; ring
  have h2 : Ledger.Lq n + 5 = (symListParams I n a Cs carriers).errExp := by
    unfold symListParams Ledger.Lq; rw [hD, one_mul]
  rw [nFlat, ← FlatNums.card_eq, cy_sum I Cs carriers, h1, h2]

theorem filterParams_eq (capS : ℕ) (hcd : I.carrierDeg = 26) (hcap : B.capOf .sym n = capS) :
    I.filterParams .sym n = gP n capS (I.filterErrDeg * Ledger.Lq n) := by
  unfold PrimitiveInputs.filterParams gP Ledger.Lq; rw [hcd, hcap]

theorem seed_eq_nGap (capS : ℕ) (hcd : I.carrierDeg = 26) (hcap : B.capOf .sym n = capS) :
    2 ^ (gP n capS (I.filterErrDeg * Ledger.Lq n)).seedBits = nGap I (n := n) := by
  rw [nGap, filterParams_eq I capS hcd hcap, card_gapSeed]

/-- **The decode's `TOT` is the SYM tape's unit count** `symNT·N²·EU`. -/
theorem tot_eq_symNT (capS : ℕ) (ha : a ≤ 4) (hcd : I.carrierDeg = 26) (hD : I.D = 1) (hcap : B.capOf .sym n = capS) :
    totV n capS (I.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n)
        (SeedFix.callKh (I.starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
        ((cyOf Cs).getD 3 0) =
      symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 *
        ((carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2) := by
  unfold totV
  rw [seed_eq_nGap I capS hcd hcap, fbv_eq_nFlat I Cs carriers capS hD hcap, stV_eq_nSt I hs Cs ha, symNT_eq,
    cy_sum I Cs carriers, ← pow_mul]
  unfold euV
  ring

theorem mask_len (X : Carrier n) : (maskGates X).length = 2 * X.length := by
  induction X with
  | nil => rfl
  | cons g t ih =>
    unfold maskGates at ih ⊢
    rw [List.flatMap_cons, List.length_append, ih]
    simp; ring

theorem pool_length : (symPool Cs carriers).length = 2 * (carriers.map (·.length)).sum + (cyOf Cs).sum := by
  unfold symPool symSlices cyOf
  rw [List.length_flatten, List.map_append, List.sum_append]
  congr 1
  · induction carriers with
    | nil => rfl
    | cons X t ih => simp only [List.map_cons, List.sum_cons, mask_len, ih]; ring
  · simp [List.map_ofFn, Function.comp_def]

theorem sum_two (l : List ℕ) (h : l.length ≤ 2) : l.sum = l.getD 0 0 + l.getD 1 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · rfl
  · simp
  · simp
  · simp at h

theorem slice_len (r : ℕ) (hr : r < carriers.length) (hr1 : r ≤ 1) :
    ((symSlices Cs carriers).getD r []).length =
      fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0) := by
  rw [symSlices_carrier Cs carriers r hr, mask_len]
  have e : ∀ k < carriers.length, (carriers.getD k []).length = (carriers.map (·.length)).getD k 0 := fun k hk => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  unfold fbL
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with h | h <;> subst h
  · rw [if_pos rfl, e 0 hr]
  · rw [if_neg (by decide), e 1 hr]

theorem slice_off (r : ℕ) (hr : r < carriers.length) (hr1 : r ≤ 1) :
    sliceOff (symSlices Cs carriers) r = fbOff r ((carriers.map (·.length)).getD 0 0) := by
  unfold fbOff
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with h | h <;> subst h
  · simp [sliceOff]
  · rcases carriers with _ | ⟨X, t⟩
    · simp at hr
    · simp [sliceOff, symSlices, mask_len]

/-- **A FILTER unit's body**: the request unit `symCallUnit e r 0` of a carrier row `r` is the FILTER bank's body at
the enumerated state's gap seed (cell row `e % N²`, labels `sliceLabs (4·row) |pool| off L`). -/
theorem filt_unit (e r : ℕ) (hr : r < carriers.length) (hr1 : r ≤ 1) (hnc : carriers.length ≤ 2) :
    SymFlat.symCallUnit I hs Cs carriers e r 0 =
      (filtRefC (filterTable (I.filterParams .sym n)
          (symEnum I hs Cs carriers (e / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).1.1
          (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)))
        (SupplierWalk.majorityThreshold (I.filterParams .sym n).walkLen)
        (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)) true
        (sliceLabs (2 * (2 * (e % (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)))
          (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
          (fbOff r ((carriers.map (·.length)).getD 0 0))
          (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)))).flatMap
        (fun t => true :: ListMachine.Rec.termWord t) := by
  have e1 : SymFlat.symCallUnit I hs Cs carriers e r 0 = SymFlat.unitBody (filtRow (symSlices Cs carriers)
      (I.filterParams .sym n) (symEnum I hs Cs carriers (e / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).1.1
      (symPool Cs carriers).length (e % (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2) n r) := by
    unfold SymFlat.symCallUnit SymFlat.symReqUnit
    rw [if_pos hr, if_pos rfl]
  have e2 : ∀ (FP : GapParams) (eg : GapSeed FP) (G row nw : ℕ),
      SymFlat.unitBody (filtRow (symSlices Cs carriers) FP eg G row nw r) =
        (filtRefC (filterTable FP eg ((symSlices Cs carriers).getD r []).length)
          (SupplierWalk.majorityThreshold FP.walkLen) ((symSlices Cs carriers).getD r []).length true
          (sliceLabs (4 * row) G (sliceOff (symSlices Cs carriers) r)
            ((symSlices Cs carriers).getD r []).length)).flatMap (fun t => true :: ListMachine.Rec.termWord t) := by
    intro FP eg G row nw
    rw [← labs_eq]
    rfl
  have hpl : (carriers.map (·.length)).sum = (carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0 :=
    sum_two _ (by simpa using hnc)
  rw [e1, e2, slice_len Cs carriers r hr hr1, slice_off Cs carriers r hr hr1, pool_length, hpl,
    show ∀ y : ℕ, 4 * y = 2 * (2 * y) from fun y => by ring]

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
