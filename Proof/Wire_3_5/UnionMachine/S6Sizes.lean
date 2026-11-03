import Lean
import Proof.Wire_3_5.Primitive.Writers.S6Fit
import Proof.Wire_3_5.Primitive.Writers.ThrSide2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.S6SizesBase


noncomputable section
set_option maxRecDepth 4096


/-! # N1–N3: the final pass's request sizes, `∀ l`, at the S6Fit statements

The S6 (`S6Fit.s6Target`) reads three bounds on the call family of `gate0 l F`, exponents before `F`, coefficients
after (verbatim in `PrimAsm.S6Fit`):

* **N1 `FpInBound`**: `|fpIn| + 1 ≤ K_in·2^k·(n+1)^{D_in}` — the request word (`CallSize.gate_word_length_le`,
  `wordBound_poly`), the printed sample `Q` pairs of `2(2kh+1)` bits (`sampleWord_len`, `Q ≤ 2^{(5kh+3)/4}·poly`,
  `CallIndexR.symCount_leR` / `thrCount_leR`, `(5kh+3)/4 ≤ 2kh = k`), the THR hash bits `≤ c_H·L²` (`ThrSide2.hbC_le`);
* **N2 `SeedCountBound`**: `|GapSeed| ≤ gapK·N^{gapZR l fe}` (`CallIndexR.gapSeed_leR`);
* **N3 `PtCountBound`**: `|centers|·|GapSeed|·Q ≤ K_p·2^{n−⌊k/4⌋}·(n+1)^{D_q}` — `|centers| = 2^{n−k}` (`card_centers`),
  `n − k + ⌊(5kh+3)/4⌋ ≤ n − ⌊k/4⌋ + 1` at `k = 2kh ≤ n` (`SymFr.kh_two`, `NumsX.rs_le`).

Every call of the family is on-star (`Call ⊇ StarAt`), so the off-star branches never occur.

* `sampleWord_len`, `pt_arith`, `in_arith`, `cW`, `dW`, `wordBound_le`, `DqS`, `KpS`, `DinS`, `KinS`,
  **`seedCount_bound`**, **`ptCount_bound`**, **`fpIn_bound`**.

Paper quantities of the main types: the final pass's input length, the filter seeds, the point evaluations
`|centers|·|E|·Q` (prim:runtime P3:3105-3115, P3:3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.S6Sizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline

/-- N3's exponent (the literals and `fe`). -/
noncomputable def DqS (l : Literals) (fe : ℕ) : ℕ :=
  CallIndexR.gapZR l fe + CallIndexR.symZI l fe + CallIndexR.thrZI l fe + 2

/-- N1's exponent (the literals and `fe`). -/
noncomputable def DinS (l : Literals) (fe : ℕ) : ℕ := dW + CallIndexR.symZI l fe + CallIndexR.thrZI l fe + 4

/-- N1's coefficient. -/
noncomputable def KinS (l : Literals) (cr fe : ℕ) : ℕ :=
  (cW + 2 * (8192 * (CallIndexR.symKI cr + CallIndexR.gapK cr)) + ThrSide.cH l + 1) * 2 ^ DinS l fe

/-- **N2**: the number of filter seeds, `∀ l`. -/
theorem seedCount_bound (l : Literals) : S6Fit.SeedCountBound l := by
  intro fe
  refine ⟨CallIndexR.gapZR l fe, fun F hfe => ⟨CallIndexR.gapK F.cr * 2 ^ CallIndexR.gapZR l fe,
    fun kclk coef A a ha r => ?_⟩⟩
  subst hfe
  have h := CallIndexR.gapSeed_leR l F kclk coef A a ha r.1.mode r.1.n
  have hN : (r.1.n + 2) ^ CallIndexR.gapZR l F.filterErrDeg ≤
      2 ^ CallIndexR.gapZR l F.filterErrDeg * (r.1.n + 1) ^ CallIndexR.gapZR l F.filterErrDeg := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  calc seedCount l F kclk coef A a ha r ≤ CallIndexR.gapK F.cr * (r.1.n + 2) ^ CallIndexR.gapZR l F.filterErrDeg := h
    _ ≤ CallIndexR.gapK F.cr * (2 ^ CallIndexR.gapZR l F.filterErrDeg *
        (r.1.n + 1) ^ CallIndexR.gapZR l F.filterErrDeg) := Nat.mul_le_mul_left _ hN
    _ = _ := by ring

/-- **N3**: the number of point evaluations, `∀ l`. -/
theorem ptCount_bound (l : Literals) : S6Fit.PtCountBound l := by
  intro fe
  refine ⟨DqS l fe, fun F hfe => ⟨KpS F.cr * 2 ^ DqS l fe, fun kclk coef A a ha r => ?_⟩⟩
  subst hfe
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  have hK := FinalPass.SymFr.kh_two l F kclk coef A a ha hs
  have hKn : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n :=
    NumsX.rs_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hcen : Fintype.card {c // ((callInputs l F kclk coef A a ha).starParams n hs).IsCenter
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) c} =
      2 ^ (n - ((gate0 l F).budget kclk coef A a ha).kOf n) :=
    StarParams.card_centers _ _
  cases mode with
  | thr =>
    have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
    have hG := CallIndexR.gapSeed_leR l F kclk coef A a ha .thr n
    have hQ := CallIndexR.thrCount_leR l F kclk coef A a ha n hs ha' Cs hd
    have hQ' : SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
        2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) *
          ((8192 * (CallIndexR.symKI F.cr + CallIndexR.gapK F.cr)) *
            (n + 2) ^ (CallIndexR.thrZI l F.filterErrDeg + 2)) :=
      hQ.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
    have h := pt_arith n (((gate0 l F).budget kclk coef A a ha).kOf n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (CallIndexR.gapZR l F.filterErrDeg)
      (CallIndexR.thrZI l F.filterErrDeg + 2) (DqS l F.filterErrDeg) _ _ (CallIndexR.gapK F.cr)
      (8192 * (CallIndexR.symKI F.cr + CallIndexR.gapK F.cr)) hK hKn hG hQ' (by unfold DqS; omega)
    show ptCountOf (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ≤ _
    simp only [ptCountOf, dif_pos hs]
    rw [hcen]
    unfold KpS
    exact h
  | sym =>
    have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
    have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
    have hG := CallIndexR.gapSeed_leR l F kclk coef A a ha .sym n
    have hQ := CallIndexR.symCount_leR l F kclk coef A a ha n hs ha' Cs carriers hd hcar
    have hQ' : SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤
        2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) *
          ((8192 * (CallIndexR.symKI F.cr + CallIndexR.gapK F.cr)) *
            (n + 2) ^ (CallIndexR.symZI l F.filterErrDeg + 2)) :=
      hQ.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
    have h := pt_arith n (((gate0 l F).budget kclk coef A a ha).kOf n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (CallIndexR.gapZR l F.filterErrDeg)
      (CallIndexR.symZI l F.filterErrDeg + 2) (DqS l F.filterErrDeg) _ _ (CallIndexR.gapK F.cr)
      (8192 * (CallIndexR.symKI F.cr + CallIndexR.gapK F.cr)) hK hKn hG hQ' (by unfold DqS; omega)
    show ptCountOf (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .sym, a', ha', Cs, carriers, translation⟩ ≤ _
    simp only [ptCountOf, dif_pos hs]
    rw [hcen]
    unfold KpS
    exact h

/-- **N1**: the final pass's input length, `∀ l`. -/
theorem fpIn_bound (l : Literals) : S6Fit.FpInBound l := by
  intro fe
  refine ⟨DinS l fe, fun F hfe => ⟨KinS l F.cr fe, fun kclk coef A a ha r => ?_⟩⟩
  subst hfe
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  have hK := FinalPass.SymFr.kh_two l F kclk coef A a ha hs
  have hKn : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n :=
    NumsX.rs_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hW := (CallSize.gate_word_length_le l F kclk coef A a ha _ hcall).trans (wordBound_le n)
  have hL : Nat.clog 2 (n + 2) ≤ n + 2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  cases mode with
  | thr =>
    have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
    have hQ := CallIndexR.thrCount_leR l F kclk coef A a ha n hs ha' Cs hd
    have hQ' : (SeedFix.thrCallSample (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).Q ≤
        2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) *
          ((8192 * (CallIndexR.symKI F.cr + CallIndexR.gapK F.cr)) *
            (n + 2) ^ (CallIndexR.thrZI l F.filterErrDeg + 2)) :=
      hQ.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
    have hH := ThrSide.hbC_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
    have hH' : (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length ≤
        ThrSide.cH l * (n + 2) ^ 2 :=
      hH.trans (Nat.mul_le_mul_left _ ((Nat.mul_le_mul hL hL).trans_eq (pow_two _).symm))
    show (PrimRequest.word ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ++
      seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .thr, a', ha', Cs, carriers, translation⟩).length +
        1 ≤ _
    simp only [seedWord, dif_pos hs]
    rw [List.length_append, List.length_append, sampleWord_len, List.length_ofFn]
    have h := in_arith n (((gate0 l F).budget kclk coef A a ha).kOf n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) _ _ _ _
      (CallIndexR.thrZI l F.filterErrDeg + 2) (DinS l F.filterErrDeg) cW dW
      (8192 * (CallIndexR.symKI F.cr + CallIndexR.gapK F.cr)) (ThrSide.cH l) hK hKn hW hQ' le_rfl hH'
      (by unfold DinS; omega) (by unfold DinS; omega) (by unfold DinS; omega)
    unfold KinS
    exact h
  | sym =>
    have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
    have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
    have hQ := CallIndexR.symCount_leR l F kclk coef A a ha n hs ha' Cs carriers hd hcar
    have hQ' : (SeedFix.symCallSample (callInputs l F kclk coef A a ha) hs Cs carriers translation).Q ≤
        2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) *
          ((8192 * (CallIndexR.symKI F.cr + CallIndexR.gapK F.cr)) *
            (n + 2) ^ (CallIndexR.symZI l F.filterErrDeg + 2)) :=
      hQ.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
    show (PrimRequest.word ⟨n, .sym, a', ha', Cs, carriers, translation⟩ ++
      seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .sym, a', ha', Cs, carriers, translation⟩).length +
        1 ≤ _
    simp only [seedWord, dif_pos hs]
    rw [List.length_append, sampleWord_len, List.length_ofFn]
    have h := in_arith n (((gate0 l F).budget kclk coef A a ha).kOf n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) _ _ _ 0
      (CallIndexR.symZI l F.filterErrDeg + 2) (DinS l F.filterErrDeg) cW dW
      (8192 * (CallIndexR.symKI F.cr + CallIndexR.gapK F.cr)) (ThrSide.cH l) hK hKn hW hQ' (Nat.le_add_right _ _)
      (Nat.zero_le _) (by unfold DinS; omega) (by unfold DinS; omega) (by unfold DinS; omega)
    unfold KinS
    exact h

end NearCubicWires.WireExponent3_5.UnionMachine.S6Sizes

end
