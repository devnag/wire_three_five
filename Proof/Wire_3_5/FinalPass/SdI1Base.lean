import Proof.Wire_3_5.FinalPass.SdW2

/-! # S4 (the seeds phase), part 50: the internal entry at a star call, read (P3:3044-3048, 3170-3178)

From S4's internal entry `SdEntry2` on the layout `gLay E tw`: the blank streams (`ent_lo`, `ent_hi`, `ent_W`), the
words at a SYM star call (`sym_w8`, `sym_w13`, `sym_ws`, `sym_ns`) and at a THR star call (`thr_w8`, `thr_ws`,
`thr_ns`); the sampled halves decoded (`dl_call`, `dr_call`: `callEqv`'s codes); the numerators within the index
counts (`symNum_le`, `thrNum_le`) and, at every request of the family, **`fpNum_le`**: `fpNum ≤ ptCount·vmax`.

Paper quantity of the main type: the printed numerator (P3:3044-3048) against the number of point evaluations. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Split
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 frontWordsOfW2 s4Core2 symCallOf thrCallOf thrWords thrNums)
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decWord digitsOf)

/-! ## The blank streams at the entry -/

section Ent

end Ent

/-! ## The words at a star call -/

section Words
variable {kc : ℕ} {En : Envelope} {B : TimeBudget kc En} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (E : SymPtEval2) {tw : ℕ} {n a' : ℕ} (ha' : a' ≤ 4)
  (carriers : List (Carrier n)) (translation : List ℕ) (σ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs))

theorem sym_w8 (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hs : I.StarAt n)
    (hw : ∀ k, σ.st (fsB (tW k)) = frontWordsOfW2 I alg E.toWords ⟨n, .sym, a', ha', Cs, carriers, translation⟩ k)
    (i : Fin 8) : σ.st (fsB (bst (30 + i.val) (by omega))) =
      s4Core2 (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        ((SeedFix.greedySampler I alg).symS Cs carriers translation hs) carriers (I.filterParams .sym n) i := by
  have h := hw ⟨i.val, by omega⟩
  exact h.trans (fwS_lt8 I alg E.toWords ha' carriers translation Cs hs i.val i.isLt)

theorem sym_w13 (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hs : I.StarAt n)
    (hw : ∀ k, σ.st (fsB (tW k)) = frontWordsOfW2 I alg E.toWords ⟨n, .sym, a', ha', Cs, carriers, translation⟩ k) :
    σ.st (fsB (bst 43 (by omega))) = [] := by
  have h := hw ⟨13, by omega⟩
  exact h.trans (fwS_mid I alg E.toWords ha' carriers translation Cs hs 13 (by omega) (by omega))

theorem sym_ws (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hs : I.StarAt n)
    (hw : ∀ k, σ.st (fsB (tW k)) = frontWordsOfW2 I alg E.toWords ⟨n, .sym, a', ha', Cs, carriers, translation⟩ k)
    (i : Fin E.nw) : σ.st (fsB (SSe (.inr (.inl i)))) = E.words (symCallOf I hs ha' Cs carriers) i := by
  have e : (SSe (.inr (.inl i)) : Fin (bns E.nw E.nsc + 1)) = tW ⟨16 + i.val, by omega⟩ :=
    Fin.ext (by simp only [SSe, sSv, tW, Function.Embedding.coeFn_mk]; omega)
  have h := hw ⟨16 + i.val, by omega⟩
  rw [e]
  exact h.trans (fwS_word I alg E.toWords ha' carriers translation Cs hs i)

theorem sym_ns (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hs : I.StarAt n)
    (hw : ∀ k, σ.st (fsB (tW k)) = frontWordsOfW2 I alg E.toWords ⟨n, .sym, a', ha', Cs, carriers, translation⟩ k) :
    σ.st (fsB tNumsS) = PrimAsm.Data.unaryList (List.ofFn (E.nums (symCallOf I hs ha' Cs carriers))) := by
  have e : (tNumsS : Fin (bns E.nw E.nsc + 1)) = tW ⟨16 + E.nw, by omega⟩ :=
    Fin.ext (by simp only [tNumsS, tW]; omega)
  have h := hw ⟨16 + E.nw, by omega⟩
  rw [e]
  exact h.trans (fwS_nums I alg E.toWords ha' carriers translation Cs hs)

theorem thr_w8 (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hs : I.StarAt n)
    (hw : ∀ k, σ.st (fsB (tW k)) = frontWordsOfW2 I alg E.toWords ⟨n, .thr, a', ha', Cs, carriers, translation⟩ k)
    (i : Fin 8) : σ.st (fsB (bst (30 + i.val) (by omega))) =
      s4Core2 (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs) carriers (I.filterParams .thr n) i := by
  have h := hw ⟨i.val, by omega⟩
  exact h.trans (fwT_lt8 I alg E.toWords ha' carriers translation Cs hs i.val i.isLt)

theorem thr_ws (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hs : I.StarAt n)
    (hw : ∀ k, σ.st (fsB (tW k)) = frontWordsOfW2 I alg E.toWords ⟨n, .thr, a', ha', Cs, carriers, translation⟩ k)
    (i : Fin 7) : σ.st (fsB (bst (38 + i.val) (by omega))) =
      thrWords (thrCallOf I alg hs ha' Cs carriers translation) i := by
  have e : (bst (38 + i.val) (by omega) : Fin (bns E.nw E.nsc + 1)) = tW ⟨8 + i.val, by omega⟩ :=
    Fin.ext (by simp only [bst, tW]; omega)
  have h := hw ⟨8 + i.val, by omega⟩
  rw [e]
  exact h.trans (fwT_word I alg E.toWords ha' carriers translation Cs hs i)

theorem thr_ns (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hs : I.StarAt n)
    (hw : ∀ k, σ.st (fsB (tW k)) = frontWordsOfW2 I alg E.toWords ⟨n, .thr, a', ha', Cs, carriers, translation⟩ k) :
    σ.st (fsB tNumsT) =
      PrimAsm.Data.unaryList (List.ofFn (thrNums (thrCallOf I alg hs ha' Cs carriers translation))) := by
  have e : (tNumsT : Fin (bns E.nw E.nsc + 1)) = tW ⟨15, by omega⟩ :=
    Fin.ext (by simp only [tNumsT, bst, tW])
  have h := hw ⟨15, by omega⟩
  rw [e]
  exact h.trans (fwT_nums I alg E.toWords ha' carriers translation Cs hs)

end Words

/-! ## The sampled halves, decoded -/

theorem dl_call (P : StarParams) (a : Fin (2 ^ SeedFix.callKh P)) :
    decWord P.b (P.r / 2) (P.n - P.r * P.b) false (digitsOf P.s (P.r / 2) (binary (P.s * (P.r / 2)) a)) =
      List.ofFn (euOf P (SeedFix.callEqv P) a) := by
  have h := Sample.errorVector_decode P false ⟨a.val, by rw [SeedFix.callN_eq]; exact a.isLt⟩
  simp only [Bool.false_eq_true, if_false] at h
  exact h.symm

theorem dr_call (P : StarParams) (b : Fin (2 ^ SeedFix.callKh P)) :
    decWord P.b (P.r / 2) (P.n - P.r * P.b) true (digitsOf P.s (P.r / 2) (binary (P.s * (P.r / 2)) b)) =
      List.ofFn (evOf P (SeedFix.callEqv P) b) := by
  have h := Sample.errorVector_decode P true ⟨b.val, by rw [SeedFix.callN_eq]; exact b.isLt⟩
  simp only [if_true] at h
  exact h.symm

/-! ## The numerators within the index counts -/

theorem symNum_le (P : StarParams) (σ : P.Translation) {a N Q : ℕ} (eqv : P.Errors ≃ Fin N)
    (S : Fin Q → Fin N × Fin N) (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) :
    NumDen.symNum P σ eqv S Cs carriers FP Pl ≤
      Fintype.card {c // P.IsCenter σ c} * (Fintype.card (GapSeed FP) * Fintype.card Pl.FlatSeed * Q) := by
  unfold NumDen.symNum
  calc _ ≤ ∑ _c : {c // P.IsCenter σ c}, ∑ _s : GapSeed FP × Pl.FlatSeed, ∑ _l : Fin Q, (1 : ℕ) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun l _ =>
          (Nat.mul_le_mul (Bool.toNat_le _) (Bool.toNat_le _)).trans (by norm_num)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, Fintype.card_prod]

theorem thrNum_le (P : StarParams) (σ : P.Translation) {a N Q : ℕ} (eqv : P.Errors ≃ Fin N)
    (S : Fin Q → Fin N × Fin N) (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) :
    NumDen.thrNum P σ eqv S Cs carriers FP alg den report ≤
      Fintype.card {c // P.IsCenter σ c} * (Fintype.card (GapSeed FP) *
        (Q * (Fintype.card (ThrEq P Cs alg) * Fintype.card (PrimeIndex (thrCutoff P Cs alg den))))) := by
  unfold NumDen.thrNum
  calc _ ≤ ∑ _c : {c // P.IsCenter σ c}, ∑ _e : GapSeed FP, ∑ _l : Fin Q,
        ∑ _gp : ThrEq P Cs alg × PrimeIndex (thrCutoff P Cs alg den), (1 : ℕ) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun l _ =>
          Finset.sum_le_sum fun gp _ => (Nat.mul_le_mul (Bool.toNat_le _) (Bool.toNat_le _)).trans (by norm_num)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, Fintype.card_prod]

/-! ## At a request of the family -/

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

