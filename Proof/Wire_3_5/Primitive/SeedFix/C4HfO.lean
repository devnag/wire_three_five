import Proof.Wire_3_5.Primitive.SeedFix.C4HfN
import Proof.Wire_3_5.Primitive.SeedFix.C4HD

/-! # The HASH child family, part 15: the printed objective at a table position

`filt:soft`, P3:2285-2290: "At prefix `p` print `V_p(z) = Δ₀Σ_yΣ_e F_aux(e,x(y,z))·E_h[H_h(x(y,z)) | p]`". At a THR
call's HASH stage (the call's data `hashDataOf`), when the atoms are the THR pool's corners at a center `c` (V2's
`atomVal_center`), the printed objective `hV p'` is the hash-sum summand at `c`:
`Σ_{(u,v)} Σ_{e'} F_aux(e', (c,u,v))·Σ_k hashElimZ(T_k(c,u,v))` (`thrFaux`, `thrPopsAt`). The pieces:
`hashTermsM_eval`; PA's `hash_val` (the HASH rows are the aux filter; `rowPoly` is `refOf`'s single factor); the
populations' gates (`hashGis`: occurrence `i` at pool gate `oOff + i`) read at the corners are `thrDigitPop`.

* `f2_eval_map`, `zPoly_eval`, `eval_rows`, `hashExprs_eval`, `hashFs_eval`, `thrPool_getD_occ`, `popAt_hashGis`,
  `lsum_flatMap`, `pops_sum`, `hashGis_length_le`, `range_cells`, **`hash_value`**.

Paper quantity of the main type: the printed conditional objective `V_p(z)` at a center. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.RepairRepresentation
open Finset

noncomputable section

theorem zPoly_eval (G row : ℕ) (sgn : Bool) (gi : ℕ) (ρ : ℕ → Bool) :
    F2Poly.eval (HashB.zPoly G row sgn gi) ρ =
      F2Poly.eval (if sgn then zPlusF2 else zMinusF2) (fun k => ρ (CompilerMachine.Pool.poolIndex G row k gi)) := by
  unfold HashB.zPoly F2Poly.eval
  rw [List.foldl_map]
  congr 1
  funext acc m
  congr 1
  induction m with
  | nil => rfl
  | cons y m ih =>
    rw [List.all_cons, ← ih]
    rfl

/-- A batch of single-factor rows: each expression is its row polynomial's bit. -/
theorem eval_rows (ρ : ℕ → Bool) : ∀ (l : List PrimAsm.Records.RowReq),
    (∀ r ∈ l, PrimAsm.WriterIface.refOf r = [(1, [C4H.rowPoly r])]) →
    ∀ i, IntExpression.eval ((l.map PrimAsm.WriterIface.refOf).getD i []) ρ =
      bitZ (F2Poly.eval ((l.map C4H.rowPoly).getD i []) ρ)
  | [], _, i => by simp [IntExpression.eval, F2Poly.eval, bitZ]
  | r :: l, h, 0 => by
      simp only [List.map_cons, List.getD_cons_zero]
      rw [h r List.mem_cons_self]
      simp [IntExpression.eval]
  | r :: l, h, i + 1 => by
      simp only [List.map_cons, List.getD_cons_succ]
      exact eval_rows ρ l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) i

theorem bitZ_bitInt {b b' : Bool} (h : bitZ b = Lists.bitInt b') : b = b' := by
  cases b <;> cases b' <;> simp [bitZ, Lists.bitInt] at h ⊢

section Link
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
  (alg : DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- The HASH expressions are the HASH rows' polynomials' bits. -/
theorem hashExprs_eval (ρ : ℕ → Bool) (i : ℕ) :
    IntExpression.eval ((PrimAsm.WriterIface.hashExprs alg I hs Cs carriers).getD i []) ρ =
      bitZ (F2Poly.eval ((C4H.hashFsOf alg I hs Cs carriers).getD i []) ρ) := by
  unfold PrimAsm.WriterIface.hashExprs C4H.hashFsOf
  refine eval_rows ρ _ (fun r hr => ?_) i
  unfold PrimAsm.Batch.hashBatch at hr
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr
  rfl

/-- **The HASH tape's row at cell `x` and aux seed `e'` is the aux filter** at the center (PA's `hash_val`). -/
theorem hashFs_eval (c0 : BitInput (I.starParams n hs).n) (ρ : ℕ → Bool) (hσ : (∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)), ∀ gi < (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length, ∀ k : Fin 4,
      ρ (CompilerMachine.Pool.poolIndex (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) k gi) =
        corners ((PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).getD gi PrimAsm.Records.dGate).eval c0
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.2)) k)) (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs))) (e' : Fin (PrimAsm.WriterIface.nE alg I hs Cs carriers)) :
    F2Poly.eval ((C4H.hashFsOf alg I hs Cs carriers).getD (SeedFix.cellNumC x * (PrimAsm.WriterIface.nE alg I hs Cs carriers) + e') []) ρ =
      gapFilter (PrimAsm.WriterIface.auxP alg I hs Cs carriers) (PrimAsm.WriterIface.auxEnum alg I hs Cs carriers e')
        (thrZres (I.starParams n hs) carriers c0 ((SeedFix.callEqv (I.starParams n hs)).symm x.1) ((SeedFix.callEqv (I.starParams n hs)).symm x.2)) := by
  have h1 := PrimAsm.WriterIface.hash_val alg I hs Cs carriers c0 ρ hσ x e'
  rw [hashExprs_eval] at h1
  exact bitZ_bitInt h1

theorem auxEnum_val (e' : Fin (PrimAsm.WriterIface.nE alg I hs Cs carriers)) :
    PrimAsm.WriterIface.auxEnum alg I hs Cs carriers e' = (PrimAsm.Enum.gapSeedEquiv (PrimAsm.WriterIface.auxP alg I hs Cs carriers)).symm e' := by
  unfold PrimAsm.WriterIface.auxEnum
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt e'.isLt)

end Link

/-- The THR pool's gate `oOff + i` is occurrence `i`'s. -/
theorem thrPool_getD_occ (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (i : Fin (thrOccs P Cs).length) :
    (PrimAsm.Records.thrPool P Cs carriers).getD (C4H.hashOOff carriers + i.val) PrimAsm.Records.dGate =
      ((thrOccs P Cs).get i).gate ∧
    C4H.hashOOff carriers + i.val < (PrimAsm.Records.thrPool P Cs carriers).length := by
  have e : PrimAsm.Records.thrPool P Cs carriers =
      (carriers.map FinalPass.Corner.maskGates).flatten ++ (thrOccs P Cs).map (·.gate) := by
    unfold PrimAsm.Records.thrPool PrimAsm.Records.thrSlices
    simp
  have hl : C4H.hashOOff carriers = ((carriers.map FinalPass.Corner.maskGates).flatten).length := rfl
  rw [e]
  constructor
  · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simp), List.getElem_map]
    rfl
  · simp [hl]

section Link2
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
  (alg : DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- **A population's gates read at the corners are its digit population** `T_d^±(c,u,v)`. -/
theorem popAt_hashGis (c0 : BitInput (I.starParams n hs).n) (ρ : ℕ → Bool) (hσ : (∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)), ∀ gi < (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length, ∀ k : Fin 4,
      ρ (CompilerMachine.Pool.poolIndex (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) k gi) =
        corners ((PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).getD gi PrimAsm.Records.dGate).eval c0
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.2)) k)) (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)))
    (g : ThrEq (I.starParams n hs) Cs alg) (pr : SupplierPrime.PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)))
    (d : Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))) (sgn : Bool) :
    HashB.popAt ρ (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) (sgn, C4H.hashGis alg I hs Cs carriers g pr d) =
      thrDigitPop (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) g pr d sgn c0 ((SeedFix.callEqv (I.starParams n hs)).symm x.1) ((SeedFix.callEqv (I.starParams n hs)).symm x.2) := by
  unfold HashB.popAt C4H.hashGis thrDigitPop digitPop
  rw [List.map_flatMap]
  congr 1
  funext i
  rw [List.map_replicate]
  congr 1
  obtain ⟨hget, hlt⟩ := thrPool_getD_occ (I.starParams n hs) Cs carriers i
  rw [zPoly_eval]
  have hc : (fun k : Fin 4 => ρ (CompilerMachine.Pool.poolIndex (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) k
      (C4H.hashOOff carriers + i.val))) =
      corners ((thrOccs (I.starParams n hs) Cs).get i).gate.eval c0 ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.1))
        ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.2)) := by
    funext k
    exact (hσ x _ hlt k).trans (congrArg (fun T : NormalizedThresholdGate (I.starParams n hs).n => corners T.eval c0
      ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.1)) ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.2)) k) hget)
  rw [hc]
  cases sgn
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (residualMinus_f2 _ _ _ _).symm
  · simp only [↓reduceIte]
    exact (residualPlus_f2 _ _ _ _).symm

theorem lsum_flatMap {α : Type} (l : List α) (f : α → List ℤ) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- **The populations' list is the sum over `(g, p, d, ±)`.** -/
theorem pops_sum (f : Bool × List ℕ → ℤ) (F : (ThrEq (I.starParams n hs) Cs alg × SupplierPrime.PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) × Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) × Bool) → ℤ)
    (hf : ∀ g pr d sgn, f (sgn, C4H.hashGis alg I hs Cs carriers g pr d) = F (g, pr, d, sgn)) :
    ((C4H.hashPopsOf alg I hs Cs carriers).map f).sum = ∑ k, F k := by
  unfold C4H.hashPopsOf
  simp only [List.map_flatMap, lsum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hf]
  simp only [← Fin.sum_univ_def]
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp (PrimAsm.Enum.thrEqEquiv (I.starParams n hs) Cs alg).symm]
  refine Finset.sum_congr rfl fun gi _ => ?_
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp (PrimAsm.Enum.primeEquiv (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)))]
  refine Finset.sum_congr rfl fun pi _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_bool, add_comm]

theorem len_rep_le {α β : Type} (l : List α) (v : α → ℕ) (x : α → β) (hv : ∀ y, v y ≤ 1) :
    (l.flatMap fun y => List.replicate (v y) (x y)).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_replicate, List.length_cons]
    have := hv y
    omega

theorem hashGis_length_le (g : ThrEq (I.starParams n hs) Cs alg) (pr : SupplierPrime.PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)))
    (d : Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))) :
    (C4H.hashGis alg I hs Cs carriers g pr d).length ≤ (thrOccs (I.starParams n hs) Cs).length := by
  unfold C4H.hashGis
  refine (len_rep_le _ _ _ fun i => ?_).trans (by simp)
  unfold digitOf
  exact Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))

theorem range_cells (N : ℕ) (f : ℕ → ℤ) :
    ∑ q ∈ range (N ^ 2), f q = ∑ x : Fin N × Fin N, f (SeedFix.cellNumC x) := by
  rw [sq, Finset.sum_range]
  exact (Fintype.sum_equiv finProdFinEquiv _ _ (fun x => rfl)).symm

theorem hD_G : (C4H.hashDataOf alg I hs Cs carriers).G = (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length := by unfold C4H.hashDataOf; rfl
theorem hD_N : (C4H.hashDataOf alg I hs Cs carriers).N = (2 ^ SeedFix.callKh (I.starParams n hs)) := by unfold C4H.hashDataOf; rfl
theorem hD_nE : (C4H.hashDataOf alg I hs Cs carriers).nE = (PrimAsm.WriterIface.nE alg I hs Cs carriers) := by unfold C4H.hashDataOf; rfl
theorem hD_Fs : (C4H.hashDataOf alg I hs Cs carriers).Fs = (C4H.hashFsOf alg I hs Cs carriers) := by unfold C4H.hashDataOf; rfl
theorem hD_pops : (C4H.hashDataOf alg I hs Cs carriers).pops = (C4H.hashPopsOf alg I hs Cs carriers) := by unfold C4H.hashDataOf; rfl

theorem hash_t_pos : 1 ≤ (C4H.hashDataOf alg I hs Cs carriers).MP.t := by
  show 1 ≤ thrCallT alg I hs Cs carriers
  unfold thrCallT listT
  omega

theorem hashPops_len : ∀ pop ∈ (C4H.hashPopsOf alg I hs Cs carriers), pop.2.length ≤ 2 ^ (C4H.hashDataOf alg I hs Cs carriers).MP.ell0 := by
  intro pop hp
  unfold C4H.hashPopsOf at hp
  simp only [List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_finRange, true_and,
    List.not_mem_nil, or_false] at hp
  obtain ⟨gi, pi, d, sgn, _, rfl⟩ := hp
  exact (hashGis_length_le alg I hs Cs carriers _ _ _).trans (MajorantParams.M_le_two_pow (C4H.hashDataOf alg I hs Cs carriers).MP)

/-- One cell `x` of the printed objective: the aux filter at the cell's pair times the populations' eliminations. -/
theorem hash_cell (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c}) (ρ : ℕ → Bool)
    (hσ : ∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)), ∀ gi < (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length, ∀ k : Fin 4,
      ρ (CompilerMachine.Pool.poolIndex (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) k gi) =
        corners ((PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).getD gi PrimAsm.Records.dGate).eval c.1
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.2)) k)
    (plen pre : ℕ) (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs))) :
    ∑ e ∈ range (PrimAsm.WriterIface.nE alg I hs Cs carriers), bitZ (F2Poly.eval ((C4H.hashFsOf alg I hs Cs carriers).getD (SeedFix.cellNumC x * (PrimAsm.WriterIface.nE alg I hs Cs carriers) + e) []) ρ) *
        ((C4H.hashPopsOf alg I hs Cs carriers).map fun pop => SeedFix.hashElimZ (C4H.hashDataOf alg I hs Cs carriers).MP (HashB.popAt ρ (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) pop) plen pre).sum =
      ∑ e' : GapSeed (PrimAsm.WriterIface.auxP alg I hs Cs carriers), bitZ (SeedFix.thrFaux (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) carriers (I.filterParams .thr n) (thrCallE alg I hs Cs carriers) e' (c, ((SeedFix.callEqv (I.starParams n hs)).symm x.1, (SeedFix.callEqv (I.starParams n hs)).symm x.2))) *
        ∑ k : (ThrEq (I.starParams n hs) Cs alg × SupplierPrime.PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) × Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) × Bool), SeedFix.hashElimZ (C4H.hashDataOf alg I hs Cs carriers).MP
          (SeedFix.thrPopsAt (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs alg (thrCallDen alg I hs Cs) k (c, ((SeedFix.callEqv (I.starParams n hs)).symm x.1, (SeedFix.callEqv (I.starParams n hs)).symm x.2))) plen pre := by
  rw [Finset.sum_range]
  refine Fintype.sum_equiv (PrimAsm.Enum.gapSeedEquiv (PrimAsm.WriterIface.auxP alg I hs Cs carriers)).symm _ _ (fun e => ?_)
  rw [hashFs_eval alg I hs Cs carriers c.1 ρ hσ x e, auxEnum_val, FinalPass.gapFilter_eq_filterBits]
  congr 1
  exact pops_sum alg I hs Cs carriers _ _ (fun g pr d sgn => by
    rw [popAt_hashGis alg I hs Cs carriers c.1 ρ hσ x g pr d sgn]
    rfl)

/-- **The printed objective at a center** (P3:2285-2290): when the atoms are the THR pool's corners at the center
`c`, `V_{p'}` is the hash-sum summand at `c`. -/
theorem hash_value (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c}) (ρ : ℕ → Bool)
    (hσ : ∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)), ∀ gi < (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length, ∀ k : Fin 4,
      ρ (CompilerMachine.Pool.poolIndex (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) k gi) =
        corners ((PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).getD gi PrimAsm.Records.dGate).eval c.1
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv (I.starParams n hs)).symm x.2)) k)
    (p' : List Bool) (hplen : p'.length ≤ 2 * (C4H.hashDataOf alg I hs Cs carriers).MP.t * (C4H.hashDataOf alg I hs Cs carriers).MP.ell0) :
    IntExpression.eval (C4H.hV (C4H.hashDataOf alg I hs Cs carriers) p') ρ =
      ∑ uv : (I.starParams n hs).Errors × (I.starParams n hs).Errors, ∑ e' : GapSeed (PrimAsm.WriterIface.auxP alg I hs Cs carriers),
        bitZ (SeedFix.thrFaux (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) carriers (I.filterParams .thr n) (thrCallE alg I hs Cs carriers) e' (c, uv)) *
          ∑ k : (ThrEq (I.starParams n hs) Cs alg × SupplierPrime.PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) × Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) × Bool), SeedFix.hashElimZ (C4H.hashDataOf alg I hs Cs carriers).MP (SeedFix.thrPopsAt (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs alg (thrCallDen alg I hs Cs) k (c, uv)) p'.length
            (SeedFix.listNum p') := by
  unfold C4H.hV
  rw [hD_G, hD_N, hD_nE, hD_Fs, hD_pops]
  rw [HashB.hashTermsM_eval (C4H.hashDataOf alg I hs Cs carriers).MP (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length (2 ^ SeedFix.callKh (I.starParams n hs)) (PrimAsm.WriterIface.nE alg I hs Cs carriers) (C4H.hashFsOf alg I hs Cs carriers) (C4H.hashPopsOf alg I hs Cs carriers) p'.length (SeedFix.listNum p')
    (fun q e => F2Poly.eval ((C4H.hashFsOf alg I hs Cs carriers).getD (q * (PrimAsm.WriterIface.nE alg I hs Cs carriers) + e) []) ρ) ρ (hash_t_pos alg I hs Cs carriers) hplen
    (hashPops_len alg I hs Cs carriers) (fun q _ e _ => rfl)]
  rw [range_cells]
  exact Fintype.sum_equiv ((SeedFix.callEqv (I.starParams n hs)).symm.prodCongr (SeedFix.callEqv (I.starParams n hs)).symm) _ _
    (fun x => hash_cell alg I hs Cs carriers translation c ρ hσ _ _ x)

end Link2

end

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
