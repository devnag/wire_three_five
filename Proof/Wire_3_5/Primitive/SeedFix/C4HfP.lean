import Proof.Wire_3_5.Primitive.SeedFix.C4HfO

/-! # The HASH child family, part 16: the recovered sums and the loop's decisions

`filt:soft`, P3:2285-2290, 2327-2336: "Reduce the printed signed score modulo `2^{Q_aux}` separately at each column
[...] Only then sum over columns [...] Greedily choose a child with no larger value". At a THR call's HASH stage (the
call's data `hashDataOf`, the compiler request on the THR pool):

* **`chValH_eq`**: under exact recovery (`alg:recovery`), the HASH child's recovered sum is
  `mult·2^{m−1}·thrHashSum p'` (V3's `sum_table`, `hash_value`);
* `greedyLoop_scaled`: the greedy loop over a positive multiple of the sums makes the same decisions;
* **`hash_loop`**: the loop over the recovered sums prints the fixed hash's bits `thrHashBits` (`hashLoop_eq`);
* **`hashFamCall`**: the HASH child family at a THR call at C4H-a's interface (`HashFamAt2`), its loop's decisions
  the fixed hash's bits.

Paper quantities of the main types: the recovered child sums `mult·2^{m−1}·thrHashSum` and the fixed hash's bits. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.RepairRepresentation
open Finset

noncomputable section

/-- **The greedy loop over a positive multiple of the sums makes the same decisions.** -/
theorem greedyLoop_scaled (m : ℕ) (R R' : List Bool → ℤ) (K : ℤ) (hK : 0 < K)
    (h : ∀ p : List Bool, p.length ≤ m → R p = K * R' p) : SeedFix.greedyLoop m R = SeedFix.greedyLoop m R' := by
  have hlt : ∀ x y : ℤ, K * x < K * y ↔ x < y := fun x y =>
    ⟨fun hh => lt_of_mul_lt_mul_left hh hK.le, fun hh => mul_lt_mul_of_pos_left hh hK⟩
  have key : ∀ j, j ≤ m → (SeedFix.greedyStep R)^[j] [] = (SeedFix.greedyStep R')^[j] [] ∧
      ((SeedFix.greedyStep R')^[j] []).length = j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨rfl, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1]
      have ht : ((SeedFix.greedyStep R')^[j] [] ++ [true]).length ≤ m := by simp [h2]; omega
      have hf : ((SeedFix.greedyStep R')^[j] [] ++ [false]).length ≤ m := by simp [h2]; omega
      refine ⟨?_, ?_⟩
      · simp only [SeedFix.greedyStep, h _ ht, h _ hf, hlt]
      · simp [SeedFix.greedyStep, h2]
  exact (key m le_rfl).1

section Table
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
  (alg : DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- **The HASH child's recovered sum is `mult·2^{m−1}·thrHashSum`** under exact recovery (`alg:recovery`), at the
compiler request on the THR pool. -/
theorem chValH_eq (R0 : CompilerMachine.Req.C3Req) (h Q psi : ℕ)
    (hP : R0.P = C4Geo.poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers) h Q psi) (hdr : R0.dRow = C4Geo.dRow (I.starParams n hs))
    (hcl : R0.cols = C4Geo.cols (I.starParams n hs)) (p' : List Bool) (hplen : p'.length ≤ 2 * (C4H.hashDataOf alg I hs Cs carriers).MP.t * (C4H.hashDataOf alg I hs Cs carriers).MP.ell0)
    (hrange : ∀ ρ : ℕ → Bool, 0 ≤ IntExpression.eval (C4H.hV (C4H.hashDataOf alg I hs Cs carriers) p') ρ ∧
      (2 : ℤ) ^ (R0.m - 1) * IntExpression.eval (C4H.hV (C4H.hashDataOf alg I hs Cs carriers) p') ρ < 2 ^ R0.P.Q) :
    (chValH R0 (C4H.hashDataOf alg I hs Cs carriers) p' : ℤ) = (C4Geo.mult (I.starParams n hs) : ℤ) * 2 ^ (R0.m - 1) *
      SeedFix.thrHashSum (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers) p' := by
  let F : BitInput (I.starParams n hs).n → ℤ := fun c =>
    if hc : (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c then 2 ^ (R0.m - 1) *
      ∑ uv : (I.starParams n hs).Errors × (I.starParams n hs).Errors, ∑ e' : GapSeed (PrimAsm.WriterIface.auxP alg I hs Cs carriers),
        bitZ (SeedFix.thrFaux (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) carriers (I.filterParams .thr n) (thrCallE alg I hs Cs carriers) e' (⟨c, hc⟩, uv)) *
          ∑ k : (ThrEq (I.starParams n hs) Cs alg × SupplierPrime.PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) × Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) × Bool), SeedFix.hashElimZ (C4H.hashDataOf alg I hs Cs carriers).MP (SeedFix.thrPopsAt (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs alg (thrCallDen alg I hs Cs) k (⟨c, hc⟩, uv)) p'.length
            (SeedFix.listNum p')
    else 0
  have hterm : ∀ row col : ℕ, ((C4Pipe.lres (2 ^ (R0.m - 1) * IntExpression.eval (C4H.hV (C4H.hashDataOf alg I hs Cs carriers) p')
      (CompilerMachine.Req.atomVal R0.P (RepairOrdinary.MatrixScorePhi.value R0.cols row)
        (RepairOrdinary.MatrixScorePhi.value R0.cols col))) R0.P.Q : ℕ) : ℤ) =
      F (C4Geo.centerAt (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) row col) := by
    intro row col
    have hc := C4Geo.centerAt_isCenter (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) row col
    simp only [F, dif_pos hc]
    rw [C4Pipe.lres_cast]
    obtain ⟨h0, h1⟩ := hrange (CompilerMachine.Req.atomVal R0.P (RepairOrdinary.MatrixScorePhi.value R0.cols row)
      (RepairOrdinary.MatrixScorePhi.value R0.cols col))
    rw [Int.emod_eq_of_lt (mul_nonneg (by positivity) h0) h1]
    congr 1
    rw [hP, hcl]
    exact hash_value alg I hs Cs carriers translation ⟨_, hc⟩ _
      (fun x gi hgi k => C4Geo.atomVal_center (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers) h Q psi row col x gi hgi k) p' hplen
  unfold chValH
  rw [hdr]
  push_cast
  simp only [hterm]
  rw [C4Geo.sum_table (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) F, nsmul_eq_mul]
  unfold SeedFix.thrHashSum SeedFix.hashSum
  rw [Fintype.sum_prod_type, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [F, dif_pos c.2]
  all_goals rfl

/-- **The loop over the HASH children's recovered sums prints the fixed hash's bits** (P3:2327-2336). -/
theorem hash_loop (R0 : CompilerMachine.Req.C3Req) (h Q psi : ℕ)
    (hP : R0.P = C4Geo.poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers) h Q psi) (hdr : R0.dRow = C4Geo.dRow (I.starParams n hs))
    (hcl : R0.cols = C4Geo.cols (I.starParams n hs))
    (hrange : ∀ p' : List Bool, p'.length ≤ 2 * (C4H.hashDataOf alg I hs Cs carriers).MP.t * (C4H.hashDataOf alg I hs Cs carriers).MP.ell0 → ∀ ρ : ℕ → Bool,
      0 ≤ IntExpression.eval (C4H.hV (C4H.hashDataOf alg I hs Cs carriers) p') ρ ∧
      (2 : ℤ) ^ (R0.m - 1) * IntExpression.eval (C4H.hV (C4H.hashDataOf alg I hs Cs carriers) p') ρ < 2 ^ R0.P.Q) :
    SeedFix.greedyLoop (2 * (C4H.hashDataOf alg I hs Cs carriers).MP.t * (C4H.hashDataOf alg I hs Cs carriers).MP.ell0) (fun p => (chValH R0 (C4H.hashDataOf alg I hs Cs carriers) p : ℤ)) =
      List.ofFn (FinalPass.thrHashBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers)) := by
  have hm : 0 < C4Geo.mult (I.starParams n hs) := by unfold C4Geo.mult; split_ifs <;> norm_num
  rw [greedyLoop_scaled _ _ (SeedFix.thrHashSum (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers))
    ((C4Geo.mult (I.starParams n hs) : ℤ) * 2 ^ (R0.m - 1)) (mul_pos (by exact_mod_cast hm) (by positivity))
    (fun p hp => chValH_eq alg I hs Cs carriers translation R0 h Q psi hP hdr hcl p hp (hrange p hp))]
  exact SeedFix.hashLoop_eq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers)

/-- **The HASH child family at a THR call** (C4H-a's `HashFamAt2`): the call's data `hashDataOf`, `s_h = 2t·ℓ₀`
decisions, the loop's decisions the fixed hash's bits `thrHashBits`. The side conditions are C4H's `HashEAt` and the
capacity `2t·ℓ₀ ≤ cC` (`caps_ge`). -/
def hashFamCall (A : C4Iface.AsmStage) (wa : WilliamsAlgorithm) (R0 : CompilerMachine.Req.C3Req) (h Q psi : ℕ)
    (hP : R0.P = C4Geo.poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers) h Q psi) (hdr : R0.dRow = C4Geo.dRow (I.starParams n hs))
    (hcl : R0.cols = C4Geo.cols (I.starParams n hs)) (c : C4H.HbCaps) (E4 : Cost.Envelope) (fr : Fin 7 → ℕ) (Kc Kch : ℕ)
    (hcC : 2 * (C4H.hashDataOf alg I hs Cs carriers).MP.t * (C4H.hashDataOf alg I hs Cs carriers).MP.ell0 ≤ c.cC)
    (he : C4H.HashEAt wa alg R0 (C4H.hashDataOf alg I hs Cs carriers) c fr Kc Kch (2 * (C4H.hashDataOf alg I hs Cs carriers).MP.t * (C4H.hashDataOf alg I hs Cs carriers).MP.ell0)) :
    C4H.HashFamAt2 A wa (C4Child.pre alg R0) (C4Child.post alg R0) (C4H.hb0 (C4H.hbX (C4H.hashDataOf alg I hs Cs carriers) c 0 0)) R0.P.Q
      (2 ^ R0.dRow * 2 ^ R0.dRow) (C4Child.chW R0) (2 * (C4H.hashDataOf alg I hs Cs carriers).MP.t * (C4H.hashDataOf alg I hs Cs carriers).MP.ell0)
      (List.ofFn (FinalPass.thrHashBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers))) :=
  hashFamAt2 A wa alg R0 (C4H.hashDataOf alg I hs Cs carriers) c E4 fr Kc Kch _ le_rfl hcC he _
    (hash_loop alg I hs Cs carriers translation R0 h Q psi hP hdr hcl he.2.2.2.2.1)

end Table

end

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
