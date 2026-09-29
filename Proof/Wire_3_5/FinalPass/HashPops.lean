import Proof.Wire_3_5.FinalPass.HashShape
import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Proof.Wire_3_5.Primitive.Writers.BShape1

/-! # The HASH call's populations and printed range (`filt:soft`, P3:2253-2293)

The populations of a HASH call (`hashPopsOf`, one per `(g, p, d, ±)`) have at most `M` gates each (binary digits: at
most one copy of each occurrence), every gate below `|𝒢|` (the occurrence slice follows the carriers' prefix), and
their stream `popsWord` has at most `|pops|·(3 + M(|𝒢|+1)) + 1` bits. The printed objective `hashTermsM` at every
prefix of at most `2t·ℓ₀` bits has value in `[0, N²·n_E·|pops|·2^{2tℓ₀}·Π_j W_j^{2t}·(M + J(3M)^{2t})]` at every
assignment (the column bound filt:column-bound, P3:2291-2293, summed over the rows, seeds and populations).

* `hashGis_length_le`, `hashGis_lt`, **`mem_hashPops`**, `hashPops_length`, **`popsWord_le`**;
* **`hashTermsM_range`** (generic in the majorant's data).

Paper quantities of the main types: the populations' sizes and the printed column value's range. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.WireExponent3_5.Filters NearCubicWires.SupplierPipeline

section Pops
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
  (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))

theorem pool_length : (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length =
    2 * (carriers.map List.length).sum + (thrOccs (I.starParams n hs) Cs).length := by
  unfold PrimAsm.Records.thrPool PrimAsm.Records.thrSlices
  rw [List.flatten_append, List.length_append, PrimAsm.Records.prefix_length]
  simp
  rfl

/-- A population has at most one copy of each occurrence (binary digits). -/
theorem hashGis_length_le (g : ThrEq (I.starParams n hs) Cs alg)
    (pr : PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)))
    (d : Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))) :
    (PrimT.C4H.hashGis alg I hs Cs carriers g pr d).length ≤ (thrOccs (I.starParams n hs) Cs).length := by
  unfold PrimT.C4H.hashGis
  rw [List.length_flatMap]
  have h := PrimAsm.BShape.sum_map_le_card (List.finRange (thrOccs (I.starParams n hs) Cs).length)
    (fun i => (List.replicate (digitOf (thrOccs (I.starParams n hs) Cs) (thrRealize (I.starParams n hs) Cs alg g) pr.val
      2 (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) i d) (PrimT.C4H.hashOOff carriers + i.val)).length)
    1 (fun i _ => by
      rw [List.length_replicate]; unfold digitOf
      have := Nat.mod_lt (redCoeff (thrOccs (I.starParams n hs) Cs) (thrRealize (I.starParams n hs) Cs alg g) pr.val i /
        2 ^ (d : ℕ)) (show 2 > 0 by norm_num)
      omega)
  rw [List.length_finRange, Nat.mul_one] at h
  exact h

/-- Every gate of a population is a pool gate. -/
theorem hashGis_lt (g : ThrEq (I.starParams n hs) Cs alg)
    (pr : PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)))
    (d : Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))) :
    ∀ gi ∈ PrimT.C4H.hashGis alg I hs Cs carriers g pr d,
      gi < (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length := by
  intro gi hgi
  unfold PrimT.C4H.hashGis at hgi
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hgi
  rw [List.eq_of_mem_replicate hi, pool_length I hs Cs carriers]
  have hoff : PrimT.C4H.hashOOff carriers = 2 * (carriers.map List.length).sum := PrimAsm.Records.prefix_length carriers
  have := i.isLt
  omega

/-- **The populations**: at most `M` gates each, every gate below `|𝒢|`. -/
theorem mem_hashPops : ∀ pop ∈ PrimT.C4H.hashPopsOf alg I hs Cs carriers,
    pop.2.length ≤ (thrOccs (I.starParams n hs) Cs).length ∧
      ∀ gi ∈ pop.2, gi < (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers).length := by
  intro pop hp
  unfold PrimT.C4H.hashPopsOf at hp
  simp only [List.mem_flatMap, List.mem_map] at hp
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hp
  exact ⟨hashGis_length_le alg I hs Cs carriers _ _ _, hashGis_lt alg I hs Cs carriers _ _ _⟩

/-- The population count is `A`. -/
theorem hashPops_length : (PrimT.C4H.hashPopsOf alg I hs Cs carriers).length = thrCallA alg I hs Cs := by
  unfold PrimT.C4H.hashPopsOf thrCallA
  simp [List.length_flatMap, Fintype.card_prod]

end Pops

/-- **The populations' stream** has at most `|pops|·(3 + M(G+1)) + 1` bits. -/
theorem popsWord_le (pops : List (Bool × List ℕ)) (M G : ℕ)
    (h : ∀ pop ∈ pops, pop.2.length ≤ M ∧ ∀ gi ∈ pop.2, gi < G) :
    (PrimT.HbM.popsWord pops).length ≤ pops.length * (3 + M * (G + 1)) + 1 := by
  unfold PrimT.HbM.popsWord
  rw [List.length_append, List.length_flatMap, List.length_singleton]
  have hs := PrimAsm.BShape.sum_map_le_card pops (fun pop => (PrimT.HbM.popRec pop).length) (3 + M * (G + 1))
    (fun pop hp => by
      unfold PrimT.HbM.popRec
      rw [List.length_append, List.length_append, List.length_flatMap, List.length_singleton]
      have h2 := PrimAsm.BShape.sum_map_le_card pop.2 (fun gi => (PrimT.HbM.elemW gi).length) (G + 1)
        (fun gi hgi => by rw [PrimT.HbM.elemW_length]; have := (h pop hp).2 gi hgi; omega)
      have h3 := Nat.mul_le_mul_right (G + 1) (h pop hp).1
      simp only [List.length_cons, List.length_nil]
      omega)
  omega

theorem bitZ_nonneg (b : Bool) : 0 ≤ bitZ b := by cases b <;> simp [bitZ]

theorem bitZ_le_one (b : Bool) : bitZ b ≤ 1 := by cases b <;> simp [bitZ]

/-- **The printed objective's range** at every prefix of at most `2t·ℓ₀` bits and every assignment. -/
theorem hashTermsM_range (MP : MajorantParams) (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ))
    (plen pre : ℕ) (ρ : ℕ → Bool) (ht : 1 ≤ MP.t) (hplen : plen ≤ 2 * MP.t * MP.ell0)
    (hL : ∀ pop ∈ pops, pop.2.length ≤ MP.M) :
    0 ≤ IntExpression.eval (PrimT.HashB.hashTermsM MP G N nE Fs pops plen pre) ρ ∧
      IntExpression.eval (PrimT.HashB.hashTermsM MP G N nE Fs pops plen pre) ρ ≤
        ((N ^ 2 * (nE * pops.length) : ℕ) : ℤ) *
          (2 ^ (2 * MP.t * MP.ell0) * ((prodW MP : ℤ) * (MP.M + MP.J * (3 * MP.M) ^ (2 * MP.t)))) := by
  have hL' : ∀ pop ∈ pops, pop.2.length ≤ 2 ^ MP.ell0 := fun pop hp => (hL pop hp).trans MP.M_le_two_pow
  rw [PrimT.HashB.hashTermsM_eval MP G N nE Fs pops plen pre (fun q e => F2Poly.eval (Fs.getD (q * nE + e) []) ρ) ρ ht
    hplen hL' (fun _ _ _ _ => rfl)]
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℤ, Bd = 2 ^ (2 * MP.t * MP.ell0) *
      ((prodW MP : ℤ) * (MP.M + MP.J * (3 * MP.M) ^ (2 * MP.t))) := ⟨_, rfl⟩
  rw [← hBd]
  have hW0 : (0 : ℤ) ≤ (prodW MP : ℤ) * (MP.M + MP.J * (3 * MP.M) ^ (2 * MP.t)) := by positivity
  have hE : ∀ q, ∀ pop ∈ pops, 0 ≤ hashElimZ MP (PrimT.HashB.popAt ρ G q pop) plen pre ∧
      hashElimZ MP (PrimT.HashB.popAt ρ G q pop) plen pre ≤ Bd := by
    intro q pop hp
    have hZ : (PrimT.HashB.popAt ρ G q pop).length ≤ MP.M := by
      rw [PrimT.HashB.popAt_length]; exact hL pop hp
    refine ⟨hashElimZ_nonneg MP _ hZ plen pre hplen, (hashElimZ_le MP _ hZ plen pre hplen).trans ?_⟩
    rw [hBd]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) hW0
  have hS : ∀ q, 0 ≤ (pops.map fun pop => hashElimZ MP (PrimT.HashB.popAt ρ G q pop) plen pre).sum ∧
      (pops.map fun pop => hashElimZ MP (PrimT.HashB.popAt ρ G q pop) plen pre).sum ≤ (pops.length : ℤ) * Bd := by
    intro q
    constructor
    · exact List.sum_nonneg fun x hx => by
        obtain ⟨pop, hp, rfl⟩ := List.mem_map.mp hx
        exact (hE q pop hp).1
    · have := List.sum_le_card_nsmul (pops.map fun pop => hashElimZ MP (PrimT.HashB.popAt ρ G q pop) plen pre) Bd
        (fun x hx => by
          obtain ⟨pop, hp, rfl⟩ := List.mem_map.mp hx
          exact (hE q pop hp).2)
      rwa [List.length_map, nsmul_eq_mul] at this
  have hT : ∀ q e, 0 ≤ bitZ (F2Poly.eval (Fs.getD (q * nE + e) []) ρ) *
      (pops.map fun pop => hashElimZ MP (PrimT.HashB.popAt ρ G q pop) plen pre).sum ∧
      bitZ (F2Poly.eval (Fs.getD (q * nE + e) []) ρ) *
        (pops.map fun pop => hashElimZ MP (PrimT.HashB.popAt ρ G q pop) plen pre).sum ≤ (pops.length : ℤ) * Bd := by
    intro q e
    have h0 := bitZ_nonneg (F2Poly.eval (Fs.getD (q * nE + e) []) ρ)
    have h1 := bitZ_le_one (F2Poly.eval (Fs.getD (q * nE + e) []) ρ)
    obtain ⟨hs0, hs1⟩ := hS q
    exact ⟨mul_nonneg h0 hs0, by nlinarith⟩
  constructor
  · exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun e _ => (hT q e).1
  · calc ∑ q ∈ Finset.range (N ^ 2), ∑ e ∈ Finset.range nE, bitZ (F2Poly.eval (Fs.getD (q * nE + e) []) ρ) *
          (pops.map fun pop => hashElimZ MP (PrimT.HashB.popAt ρ G q pop) plen pre).sum
        ≤ ∑ _q ∈ Finset.range (N ^ 2), ∑ _e ∈ Finset.range nE, (pops.length : ℤ) * Bd :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun e _ => (hT q e).2
      _ = ((N ^ 2 * (nE * pops.length) : ℕ) : ℤ) * Bd := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
          push_cast; ring

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
