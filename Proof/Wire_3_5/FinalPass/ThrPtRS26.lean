import Proof.Wire_3_5.FinalPass.ThrPtRS25

/-! # S2 (THR per point), part 40: the loops' sum is `Σ_{g,p} R̂_{g,p}` (P3:2587-2630)

`rowVal P Cs alg den D c u v j p`: row `(g, p)`'s `[R̂_{g,p}(c, u, v)]` at `g`'s index `j` (`thrEqEquiv`), `0` off
the rows. **`rsum_loops`**: `rsumThr` (the per-point sum over `ThrEq × PrimeIndex`) is the loops' sum
`Σ_{j < |𝒢|} Σ_{p ∈ primesList} rowVal j p` (primes in increasing order, `primesList_sorted`). Paper quantity:
`Σ_{g,p} R̂_{g,p}(c, u, v)` (P3:2587-2630, the per-point value). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline

section Sum
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)

/-- The number of `g`'s indices. -/
abbrev gN : ℕ :=
  ∏ i : Fin (List.ofFn Cs).length, (RepairOrdinary.ThresholdRows.children alg ((List.ofFn Cs).get i)).length

theorem card_thrEq : Fintype.card (Primitive.ThrEq P Cs alg) = gN P Cs alg := by
  rw [Fintype.card_congr (PrimAsm.Enum.thrEqEquiv P Cs alg), Fintype.card_fin]

/-- Row `(g, p)`'s `[R̂]` at `g`'s index `j`. -/
noncomputable def rowVal (D : Lists.ListData) (c : BitInput P.n) (u v : P.Errors) (j p : ℕ) : ℕ :=
  if hj : j < gN P Cs alg then
    if hp : p ∈ SupplierPrime.primesUpTo (Primitive.thrCutoff P Cs alg den) then
      (Primitive.thrRhat P Cs alg den (ListFast.listReportFast D) ((PrimAsm.Enum.thrEqEquiv P Cs alg).symm ⟨j, hj⟩)
        ⟨p, hp⟩ c u v).toNat
    else 0
  else 0

theorem rowVal_le (D : Lists.ListData) (c : BitInput P.n) (u v : P.Errors) (j p : ℕ) :
    rowVal P Cs alg den D c u v j p ≤ 1 := by
  unfold rowVal
  split_ifs
  · exact Bool.toNat_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem list_sum_primes (c : ℕ) (h : ℕ → ℕ) :
    ((PrimThrW.Joins.primesList c).map h).sum = ∑ p ∈ SupplierPrime.primesUpTo c, h p := by
  rw [PrimThrW.Joins.primesList_sorted, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]

theorem row_sum (D : Lists.ListData) (c : BitInput P.n) (u v : P.Errors) (g : Primitive.ThrEq P Cs alg) :
    ∑ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den),
        (Primitive.thrRhat P Cs alg den (ListFast.listReportFast D) g pr c u v).toNat =
      ((PrimThrW.Joins.primesList (Primitive.thrCutoff P Cs alg den)).map
        (rowVal P Cs alg den D c u v (PrimAsm.Enum.thrEqEquiv P Cs alg g))).sum := by
  rw [list_sum_primes, ← Finset.sum_attach (SupplierPrime.primesUpTo (Primitive.thrCutoff P Cs alg den)),
    Finset.univ_eq_attach]
  refine Finset.sum_congr rfl (fun pr _ => ?_)
  have hg : (PrimAsm.Enum.thrEqEquiv P Cs alg).symm
      ⟨(PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ), (PrimAsm.Enum.thrEqEquiv P Cs alg g).isLt⟩ = g := by
    rw [Fin.eta, Equiv.symm_apply_apply]
  unfold rowVal
  rw [dif_pos (PrimAsm.Enum.thrEqEquiv P Cs alg g).isLt, dif_pos pr.2, hg]

theorem sum_range_equiv (F : ℕ → ℕ) :
    ∑ g : Primitive.ThrEq P Cs alg, F (PrimAsm.Enum.thrEqEquiv P Cs alg g) =
      ∑ j ∈ Finset.range (Fintype.card (Primitive.ThrEq P Cs alg)), F j := by
  rw [card_thrEq, ← Fin.sum_univ_eq_sum_range]
  exact Equiv.sum_comp (PrimAsm.Enum.thrEqEquiv P Cs alg) (fun i => F i)

/-- **The loops' sum is the per-point sum.** -/
theorem rsum_loops (D : Lists.ListData) (c : BitInput P.n) (u v : P.Errors) :
    Seams.rsumThr P Cs alg den (ListFast.listReportFast D) c u v =
      ∑ j ∈ Finset.range (Fintype.card (Primitive.ThrEq P Cs alg)),
        ((PrimThrW.Joins.primesList (Primitive.thrCutoff P Cs alg den)).map (rowVal P Cs alg den D c u v j)).sum := by
  unfold Seams.rsumThr
  rw [Fintype.sum_prod_type]
  rw [← sum_range_equiv P Cs alg (fun j =>
    ((PrimThrW.Joins.primesList (Primitive.thrCutoff P Cs alg den)).map (rowVal P Cs alg den D c u v j)).sum)]
  exact Finset.sum_congr rfl (fun g _ => row_sum P Cs alg den D c u v g)

end Sum

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
