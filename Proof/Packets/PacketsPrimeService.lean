import Proof.Packets.PacketsGlueMetaMul
import Proof.Packets.PacketsPrimeCount

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
noncomputable section

/-! ## The prime index is the count of smaller primes -/

/-- The increasing enumeration: the index of the prime `x ≤ c` is the number of primes below it. -/
theorem idx_eq_count (c : ℕ) (x : PrimeIndex c) :
    ((primeIndexFinEquiv c) x).val = PrimeCount.pc (x.val - 1) := by
  have he : (primeIndexFinEquiv c) x =
      (Fintype.orderIsoFinOfCardEq (PrimeIndex c) (rfl : Fintype.card (PrimeIndex c) = _)).symm x := rfl
  rw [he]
  set e := Fintype.orderIsoFinOfCardEq (PrimeIndex c) (rfl : Fintype.card (PrimeIndex c) = _)
  have h1 : (Finset.univ.filter (fun y : PrimeIndex c => y < x)) =
      (Finset.Iio (e.symm x)).map e.toEquiv.toEmbedding := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Iio]
    constructor
    · intro hy
      refine ⟨e.symm y, e.symm.lt_iff_lt.mpr hy, ?_⟩
      simp
    · rintro ⟨i, hi, rfl⟩
      have h := e.lt_iff_lt.mpr hi
      simpa using h
  have h2 : (Finset.univ.filter (fun y : PrimeIndex c => y < x)).card = (e.symm x).val := by
    rw [h1, Finset.card_map, Fin.card_Iio]
  have hx := mem_primesUpTo.mp x.property
  have hx2 := hx.1.two_le
  have hmap : (Finset.univ.filter (fun y : PrimeIndex c => y < x)).map (Function.Embedding.subtype _) =
      primesUpTo (x.val - 1) := by
    ext q
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' := mem_primesUpTo.mp y.property
      have hlt : y.val < x.val := hy
      exact mem_primesUpTo.mpr ⟨hy'.1, by omega⟩
    · intro hq
      have hq' := mem_primesUpTo.mp hq
      refine ⟨⟨q, mem_primesUpTo.mpr ⟨hq'.1, by omega⟩⟩, ?_, rfl⟩
      show q < x.val
      omega
  have h3 : (Finset.univ.filter (fun y : PrimeIndex c => y < x)).card = PrimeCount.pc (x.val - 1) := by
    rw [PrimeCount.pc_eq, ← hmap, Finset.card_map]
  omega

/-- A prime `v ≤ c` sits at index `π (v - 1)`. -/
theorem primeAt_of_count (c v : ℕ) (hv : v.Prime) (hvc : v ≤ c) :
    primeAt c (PrimeCount.pc (v - 1)) = v := by
  have hx := idx_eq_count c ⟨v, mem_primesUpTo.mpr ⟨hv, hvc⟩⟩
  have hlt : PrimeCount.pc (v - 1) < Fintype.card (PrimeIndex c) := by
    rw [← hx]; exact ((primeIndexFinEquiv c) ⟨v, mem_primesUpTo.mpr ⟨hv, hvc⟩⟩).isLt
  unfold primeAt
  rw [dif_pos hlt]
  have e : (⟨PrimeCount.pc (v - 1), hlt⟩ : Fin (Fintype.card (PrimeIndex c))) =
      (primeIndexFinEquiv c) ⟨v, mem_primesUpTo.mpr ⟨hv, hvc⟩⟩ := Fin.ext hx.symm
  rw [e, Equiv.symm_apply_apply]

/-- The first prime is `2`. -/
theorem primeAt_zero (c : ℕ) (hc : 2 ≤ c) : primeAt c 0 = 2 := by
  have h := primeAt_of_count c 2 Nat.prime_two hc
  rwa [show PrimeCount.pc (2 - 1) = 0 from PrimeCount.pc_one] at h

/-! ## `primeSum` -/

/-! ## `primeOfIndex` -/

/-! ## `nextPrime` -/



end
end NearCubicWires.PacketsGlue.RequestMeta

