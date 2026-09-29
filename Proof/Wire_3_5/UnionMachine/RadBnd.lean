import Proof.Wire_3_5.UnionMachine.RadDigL

/-! # RADIX, stage 5a (10): the digit populations' sizes and labels (P3:2596-2599)

Row `(g, p)`'s digit `d` population `gis_d = thrDigGis … d` holds `v_{i,d} ∈ {0, 1}` copies (radix `b₀ = 2`) of the
pool index `oOff + i` of occurrence `i`, so `|gis_d| ≤ |thrOccs| ≤ G := |thrPool|` and every index is `< G`; each
index carries four corner labels `(4·row + k)·G + gi < (4·row + 4)·G`. These are the Route-B capacity statement's
digit conditions (`RadSpec.RadCapsStmt`) and the truncation's `L_d ≤ G`.

* `thrPool_length` (`|thrPool| = oOff + |thrOccs|`), `labsOf_length`, `labsOf_le`;
* **`thrDigGis_lt`**, **`thrDigGis_length_le`**, **`thrDigs_caps`**.

Paper quantity of the main type: the digit populations `v_{i,d}` of row `(g, p)` and their labels (P3:2598-2599). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadBnd
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.SupplierPipeline

theorem labsOf_length (G row : ℕ) (gis : List ℕ) :
    (CompilerMachine.Pool.labsOf G row gis).length = 4 * gis.length := by
  unfold CompilerMachine.Pool.labsOf
  induction gis with
  | nil => rfl
  | cons gi gis ih => simp [List.flatMap_cons, ih]; ring

theorem labsOf_le (G row : ℕ) (gis : List ℕ) (h : ∀ gi ∈ gis, gi < G) :
    ∀ lab ∈ CompilerMachine.Pool.labsOf G row gis, lab ≤ (4 * row + 4) * G := by
  intro lab hlab
  unfold CompilerMachine.Pool.labsOf at hlab
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hlab
  obtain ⟨gi, hgi, k, hk, rfl⟩ := hlab
  have h1 := h gi hgi
  unfold CompilerMachine.Pool.poolIndex
  have h2 : (4 * row + k) * G + G ≤ (4 * row + 4) * G := by nlinarith
  omega

section Thr
variable (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Carrier P.n)) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)

theorem thrPool_length :
    (thrPool P Cs carriers).length = thrOff P Cs carriers + (thrOccs P Cs).length := by
  have hoff : thrOff P Cs carriers = ((carriers.map FinalPass.Corner.maskGates).map List.length).sum := by
    unfold thrOff sliceOff thrSlices
    rw [List.take_left' (by simp)]
  rw [hoff]
  unfold thrPool thrSlices
  simp [List.length_flatten]

theorem thrDigGis_lt (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (d : Fin (thrDigits P Cs algorithm den)) :
    ∀ gi ∈ thrDigGis P Cs carriers algorithm den g pr d, gi < (thrPool P Cs carriers).length := by
  intro gi hgi
  unfold thrDigGis at hgi
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_replicate] at hgi
  obtain ⟨i, -, rfl⟩ := hgi
  rw [thrPool_length]
  have := i.isLt
  omega

theorem thrDigGis_length_le (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (d : Fin (thrDigits P Cs algorithm den)) :
    (thrDigGis P Cs carriers algorithm den g pr d).length ≤ (thrPool P Cs carriers).length := by
  have hle : (thrDigGis P Cs carriers algorithm den g pr d).length ≤ (thrOccs P Cs).length := by
    unfold thrDigGis
    rw [List.length_flatMap]
    have hb : ∀ i : Fin (thrOccs P Cs).length, (List.replicate (digitOf (thrOccs P Cs) (thrRealize P Cs algorithm g)
        pr.val 2 (thrDigits P Cs algorithm den) i d) (thrOff P Cs carriers + i)).length ≤ 1 := by
      intro i
      rw [List.length_replicate]
      unfold digitOf
      have := Nat.mod_lt (redCoeff (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val i / 2 ^ (d : ℕ)) (by norm_num : 2 > 0)
      omega
    calc ((List.finRange (thrOccs P Cs).length).map fun i => (List.replicate (digitOf (thrOccs P Cs)
            (thrRealize P Cs algorithm g) pr.val 2 (thrDigits P Cs algorithm den) i d)
            (thrOff P Cs carriers + i)).length).sum
        ≤ ((List.finRange (thrOccs P Cs).length).map fun _ => 1).sum :=
          List.sum_le_sum (fun i _ => hb i)
      _ = (thrOccs P Cs).length := by simp
  rw [thrPool_length]
  omega

/-- **The RADIX row's digit conditions** (Route B's `RadCapsStmt` at `Lmax = G = |thrPool|`, `Mlab = (4row+4)G`):
every digit has at most `G` occurrences, exactly four labels per occurrence, labels at most `(4·row + 4)·G`. -/
theorem thrDigs_caps (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (row : ℕ) :
    ∀ dg ∈ thrDigs P Cs carriers algorithm den g pr (thrPool P Cs carriers).length row,
      dg.1 ≤ (thrPool P Cs carriers).length ∧ dg.2.length = 4 * dg.1 ∧
        ∀ lab ∈ dg.2, lab ≤ (4 * row + 4) * (thrPool P Cs carriers).length := by
  intro dg hdg
  unfold thrDigs at hdg
  rw [List.mem_ofFn] at hdg
  obtain ⟨d, rfl⟩ := hdg
  exact ⟨thrDigGis_length_le P Cs carriers algorithm den g pr d, labsOf_length _ _ _,
    labsOf_le _ _ _ (thrDigGis_lt P Cs carriers algorithm den g pr d)⟩

end Thr

end NearCubicWires.WireExponent3_5.UnionMachine.RadBnd
