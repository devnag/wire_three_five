import Proof.Wire_3_5.FinalPass.ThrPtRS27

/-! # S2 (THR per point), part 42: every row meets its contract (P3:2587-2630)

For the call's tuple at the point: `RowCaps g p` (the row's capacities), `rowCostAt g p` (its step bound), `Crow j p`
(the bound at `g`'s index `j`). **`rows_ok`**: `rowStep` meets `RowStepOK` at every `g`'s index `j < |𝒢|` and every
prime `p ≤` the cutoff, with gain `rowVal j p = [R̂_{g,p}(c, u, v)]` (`rowStep_spec`, `termOk_eq`). Paper quantity:
`R̂_{g,p}(c, u, v)` computed row by row. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline

section Rows
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (D : Lists.ListData) (c : BitInput P.n)
  (u v : P.Errors)

/-- The digits' reports of row `(g, p)` at the point. -/
noncomputable def repsAt (g : Primitive.ThrEq P Cs alg) (p : ℕ) (sgn : Bool) : List ℕ :=
  tRepL D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length) (Term.thrCoeffs P Cs alg g p)
    (Term.occCorners P Cs c u v) sgn (Primitive.thrDigits P Cs alg den)

/-- Row `(g, p)`'s step bound. -/
noncomputable def rowCostAt (g : Primitive.ThrEq P Cs alg) (p : ℕ) : ℕ :=
  rowCost (DigsBody.rowWImpl.bound (Digs.digsN P Cs [] alg den p)) p (Term.thrR0 P Cs alg g p)
    (Primitive.thrOccs P Cs).length p (Primitive.thrDigits P Cs alg den) D.M
    (ListEval.capOf D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length) (Primitive.thrOccs P Cs).length)
    (Term.thrCoeffs P Cs alg g p) (Term.thrWeights P Cs alg den p) (repsAt P Cs alg den D c u v g p true)
    (repsAt P Cs alg den D c u v g p false)

/-- The step bound at `g`'s index `j` and the prime `p`. -/
noncomputable def Crow (j p : ℕ) : ℕ :=
  if hj : j < gN P Cs alg then
    if p ∈ SupplierPrime.primesUpTo (Primitive.thrCutoff P Cs alg den) then
      rowCostAt P Cs alg den D c u v ((PrimAsm.Enum.thrEqEquiv P Cs alg).symm ⟨j, hj⟩) p
    else 0
  else 0

/-- **Row `(g, p)`'s capacities.** -/
def RowCaps (cap : ℕ) (g : Primitive.ThrEq P Cs alg) (p : ℕ) : Prop :=
  DigsBody.rowWImpl.need (Digs.digsN P Cs [] alg den p) ≤ cap ∧
  popCap p (Term.thrR0 P Cs alg g p) (Primitive.thrOccs P Cs).length p (Primitive.thrDigits P Cs alg den) ≤ cap ∧
  ListEval.capOf D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length) (Primitive.thrOccs P Cs).length ≤
    cap ∧
  2 * Primitive.thrDigits P Cs alg den * (D.M + 1) + 2 * (D.M + 1) + Primitive.thrDigits P Cs alg den ≤ cap ∧
  Term.capT p (Term.thrR0 P Cs alg g p) (Primitive.thrOccs P Cs).length (Term.thrCoeffs P Cs alg g p)
    (Term.thrWeights P Cs alg den p) (repsAt P Cs alg den D c u v g p true) (repsAt P Cs alg den D c u v g p false)
    ≤ cap ∧
  (Term.rowWord p (Term.thrR0 P Cs alg g p) (Term.thrCoeffs P Cs alg g p) (Term.thrWeights P Cs alg den p)).length +
    (Primitive.thrOccs P Cs).length + Primitive.thrDigits P Cs alg den ≤ cap

theorem thrR0_lt (g : Primitive.ThrEq P Cs alg) (p : ℕ) (hp : 0 < p) : Term.thrR0 P Cs alg g p < p := by
  unfold Term.thrR0
  have h1 := Int.emod_lt_of_pos (-(Primitive.thrRealize P Cs alg g).target) (by exact_mod_cast hp : (0 : ℤ) < p)
  have h2 := Int.emod_nonneg (-(Primitive.thrRealize P Cs alg g).target) (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)
  omega

theorem coeffs_le (g : Primitive.ThrEq P Cs alg) (p : ℕ) (hp : 0 < p) : ∀ x ∈ Term.thrCoeffs P Cs alg g p, x ≤ p := by
  intro x hx
  unfold Term.thrCoeffs at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (Primitive.redCoeff_lt _ _ p hp i).le

theorem weights_le (p : ℕ) (hp : 0 < p) : ∀ x ∈ Term.thrWeights P Cs alg den p, x ≤ p := by
  intro x hx
  unfold Term.thrWeights at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (Nat.mod_lt _ hp).le

theorem rowsOf_len (L j : ℕ) : (ListEval.rowsOf D L j).length = L := by
  simp [ListEval.rowsOf]

/-- **Every row meets its contract.** -/
theorem rows_ok (cap : ℕ) (ha' : a' ≤ 4) (σB : WState 16 118)
    (hB : BaseOK σB a' (Primitive.thrDigits P Cs alg den) (Primitive.thrOccs P Cs).length)
    (hpay : ∀ i : Fin 4, σB.st (payS i) = if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else [])
    (hT5 : σB.st 9 = ListEval.levelWord D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length))
    (j : ℕ) (hj : j < gN P Cs alg) (p : ℕ) (hp : p ∈ SupplierPrime.primesUpTo (Primitive.thrCutoff P Cs alg den))
    (hcaps : RowCaps P Cs alg den D c u v cap ((PrimAsm.Enum.thrEqEquiv P Cs alg).symm ⟨j, hj⟩) p) :
    RowStepOK cap σB (Primitive.thrOccs P Cs).length (Primitive.thrDigits P Cs alg den) (Term.occCorners P Cs c u v) j
      (rowVal P Cs alg den D c u v j p) (Crow P Cs alg den D c u v j p) p := by
  intro t hR hgi htp hacc
  obtain ⟨g, hg⟩ : ∃ g, g = (PrimAsm.Enum.thrEqEquiv P Cs alg).symm ⟨j, hj⟩ := ⟨_, rfl⟩
  rw [← hg] at hcaps
  obtain ⟨hcW, hc1, hc2, hc3, hc4, hc6⟩ := hcaps
  have hpos : 0 < p := (SupplierPrime.mem_primesUpTo.mp hp).1.pos
  have hF : rowVal P Cs alg den D c u v j p =
      (Term.thrTermOk p (Term.thrR0 P Cs alg g p) (Term.occCorners P Cs c u v) (Term.thrCoeffs P Cs alg g p)
        (Term.thrWeights P Cs alg den p) (repsAt P Cs alg den D c u v g p true)
        (repsAt P Cs alg den D c u v g p false)).toNat := by
    unfold rowVal repsAt
    rw [dif_pos hj, dif_pos hp, ← hg, ← termOk_eq P Cs alg den D g ⟨p, hp⟩ c u v]
  have hC : Crow P Cs alg den D c u v j p = rowCostAt P Cs alg den D c u v g p := by
    unfold Crow
    rw [dif_pos hj, if_pos hp, ← hg]
  rw [hF, hC]
  exact rowStep_spec cap P ha' Cs alg den g ⟨p, hp⟩ σB (Primitive.thrDigits P Cs alg den) (Primitive.thrOccs P Cs).length
    hB hpay rfl D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length) hT5
    (fun j' _ => rowsOf_len D _ j') (Term.thrR0 P Cs alg g p) (Term.thrCoeffs P Cs alg g p)
    (Term.thrWeights P Cs alg den p) rfl rfl rfl (by simp [Term.thrCoeffs]) (thrR0_lt P Cs alg g p hpos) p
    (coeffs_le P Cs alg g p hpos) (weights_le P Cs alg den p hpos) (Term.occCorners P Cs c u v)
    (occCorners_length P Cs c u v) t hR (by rw [hg, Equiv.apply_symm_apply]; exact hgi) htp hcW hc1 hc2 hc3 hc4 hacc
    hc6

end Rows

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
