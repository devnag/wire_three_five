import Proof.Wire_3_5.FinalPass.ThrPtRS24

/-! # S2 (THR per point), part 39: the machine's reports are the paper's `t^±_d` (P3:2596-2630)

**`popBits_occ`**: the population bits of the occurrences' corner word are `Z^±_i` (`occPlus`, `occMinus`).
**`popZ_report`**: the report machine's value on the padded population of digit `d` is the list's report of the
digit list `thrDigitPop g p d ±` (P3:2598-2599, 1472-1477). **`tRepL_eq`**: the digits' reports are `thrReps`.
**`termOk_eq`**: stage 8's factor at row `(g, p)` is `R̂_{g,p}(c, u, v)` (`thrRhat`, through `thrRhat_eq_termOk`).
Paper quantity: `R̂_{g,p}(c, u, v)` at the list report `listReportFast D`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop NearCubicWires.SupplierPipeline

theorem map_eq_ofFn {α β : Type} (l : List α) (f : α → β) : l.map f = List.ofFn fun i : Fin l.length => f l[i] :=
  List.ext_getElem (by simp) (fun i h1 h2 => by simp)

section Row
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)

theorem popBits_occ (sgn : Bool) (c : BitInput P.n) (u v : P.Errors) :
    popBits sgn (Term.occCorners P Cs c u v) =
      List.ofFn (if sgn then Primitive.occPlus (Primitive.thrOccs P Cs) c (P.errorVector P.leftBlock u)
          (P.errorVector P.rightBlock v)
        else Primitive.occMinus (Primitive.thrOccs P Cs) c (P.errorVector P.leftBlock u)
          (P.errorVector P.rightBlock v)) := by
  have h := popBits_cornerWord ((Primitive.thrOccs P Cs).map fun o => o.gate.eval) c (P.errorVector P.leftBlock u)
    (P.errorVector P.rightBlock v)
  unfold Term.occCorners
  cases sgn
  · rw [h.2, List.map_map, map_eq_ofFn]
    rfl
  · rw [h.1, List.map_map, map_eq_ofFn]
    rfl

theorem occCorners_length (c : BitInput P.n) (u v : P.Errors) :
    (Term.occCorners P Cs c u v).length = 4 * (Primitive.thrOccs P Cs).length := by
  unfold Term.occCorners
  rw [cw_len, List.length_map]

/-- **The padded population's report is the digit list's report.** -/
theorem popZ_report (D : Lists.ListData) (g : Primitive.ThrEq P Cs alg)
    (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) (d : Fin (Primitive.thrDigits P Cs alg den))
    (sgn : Bool) (c : BitInput P.n) (u v : P.Errors) :
    ListEval.reportRef D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length)
        (popZ sgn d (Term.thrCoeffs P Cs alg g pr.val) (Term.occCorners P Cs c u v)) =
      ListFast.listReportFast D (Primitive.thrDigitPop P Cs alg den g pr d sgn c u v) := by
  have hpl : (popZ sgn d (Term.thrCoeffs P Cs alg g pr.val) (Term.occCorners P Cs c u v)).length =
      (Primitive.thrOccs P Cs).length := by
    rw [popZ_length, Term.thrCoeffs, List.length_ofFn]
  rw [ListEval.reportRef_eq_fast D _ _ hpl]
  unfold popZ
  rw [fast_pad]
  congr 1
  unfold Term.thrCoeffs
  rw [selB_ofFn sgn d _ _ _ _ (occCorners_length P Cs c u v) (popBits_occ P Cs sgn c u v)]
  unfold Primitive.thrDigitPop Primitive.digitPop Primitive.digitOf
  congr 1
  funext i
  rw [rep_mod2]

/-- **The digits' reports are `thrReps`.** -/
theorem tRepL_eq (D : Lists.ListData) (g : Primitive.ThrEq P Cs alg)
    (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) (sgn : Bool) (c : BitInput P.n)
    (u v : P.Errors) :
    tRepL D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length) (Term.thrCoeffs P Cs alg g pr.val)
        (Term.occCorners P Cs c u v) sgn (Primitive.thrDigits P Cs alg den) =
      Term.thrReps P Cs alg den (ListFast.listReportFast D) g pr sgn c u v := by
  unfold tRepL Term.thrReps
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact popZ_report P Cs alg den D g pr ⟨i, by simpa using h1⟩ sgn c u v

/-- **Stage 8's factor at row `(g, p)` is `R̂_{g,p}(c, u, v)`.** -/
theorem termOk_eq (D : Lists.ListData) (g : Primitive.ThrEq P Cs alg)
    (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) (c : BitInput P.n) (u v : P.Errors) :
    Term.thrTermOk pr.val (Term.thrR0 P Cs alg g pr.val) (Term.occCorners P Cs c u v)
        (Term.thrCoeffs P Cs alg g pr.val) (Term.thrWeights P Cs alg den pr.val)
        (tRepL D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length) (Term.thrCoeffs P Cs alg g pr.val)
          (Term.occCorners P Cs c u v) true (Primitive.thrDigits P Cs alg den))
        (tRepL D.M D.J D.W (ListEval.rowsOf D (Primitive.thrOccs P Cs).length) (Term.thrCoeffs P Cs alg g pr.val)
          (Term.occCorners P Cs c u v) false (Primitive.thrDigits P Cs alg den)) =
      Primitive.thrRhat P Cs alg den (ListFast.listReportFast D) g pr c u v := by
  rw [tRepL_eq, tRepL_eq, Term.thrRhat_eq_termOk]

end Row

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
