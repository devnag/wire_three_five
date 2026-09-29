import Proof.Wire_3_5.FinalPass.Greedy

/-! # Final pass: the threshold-top printed value at the bit level (P3:2600-2630, 3131-3135, 3170-3175)

Realizes the computable form of the `THR` printed value of `lem:primitive`: the fixed count hash of `filt:soft` found by
the greedy method of conditional expectations over the rational objective `𝒰(h) = E_x a(x)H_h(x)` (P3:2238-2251; the
auxiliary filter at the bit level, the majorant's lists at the bit-level labels), the digit lists' reports by following
the reconstructed state, the reported modular rows `R̂_{g,p}` at the reported residues (row:thr-reported), the actual
regular masks, and the rational average over columns, seeds and sampled pairs (P3:2739-2741, 3170-3175).

Paper quantities: the auxiliary filter's acceptance `auxQ` (`a(x)`), the majorant `HQ` (`H_h(x)` at a seed code), the
objective `objQ` (`𝒰`), the fixed hash `thrHashBits`, the digit lists' reporter `thrReportBits`, and the printed rational
`thrValueBits`. Results: `auxMean_eq`, `H_seedCode_eq`, `softObjective_eq`, **`thrHash_eq`** (the primitive's fixed hash is
the code of the rational greedy's bits), **`thrReport_eq_bits`**, and **`thrValueBits_eq`** (`thrValueBits = thrValue`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive

section ThrHash
variable (P : StarParams) (σ : P.Translation) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Carrier P.n)) (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
  (e t J : ℕ)

/-- The auxiliary filter's acceptance mean `a(x)` at a point, in `ℚ`, with the bit-level filter. -/
def auxQ (pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) : ℚ :=
  qMean fun e' : GapSeed (thrAux P carriers FP e) =>
    bitQ (filterBits (thrAux P carriers FP e) e' (thrZres P carriers pt.1.1 pt.2.1 pt.2.2))

/-- One population's majorant term `c_J + Σ_{j<J} δ_j^{2t}/W_j^{2t}`, in `ℚ`. -/
def termQ (D : ListData) (t : ℕ) (Z : List Bool) : ℚ :=
  (D.levelCount D.J Z : ℚ) + ∑ j ∈ Finset.range D.J, (D.levelDelta j Z : ℚ) ^ (2 * t) / (D.W j : ℚ) ^ (2 * t)

/-- **The majorant `H_h(x)` at a seed code**, summed over the digit populations of all rows (P3:2141-2144). -/
def HQ (s : Fin (2 * (thrMajorant P Cs carriers FP algorithm den e t J).t *
      (thrMajorant P Cs carriers FP algorithm den e t J).ell0) → Bool)
    (pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) : ℚ :=
  ∑ k : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den) × Fin (thrDigits P Cs algorithm den) × Bool,
    termQ (MajorantBits.dataBits (thrMajorant P Cs carriers FP algorithm den e t J) s) t
      (thrDigitPop P Cs algorithm den k.1 k.2.1 k.2.2.1 k.2.2.2 pt.1.1 pt.2.1 pt.2.2)

/-- **The objective** `𝒰 = E_x a(x)H_h(x)` at a seed code, in `ℚ` (P3:2239-2241). -/
def objQ (s : Fin (2 * (thrMajorant P Cs carriers FP algorithm den e t J).t *
      (thrMajorant P Cs carriers FP algorithm den e t J).ell0) → Bool) : ℚ :=
  qMean fun pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors) =>
    auxQ P σ carriers FP e pt * HQ P σ Cs carriers FP algorithm den e t J s pt

/-- **The fixed hash's bits**: the rational greedy's choice (P3:2238-2251). -/
def thrHashBits : Fin (2 * (thrMajorant P Cs carriers FP algorithm den e t J).t *
    (thrMajorant P Cs carriers FP algorithm den e t J).ell0) → Bool :=
  greedyQ _ (objQ P σ Cs carriers FP algorithm den e t J)

/-- **The digit lists' reporter at the fixed hash**, by following the reconstructed state. -/
def thrReportBits : List Bool → ℕ :=
  ListFast.listReportFast
    (MajorantBits.dataBits (thrMajorant P Cs carriers FP algorithm den e t J) (thrHashBits P σ Cs carriers FP algorithm den e t J))

theorem auxMean_eq (pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) :
    auxMean (fun e' (x : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) =>
        gapFilter (thrAux P carriers FP e) e' (thrZres P carriers x.1.1 x.2.1 x.2.2)) pt =
      ((auxQ P σ carriers FP e pt : ℚ) : ℝ) := by
  unfold auxMean auxQ
  rw [← uMean_cast]
  congr 1
  funext e'
  simp only [bitQ_cast, gapFilter_eq_filterBits]

theorem H_seedCode_eq (s : Fin (2 * (thrMajorant P Cs carriers FP algorithm den e t J).t *
      (thrMajorant P Cs carriers FP algorithm den e t J).ell0) → Bool)
    (pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) :
    (thrMajorant P Cs carriers FP algorithm den e t J).H (thrPops P Cs algorithm den pt.1.1 pt.2.1 pt.2.2)
        ((thrMajorant P Cs carriers FP algorithm den e t J).seedCode s) =
      ((HQ P σ Cs carriers FP algorithm den e t J s pt : ℚ) : ℝ) := by
  unfold MajorantParams.H HQ thrPops
  rw [MajorantBits.data_seedCode, List.map_map, Finset.sum_map_toList]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, termQ]
  push_cast
  rfl

theorem softObjective_eq (s : Fin (2 * (thrMajorant P Cs carriers FP algorithm den e t J).t *
      (thrMajorant P Cs carriers FP algorithm den e t J).ell0) → Bool) :
    softObjective
        (fun e' (x : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) =>
          gapFilter (thrAux P carriers FP e) e' (thrZres P carriers x.1.1 x.2.1 x.2.2))
        (fun h (x : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) =>
          (thrMajorant P Cs carriers FP algorithm den e t J).H (thrPops P Cs algorithm den x.1.1 x.2.1 x.2.2) h)
        ((thrMajorant P Cs carriers FP algorithm den e t J).seedCode s) =
      ((objQ P σ Cs carriers FP algorithm den e t J s : ℚ) : ℝ) := by
  unfold softObjective objQ
  rw [← uMean_cast]
  congr 1
  funext pt
  simp only []
  rw [auxMean_eq, H_seedCode_eq]
  push_cast
  rfl

/-- **The primitive's fixed hash is the code of the rational greedy's bits.** -/
theorem thrHash_eq :
    thrHash P σ Cs carriers FP algorithm den e t J =
      (thrMajorant P Cs carriers FP algorithm den e t J).seedCode (thrHashBits P σ Cs carriers FP algorithm den e t J) := by
  unfold thrHash thrHashBits
  congr 1
  rw [← greedy_cast]
  congr 1
  funext s
  exact softObjective_eq P σ Cs carriers FP algorithm den e t J s

/-- **The digit lists' reports at the fixed hash are the bit-level fast reports.** -/
theorem thrReport_eq_bits :
    thrReport P σ Cs carriers FP algorithm den e t J = thrReportBits P σ Cs carriers FP algorithm den e t J := by
  funext Z
  unfold thrReport thrReportBits
  rw [thrHash_eq, MajorantBits.data_seedCode, ListFast.listReport_eq_fast]

end ThrHash

/-! ## The printed rational -/

section Value
variable (P : StarParams) (σ : P.Translation) {a : ℕ} {N Q : ℕ} (eqv : P.Errors ≃ Fin N)
  (S : Fin Q → Fin N × Fin N)

/-- **The THR printed rational, computable**: `(Σ_zΣ_eΣ_ℓΣ_{g,p}(1/|𝒫|)M·R̂_{g,p})/(|Z|·|E|·Q)` with the bit-level mask
and a computable reporter. -/
def thrValueBits (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) : ℚ :=
  (∑ c : {c // P.IsCenter σ c}, ∑ e : GapSeed FP, ∑ l : Fin Q,
      ∑ gp : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den),
        (1 / (Fintype.card (PrimeIndex (thrCutoff P Cs algorithm den)) : ℚ)) *
          (bitQ (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))) *
            bitQ (thrRhat P Cs algorithm den report gp.1 gp.2 c.1 (eqv.symm (S l).1) (eqv.symm (S l).2)))) /
    (Fintype.card {c // P.IsCenter σ c} * Fintype.card (GapSeed FP) * Q)

theorem thrValueBits_eq (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) :
    thrValueBits P σ eqv S Cs carriers FP algorithm den report =
      thrValue P σ eqv S Cs carriers FP algorithm den report := by
  unfold thrValueBits thrValue
  simp only [symMask_eq_maskBits]

end Value

end NearCubicWires.WireExponent3_5.FinalPass
