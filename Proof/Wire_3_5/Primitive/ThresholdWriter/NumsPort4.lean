import Proof.Wire_3_5.Primitive.ThresholdWriter.NumsPort3

/-! # W6 in port form, v4: `NumsPort4`, the THR numbers with a stated capacity `need`

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231 (as `Nums3.NumsPort3`): the THR call's numbers on ports `0 … 20`. The
numbers machine keeps its numbers in word registers filled once from the count `1^V` (port `20`), so `V` must dominate
the largest register value. Each new field names what it bounds:
* `need` dominates `K = 8(|𝒢|+1)n^D` (P3:2552-2557: "Given a fixed `D>0`, … `≤ n^{-D}`");
* the prime cutoff `(max 24 (6(E+1)(K+1)))²` (P3:2552-2553: "a polynomial-size set of polynomially bounded primes");
* `Σ_{p ≤ cut} p` (P3:2618-2620: "The exposed state alphabet has size `p = n^{O(1)}`", summed over the primes);
* `8·K·A·B_*`, whose `clog₂` is the fixed hash's list depth `J` (P3:2220-2231, filt:soft).
All are polynomial in `n + cap_T` with a degree fixed by `D` (P3:3114-3115: "All powers of `n` are fixed before a fixed
`r`").

* **`NumsPort4 alg Dexp`**: `NumsPort3` plus `need`, `Cn`, `Dn`, `need_poly` and the run hypothesis
  `need (n + cap_T) ≤ V`; ports, `TF2Ok` and the cost measure `n + V + cap_T` unchanged;
* `NumsPort4.ofV3` (a v3 machine is a v4 machine with `need = 0`).

Paper quantities of the main type: as `NumsPort2` (`|𝒢|`, `K`, the cutoff, `Σp`, `τ₀`, the fixed hash's
`M, A, B_*, J, t, e, ℓ₀, p`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.Nums4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimThrW.Joins NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimThrW.Nums3

/-- **The THR numbers on ports, v4** (the count `1^V` from the caller, `TF2Ok`, and `need (n + cap_T) ≤ V`). -/
structure NumsPort4 (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) where
  x : ℕ
  s : ℕ
  M : Machine (21 + x) s
  cost : ℕ → ℕ
  Cc : ℕ
  Dc : ℕ
  cost_poly : ∀ m, ValidatorPolynomialDomination.PolyBounded (cost m) m Cc Dc
  need : ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  need_poly : ∀ m, ValidatorPolynomialDomination.PolyBounded (need m) m Cn Dn
  run : ∀ (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (codes : List ℕ)
    (tl : List Bool) (ncar capT V : ℕ),
    1 ≤ P.n → a' ≤ 4 → (∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) → ncar ≤ 2 → 1 ≤ capT →
    TopFront2.TF2Ok Cs codes V → need (P.n + capT) ≤ V →
    ∃ J : Fin x → List Bool, (∀ j, (J j).length ≤ cost (P.n + V + capT)) ∧
      Step M (cost (P.n + V + capT)) (fun _ => 0)
        (Fin.addCases (m := 21) (n := x) (motive := fun _ => List Bool)
          (nums3InPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := 21) (n := x) (motive := fun _ => List Bool)
          (nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
            (thrNumVals P Cs alg Dexp ncar capT)) J)

end NearCubicWires.WireExponent3_5.PrimThrW.Nums4
