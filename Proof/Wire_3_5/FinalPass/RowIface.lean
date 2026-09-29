import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.TermThrEval

/-! # Stage 8's row word as a word program: the type `RowW` (P3:2585-2630)

Stage 8 (`Term.thr8_spec`) reads THR row `(g, p)` as `Term.rowWord p r₀ as ws` (`1^p 0`, `1^{r₀} 0`, `1^{a_i} 0` per
occurrence, `1 1^{w_d} 0` per digit, a final `0`), with `r₀ = Term.thrR0 g p`, `as = Term.thrCoeffs g p`,
`ws = Term.thrWeights p` (`Term.thrRhat_eq_termOk`). `RowW` is the word program that writes it from the same entry
as `Digs.DigsW` (`Digs.DigsIn`: the front end's payloads, the selection's index, `p`, `τ₀`, `oOff`), on any layout,
changing nothing but the output stream. Main declaration: **`RowW`**. Paper quantity: the word of row `(g, p)` of
`row:thr-reported` that stage 8 evaluates. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- **The row program**: one word program per layout, with capacity `need` and cost `bound`
polynomial in the entry size. From every `DigsIn` entry it writes stage 8's word of row `(g, p)` on `Dg` and changes
nothing else. -/
structure RowW where
  prog : ∀ {ns nr : ℕ}, (Fin 4 → Fin (ns + 1)) → Fin (ns + 1) → (Fin digsK ↪ Fin nr) → WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ N, need N ≤ C * (N + 1) ^ D
  bound_le : ∀ N, bound N ≤ C * (N + 1) ^ D
  run : ∀ {ns nr : ℕ} (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (R : Fin digsK ↪ Fin nr),
    Function.Injective Pay → (∀ i, Pay i ≠ Dg) →
    ∀ (P : StarParams) {a' : ℕ}, a' ≤ 4 → ∀ (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
      (carriers : List (Stars.Carrier P.n)) (alg : DecompositionAlgorithm) (den : ℕ)
      (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den))
      (cap : ℕ) (σ : WState ns nr),
    DigsIn Pay Dg R P Cs carriers alg den g pr σ →
    need (digsN P Cs carriers alg den pr.val) ≤ cap →
    WExec cap (prog Pay Dg R) σ
      (σ.sets Dg (Term.rowWord pr.val (Term.thrR0 P Cs alg g pr.val) (Term.thrCoeffs P Cs alg g pr.val)
        (Term.thrWeights P Cs alg den pr.val)))
      (bound (digsN P Cs carriers alg den pr.val))

end NearCubicWires.WireExponent3_5.FinalPass.Digs
