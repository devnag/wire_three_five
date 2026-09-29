import Proof.Wire_3_5.FinalPass.SdSeedL

/-! # S4 (the seeds phase), part 22: the seed loop's sum is the final pass's numerator (P3:3044-3048)

The seed loop adds `Σ_{e ∈ es} Gs e` (`seedLoop_spec`); at the call's sample (the halves' error vectors
`euOf`/`evOf` through the sampler's indexing `eqv`, the per-point values `VfOf val`) and every filter seed once
(`es = (finRange |seeds|).map g`, `g` any enumeration), that sum is the numerator:

* **`sTerm_mask`**: a sampled pair's term is `M(e, x)·val(c, u, v)` at `x = c + u + v` (the two carriers' factors
  are the call's mask, `Corner.maskBits_point`, `all_carF`);
* **`gs_eq`**: one seed's term is `Σ_c Σ_ℓ M(e, x_{c,ℓ})·val(c, u_ℓ, v_ℓ)`;
* **`seeds_gs`**: over every seed, `Σ_c Σ_e Σ_ℓ M·val`;
* **`num_sym`**, **`num_thr`**: at `val = rsumSym` (resp. `rsumThr`) that is `symNum` (resp. `thrNum`), through
  `symNum_pt`/`ptSym_mask` (resp. `thrNum_pt`/`ptThr_mask`).

Paper quantity of the main type: the numerator `Σ_{c,e,e',ℓ} M(e, x_{c,ℓ})·R̂_{e'}(x_{c,ℓ})` of the final pass's value
(P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.NumDen NearCubicWires.WireExponent3_5.FinalPass.Corner

section Num
variable (P : StarParams) (σT : P.Translation) {N Q : ℕ} (eqv : P.Errors ≃ Fin N) (S : Fin Q → Fin N × Fin N)
  (carriers : List (Carrier P.n)) (FP : GapParams)

/-- The left half of sampled index `a`: its error vector. -/
def euOf (a : Fin N) : BitInput P.n := P.errorVector P.leftBlock (eqv.symm a)

/-- The right half of sampled index `b`: its error vector. -/
def evOf (b : Fin N) : BitInput P.n := P.errorVector P.rightBlock (eqv.symm b)

/-- The per-point values at the sampled indices. -/
def VfOf (val : BitInput P.n → P.Errors → P.Errors → ℕ) (c : BitInput P.n) (a b : Fin N) : ℕ :=
  val c (eqv.symm a) (eqv.symm b)

variable (val : BitInput P.n → P.Errors → P.Errors → ℕ)

theorem sTerm_mask (hk : carriers.length ≤ 2) (e : GapSeed FP) (c : BitInput P.n) (hc : P.IsCenter σT c)
    (ab : Fin N × Fin N) :
    sTerm FP e carriers c (euOf P eqv) (evOf P eqv) (VfOf P eqv val c) ab =
      (maskBits P σT carriers FP e (P.point c (eqv.symm ab.1) (eqv.symm ab.2))).toNat *
        val c (eqv.symm ab.1) (eqv.symm ab.2) := by
  unfold sTerm VfOf euOf evOf
  rw [maskBits_point P hc, all_carF FP e carriers hk]

/-- **One seed's term** at the call's sample. -/
theorem gs_eq (hk : carriers.length ≤ 2) (e : GapSeed FP) :
    Gs FP e P σT carriers (List.ofFn S) (euOf P eqv) (evOf P eqv) (VfOf P eqv val) =
      ∑ c : {c // P.IsCenter σT c}, ∑ l : Fin Q,
        (maskBits P σT carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
          val c.1 (eqv.symm (S l).1) (eqv.symm (S l).2) := by
  unfold Gs sSum
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  exact sTerm_mask P σT eqv carriers FP val hk e c.1 c.2 (S l)

/-- **Every seed's term**: the seed loop's sum at any enumeration of the seeds. -/
theorem seeds_gs (hk : carriers.length ≤ 2) {nE : ℕ} (g : Fin nE ≃ GapSeed FP) :
    (((List.finRange nE).map g).map fun e =>
        Gs FP e P σT carriers (List.ofFn S) (euOf P eqv) (evOf P eqv) (VfOf P eqv val)).sum =
      ∑ c : {c // P.IsCenter σT c}, ∑ e : GapSeed FP, ∑ l : Fin Q,
        (maskBits P σT carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
          val c.1 (eqv.symm (S l).1) (eqv.symm (S l).2) := by
  rw [List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp g (fun e => Gs FP e P σT carriers (List.ofFn S) (euOf P eqv) (evOf P eqv) (VfOf P eqv val))]
  simp only [gs_eq P σT eqv S carriers FP val hk]
  exact Finset.sum_comm

/-- **The SYM numerator** is the seed loop's sum at `val = rsumSym`. -/
theorem num_sym {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (Pl : Lists.FlatListParams)
    (hk : carriers.length ≤ 2) {nE : ℕ} (g : Fin nE ≃ GapSeed FP) :
    (((List.finRange nE).map g).map fun e =>
        Gs FP e P σT carriers (List.ofFn S) (euOf P eqv) (evOf P eqv) (VfOf P eqv (rsumSym P Cs Pl))).sum =
      symNum P σT eqv S Cs carriers FP Pl := by
  rw [seeds_gs P σT eqv S carriers FP _ hk g, symNum_pt]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun l _ => ?_)))
  rw [ptSym_mask]

/-- **The THR numerator** is the seed loop's sum at `val = rsumThr`. -/
theorem num_thr {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ)
    (hk : carriers.length ≤ 2) {nE : ℕ} (g : Fin nE ≃ GapSeed FP) :
    (((List.finRange nE).map g).map fun e =>
        Gs FP e P σT carriers (List.ofFn S) (euOf P eqv) (evOf P eqv)
          (VfOf P eqv (rsumThr P Cs algorithm den report))).sum =
      thrNum P σT eqv S Cs carriers FP algorithm den report := by
  rw [seeds_gs P σT eqv S carriers FP _ hk g, thrNum_pt]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun l _ => ?_)))
  rw [ptThr_mask]

end Num

end NearCubicWires.WireExponent3_5.FinalPass.Sd
