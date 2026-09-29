import Proof.Packets.PacketsMetaStageRun
import Proof.Wire_3_5.Primitive.ThresholdWriter.TopFront

/-! # W6 part 1: `|𝒢|` and the magnitude exponent by proof 1's PacketsMeta program (`metaC`, `metaE`)

P3:2543-2558 (row:threshold-rows): the family `𝒢` of equations `L_g` and the prime cutoff, fixed by the family's
magnitude envelope (`thrCutoff = canonicalPrimeCutoff (familyMagnitudeExponent …) K`). The magnitudes are far beyond
any unary register, so the envelope is computed by proof 1's verified binary program (`PacketsMeta.Prog.prog`: the
circuits' tables from their payloads `Request.topWord`, the nested sums `Fv = familyMagnitudeBound`, `Cv = |Sel|`),
with a tail of ours in place of proof 1's cutoff tail (the THR target uses `K = 8(|𝒢|+1)n^D`):

* the `|𝒢|` tail is base's `Tail.selTailM` (`selTail_run`; its cost `costC`); **`tailE`** / **`tailE_run`** (ours:
  `E := clog₂(F+1)` by proof 1's `segA`, `segB`, then `K := E` in unary);
* `nw0` (the program's native word: the THR tag and three zeros), `metaW` (the register width), `width_facts` (every
  width hypothesis of `prog_thr` at `nw0`, from base's `StageRun.Fv_le`/`Cv_le`/`rec_bound`), **`meta_run`** (the
  program with any tail, from `frame topWord`, `frame nw0`: the tail's unary output on tape `1`);
* **`metaC`** (`1^{Cv}`), **`metaE`** (`1^{clog₂(Fv+1)}`), for any fourfold THR request;
* `tw_payOf` (the top word is `(List.ofFn Cs).flatMap (payOf alg)`, the front end's payloads, `topWord_thr`),
  **`Cv_thr`** (`Cv = |ThrEq|`), **`E_thr`** (`clog₂(Fv+1) = familyMagnitudeExponent (thrRealize …)`).

Paper quantities of the main types: `|𝒢|` and the family's magnitude exponent. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.W6Meta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.PacketsMeta NearCubicWires.PacketsMeta.Lev NearCubicWires.PacketsMeta.Setup
open NearCubicWires.PacketsMeta.Tail NearCubicWires.PacketsMeta.Prog NearCubicWires.PacketsMeta.Spec
open NearCubicWires.PacketsMeta.Bounds

/-! ## The two tails -/

/-- The `|𝒢|` tail's cost (base's `selTail_run`). -/
def costC (W C : ℕ) : ℕ := (2 * W + 3) + 1 + (C + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2)

/-- **The magnitude-exponent tail**: proof 1's `segA`, `segB` (`E := clog₂(F+1)`), then `K := E` in unary. -/
noncomputable def tailE := Composition.machine (Composition.machine segA segB) (Composition.machine (cpyI rK rE) outLoop)

/-- The magnitude-exponent tail's cost. -/
def costE (W F : ℕ) : ℕ :=
  ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3))) + 1 +
    (Nat.clog 2 (F + 1) + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + (2 * W + 3)) + 2) + 1 +
    costC W (Nat.clog 2 (F + 1))

theorem tailE_run {W : ℕ} (F C T : ℕ) (b : Bool) (hW : 1 ≤ W) (hF : 2 * (F + 1) ≤ 2 ^ W)
    (hk : Nat.clog 2 (F + 1) < 2 ^ W) :
    LRuns W tailE (costE W F) (tst F C T 0 0 0 0 0 0 0 0 b 0)
      (tst F C T (2 ^ Nat.clog 2 (F + 1)) (Nat.clog 2 (F + 1)) (F + 1) 0 0 0 0 0 false (Nat.clog 2 (F + 1))) := by
  have hA := segA_run (W := W) F C T b (by omega) hW
  have hB := segB_run (W := W) F C T hF
  have hc := cpy_at (W := W) (tst F C T (2 ^ Nat.clog 2 (F + 1)) (Nat.clog 2 (F + 1)) (F + 1) 0 0 0 0 0 false 0)
    rl rK rE fl (by decide) 0 (Nat.clog 2 (F + 1)) false rfl rfl rfl rfl hk
  have e : Function.update (Function.update
      (tst F C T (2 ^ Nat.clog 2 (F + 1)) (Nat.clog 2 (F + 1)) (F + 1) 0 0 0 0 0 false 0) rK
        (.reg (Nat.clog 2 (F + 1)))) fl (.flag false) =
      tst F C T (2 ^ Nat.clog 2 (F + 1)) (Nat.clog 2 (F + 1)) (F + 1) 0 0 0 0 (Nat.clog 2 (F + 1)) false 0 := by
    funext j; fin_cases j <;> rfl
  rw [e] at hc
  have hO := outLoop_run (W := W) F C T (2 ^ Nat.clog 2 (F + 1)) (Nat.clog 2 (F + 1)) (F + 1) 0 0 0 0
    (Nat.clog 2 (F + 1)) false hk
  exact (hA.seq hB).seq (hc.seq hO)

/-! ## The program with our tails -/

/-- **The program's native word**: the THR tag and three zeros (the tails read only the circuits' data). -/
def nw0 : List Bool := natWord 1 ++ natWord 0 ++ natWord 0 ++ natWord 0

theorem nw0_len : nw0.length = 12 := by
  simp [nw0, ReadNat.natWord_length, natBitLength]

/-- The register width at a top word. -/
def metaW (tw : List Bool) : ℕ := 32 * (nw0.length + tw.length)

/-- The program's cost at a top word. -/
def progCost (tw : List Bool) (ds : List CD) (nT : ℕ) : ℕ :=
  hdrCost nw0 tw (metaW tw) + 1 +
    ((2 * metaW tw + 3) + (((2 * metaW tw + 3) + 1 + (2 * metaW tw + 3)) + 0 + thrCost (metaW tw) ds nT + 2) + 0 + 2)

section Run
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4)
include four

theorem width_facts :
    2 ≤ metaW (twOf (dsOf a r)) ∧ 4 * (twOf (dsOf a r)).length + 11 ≤ metaW (twOf (dsOf a r)) ∧
      (∀ j, Fits (metaW (twOf (dsOf a r))) (dOf (dsOf a r) j)) ∧
      Fv (dsOf a r) < 2 ^ metaW (twOf (dsOf a r)) ∧ Cv (dsOf a r) < 2 ^ metaW (twOf (dsOf a r)) ∧
      2 * (Fv (dsOf a r) + 1) ≤ 2 ^ metaW (twOf (dsOf a r)) ∧
      Nat.clog 2 (Fv (dsOf a r) + 1) < 2 ^ metaW (twOf (dsOf a r)) := by
  have hF := StageRun.Fv_le a r four 0 0
  have hC := StageRun.Cv_le a r four 0 0
  unfold metaW
  rw [nw0_len]
  set R := (twOf (dsOf a r)).length with hR
  have hpw : ∀ m k, m ≤ k → 2 ^ m ≤ 2 ^ k := fun m k h => Nat.pow_le_pow_right (by norm_num) h
  have hpl : ∀ m k, m < k → 2 ^ m < 2 ^ k := fun m k h => Nat.pow_lt_pow_right (by norm_num) h
  have hF1 : Fv (dsOf a r) + 1 ≤ 2 ^ (8 * R + 11) := by
    have e : 2 ^ (8 * R + 11) = 2 * 2 ^ (8 * R + 10) := by rw [pow_succ]; ring
    have := Nat.one_le_two_pow (n := 8 * R + 10)
    omega
  refine ⟨by omega, by omega, ?_, lt_of_le_of_lt hF (hpl _ _ (by omega)), lt_of_le_of_lt hC (hpl _ _ (by omega)), ?_, ?_⟩
  · intro j
    apply fits_of_len
    by_cases hj : j.val < (dsOf a r).length
    · rw [dOf_lt _ j hj]
      have := pay_le_tw (dsOf a r) j.val hj
      omega
    · rw [dOf_ge _ j (by omega), pay_pad_len]
      omega
  · have e : 2 ^ (8 * R + 12) = 2 * 2 ^ (8 * R + 11) := by rw [pow_succ]; ring
    have := hpw (8 * R + 12) (32 * (12 + R)) (by omega)
    omega
  · have he : Nat.clog 2 (Fv (dsOf a r) + 1) ≤ 8 * R + 11 := Nat.clog_le_of_le_pow hF1
    have := Nat.lt_two_pow_self (n := 32 * (12 + R))
    omega

/-- **The program with any tail**: from `frame topWord` and `frame nw0` (every other tape blank, heads `0`), the
tail's unary output on tape `1`. -/
theorem meta_run {sT : ℕ} (Tm : Machine 17 sT) (nT : ℕ) (ρT : Fin 17 → TS) (v : ℕ)
    (hT : ∀ b, LRuns (metaW (twOf (dsOf a r))) Tm nT (tst (Fv (dsOf a r)) (Cv (dsOf a r)) 0 0 0 0 0 0 0 0 0 b 0) ρT)
    (hv : ρT 16 = .out v) :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step (prog Tm) (progCost (twOf (dsOf a r)) (dsOf a r) nT) (fun _ => 0)
        (PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame (twOf (dsOf a r))) (RepairOrdinary.frame nw0))
        H1 A1 ∧ A1 ⟨1, by omega⟩ = List.replicate v true := by
  obtain ⟨h2, hR, hfit, hFm, hCm, -, -⟩ := width_facts a r four
  have hb1 : natBitLength 0 ≤ metaW (twOf (dsOf a r)) := by
    have : natBitLength 0 = 1 := by simp [natBitLength]
    omega
  have hrun := prog_thr nw0 [] 0 0 0 (by simp [nw0]) (dsOf a r) (metaW (twOf (dsOf a r))) rfl h2 hb1 hb1 hb1
    (twOf (dsOf a r)).length hR hfit (fun j x hx => StageRun.rec_bound a r four 0 0 j x hx) hFm hCm Tm nT ρT v hT hv
  exact StageRun.step_of_lruns (prog Tm) _ _ nw0 (twOf (dsOf a r)) v hrun

/-- **`Cv = |Sel|` in unary** (base's `selTailM`). -/
theorem metaC :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step (prog selTailM) (progCost (twOf (dsOf a r)) (dsOf a r) (costC (metaW (twOf (dsOf a r))) (Cv (dsOf a r))))
        (fun _ => 0)
        (PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame (twOf (dsOf a r))) (RepairOrdinary.frame nw0))
        H1 A1 ∧ A1 ⟨1, by omega⟩ = List.replicate (Cv (dsOf a r)) true := by
  obtain ⟨-, -, -, -, hCm, -, -⟩ := width_facts a r four
  exact meta_run a r four selTailM _ _ (Cv (dsOf a r)) (fun b => selTail_run _ _ 0 b hCm) rfl

/-- **`clog₂ (Fv + 1)` in unary** (our `tailE`). -/
theorem metaE :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step (prog tailE) (progCost (twOf (dsOf a r)) (dsOf a r) (costE (metaW (twOf (dsOf a r))) (Fv (dsOf a r))))
        (fun _ => 0)
        (PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame (twOf (dsOf a r))) (RepairOrdinary.frame nw0))
        H1 A1 ∧ A1 ⟨1, by omega⟩ = List.replicate (Nat.clog 2 (Fv (dsOf a r) + 1)) true := by
  obtain ⟨h2, -, -, -, -, hF2, hk⟩ := width_facts a r four
  exact meta_run a r four tailE _ _ (Nat.clog 2 (Fv (dsOf a r) + 1)) (fun b => tailE_run _ _ 0 b (by omega) hF2 hk) rfl

end Run

/-! ## The two numbers of a THR tuple -/

section Thr
variable (alg : DecompositionAlgorithm) (P : WireExponent3_5.Shared.StarParams) {a' : ℕ}
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)

theorem tw_payOf (ha : a' ≤ 4) :
    twOf (dsOf alg (Primitive.thrRequest P Cs)) = (List.ofFn Cs).flatMap (PrimThrW.TopFront.payOf alg) := by
  rw [tw_eq alg (Primitive.thrRequest P Cs) (by simpa using ha) 0 0, CutoffMath.topWord_thr]
  rfl

/-- The program's `Cv` is `|ThrEq|`. -/
theorem Cv_thr (ha : a' ≤ 4) : Cv (dsOf alg (Primitive.thrRequest P Cs)) = Fintype.card (Primitive.ThrEq P Cs alg) :=
  Cv_eq alg (Primitive.thrRequest P Cs) (by show (List.ofFn Cs).length ≤ 4; rw [List.length_ofFn]; exact ha)

/-- The program's exponent is the family's magnitude exponent. -/
theorem E_thr (ha : a' ≤ 4) : Nat.clog 2 (Fv (dsOf alg (Primitive.thrRequest P Cs)) + 1) =
    familyMagnitudeExponent (Primitive.thrRealize P Cs alg) := by
  rw [Fv_eq alg (Primitive.thrRequest P Cs) (by show (List.ofFn Cs).length ≤ 4; rw [List.length_ofFn]; exact ha)]
  rfl

end Thr

end NearCubicWires.WireExponent3_5.PrimThrW.W6Meta
