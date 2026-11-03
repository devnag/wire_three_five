import Proof.Wire_3_5.FinalPass.TermRef
import Proof.Wire_3_5.Primitive.PrimitiveThr

/-! # Final pass, stage 8 (THR): the reported modular row from the corners (P3:2587-2630, 3170-3178)

At one sampled pair the THR term of the printed value is `(1/|𝒫|)·M(e,x)·R̂_{g,p}(c,u,v)` (`thrValueBits`), with the
reported modular row `R̂_{g,p} = 1[A + B + s ≡ 0 (mod p)]` (`thrRhat`, row:thr-reported): `A = −target +
Σ_ia_i(X_i(c+u) − X_i(c))`, `B = Σ_ia_iX_i(c+v)` and `s = Σ_d2^d(t_d^+ − t_d^−)` from the digit lists' reports.
Modulo `p`, `A + B` is a function of the OCCURRENCES' corner word (shared by every row `(g,p)`) and the row's reduced
coefficients `redCoeff` (`< p`): each occurrence adds `a_i·(#1 + #2 − #3)`. This module gives the row in the form a
machine computes it with a counter modulo `p`:
- `modAB p X as`: `Σ_i a_i(X_{i,1} + X_{i,2} − X_{i,3})` over the corner groups, in `ZMod p`;
- `modDig p ws t⁺ t⁻`: `Σ_d w_d(t_d^+ − t_d^−)` with `w_d = 2^d mod p`;
- `thrTermOk p r₀ X as ws t⁺ t⁻ = [r₀ + modAB + modDig ≡ 0]` with `r₀ = (−target) mod p`;
- **`thrRhat_eq_termOk`**: `thrRhat` is `thrTermOk` at the row's residue, coefficients and digit weights. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Term
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop

/-! ## The modular sums -/

/-- `Σ_i a_i(X_{i,1} + X_{i,2} − X_{i,3})` over the corner groups, modulo `p`. -/
def modAB (p : ℕ) : List Bool → List ℕ → ZMod p
  | _ :: b1 :: b2 :: b3 :: X, a :: as =>
      (a : ZMod p) * ((b1.toNat : ZMod p) + b2.toNat - b3.toNat) + modAB p X as
  | _, _ => 0

/-- `Σ_d w_d(t_d^+ − t_d^−)` modulo `p`. -/
def modDig (p : ℕ) : List ℕ → List ℕ → List ℕ → ZMod p
  | w :: ws, t :: tp, s :: tm => (w : ZMod p) * ((t : ZMod p) - s) + modDig p ws tp tm
  | _, _, _ => 0

/-- **The reported modular row from the corners**: `[r₀ + Σ_ia_i(#1 + #2 − #3) + Σ_dw_d(t_d^+ − t_d^−) ≡ 0 (mod p)]`. -/
def thrTermOk (p r0 : ℕ) (X : List Bool) (as ws tp tm : List ℕ) : Bool :=
  decide ((r0 : ZMod p) + modAB p X as + modDig p ws tp tm = 0)

/-! ## Bridges -/

theorem natCast_toNat_emod (p : ℕ) (hp : 0 < p) (w : ℤ) : (((w % (p : ℤ)).toNat : ℕ) : ZMod p) = (w : ZMod p) := by
  have hnn := Int.emod_nonneg w (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)
  have hk : (((w % (p : ℤ)).toNat : ℕ) : ℤ) = w % (p : ℤ) := Int.toNat_of_nonneg hnn
  calc (((w % (p : ℤ)).toNat : ℕ) : ZMod p) = ((((w % (p : ℤ)).toNat : ℕ) : ℤ) : ZMod p) := (Int.cast_natCast _).symm
    _ = ((w % (p : ℤ) : ℤ) : ZMod p) := by rw [hk]
    _ = (w : ZMod p) := ZMod.intCast_mod _ _

theorem toNat_cast_bitZ (p : ℕ) (b : Bool) : ((b.toNat : ℕ) : ZMod p) = ((bitZ b : ℤ) : ZMod p) := by
  cases b <;> simp [bitZ]

theorem cornerWord_cons {n : ℕ} (T : BitInput n → Bool) (Ts : List (BitInput n → Bool)) (c u v : BitInput n) :
    cornerWord (T :: Ts) c u v =
      corners T c u v 0 :: corners T c u v 1 :: corners T c u v 2 :: corners T c u v 3 :: cornerWord Ts c u v := by
  simp [cornerWord, List.ofFn_succ]

/-- **`A + B` modulo `p` from the corners** of a weighted gate list. -/
theorem modAB_gates {n : ℕ} (p : ℕ) (hp : 0 < p) (gates : List (ℤ × NormalizedThresholdGate n)) (c u v : BitInput n) :
    modAB p (cornerWord (gates.map fun q => q.2.eval) c u v) (gates.map fun q => (q.1 % (p : ℤ)).toNat) =
      ((rowLeft (0 : ℤ) gates c u + rowRight gates c v : ℤ) : ZMod p) := by
  induction gates with
  | nil => simp [modAB, cornerWord, rowLeft, rowRight]
  | cons q gs ih =>
    rw [List.map_cons, List.map_cons, cornerWord_cons, modAB, ih]
    unfold rowLeft rowRight
    simp only [List.map_cons, List.sum_cons, zero_add]
    rw [natCast_toNat_emod p hp, toNat_cast_bitZ, toNat_cast_bitZ, toNat_cast_bitZ]
    have e1 : corners q.2.eval c u v 1 = q.2.eval (xorInput c u) := rfl
    have e2 : corners q.2.eval c u v 2 = q.2.eval (xorInput c v) := rfl
    have e3 : corners q.2.eval c u v 3 = q.2.eval c := rfl
    rw [e1, e2, e3]
    push_cast
    ring

theorem modDig_ofFn (p : ℕ) : ∀ (τ : ℕ) (w a b : Fin τ → ℕ),
    modDig p (List.ofFn w) (List.ofFn a) (List.ofFn b) = ∑ d, (w d : ZMod p) * ((a d : ZMod p) - b d)
  | 0, _, _, _ => by simp [modDig]
  | τ + 1, w, a, b => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, modDig, modDig_ofFn p τ, Fin.sum_univ_succ]

theorem eqGates_map_eval {n : ℕ} (occs : List (SupportedNormalizedGate n)) (eq : LabelledEquation (Fin occs.length)) :
    (eqGates occs eq).map (fun q => q.2.eval) = occs.map fun o => o.gate.eval := by
  unfold eqGates
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

section Thr
variable (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
  (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ)

/-- The occurrences' corner word at the sampled pair (shared by every row `(g,p)`). -/
def occCorners (c : BitInput P.n) (u v : P.Errors) : List Bool :=
  cornerWord ((thrOccs P Cs).map fun o => o.gate.eval) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)

/-- The row's residue `r₀ = (−target) mod p`. -/
def thrR0 (g : ThrEq P Cs algorithm) (p : ℕ) : ℕ := ((-(thrRealize P Cs algorithm g).target) % (p : ℤ)).toNat

/-- The row's reduced coefficients `a_i = w_i mod p`. -/
def thrCoeffs (g : ThrEq P Cs algorithm) (p : ℕ) : List ℕ :=
  List.ofFn (redCoeff (thrOccs P Cs) (thrRealize P Cs algorithm g) p)

/-- The digit weights `2^d mod p`. -/
def thrWeights (p : ℕ) : List ℕ := List.ofFn fun d : Fin (thrDigits P Cs algorithm den) => 2 ^ (d : ℕ) % p

/-- The digit lists' reports `t_d^±` of row `(g,p)`. -/
def thrReps (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (sgn : Bool)
    (c : BitInput P.n) (u v : P.Errors) : List ℕ :=
  List.ofFn fun d => report (thrDigitPop P Cs algorithm den g pr d sgn c u v)

/-- **The reported modular row is `thrTermOk`** at the row's residue, reduced coefficients, digit weights and the digit
lists' reports, on the occurrences' corner word. -/
theorem thrRhat_eq_termOk (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (c : BitInput P.n) (u v : P.Errors) :
    thrRhat P Cs algorithm den report g pr c u v =
      thrTermOk pr.val (thrR0 P Cs algorithm g pr.val) (occCorners P Cs c u v) (thrCoeffs P Cs algorithm g pr.val)
        (thrWeights P Cs algorithm den pr.val) (thrReps P Cs algorithm den report g pr true c u v)
        (thrReps P Cs algorithm den report g pr false c u v) := by
  have hp : 0 < pr.val := Nat.pos_of_ne_zero (NeZero.ne _)
  unfold thrRhat thrReported thrTermOk
  congr 1
  have hX : occCorners P Cs c u v = cornerWord ((eqGates (thrOccs P Cs) (thrRealize P Cs algorithm g)).map
      fun q => q.2.eval) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) := by
    rw [eqGates_map_eval]; rfl
  have hA : thrCoeffs P Cs algorithm g pr.val =
      (eqGates (thrOccs P Cs) (thrRealize P Cs algorithm g)).map fun q => (q.1 % (pr.val : ℤ)).toNat := by
    unfold thrCoeffs eqGates redCoeff
    rw [List.map_ofFn]
    rfl
  rw [hX, hA, modAB_gates pr.val hp, thrWeights, thrReps, thrReps, modDig_ofFn]
  unfold thrLeft thrRight thrR0 thrResHat tupleResidue
  rw [natCast_toNat_emod pr.val hp]
  have hL : rowLeft (-(thrRealize P Cs algorithm g).target) (eqGates (thrOccs P Cs) (thrRealize P Cs algorithm g)) c
      (P.errorVector P.leftBlock u) = -(thrRealize P Cs algorithm g).target +
        rowLeft (0 : ℤ) (eqGates (thrOccs P Cs) (thrRealize P Cs algorithm g)) c (P.errorVector P.leftBlock u) := by
    unfold rowLeft; ring
  rw [hL]
  have hw : ∀ d : Fin (thrDigits P Cs algorithm den), ((2 ^ (d : ℕ) % pr.val : ℕ) : ZMod pr.val) = 2 ^ (d : ℕ) := by
    intro d; rw [ZMod.natCast_mod]; push_cast; rfl
  simp only [hw]
  push_cast
  ring

end Thr

end NearCubicWires.WireExponent3_5.FinalPass.Term
