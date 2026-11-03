import Proof.Wire_3_5.Primitive.Writers.ThrK7Base
import Proof.Wire_3_5.Primitive.Writers.ThrEAt3
import Proof.Wire_3_5.Primitive.Writers.ThrSide10Base

/-! # PA2 c4 THR block, piece 7 part 2: the THR constants and the builder `ThrFreeOkB7`

The THR twin of the `symCof`/`symCDs`/`symFreeOk` (SymBuild) at the v7 contract (v6 + the strip):
* the strip's bound: `kbT_codes` (the call's circuit and carrier codes within `kbT n`), `strip_req` (the translation's
  words, at any call), `stripP` (one polynomial above the eight premises: `|req.word| ≤ wordBound`, `|hbF| ≤ c_H L²`,
  `kbT`, the translation, the counts) with **`stripP_poly`**, **`strip_le`** (`ThrStripAt pr` once
  `stripP l n ≤ 2pr + 2`);
* **`thrCof`** (the THR constants at `fe`, fixed before `F`: `d_T = 2e_N`, `d_C = 12d_T`, `d_Q = cST + 1`,
  `d_H = coef·4^{deg} + 2`, `e_H = 26deg + 1`, `d_D = dDT`, `d_P`/`e_P` above the precondition's and the strip's
  polynomial, `d_A = symDAc`, `d_R = 0`), **`thrCDt`** (the load floor: `occCDT + 16·thrC1 + symHC`);
* `c3KT`, **`c3_thr2`** (the C3 load), **`thr_pad`**, **`thr_side`** (`ThrEAt3` from `thrEAt`), **`thr_strip`**;
* **`thrFreeOk`** : `ThrFreeOkB7 l wa`.

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of the THR stage and their bounds
(P3:2929-2941, 3011-3016, 3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC cDa one_le_L coOf symHC symDAc symKn small_of kL_le_loadPsi)

/-! ## The strip's bound -/

/-- `kbT` is polynomial. -/
theorem kbT_poly : PolynomiallyBounded ThrFam.kbT :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_add (polynomiallyBounded_comp CallSize.pb_circBits CallSize.pb_codeParam)
      (polynomiallyBounded_comp CallSize.pb_carrierBits CallSize.pb_codeParam))


/-- **The translation's words at a call** (as in `CallSize.word_length_le`). -/
theorem strip_req {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) (req : PrimRequest)
    (h : I.Call req) :
    8 * req.translation.length + 2 * (RepairRepresentation.natListWord req.translation).length + 16 ≤
      8 * req.n + 2 * ((2 * req.n + 3) * (req.n + 1)) + 16 := by
  obtain ⟨_, _, _, _, ⟨htlen, htval⟩, hstar, _⟩ := h
  have hr4 := hstar.2.2.1
  have hl : req.translation.length ≤ req.n := by rw [htlen]; omega
  have h5 : (RepairRepresentation.natListWord req.translation).length ≤ (2 * req.n + 3) * (req.n + 1) := by
    unfold RepairRepresentation.natListWord
    rw [List.length_append]
    have e1 := CallSize.natWord_len_le_self req.translation.length
    have e2 : (req.translation.flatMap RepairRepresentation.natWord).length ≤
        req.translation.length * (2 * req.n + 3) := by
      apply CallSize.flatMap_length_le
      intro t ht
      have g1 := htval t ht
      have g2 : 2 ^ Nat.log 2 (req.n / B.rOf req.n + 1) ≤ req.n / B.rOf req.n + 1 :=
        Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
      have g3 : req.n / B.rOf req.n ≤ req.n := Nat.div_le_self _ _
      have := CallSize.natWord_len_le_self t
      omega
    have e3 := Nat.mul_le_mul_right (2 * req.n + 3) hl
    have e4 : (2 * req.n + 3) * (req.n + 1) = req.n * (2 * req.n + 3) + (2 * req.n + 3) := by ring
    omega
  omega

section Gate

/-! ## The THR constants -/


end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
