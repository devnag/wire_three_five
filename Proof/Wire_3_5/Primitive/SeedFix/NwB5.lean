import Proof.Wire_3_5.Primitive.SeedFix.NwB4
import Proof.Wire_3_5.Primitive.Writers.UnaryArith

/-! # NW phase (b), part 5: the multiplication kit on the cell bank

`NumsC.mulStep` on the block `R6 = (444 … 449)`: **`mulR`** (`a := a·r` for a register `r`) and **`mulC`**
(`a := a·c` for a constant `c`), each leaving every other register unchanged (`mulR_spec`, `mulC_spec`).

Paper quantity of the main type: the products of phase (b)'s value `V = |PrimeIndex(cut)|·|E|·Q` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine

def rA : Fin LNR := ⟨444, by decide⟩
def rMm : Fin LNR := ⟨445, by decide⟩
def rT6 : Fin LNR := ⟨446, by decide⟩
def rU6 : Fin LNR := ⟨447, by decide⟩
def rW6 : Fin LNR := ⟨448, by decide⟩
def rV6 : Fin LNR := ⟨449, by decide⟩

/-- The multiplication block `(a, m, t, u, w, v)`. -/
def R6 : Fin 6 ↪ Fin LNR := ⟨![rA, rMm, rT6, rU6, rW6, rV6], by decide⟩

theorem R6_0 : R6 0 = rA := rfl
theorem R6_1 : R6 1 = rMm := rfl
theorem R6_2 : R6 2 = rT6 := rfl
theorem R6_3 : R6 3 = rU6 := rfl
theorem R6_4 : R6 4 = rW6 := rfl
theorem R6_5 : R6 5 = rV6 := rfl

variable (cap : ℕ) (x : ℕ)

/-- `a := a·r` for a register `r`. -/
def mulR (r : Fin LNR) : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR r rMm rTm) (.seq (UnionMachine.NumsC.mulStep R6) (WM.clear rMm))

/-- `a := a·c` for a constant `c`. -/
def mulC (c : ℕ) : WM (LNS x) LNR := .seq (StarNums.incN rMm c) (.seq (UnionMachine.NumsC.mulStep R6) (WM.clear rMm))

/-- The multiplication's scratch at `0`. -/
structure MZ (σ : WState (LNS x) LNR) : Prop where
  m : σ.val rMm = 0
  t : σ.val rT6 = 0
  u : σ.val rU6 = 0
  w : σ.val rW6 = 0
  v : σ.val rV6 = 0
  tm : σ.val rTm = 0

theorem mul_final (σ : WState (LNS x) LNR) (a v : ℕ) (ha : σ.val rA = a) (hz : σ.val rMm = 0) :
    ((σ.setv rMm v).setv rA (a * v)).setv rMm 0 = σ.setv rA (a * v) := by
  have dAM : rA ≠ rMm := by decide
  refine WState.eq rfl rfl ?_ rfl
  funext q
  simp only [WState.setv_val, Function.update_apply]
  by_cases hq : q = rMm
  · subst hq; simp [dAM, Ne.symm dAM, hz]
  · by_cases hqa : q = rA
    · subst hqa; simp [dAM]
    · simp [hq, hqa]

theorem mul_cost (cap a v s : ℕ) (hac : a ≤ cap) (hvc : v ≤ cap) (hs : s ≤ UnaryPow.sq cap) :
    s + 1 + (UnionMachine.NumsC.mulCost a v + 1 + (3 * v + 1)) ≤ 64 * (cap + 1) * (cap + 1) + 2 * UnaryPow.sq cap := by
  have h1 := UnionMachine.NumsC.mulCost_le a v cap hac
  have h3 : 60 * (cap + 1) * (v + 1) ≤ 60 * (cap + 1) * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
  have h5 : 3 * v + 3 ≤ 4 * (cap + 1) * (cap + 1) := by nlinarith
  have e6 : 64 * (cap + 1) * (cap + 1) = 60 * (cap + 1) * (cap + 1) + 4 * (cap + 1) * (cap + 1) := by ring
  have hsq := UnaryPow.sq_ge cap
  omega

theorem mulR_spec (r : Fin LNR) (hr : r ≠ rMm) (hrT : r ≠ rTm) (hrA : r ≠ rA) (σ : WState (LNS x) LNR) (a v : ℕ)
    (ha : σ.val rA = a) (hv : σ.val r = v) (hz : MZ x σ) (hc : a * v ≤ cap) (hac : a ≤ cap) (hvc : v ≤ cap) :
    ∃ c, WExec cap (mulR x r) σ (σ.setv rA (a * v)) c ∧ c ≤ 64 * (cap + 1) * (cap + 1) + 2 * UnaryPow.sq cap := by
  have dMT : rMm ≠ rTm := by decide
  have dAM : rA ≠ rMm := by decide
  have d2 : rT6 ≠ rMm := by decide
  have d3 : rU6 ≠ rMm := by decide
  have d4 : rW6 ≠ rMm := by decide
  have d5 : rV6 ≠ rMm := by decide
  have e1 := SparseNum.copy1 cap r rMm rTm hr hrT dMT v σ hv hz.m hz.tm hvc
  have ha1 : (σ.setv rMm v).val (R6 0) = a := by simp [R6_0, Function.update_apply, dAM, ha]
  have hv1 : (σ.setv rMm v).val (R6 1) = v := by simp [R6_1]
  have e2 := UnionMachine.NumsC.mulStep_spec cap R6 (σ.setv rMm v)
    (by simp [R6_2, Function.update_apply, hz.t, d2]) (by simp [R6_3, Function.update_apply, hz.u, d3])
    (by simp [R6_4, Function.update_apply, hz.w, d4]) (by simp [R6_5, Function.update_apply, hz.v, d5])
    (by rw [ha1, hv1]; exact hc) (by rw [ha1]; exact hac) (by rw [hv1]; exact hvc)
  rw [ha1, hv1, R6_0] at e2
  have e3 := wclear_spec cap rMm v ((σ.setv rMm v).setv rA (a * v))
    (by simp [Function.update_apply, Ne.symm dAM]) (by simp [Function.update_apply, Ne.symm dAM]; exact hvc)
  rw [mul_final x σ a v ha hz.m] at e3
  exact ⟨_, WExec.seq e1 (WExec.seq e2 e3), mul_cost cap a v _ hac hvc le_rfl⟩

theorem mulC_spec (c0 : ℕ) (σ : WState (LNS x) LNR) (a : ℕ) (ha : σ.val rA = a) (hz : MZ x σ) (hc : a * c0 ≤ cap)
    (hac : a ≤ cap) (hvc : c0 ≤ cap) :
    ∃ c, WExec cap (mulC x c0) σ (σ.setv rA (a * c0)) c ∧
      c ≤ 64 * (cap + 1) * (cap + 1) + 2 * UnaryPow.sq cap + 4 * c0 := by
  have dAM : rA ≠ rMm := by decide
  have d2 : rT6 ≠ rMm := by decide
  have d3 : rU6 ≠ rMm := by decide
  have d4 : rW6 ≠ rMm := by decide
  have d5 : rV6 ≠ rMm := by decide
  have e1 := StarNums.incN_spec cap rMm c0 σ (by rw [hz.m]; omega)
  rw [hz.m, Nat.zero_add] at e1
  have ha1 : (σ.setv rMm c0).val (R6 0) = a := by simp [R6_0, Function.update_apply, dAM, ha]
  have hv1 : (σ.setv rMm c0).val (R6 1) = c0 := by simp [R6_1]
  have e2 := UnionMachine.NumsC.mulStep_spec cap R6 (σ.setv rMm c0)
    (by simp [R6_2, Function.update_apply, hz.t, d2]) (by simp [R6_3, Function.update_apply, hz.u, d3])
    (by simp [R6_4, Function.update_apply, hz.w, d4]) (by simp [R6_5, Function.update_apply, hz.v, d5])
    (by rw [ha1, hv1]; exact hc) (by rw [ha1]; exact hac) (by rw [hv1]; exact hvc)
  rw [ha1, hv1, R6_0] at e2
  have e3 := wclear_spec cap rMm c0 ((σ.setv rMm c0).setv rA (a * c0))
    (by simp [Function.update_apply, Ne.symm dAM]) (by simp [Function.update_apply, Ne.symm dAM]; exact hvc)
  rw [mul_final x σ a c0 ha hz.m] at e3
  have hk := mul_cost cap a c0 0 hac hvc (Nat.zero_le _)
  exact ⟨_, WExec.seq e1 (WExec.seq e2 e3), by omega⟩

end NearCubicWires.WireExponent3_5.PrimT.NwB
