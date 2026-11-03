import Proof.Wire_3_5.Foundations.OutMachineCarBound
import Proof.Wire_3_5.FinalPass.CoreIfaceBase
import Proof.Wire_3_5.Primitive.Writers.ReqBridge
import Proof.Wire_3_5.FinalPass.S5TNum3Base

/-! # X6 carrier phase, part 8: the phase

"For each name, use the regular filter of filt:gap on its signed mixed-residual population" (P3:3071-3076); the final
pass reads each named carrier's atoms as the table `gatesW h (maskGates X)` (P3:3049-3050, 3074-3080), in polynomial
time (P3:3175-3178). From the final pass's input `frame (fpIn r)` (the request's word, then the seed word), the pipeline
`carM DtC (eraseOf keepL)` at the capacity `2^{DtC}·(|fpIn| + 1)^{DtC}` writes the five carrier words:

* **`carRun`**: the run at every request, within `CsOf DtC·(|fpIn| + 1)^{2·DtC}` steps, the words on `sOutE`, the
  input kept, every other stream `0^T`, every head and register `0`;
* **`carPhase : ∀ l, CarPhaseM l`** (`CoreWordsM`, the zero-residue contract);
* **`CarPhaseMJ l`** `:= CoreWordsMJ l 5 (carWords l)`, **`carPhaseJ := (carPhase l).toMJ`** (the
  bounded-residue contract SA and SB dock).

Paper quantity of the main type: the carriers' mask tables and gate counts (P3:3049-3050, 3071-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarGen
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarS NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound

/-- The five output streams, in `carWords`' order (PA's layout). -/
def tk : Fin 5 → Fin (DS + 1) := ![sCar 0 3, sCar 1 3, sCar 0 5, sCar 1 5, CarM2.s6]

theorem tk_inj : Function.Injective tk := by decide

theorem tk_ne : ∀ k : Fin 5, tk k ≠ sIN := by decide

/-- **The phase's output streams** on the outer layout. -/
def sOutE : Fin 5 ↪ Fin (NS + 1) := ⟨fun k => oS (tk k), oS_inj.comp tk_inj⟩

theorem sOutE_ne : ∀ k, sOutE k ≠ oS sIN := fun k e => tk_ne k (oS_inj e)

theorem mem_keep (i : Fin (NS + 1)) (hi : i.val < DS + 1) (h1 : i ≠ oS sIN) (h2 : ∀ k, i ≠ sOutE k) :
    i ∈ eraseOf keepL := by
  rw [mem_eraseOf]
  refine ⟨⟨i.val, hi⟩, ?_, Fin.ext rfl⟩
  intro hm
  have hio : i = oS ⟨i.val, hi⟩ := Fin.ext rfl
  simp only [keepL, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e <;> rw [e] at hio
  · exact h1 hio
  · exact h2 0 hio
  · exact h2 1 hio
  · exact h2 2 hio
  · exact h2 3 hio
  · exact h2 4 hio

/-- The phase's machine with its size. -/
noncomputable def carMach : (s : ℕ) × Machine (NS + 2 + NR) s := ⟨_, carM DtC (eraseOf keepL)⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.CarGen
