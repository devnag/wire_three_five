import Codec.PairFrame
import Codec.Seek

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Joins

variable {ns nr : ℕ} (cap : ℕ)

section Regs

end Regs

/-- The pair call of the worker (the near-cubic-gates paper): circuits `i` and `j`, no parity, radius `ω`. -/
def pairCallOf {q : ℕ} (Cs : ℕ → NCircuit q) (i j : ℕ) (ω : ℚ) : Call := ⟨q, .pair, Cs i, Cs j, [], ω⟩

section Spec
variable (Rg : Fin 16 ↪ Fin nr)

/-! ## Single and parity calls -/

/-- The single/parity call of the worker: circuit `j`, the empty second circuit, parity list `ps`, radius `ω`
(`Worker.Guess.singleCall`: tag `parity` when the list is nonempty, `single` otherwise). -/
def oneCallOf {q : ℕ} (Cs : ℕ → NCircuit q) (j : ℕ) (ps : List ℕ) (ω : ℚ) : Call :=
  ⟨q, if ps = [] then .single else .parity, Cs j, NCircuit.empty q, ps, ω⟩

/-- The word of the empty second circuit (the same for every width). -/
def emptyCW : List Bool := natWord 0 ++ natWord 0 ++ (natWord 1 ++ bitWord false)

end Spec

end NearCubicGates.Close.Codec
