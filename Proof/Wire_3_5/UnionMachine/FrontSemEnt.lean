import Lean
import Proof.Wire_3_5.UnionMachine.FrontDecode
import Proof.Wire_3_5.UnionMachine.FrontSemPOBase
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.FrontSemEntBase


noncomputable section
set_option maxRecDepth 4096


/-! # C6 front, the semantic core (2): the grid entries as the table writer reads them (P3:3672-3674)

The guess's rest holds the codec entries `intWord σ ++ natWord c` (`FrontDecode.encE`); the table writer and the
carrier-code writer read them as `FrontTW.entW (σ < 0, σ ≠ 0, c)` (`gridWord` sign, then the code). On grid signs the
two words agree: **`entsW_esOf`**. The entries by index: **`esOf_getD`**; the atoms' codes: **`codeE_esOf`**.

Paper quantity of the main type: the grid entries (signs and atoms' codes) of the parsed guess. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- **The guess's entries as the table writer reads them.** -/
def esOf : List (Bool × Bool × ℕ) := (entsG g).map entOf

theorem esOf_length : (esOf g).length = (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * g.s := by
  unfold esOf; rw [List.length_map, entsG_length]

/-- **On grid signs the two entry words agree.** -/
theorem entsW_esOf (hg : ∀ e ∈ entsG g, e.1 ∈ gridSet) : FrontTW.entsW (esOf g) = ((entsG g).map encE).flatten :=
  entsW_map _ hg

/-- **The entries by index.** -/
theorem esOf_getD (X : PcppVar g.pcpp) (a : Fin g.s) :
    (esOf g).getD (X.val * g.s + a.val) (false, false, 0) =
      (decide (g.sign X a < 0), decide (g.sign X a ≠ 0), g.mode.code (g.atom X a)) := by
  unfold esOf entsG
  show (List.map entOf _).getD _ (entOf (0, 0)) = _
  rw [List.getD_map, getD_linE (0, 0) _ X a]
  rfl

/-- **The atoms' codes by index.** -/
theorem codeE_esOf (X : PcppVar g.pcpp) (a : Fin g.s) :
    FrontFmtCA.codeE (esOf g) (X.val * g.s + a.val) = g.mode.code (g.atom X a) := by
  unfold FrontFmtCA.codeE
  rw [esOf_getD]

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt

end
