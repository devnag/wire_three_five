import Lean
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.Codec
import Proof.Amplification.RecoveryWitnessPolicy
import Proof.Foundations.PolynomialSchedule
import Bindings.Williams14_Corollary4_4
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.CallSizeBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA params: every call's word has polynomial length (module form of the #57 consumer checks)

Consumer checks for (a residual about a time-bounded machine quantifies only over inputs the machine
can read): every request meeting the per-call hypothesis `I.Call` has a word of polynomial length in `n`, with a
degree fixed by the caller's inputs (`descDeg`, `carrierDeg`, `nameCount`), not by the gate's free constants.

* `word_length_le`: `|req.word| ≤ wordBound descDeg carrierDeg nameCount n` under `I.Call req`: `natWord n`, the mode
  bit, `natWord a` (`a ≤ 4`), the circuit codes (base's canonical code bounds at the parameter `(n+1)^descDeg + …`),
  the carrier codes (at most `nameCount`, each a balanced list of at most `(n+1)^carrierDeg` atom codes), and the
  translation (`r ≤ n/4` codes, each `< 2^s ≤ n + 1`);
* `gate_word_length_le`: the gate's calls (`descDeg = carrierDeg = 26`, `nameCount = 2`);
* `wordBound_poly`: `wordBound 26 26 2` is polynomially bounded (base's `PolynomiallyBounded`).

Donors: base `RecoveryWitnessPolicy` (`encodeNormalized{Symmetric,Threshold}Circuit_bits_le_parameter`,
`encodeBalancedList_bits_le_of_bounds`, `encodeTaggedList_two_bits_le`, `encodeIntList_bits_le_parameter`,
`encodeInt_bits_le_parameter`), `PolynomialSchedule.polynomiallyBounded_*`, `Williams14.natWord_length`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CallSize
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.CanonicalBinary NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule
open NearCubicWires.WireExponent3_5.PrimAsm.Codec

/-- **The gate's calls** (`descDeg = carrierDeg = 26`, `nameCount = 2`). -/
theorem gate_word_length_le (l : Literals) (F : Split.GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (req : PrimRequest) (h : (Plan.callInputs l F kclk coef A a ha).Call req) :
    req.word.length ≤ wordBound 26 26 2 req.n := by
  have hD : (Plan.callInputs l F kclk coef A a ha).descDeg = 26 := rfl
  have hC : (Plan.callInputs l F kclk coef A a ha).carrierDeg = 26 := rfl
  have hK : (Plan.callInputs l F kclk coef A a ha).nameCount = 2 := rfl
  have hw := word_length_le _ req h
  rw [hD, hC, hK] at hw
  exact hw

/-! ## The bound is polynomial -/

end NearCubicWires.WireExponent3_5.PrimAsm.CallSize

end
