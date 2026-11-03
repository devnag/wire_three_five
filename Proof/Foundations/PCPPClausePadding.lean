import Proof.Foundations.PaddedOracleRestriction
import Proof.Foundations.ProjectionWidthEnvelope
import Proof.Foundations.SupplierPrinter

/-!
# Branch-independent PCPP clause padding

The pointwise PCPP may return a circuit-dependent clause-address width.  The
headline schedule, however, must be fixed before the Case-1/Case-2 split.  This
module derives one source-only width envelope and repeats every native clause
over the added high address bits.  The repetition preserves the exact
acceptance fraction and keeps every padded query on the factory's one fixed
clause runner.
-/

namespace NearCubicWires.PCPPClausePadding

open Finset
open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPrinter

theorem binaryAddress_val_eq_ofBits {width : ℕ} (bits : BitInput width) :
    (binaryAddress bits).val = Nat.ofBits bits := by
  unfold binaryAddress
  change
    encodeBitInput bits % 2 ^ width =
      Nat.ofBits bits
  rw [encodeBitInput_eq_ofBits]
  exact Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow bits)

/-! ## Simultaneous outer-randomness and clause-address padding -/

/-! ## Source-only outer and clause-width envelopes -/

end NearCubicWires.PCPPClausePadding
