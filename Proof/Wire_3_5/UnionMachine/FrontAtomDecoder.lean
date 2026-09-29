import Proof.CaseAnalysis.RowsCircuitPadding
import Proof.CaseAnalysis.RowsCircuitSymmetricRun
import Proof.CaseAnalysis.RowsCircuitThresholdRun
import Proof.Wire_3_5.UnionMachine.CodecBound
import Proof.Wire_3_5.UnionMachine.UnionCodec

/-! # C6 front, U1b: the Theorem 2.5 repository's atom decoders, padded for reuse (P3:3670)

"It rejects malformed descriptions, oversized atoms" (P3:3670): the codec reads every grid atom with the canonical
decoder of its class mode (`decodeAtom`), which is the Theorem 2.5 repository's circuit decoder (`CloseoutRowsCircuit{Threshold,Symmetric}Run`,
1703 tapes, flag tape `1700`) up to its wire and description bounds (base `RowsCircuitMeaning`). The union runs one
decoder per atom on the SAME tapes, so it runs the decoder in base's padded workspace (`CloseoutRowsCircuitPadding`:
the raw tape padded to `P`, the private tapes to `H`).

* **`dec m`**: the decoder of class mode `m`; **`dec_step`**: from the padded entry with the atom's code bits `bits`,
  a run within `WholeBudget.budget P |bits|` whose flag is `passedM m q W L bits`, which keeps the raw tape, the driver
  and (on a pass) the template and policy tapes, appends the native record to the output tape, and leaves every
  private tape at most `H` long;
* **`passedM_iff`**: past the bounds `W, L ≥ 20·(nbl (value bits) + 4)` (C6's `CodecBound`), the
  flag is exactly `(decodeAtom m q (value bits)).isSome`.

Paper quantity: the canonical decoding of one guessed atom. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomDecoder
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.WireExponent3_5.Transfer

/-- The decoder's state count. -/
noncomputable def decS : Mode → ℕ
  | .thr => CloseoutRowsCircuitThresholdRun.program.1
  | .sym => CloseoutRowsCircuitSymmetricRun.program.1

/-- **The decoder of a class mode.** -/
noncomputable def dec : (m : Mode) → Machine 1703 (decS m)
  | .thr => CloseoutRowsCircuitThresholdRun.machine
  | .sym => CloseoutRowsCircuitSymmetricRun.machine

/-- Its verdict. -/
def passedM : Mode → ℕ → ℕ → ℕ → List Bool → Prop
  | .thr, q, W, L, bits => CloseoutRowsCircuitThresholdRun.passed q W L bits
  | .sym, q, W, L, bits => CloseoutRowsCircuitSymmetricRun.passed q W L bits

/-- Its native record. -/
noncomputable def nativeM : Mode → ℕ → List Bool → List Bool
  | .thr, q, bits => CloseoutRowsCircuitThresholdRun.native q bits
  | .sym, q, bits => CloseoutRowsCircuitSymmetricRun.native q bits

/-- **One padded decoder run.** -/
theorem dec_step (m : Mode) (P H q W L : ℕ) (bits out : List Bool)
    (hC : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P) (hH : P + 1 ≤ H) :
    ∃ r : ExecutionReceipt 1703 (decS m),
      runFrom (dec m) (CloseoutRowsCircuitWholeBudget.budget P bits.length)
        ⟨(dec m).start, CloseoutRowsCircuitColdEntry.heads out, CloseoutRowsCircuitPadding.input P H q W L bits out⟩ =
          some r ∧
      r.steps ≤ CloseoutRowsCircuitWholeBudget.budget P bits.length ∧ r.final.heads 1700 = 0 ∧
      (readTapeBit (r.final.tapes 1700) 0 = true ↔ passedM m q W L bits) ∧
      r.final.heads 1 = 0 ∧ r.final.tapes 1 = ZeroPadding.pad P (frame bits) ∧
      r.final.heads 1694 = 0 ∧ r.final.tapes 1694 = List.replicate P true ∧
      (passedM m q W L bits →
        r.final.heads = CloseoutRowsCircuitColdEntry.heads (out ++ nativeM m q bits) ∧
        r.final.tapes 1688 = out ++ nativeM m q bits ∧ r.final.tapes 1674 = UnaryTemplate.tape q ∧
        r.final.tapes 1694 = List.replicate P true ∧ r.final.tapes 1698 = List.replicate W true ∧
        r.final.tapes 1699 = List.replicate L true ∧ r.final.tapes 1 = ZeroPadding.pad P (frame bits) ∧
        ∀ i, i ≠ 1 → i ≠ 1674 → i ≠ 1694 → i ≠ 1698 → i ≠ 1699 → i ≠ 1688 → (r.final.tapes i).length ≤ H) := by
  cases m
  · obtain ⟨base, br, bs, bfh, bflag, brh, braw, bdh, bd, bgood⟩ :=
      CloseoutRowsCircuitThresholdRun.cold_run P q W L bits out hC
    exact CloseoutRowsCircuitPadding.run CloseoutRowsCircuitThresholdRun.machine P H q W L _ bits out
      (CloseoutRowsCircuitThresholdRun.native q bits) _ base br bs bfh bflag brh braw bdh bd bgood hH
  · obtain ⟨base, br, bs, bfh, bflag, brh, braw, bdh, bd, bgood⟩ :=
      CloseoutRowsCircuitSymmetricRun.cold_run P q W L bits out hC
    exact CloseoutRowsCircuitPadding.run CloseoutRowsCircuitSymmetricRun.machine P H q W L _ bits out
      (CloseoutRowsCircuitSymmetricRun.native q bits) _ base br bs bfh bflag brh braw bdh bd bgood hH


end NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomDecoder
