import Proof.Wire_3_5.UnionMachine.FrontDescRound

/-! # C6 front, U5: the description-flag loop (P3:3670, 3083-3094)

The loop runs one round (`FrontDescRound.roundD_step`) per grid entry of the guess rest `r`, `E` rounds in all,
under its condition `J ≠ 0`, and appends one verdict bit per atom to the flag string: bit `i` is
`passedM m q W L (pay i)`, the decoder's verdict at policy `L` on the `i`-th atom's code, which on a decodable atom is
`descriptionBits ≤ L` (base `CloseoutRowsCircuitMeaning.*_exact`). Main statement: **`desc_loop`**.
Paper quantity: the description flags `descriptionBits (atom) ≤ (q+1)^descDeg` of every guessed atom. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontDescLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit NearCubicWires.WireExponent3_5.UnionMachine.FrontDescLayout
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDescStages NearCubicWires.WireExponent3_5.UnionMachine.FrontDescRound
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## The verdict is the description envelope -/

open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.WireExponent3_5.Transfer in
/-- **On a decodable atom, the verdict at policy `L` is `descriptionBits ≤ L`** (base
`CloseoutRowsCircuitMeaning.threshold_exact` / `symmetric_exact`; the wire bound never binds past the codec bound). -/
theorem passedM_desc (m : Mode) (q W L : ℕ) (bits : List Bool) (c : m.Circuit q)
    (hc : decodeAtom m q (value bits) = some c) (hW : 20 * (natBitLength (value bits) + 4) ≤ W) :
    FrontAtomDecoder.passedM m q W L bits ↔ m.descriptionBits c ≤ L := by
  cases m
  · show CloseoutRowsCircuitThresholdRun.passed q W L bits ↔ _
    rw [CloseoutRowsCircuitMeaning.threshold_exact]
    constructor
    · rintro ⟨c', hc', -, hd⟩
      have e : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst e; exact hd
    · intro hd
      have b := UnionMachine.CodecBound.atomBound_thr q (value bits) c hc
      exact ⟨c, hc, b.1.trans hW, hd⟩
  · show CloseoutRowsCircuitSymmetricRun.passed q W L bits ↔ _
    rw [CloseoutRowsCircuitMeaning.symmetric_exact]
    constructor
    · rintro ⟨c', hc', -, hd⟩
      have e : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst e; exact hd
    · intro hd
      have b := UnionMachine.CodecBound.atomBound_sym q (value bits) c hc
      exact ⟨c, hc, b.1.trans hW, hd⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FrontDescLoop
