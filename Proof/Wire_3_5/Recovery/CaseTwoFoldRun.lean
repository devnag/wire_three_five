import Proof.Wire_3_5.Recovery.CaseTwoFold

/-! # The uniform Case-2 XOR fold at the padded request (P3:3729-3733, 3818-3822; D1.6 A2)

Realizes "`f^{⊕t(q)}`" (P3:3732-3733) of the hybrid Case 2 for a copy count given as DATA (the counter word
`CompareMachine.word c`), as the paper's growing schedule requires ("the least `t` with `e_t ≤ L^{−τ}`",
P3:3818-3822; one fixed `E^NP` program serves every `q`, P3:3758-3759): `c` rounds of `WireExponent3_5CaseTwoFold`'s
worker on ONE reused bank (`uniformFold_ready`), the scratch erased between rounds and the offset advanced by
the block width `w` (base `CaseTwoAdvance`).

Paper quantity of the main type (`fold_run`): the accumulator after `c` rounds is the padded XOR power of the padded
request's unsigned honest proof table, `padCore (xorPower (paddedUnsigned (a.output req) hcb) c) hfit x` (base
`FixedFold.padded_xor`), at every copy count `c` and address `x` with `c·w ≤ |x|`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
open NearCubicWires.RecoveryPipeline (padCore)

noncomputable section

/-! ## The scratch tapes -/

section Pad


end Pad

/-! ## The advance -/

/-! ## The fold -/

section Fold

end Fold

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun
