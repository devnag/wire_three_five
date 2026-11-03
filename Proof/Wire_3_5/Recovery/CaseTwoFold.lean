import Proof.Wire_3_5.Recovery.CaseTwoPadWhole
import Proof.Wire_3_5.Transfer.FoldBody
import Proof.Wire_3_5.Recovery.CertSched
import Proof.CaseAnalysis.CaseTwoXorMeaning
import Proof.CaseAnalysis.CaseTwoAddressMeaning
import Proof.CaseAnalysis.CaseTwoSliceFrame
import Proof.CaseAnalysis.CaseTwoAdvance
import Proof.PCP.PCPUnaryCopy

/-! # One round of the uniform Case-2 XOR fold at the padded request (P3:3729-3733, 3761-3763; D1.6 A1)

Realizes one copy of "`f^{⊕t(q)}`" (P3:3732-3733) for the hybrid Case 2, where "each honest proof bit is computed by
the deterministic PCPP algorithm" (P3:3762-3763) on `S₂`'s padded request, with a copy count that GROWS with `q`
("the least `t` with `e_t ≤ L^{−τ}`", P3:3818-3822): one fixed program must evaluate `t(q)+1` copies for every `q`,
so the copies share ONE reused bank and the block index is DATA, a unary offset `1^{i·w}` on a port (base's fixed-copy
fold `CloseoutCaseTwo.FixedFold` has one bank per copy and the block index in the machine).

One round, on a bank whose ports are the framed hierarchy input, the framed oracle descriptor, the accumulator, the
framed address `frame x`, the offset `1^{i·w}` and the block width `1^w` (both `false`-padded to the bank's capacity),
and the width `1^q`:
* copy `1^q` onto the block's width tape (base `PCPUnaryCopy`);
* crop block `i` of the address, `frame (x[i·w, (i+1)·w))`, onto the block's address tape (base `SliceFrame`);
* run the padded whole block at block `0` with its head reset, and XOR its honest bit into the accumulator (base
  `XorBody`).
The advance adds `w` to the offset in place (base `CaseTwoAdvance`).

Paper quantity of the main type: the unsigned honest proof bit of the padded request at block `i`,
`paddedUnsigned (a.output req) hcb (field x (i·w) w)`, XORed into the accumulator (`round_run`), and the offset's advance
(`advance_run`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

/-! ## The block's address window -/

/-- **One block of the address is the occurrence address word**: `x[o, o+q+cap+1) = u · clause · pad · position`. -/
theorem block_word {N : ℕ} (point : BitInput N) (offset q cb cap : ℕ) (hcb : cb ≤ cap) :
    List.ofFn (AddressWindow.field point offset (q + cap + 1)) =
      AddressFields.word (AddressWindow.field point offset q) (AddressWindow.field point (offset + q) cb)
        (AddressWindow.padding point offset q cb cap) (AddressWindow.read point (offset + q + cap)) := by
  have he : q + cap + 1 = q + (cb + ((cap - cb) + 1)) := by omega
  rw [he, AddressWindow.field_split, AddressWindow.field_split, AddressWindow.field_split,
    AddressWindow.field_one]
  have hp : offset + q + cb + (cap - cb) = offset + q + cap := by omega
  simp only [AddressFields.word, AddressWindow.padding, Nat.add_assoc] at hp ⊢
  rw [hp]

/-- **The address splits at a block** that fits: `x = x[0,o) · x[o,o+w) · x[o+w,N)`. -/
theorem split_at {N : ℕ} (point : BitInput N) (offset width : ℕ) (hfit : offset + width ≤ N) :
    List.ofFn point = List.ofFn (AddressWindow.field point 0 offset) ++
      List.ofFn (AddressWindow.field point offset width) ++ AddressWindow.tail point offset width := by
  have key : ∀ m, m = N → List.ofFn (AddressWindow.field point 0 m) = List.ofFn (AddressWindow.field point 0 N) := by
    intro m hm; subst hm; rfl
  calc List.ofFn point = List.ofFn (AddressWindow.field point 0 N) := (AddressWindow.full_field point).symm
    _ = List.ofFn (AddressWindow.field point 0 (offset + (width + (N - (offset + width))))) :=
        (key _ (by omega)).symm
    _ = _ := by
        rw [AddressWindow.field_split, AddressWindow.field_split]
        simp only [Nat.zero_add, AddressWindow.tail, List.append_assoc]

/-! ## The worker's tapes -/






section BankValues


end BankValues

/-! ## One round -/

section Round


section RoundIn


end RoundIn

end Round

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
