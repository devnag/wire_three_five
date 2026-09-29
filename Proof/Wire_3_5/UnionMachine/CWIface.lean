import Proof.Wire_3_5.UnionMachine.CodeWritersEnv

/-! # C6 front, U5: the code writers' interface, version 2

The union's calls name codes the guess does not contain (P3:3071-3094, `PrimRequest.word`): each call's named carrier
("It then selects the common star translation, constructs the shared coordinate filters", P3:3673-3674) and the
canonical codes of the two atoms the setup supplies, the encoding parity of each systematic support ("Systematic
parities are constructed from the PCPP output", P3:3672) and the constant; the envelope bit of each named carrier
decides `lem:primitive`'s precondition "at the same fixed description envelope" (P3:3092-3094).

Version 1 (`Proof.Wire_3_5.UnionMachine.CodeWriters`, `…CodeWritersEnv`) asked every tape other than the two ports to be
EMPTY at the halt. A written tape never becomes empty again (`writeTapeBit` returns a cons in every branch), so a
version-1 writer could never write a scratch tape, and no donor machine could be docked into one. Version 2 keeps the
ports exact and lets the writer leave a RESIDUE `J` on its other tapes, of length at most the step bound. That is
what the union front's per-variable loop consumes (`Transfer.foldBody_ready`: the worker's residue is erased back to
`false` up to a capacity, `hlen`).

* **`outBankJ i o u v J`**: `frame u` kept on the input tape `i`, `frame v` on the output tape `o`, `J` elsewhere.
* **`CarrierWriterJ m`** (`carrier_ready`): `u = codesWord m cs`, `v = natWord (Carrier.code (carrierOf m cs))`.
* **`ParityWriterJ m`** (`parity_ready`): `u = bitmap S`, `v = natWord (m.code (unionParityAtom m q S))`.
* **`ConstWriterJ m`** (`const_ready`): `u = 1^q`, `v = natWord (m.code (unionConstAtom m q))`.
* **`EnvWriterJ m deg`** (`env_ready`): `u = natWord q ++ codesWord m cs`, `v = [envBit m deg cs]`.
* **`WritersJ`**, **`EnvWritersJ`**: both class modes (and every degree).
Every run takes at most `B = K·(|u| + q + 1)^d` steps, and every residue tape has at most `B` cells.

The anchors (`carrier_anchor`, `parity_anchor`, `env_anchor`) read the version-1 identities `carrier_eq`,
`parity_eq`, `envBit_iff` through these runs: at a variable `X` of the check data, the writers produce the code
of `D.carrier X`, the code of `D.parity X`, and the bit of `(D.carrier X).WithinEnvelope deg`.

Paper quantity of the main types: the codes of the calls' named carriers and of the setup's atoms, and the envelope
bit of a named carrier. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWIface
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters
open NearCubicWires.RepairRepresentation (natWord)

/-- **The output bank with a residue**: `frame u` kept on `i`, `frame v` on `o`, the residue `J` on every other tape. -/
def outBankJ {t : ℕ} (i o : Fin t) (u v : List Bool) (J : Fin t → List Bool) : Fin t → List Bool :=
  fun j => if j = i then frame u else if j = o then frame v else J j

theorem outBankJ_in {t : ℕ} (i o : Fin t) (u v : List Bool) (J : Fin t → List Bool) : outBankJ i o u v J i = frame u := by
  simp [outBankJ]

theorem outBankJ_out {t : ℕ} (i o : Fin t) (h : i ≠ o) (u v : List Bool) (J : Fin t → List Bool) :
    outBankJ i o u v J o = frame v := by
  simp [outBankJ, Ne.symm h]

theorem outBankJ_other {t : ℕ} (i o j : Fin t) (hi : j ≠ i) (ho : j ≠ o) (u v : List Bool) (J : Fin t → List Bool) :
    outBankJ i o u v J j = J j := by
  simp [outBankJ, hi, ho]

/-- **The carrier-code writer** of mode `m`, version 2 (`carrier_ready`). -/
structure CarrierWriterJ (m : Mode) extends WordStage where
  carrier_ready : ∀ (q : ℕ) (cs : List (m.Circuit q)),
    ∃ J : Fin t → List Bool, (∀ j, (J j).length ≤ K * ((codesWord m cs).length + q + 1) ^ d) ∧
      ClockJoin.ReadyRun M (K * ((codesWord m cs).length + q + 1) ^ d) (inBank inS (codesWord m cs))
        (outBankJ inS outS (codesWord m cs) (natWord (Stars.Carrier.code (carrierOf m cs))) J)

/-- **The parity-code writer** of mode `m`, version 2 (`parity_ready`). -/
structure ParityWriterJ (m : Mode) extends WordStage where
  parity_ready : ∀ (q : ℕ) (S : Finset (Fin q)),
    ∃ J : Fin t → List Bool, (∀ j, (J j).length ≤ K * ((bitmap S).length + q + 1) ^ d) ∧
      ClockJoin.ReadyRun M (K * ((bitmap S).length + q + 1) ^ d) (inBank inS (bitmap S))
        (outBankJ inS outS (bitmap S) (natWord (m.code (unionParityAtom m q S))) J)

/-- **The constant-code writer** of mode `m`, version 2 (`const_ready`). -/
structure ConstWriterJ (m : Mode) extends WordStage where
  const_ready : ∀ q : ℕ,
    ∃ J : Fin t → List Bool, (∀ j, (J j).length ≤ K * ((List.replicate q true).length + q + 1) ^ d) ∧
      ClockJoin.ReadyRun M (K * ((List.replicate q true).length + q + 1) ^ d) (inBank inS (List.replicate q true))
        (outBankJ inS outS (List.replicate q true) (natWord (m.code (unionConstAtom m q))) J)

/-- **The three writers for both class modes**, version 2. -/
structure WritersJ where
  carrier : ∀ m : Mode, CarrierWriterJ m
  parity : ∀ m : Mode, ParityWriterJ m
  const : ∀ m : Mode, ConstWriterJ m

/-! ## The anchors: the writers compute the quantities -/

section Anchor

end Anchor

end NearCubicWires.WireExponent3_5.UnionMachine.CWIface
