import Proof.Wire_3_5.UnionMachine.UnionSchedule
import Proof.Wire_3_5.UnionMachine.UnionAtoms
import Proof.Wire_3_5.UnionMachine.FrontKit

/-! # C6 front, U5: the canonical code writers' interface (the portable tail pool)

The union's calls name codes the guess does not contain (P3:3071-3094, `PrimRequest.word`): each call's named carrier
`Stars.Carrier.code (carrier X)` ("It then selects the common star translation, constructs the shared coordinate
filters", P3:3673-3674; the carrier of a PCPP variable is the gates of its grid atoms and, for a systematic variable,
of its encoding parity, `UnionCheckData.carrier`), and the canonical codes `Mode.code` of the two atoms the
setup supplies: the encoding parity of each systematic support ("Systematic parities are constructed from the PCPP
output", P3:3672) and the constant. This module fixes the three writers' types; whoever builds them fills these
structures (base `PCPPRequestPair` / `PCPPRequestTaggedCons` / `PCPPRequestCircuitTag` / `DecompositionSignedPair`,
v8's balanced-list serializer, PA's codec kit).

Each writer is a clean word-to-word machine (**`WordStage`**): from `frame u` on its input tape, every other tape
blank and every head at `0`, it halts with `frame u` kept, `frame v` on its output tape, every other tape blank and
every head at `0`, within `K·(|u| + q + 1)^d` steps (`K`, `d` fixed by the writer). Clean exits let the front run a
writer once per PCPP variable on the same tapes.

* **`CarrierWriter m`** (`carrier_ready`): `u` = the codes `natWord (m.code c)` of a list of circuits `cs`, `v` =
  `natWord (Carrier.code ((cs.map m.gates).flatten))`; at `cs = carrierAtoms D X` this is the code of T's
  `D.carrier X` (**`carrier_eq`**).
* **`ParityWriter m`** (`parity_ready`): `u` = the support's bitmap over `Fin q`, `v` = `natWord (m.code
  (unionParityAtom m q S))` (`D.parity X` at `S = D.support X`, **`parity_eq`**).
* **`ConstWriter m`** (`const_ready`): `u = 1^q`, `v` = `natWord (m.code (unionConstAtom m q))` (`D.const`).

Paper quantity of the main types: the codes of the calls' named carriers and of the setup's atoms. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairRepresentation (natWord)

/-- The input bank of a word stage: `frame u` on tape `i`, every other tape blank. -/
def inBank {t : ℕ} (i : Fin t) (u : List Bool) : Fin t → List Bool := fun j => if j = i then frame u else []

/-- **A clean word-to-word machine** on its own `t` tapes, with a polynomial step bound fixed by the machine. -/
structure WordStage where
  t : ℕ
  s : ℕ
  M : Machine t s
  inS : Fin t
  outS : Fin t
  hio : inS ≠ outS
  K : ℕ
  d : ℕ

/-- The atoms' codes, one `natWord` field each. -/
def codesWord (m : Mode) {q : ℕ} (cs : List (m.Circuit q)) : List Bool := (cs.map fun c => natWord (m.code c)).flatten

/-- The carrier of a list of circuits: their charged gates, in order. -/
def carrierOf (m : Mode) {q : ℕ} (cs : List (m.Circuit q)) : Stars.Carrier q := (cs.map m.gates).flatten

/-- A support's bitmap over `Fin q`. -/
def bitmap {q : ℕ} (S : Finset (Fin q)) : List Bool := List.ofFn fun i : Fin q => decide (i ∈ S)

/-! ## The interface computes the quantities -/

section Anchor
variable (D : UnionCheckData)

/-- The circuits whose gates form the carrier of `X`: its grid atoms, then (if systematic) its encoding parity. -/
def carrierAtoms (X : PcppVar D.pcpp) : List (D.mode.Circuit D.q) :=
  List.ofFn (D.atom X) ++ (if D.sysBit X then [D.parity X] else [])

/-- **The carrier writer's output at `carrierAtoms D X` is the code of the carrier of `X`.** -/
theorem carrier_eq (X : PcppVar D.pcpp) : carrierOf D.mode (carrierAtoms D X) = D.carrier X := by
  unfold carrierOf carrierAtoms UnionCheckData.carrier
  rw [List.map_append, List.flatten_append, List.map_ofFn]
  split_ifs <;> simp [Function.comp_def]

end Anchor

end NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters
