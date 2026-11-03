import Proof.Packets.PacketsXWalkTimeLoop
import Proof.Packets.PacketsXWalkSampleWord
import Proof.Supplier.SupplierWalkBridge

/-! # The walk-bank producer: its interface (shared piece "Walk-bank producer")

Paper: the regular filter's seed is a walk: "Pad the base seed to an even number of bits and use the explicit powered
Margulis walk [...] The walk starts uniformly" and "The powered graph has fixed degree, so the seed consists of the
initial base seed and `O(t)` edge-label bits" (P3:2083-2087, 2098-2100). A seed is enumerated by its index, a binary
word of `160n + 2r` bits (base `WalkSampleWord.binary_eq`: the edge-label words, then the start vertex).

The walk itself is base's `WalkTimeLoop.run`: from the bank `WalkTimeLoop.A R L sample tail 0` (the start vertex's
coordinate words, the unary work tapes, the edge-label word) with the counter `CompareMachine.word n`, it follows the
`n` powered edges. The consumers (PA's writer cells, the input of C5's `stage6_step` / `builderStepL`; FP's
final-pass seed loop) need that bank from the seed index. This module is the producer's TYPE, before the machine
is built (interface first):

* the ports, in `WalkTimeLoop.run`'s own order: tapes `0 … 7` the bank, `8` the counter; then `9` the framed seed
  index word (kept), `10 … 13` the unary rulers `1^r`, `1^n`, `1^R`, `1^LW` (kept); then `x` scratch tapes;
* **`WalkBankProducer`**: from every port blank but `9 … 13` and blank scratch, within `walkBankCost r n R LW` steps,
  the machine halts with the bank `WalkTimeLoop.A R LW sample [] 0` and the counter `CompareMachine.word n` at
  `WalkTimeLoop.run`'s entry heads (`outHeads`), the inputs kept, and residues of length at most the cost on the
  scratch tapes (the bounded-residue form of);
* `seedIndexWord_eq` (the index word is base's `WalkSampleWord.word` at `r = toeplitzWalkSideBits rank`),
  `bank_entry` / `heads_entry` (the first nine ports are exactly `WalkTimeLoop.run`'s entry).

Paper quantity of the main type: the walk sample's start vertex and edge labels, as the bank `WalkTimeLoop.A`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge
open Theorem25Completion

/-- **The seed index word**: the walk sample's index in `160n + 2r` bits, low bit first. -/
def seedIndexWord (r n : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) : List Bool :=
  SignedSortKey.binary (160 * n + 2 * r) (positiveWalkSampleFinEquiv (2 ^ r) n sample).val

/-- The ports at entry: the bank and the counter blank, the framed index word, the rulers `1^r, 1^n, 1^R, 1^LW`. -/
def inPorts (r n R LW : ℕ) (w : List Bool) : Fin 14 → List Bool :=
  ![[], [], [], [], [], [], [], [], [], frame w, List.replicate r true, List.replicate n true, List.replicate R true,
    List.replicate LW true]

/-- The ports at exit: `WalkTimeLoop.run`'s entry bank and counter, then the inputs kept. -/
def outPorts (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) : Fin 14 → List Bool :=
  Fin.addCases (m := 9) (n := 5) (motive := fun _ => List Bool)
    (Fin.addCases (m := 8) (n := 1) (motive := fun _ => List Bool) (WalkTimeLoop.A R LW sample [] 0)
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n))
    ![frame (seedIndexWord r n sample), List.replicate r true, List.replicate n true, List.replicate R true,
      List.replicate LW true]

/-- The heads at exit: `WalkTimeLoop.run`'s entry heads on the bank and the counter, `0` on the kept inputs. -/
def outHeads (n : ℕ) : Fin 14 → ℕ :=
  Fin.addCases (m := 9) (n := 5) (motive := fun _ => ℕ)
    (Fin.addCases (m := 8) (n := 1) (motive := fun _ => ℕ) (WalkTimeLoop.H n 0) (fun _ => 1)) (fun _ => 0)

/-- The producer's time bound (quadratic in the index word and the rulers). -/
def walkBankCost (r n R LW : ℕ) : ℕ := 1000 * (160 * n + 2 * r + R + LW + 2) ^ 2

/-- **The walk-bank producer**: one machine on `14 + x` tapes; for every walk sample, from the framed index word and
the rulers (every other tape blank, every head at `0`), it halts within `walkBankCost` with `WalkTimeLoop.run`'s entry
bank on ports `0 … 8`, the inputs kept on `9 … 13`, and residues bounded by the cost on the scratch tapes. -/
structure WalkBankProducer where
  x : ℕ
  s : ℕ
  M : Machine (14 + x) s
  run : ∀ (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)), 2 * r + 1 ≤ R → 2 * r + 1 ≤ LW →
    ∃ J : Fin x → List Bool, (∀ j, (J j).length ≤ walkBankCost r n R LW) ∧
      Step M (walkBankCost r n R LW) (fun _ => 0)
        (Fin.addCases (m := 14) (n := x) (motive := fun _ => List Bool) (inPorts r n R LW (seedIndexWord r n sample))
          (fun _ => []))
        (Fin.addCases (m := 14) (n := x) (motive := fun _ => ℕ) (outHeads n) (fun _ => 0))
        (Fin.addCases (m := 14) (n := x) (motive := fun _ => List Bool) (outPorts r n R LW sample) J)

end NearCubicWires.WireExponent3_5.PrimT.WalkBank
