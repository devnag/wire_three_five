import Proof.Wire_3_5.Primitive.SeedFix.C4H

/-! # C4HD: the HASH call's printed-objective data (definitions)

`filt:soft`, P3:2253-2290: the HASH call's data for the Hb printer (`C4H.HashData`), at the call's
own numbers: the majorant `thrMajorant` (the call's `den`, `e`, `t`, `J`), the pool's gate count `G = |thrPool|`, the star's
`N = 2^{k_h}`, the aux seeds `nE`, the HASH tape's rows `Fs` (PA's `hashBatch` rows: each aux FILTER row is `filtRefC`'s
single term `1·filtPolyC …`, so `htWord Fs` is PA's `hashTape`), and the populations `pops`: one per `(g, p, d, ±)`
(`thrEqEquiv`, `primeEquiv`, digits, sign; determined order), with the pool gate of occurrence `i` (at `oOff + i`,
`oOff = |carriers' mask gates|`) repeated its digit `v_{i,d}` times (`digitPop`).

* `rowPoly`, `hashFsOf`, `hashOOff`, `hashGis`, `hashPopsOf`, **`hashDataOf`**.

Paper quantity of the main type: the data of the HASH call's printed conditional objective `V_p(z)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Batch

noncomputable section

/-- The F₂ polynomial of a FILTER row request (`filtRefC`'s single factor); other rows have none. -/
def rowPoly : RowReq → List (List ℕ)
  | .filt r => ListMachine.Row.filtPolyC r.thr r.tbl r.L r.sgn r.labs
  | _ => []

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
  (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **The HASH tape's rows** as F₂ polynomials (PA's `hashBatch`, row `q·nE + e'`). -/
def hashFsOf : List (List (List ℕ)) :=
  (hashBatch (I.starParams n hs) carriers (I.filterParams .thr n) (thrCallE alg I hs Cs carriers)
    (2 ^ SeedFix.callKh (I.starParams n hs)) (nE alg I hs Cs carriers) (auxEnum alg I hs Cs carriers)
    (thrPool (I.starParams n hs) Cs carriers).length n).map rowPoly

/-- The pool offset of the THR occurrences (the carriers' mask gates first). -/
def hashOOff : ℕ := (carriers.map FinalPass.Corner.maskGates).flatten.length

/-- The pool gates of the population `(g, p, d)`: occurrence `i`'s gate `oOff + i`, `v_{i,d}` times (`digitPop`). -/
def hashGis (g : ThrEq (I.starParams n hs) Cs alg)
    (pr : SupplierPrime.PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)))
    (d : Fin (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))) : List ℕ :=
  (List.finRange (thrOccs (I.starParams n hs) Cs).length).flatMap fun i =>
    List.replicate (digitOf (thrOccs (I.starParams n hs) Cs) (thrRealize (I.starParams n hs) Cs alg g) pr.val 2
      (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) i d) (hashOOff carriers + i.val)

/-- **The populations** `(±, gates)`, one per `(g, p, d, ±)`, in the determined order (`thrEqEquiv`, `primeEquiv`,
digits, sign `false` then `true`). -/
def hashPopsOf : List (Bool × List ℕ) :=
  (List.finRange _).flatMap fun gi =>
    (List.finRange _).flatMap fun pi =>
      (List.finRange (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))).flatMap fun d =>
        [false, true].map fun sgn =>
          (sgn, hashGis alg I hs Cs carriers ((Enum.thrEqEquiv (I.starParams n hs) Cs alg).symm gi)
            (Enum.primeEquiv (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) pi) d)

/-- **The HASH call's printed-objective data** (`C4H.HashData`). -/
def hashDataOf : HashData :=
  ⟨thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs)
      (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers),
    (thrPool (I.starParams n hs) Cs carriers).length, 2 ^ SeedFix.callKh (I.starParams n hs), nE alg I hs Cs carriers,
    hashFsOf alg I hs Cs carriers, hashPopsOf alg I hs Cs carriers⟩

end Call

end

end NearCubicWires.WireExponent3_5.PrimT.C4H
