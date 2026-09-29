import Proof.Wire_3_5.Compiler.MachineC3aLayout
import Proof.Wire_3_5.Compiler.MachineTopLoad

/-! # C3a′'s machine obligation: the input record and the enclosing term (P3:1596-1664, 1896-1906)

Paper: alg:disjoint, "There is an explicitly constructible list of at most `max(1, fℓ)` integer affine equations
[...] Construction is polynomial in the explicit output size" (P3:1604-1615), and alg:pullback in the star instance,
"For a common pool over all `2^k` rows [...] it gives `P_ex ≤ 2^k n^{O(1)}`" (P3:1661-1664). The pool builder's
machine obligation is `Implements (c3ap a E c3aInput coef aPar)`: the contract's `RewoundWordFunction` at its class
budget in the preprocessing class, on the admissible requests of C3a′.

The machine reads the request (`PoolReq`) as one record of eleven framed fields (`Top.loadRec`, the C3 loader's
format), each a natural encoding of a request field, so that the producer never needs the decomposition's output:
* `1^n`;
* `frame (segment gates 1^n)`: base's native request stream of the carrier gates (a count header, the arity `1^n` as
  the opaque top payload, one framed native word per gate), framed once more so that the machine can measure it (the
  decomposition's capacity is manufactured from its length, as in base's `Cold.cold_run`);
* `frame side`;
* `1^{width}`;
* the flip patterns as a stream of frames (`Kit.streamTape flips []`);
* `1^h` and `1^{Q'}`;
* four empty fields.

**`c3aImplements_of`** is the enclosing term: from a machine run (the residual `C3aRun`: from the word function's
entry bank to a bank with every head at cell 0 whose output tape is the contract's encoding of the reference) and a
class bound (the residual `C3aWithin`), it yields the machine obligation. The paper quantities are the pool and its
children table (the contract's words (1) and (2)) and the construction cost. Main declarations: `c3aTop`,
`c3aInput`, `C3aRun`, `C3aWithin`, **`c3aImplements_of`**, **`c3aCertified_of`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-- The opaque top payload of the gates' native stream: the arity in unary. -/
def c3aTop (R : PoolReq) : List Bool := List.replicate R.n true

/-- **The pool builder's input record** (eleven framed fields in the C3 loader's format). -/
def c3aInput (R : PoolReq) : List Bool :=
  Top.loadRec (List.replicate R.n true) (frame (segment R.gates (c3aTop R))) (frame R.side)
    (List.replicate R.width true) (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true)
    [] [] [] []


end NearCubicWires.WireExponent3_5.CompilerMachine.C3a
