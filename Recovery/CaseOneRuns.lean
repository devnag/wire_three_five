import Joins.Transfer
import Proof.MachineModel.ClockJoin

/-!
# The Case 1 machine (`CaseOneRuns`), (a′) form

The near-cubic-gates paper's extraction of the hard table (the three-way split, coordinator decision F2): Case 1 (i) "no `B_src` passes CHECK, so `X_z` is
`q^G`-hard" and Case 1 (iii) "`O*` has no `q^G`-gate circuit, so `O*` is `q^G`-hard"; the uniform recovery (sec:all-lengths): "run the
general amplifier" on that hard function and pad it. Both hard functions are PERIODIC tables on `q` bits:
* (i) `X_z = Transfer.GateParams.srcFn s g ν z` reads `z` at the first `ν` address bits;
* (iii) `O* = Transfer.pfFn t` reads the first honest oracle table `t` at the first `ℓ` address bits (`false` past `q`).
`cycFn a w q` is that common form: the table `w` of length `2^a` read at the first `a` of `q` address bits; its truth
table is `w` repeated cyclically (`Recovery.C1Sem`). One deterministic machine computes both Case 1 values from the
words the E^NP program holds: the framed table `w` (followed by anything: for (i) the retained hierarchy word
`frame z ++ frame T.bits`, for (iii) the stage-2 output `frame (List.ofFn t)`), the framed final address and `1^q`.

Seam (GR's common program): the machine is used only through its tape count, its machine, the three input
ports `j ↦ j` and one output port of index at least `3`; every non-port tape starts empty; the run is a
`ClockJoin.ReadyRun` within `C·(2^n+1)^E`; the output port holds the framed bit.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces NearCubicGates.Close.Transfer

/-- The periodic function on `q` address bits given by a table `w` of length `2^a`: `w` at the first `a` address bits
(`false` past `q`) — the common form of Case 1 (i) `X_z` and Case 1 (iii) `O*` (the near-cubic-gates paper's extraction of the hard table). -/
def cycFn (a : ℕ) (w : BitInput (2 ^ a)) (q : ℕ) : BoolFunction q := fun r =>
  w (binaryAddress fun j : Fin a => if h : j.val < q then r ⟨j.val, h⟩ else false)

/-- The three input words of the Case 1 machine: the framed table (with any suffix), the framed final address, `1^q`. -/
def threeWords (table address : List Bool) (q : ℕ) : Fin 3 → List Bool :=
  ![table, address, List.replicate q true]

/-- The Case 1 machine's entry bank: the three words on the ports `j ↦ j`, every other tape empty. -/
def oneInput (t : ℕ) (table address : List Bool) (q : ℕ) : Fin t → List Bool :=
  fun i => if h : i.val < 3 then threeWords table address q ⟨i.val, h⟩ else []

/-- **The Case 1 machine (statement, (a′) form; the near-cubic-gates paper's extraction of the hard table to its uniform recovery).** For every schedule amplifier, one fixed
machine, started on `frame (List.ofFn w) ++ rest`, `frame (List.ofFn point)` and `1^q`, returns the framed value at
`point` of the amplified periodic function `cycFn a w q`, padded to the final arity `n` (`GateParams.amplified`),
whenever `1 ≤ q ≤ n` and the amplified arity fits `n`, within `C·(2^n+1)^E`. -/
def CaseOneRuns : Prop :=
  ∀ {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d),
    ∃ (t states : ℕ) (machine : LocalBitMultitape.Machine t states) (output : Fin t), 3 ≤ output.val ∧
    ∃ C E : ℕ, ∀ (a q : ℕ) (w : BitInput (2 ^ a)) (rest : List Bool) (n : ℕ) (point : BitInput n),
      1 ≤ q → q ≤ n → (amplifier.output q (cycFn a w q)).arity ≤ n →
      ∃ out, ClockJoin.ReadyRun machine (C * (2 ^ n + 1) ^ E)
        (oneInput t (RepairOrdinary.frame (List.ofFn w) ++ rest) (RepairOrdinary.frame (List.ofFn point)) q) out ∧
        out output = RepairOrdinary.frame (GateParams.amplified amplifier q (cycFn a w q) n point).toNat.bits

end NearCubicGates.Close.Recovery
