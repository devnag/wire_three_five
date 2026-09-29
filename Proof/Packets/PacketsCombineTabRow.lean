import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.OfFn
import Std.Tactic
import Proof.Packets.MaskSelect
import Proof.Packets.PacketsXNormalizedDegreeCore
import Proof.Packets.PhysicalCopyInto
import Proof.Packets.PhysicalRepeatStep

/-! # P2 (iii) table writer, part 3: the row machine (one code's row of the THR selection table)

Consumer: the THR selection-table writer (`ThrMeta`'s tape 15, `Proof/Packets/PacketsCombineThrLocal.lean`): per code `c`
(ascending) the one-hot blocks of its digit tuple, then the acceptance bit
`modularTupleAccepts prime residue 2` = `decide ((res + radixList ds 0) % p = 0)` (`rowOf`,
`PacketsCombineTabMeaning`). Paper: A.13.7 (`paper.tex:3113-3142`), the tuples are internal preprocessing
charged in `T_prep` (`paper.tex:1197-1200`); budget class source-polynomial (a fixed polynomial of
`m, D, p, res`).

`rowM : Machine 8 22`, tapes: `0` the marker `[true]`, `1` the tuple tape `Tt m ds`, `2` the block-end tape
`Bt m D` (these three are the odometer's), `3` a word reading as `word (D*m)` (the copy bound), `4` the
residue register `R` (reads as `word (p-1)`; value = head position), `5` the doubling register (reads as
`word p`), `6` a word reading as `word res`, `7` the output (appended at its end).
Phases: copy the `D*m` tuple cells to the output (states `0,1`); walk back over the blocks, most significant
first, computing `radixList ds 0 mod p` by Horner's rule (states `2..13`: at each block `R := 2R mod p` through
the doubling register, then `+ digit` by counting the cells left of the set bit); add `res` (states
`14..17`); append `R = 0` and rewind (states `18..20`). No division, no binary arithmetic: every register
operation is a head walk. This module: the machine, its configurations, every transition, the register
walks.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

/-! ## The machine -/

/-- The seven tapes the row machine only reads. -/
structure RowTapes where
  L : List Bool
  T : List Bool
  B : List Bool
  KW : List Bool
  R : List Bool
  R2 : List Bool
  RS : List Bool

/-- The row configuration: group head `g` (tapes `0..3`), `R` at `x`, doubling register at `y`, residue
word at `z`, output head at its end. -/
def rc (W : RowTapes) (q : Fin 22) (g x y z : ℕ) (out : List Bool) : Configuration 8 22 :=
  ⟨q, ![g, g, g, g, x, y, z, out.length], ![W.L, W.T, W.B, W.KW, W.R, W.R2, W.RS, out]⟩

@[simp] theorem rc_control (W : RowTapes) (q : Fin 22) (g x y z : ℕ) (out : List Bool) :
    (rc W q g x y z out).control = q := rfl

/-! ## Transitions -/

section Trans

end Trans

/-! ## Registers reading as unary words -/

/-! ## Left walks on one register -/

section Walks

end Walks

/-! ## One modular increment of `R` -/

section Inc

end Inc

/-! ## Doubling `R` modulo `p` -/

section Double

end Double

end NearCubicWires.PacketsCombine.Tab

