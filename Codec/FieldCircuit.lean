import Codec.FieldGate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Table bits -/

/-! ## A counted emitting loop -/

/-! ## The circuit field, read at a position -/

/-- Positions inside a circuit field at `p` on native width `q`. -/
def cK (w : List Bool) (p : ℕ) : ℕ := fieldLen w p
def cP1 (w : List Bool) (p : ℕ) : ℕ := p + cK w p + 1
def cPg (w : List Bool) (p q : ℕ) : ℕ := iter (fun r => gateEnd w r q) (cP1 w p) (cK w p)
def cPc (w : List Bool) (p q : ℕ) : ℕ := iter (intEnd w) (cPg w p q) (cK w p)
def cL (w : List Bool) (p q : ℕ) : ℕ := fieldLen w (cPc w p q)
def cP2 (w : List Bool) (p q : ℕ) : ℕ := cPc w p q + cL w p q + 1
def circuitEnd (w : List Bool) (p q : ℕ) : ℕ := cP2 w p q + cL w p q

/-! ## States of the circuit transcoder -/

section Shape

end Shape

end NearCubicGates.Close.Codec
