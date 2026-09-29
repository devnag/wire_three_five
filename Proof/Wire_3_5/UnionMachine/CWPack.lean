import Proof.Wire_3_5.UnionMachine.CWSym

/-! # C6 front, U5: the code writers as terms of the interface (FP's (b1))

A writer is a machine, its ports, its time polynomial and its run. The packers below take the machine and the run
as ARGUMENTS, so the structure is built over an abstract machine: the kernel checks a writer term by substitution only
and never compares a concrete machine (such as the carrier core `CWMain.coreM`, 913 tapes) with a projection of a
stage constant, the comparison that made every direct packaging recurse too deep in the kernel.

* **`carrierWriterOf`**, **`parityWriterOf`**, **`envWriterOf`**: a writer of the interface from a run.
* **`symCarrierWriter`**: the `SYM∘THR` carrier writer, FP's `CWSym.sym_ready` on `CWMain.coreM`.

Paper quantity of the main type: the code of a call's named carrier (P3:3071-3094, 3673-3674). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWPack
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters NearCubicWires.WireExponent3_5.UnionMachine.CWIface
open NearCubicWires.RepairRepresentation (natWord)

/-- **A carrier writer of mode `m`** from a machine, its ports, its time polynomial `K·(n+1)^d` and its run. -/
def carrierWriterOf (m : Mode) {t s : ℕ} (M : Machine t s) (inS outS : Fin t) (hio : inS ≠ outS) (K d : ℕ)
    (h : ∀ (q : ℕ) (cs : List (m.Circuit q)),
      ∃ J : Fin t → List Bool, (∀ j, (J j).length ≤ K * ((codesWord m cs).length + q + 1) ^ d) ∧
        ClockJoin.ReadyRun M (K * ((codesWord m cs).length + q + 1) ^ d) (inBank inS (codesWord m cs))
          (outBankJ inS outS (codesWord m cs) (natWord (Stars.Carrier.code (carrierOf m cs))) J)) :
    CarrierWriterJ m where
  t := t
  s := s
  M := M
  inS := inS
  outS := outS
  hio := hio
  K := K
  d := d
  carrier_ready := h

/-- **A parity writer of mode `m`** from a machine, its ports, its time polynomial and its run. -/
def parityWriterOf (m : Mode) {t s : ℕ} (M : Machine t s) (inS outS : Fin t) (hio : inS ≠ outS) (K d : ℕ)
    (h : ∀ (q : ℕ) (S : Finset (Fin q)),
      ∃ J : Fin t → List Bool, (∀ j, (J j).length ≤ K * ((bitmap S).length + q + 1) ^ d) ∧
        ClockJoin.ReadyRun M (K * ((bitmap S).length + q + 1) ^ d) (inBank inS (bitmap S))
          (outBankJ inS outS (bitmap S) (natWord (m.code (unionParityAtom m q S))) J)) :
    ParityWriterJ m where
  t := t
  s := s
  M := M
  inS := inS
  outS := outS
  hio := hio
  K := K
  d := d
  parity_ready := h

/-- **The `SYM∘THR` carrier writer**: FP's core machine and run (`CWSym.sym_ready`). -/
noncomputable def symCarrierWriter : CarrierWriterJ .sym :=
  carrierWriterOf .sym CWMain.coreM 0 1 (by decide) (CWBounds.Kc + 3) 26 CWSym.sym_ready

end NearCubicWires.WireExponent3_5.UnionMachine.CWPack
