import Proof.Wire_3_5.UnionMachine.RadSetupB2

/-! # RADIX, Route B, exit v2: the setup's exit with the pipe's blank streams (`RadReadyB2`, `RadSetupSpecB3`)

P3:2585-2623. `RadSetupB.RadReadyB` (as `Joins.RadReady`) demands EVERY stream outside `0, 1, 2, 3, 113, 150` empty,
but the entry `RsIn3` has W6's words on `130`, `131`, `132` (`frame (binary ℓ₀ p_mod)` is never empty) and the
payloads on `133 … 136`, and a machine's tapes never shrink (`writeTapeBit`): `RadSetupSpecB2` has no inhabitant.
Likewise `RsIn3.blankT` is not reachable (the unit chain's ports leave residues on the scratch tapes `sT`). The RADIX
pipe (`RadPipe.radPipe_ready`) reads the blank streams only on its scratch `portP j = 29 + j` (`30 … 76`) and no `sT`.

* **`RsIn4`**: `RadSetupB2.RsIn3` without `blankT`;
* **`RadReadyB2`**: `RadReadyB` with `blank` on the streams below `130` (outside `0, 1, 2, 3, 113`), no `blankT`;
* **`RadSetupSpecB3 x l F`**: `RadSetupB2.RadSetupSpecB2` from `RsIn4`, ending in `RadReadyB2`.

Paper quantity of the main type: the RADIX row's C2 request (`RadSetup.radReqOf`) with its row's capacities. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB2

/-- **The RADIX setup's entry bank, v4** (addendum): `RadSetupB2.RsIn3` without `blankT` (the unit chain's
number and front-end ports leave residues on the producer's scratch tapes `sT`). -/
structure RsIn4 (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (v : Fin 20 → ℕ)
    (prW winW modW : List Bool) (ncar capT : ℕ) (pays : Fin 4 → List Bool) (a' : ℕ) : Prop where
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s113 : σ.st (sk x 113) = u
  h113 : σ.sh (sk x 113) = 0
  sPr : σ.st (sk x sPrK) = prW
  hPr : σ.sh (sk x sPrK) = 0
  sWin : σ.st (sk x sWinK) = winW
  hWin : σ.sh (sk x sWinK) = 0
  sMod : σ.st (sk x sModK) = modW
  hMod : σ.sh (sk x sModK) = 0
  sPay : ∀ i : Fin 4, σ.st (sk x (sPayK i)) = pays i
  hPay : ∀ i : Fin 4, σ.sh (sk x (sPayK i)) = 0
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → k.val ≠ 130 → k.val ≠ 131 →
    k.val ≠ 132 → (k.val < 133 ∨ 137 ≤ k.val) → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  vals : ∀ i : Fin 20, σ.val (rsReg i) = v i
  vNc : σ.val rNcK = ncar
  vCap : σ.val rCapK = capT
  vA : σ.val rAK = a'
  zero : ∀ r : Fin LNR, (r.val < 250 ∨ (400 ≤ r.val ∧ r.val < 410) ∨ 433 ≤ r.val) → σ.val r = 0
  cell : σ.cell = false

/-- **A Route-B RADIX-ready cell state, v2**: `RadSetupB.RadReadyB` with the blank streams only below `130`
(outside the request `0`, the output `1`, the counter `2`, the record `3` and the data `113`), no `blankT`. -/
structure RadReadyB2 (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (q : RadReqB) :
    Prop where
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s3 : σ.st (sk x 3) = frame q.record
  h3 : σ.sh (sk x 3) = 0
  s113 : σ.st (sk x 113) = u
  h113 : σ.sh (sk x 113) = 0
  s150 : σ.st (sk x 150) = [true]
  h150 : σ.sh (sk x 150) = 0
  blank : ∀ k : Fin 161, k.val < 130 → k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 3 → k.val ≠ 113 →
    σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  pre : q.r.Pre
  caps : q.Caps

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3
