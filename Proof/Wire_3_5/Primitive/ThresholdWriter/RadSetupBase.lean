import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase

/-! # THR, W7 seam: the RADIX row setup TYPE (`RadSetupSpec`; PA2 builds it, THR docks it)

P3:2585-2623 (row:radix): row `(g, p)` reduces its coefficients modulo `p`, writes each `a_i` in radix `b₀ = 2` with
`τ₀` digits, gives residual `Z_i^±` exactly `v_{i,d}` labelled copies per digit and sign, applies the single fixed count
hash of `filt:soft` to every digit population, and prints `H_{g,p,s}` of `(row:radix)`; "the `2^{O(L²)}` internal digit
tuples are expansion preprocessing". A THR entry's last printed row is `Records.radRow … D g pr s G row n`, whose C2
request is **`radReqOf`** (`radRow_eq`): the fixed hash's list data `D = thrCallD` (`MajorantBits.dataBits` of the
majorant parameters and the hash bits), the digits `thrDigs … g pr G row`, `p`, `b₀ = 2`, `s`, `n`.

* `rsReg i = 410 + i` (`i < 20`), streams `130`, `131`, `132`: the setup's inputs on the cell layout;
* **`radVals`**: the twenty register values (the row's indices, then W6's numbers);
* **`RsIn`**: the setup's entry bank (the unit's request, output, counter and data kept as in `FsIn2`; the twenty
  values; W6's three words; heads `0` but the output's; registers outside `250 … 399` and `410 … 429` zero; the cell
  `false`);
* `QuasiBounded` (`v ≤ C·(n+2)^D·2^{K·L²}`, `L = ⌈log₂(n+2)⌉`: the paper's `2^{O(L²)}` expansion);
* **`RadSetupSpec x l F`**: a machine on the cell layout's encoded banks, from `RsIn` at every THR call of the gate, to
  `Joins.RadReady` for `radReqOf` (C2's `radContract` input on stream `3`, the RADIX flag on `150`).

Paper quantity of the main type: the RADIX row's C2 request (its record `radRowRecC D digs p 2 s`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins

/-! ## The inputs on the cell layout -/

/-- The setup's twenty input registers `410 … 429`. -/
def rsReg (i : Fin 20) : Fin LNR := ⟨410 + i.val, by have := i.isLt; unfold LNR; omega⟩

/-- The primes stream (W6's `sPr`), the level-records stream (`sWin`), the modulus-word stream (`sMod`). -/
def sPrK : Fin 161 := 130
def sWinK : Fin 161 := 131
def sModK : Fin 161 := 132

/-- The paper's expansion bound `v ≤ C·(n+2)^D·2^{K·L²}`, `L = ⌈log₂(n+2)⌉`. -/
def QuasiBounded (v n C D K : ℕ) : Prop := v ≤ C * (n + 2) ^ D * 2 ^ (K * Nat.clog 2 (n + 2) ^ 2)

section Call

end Call

end NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
