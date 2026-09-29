import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJ

/-! # THR, W7 seam: the RADIX row setup TYPE (`RadSetupSpec`; builds it, THR docks it)

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
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- The THR numbers at the call (`Dexp = D`, the call's carriers and THR filter cap). -/
noncomputable abbrev callNums : ThrNumVals :=
  thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (callInputs l F kclk coef A a ha).D
    carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap

/-- **The twenty register values** of the RADIX setup: `gi` (the selection's index), `p`, `s`, the star row, `|thrPool|`,
the occurrence offset `thrOff`, `n`, then W6's `|𝒢|, K, cut, #primes, Σp, τ₀, M, A, B_*, J, t, ℓ₀, p_mod`. -/
noncomputable def radVals (gi p s row : ℕ) : Fin 20 → ℕ :=
  ![gi, p, s, row, (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length,
    Records.thrOff ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers, n,
    (callNums l F kclk coef A a ha hs Cs carriers).nG, (callNums l F kclk coef A a ha hs Cs carriers).den,
    (callNums l F kclk coef A a ha hs Cs carriers).cut, (callNums l F kclk coef A a ha hs Cs carriers).nPr,
    (callNums l F kclk coef A a ha hs Cs carriers).pSum, (callNums l F kclk coef A a ha hs Cs carriers).dig,
    (callNums l F kclk coef A a ha hs Cs carriers).M, (callNums l F kclk coef A a ha hs Cs carriers).A,
    (callNums l F kclk coef A a ha hs Cs carriers).Bs, (callNums l F kclk coef A a ha hs Cs carriers).J,
    (callNums l F kclk coef A a ha hs Cs carriers).tt, (callNums l F kclk coef A a ha hs Cs carriers).ell0,
    (callNums l F kclk coef A a ha hs Cs carriers).pMod]

/-- **The RADIX row's C2 request** at selection `g`, prime `pr`, residue `s`, star row `row`. -/
noncomputable def radReqOf (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
    (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (s : ZMod pr.val) (row : ℕ) : ListMachine.Row.RadReq :=
  ⟨Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation,
    Records.thrDigs ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) g pr
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length row,
    pr.val, 2, s.val, n⟩

/-- The THR entry's RADIX row is `radReqOf`'s request (`Records.thrGroups`' last group). -/
theorem radRow_eq (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
    (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (s : ZMod pr.val) (row : ℕ) :
    Records.radRow ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) g pr s
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length row n =
      .rad (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row) := rfl

end Call

end NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
