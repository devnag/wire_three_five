import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpec
import Proof.Wire_3_5.FinalPass.DigsIface

/-! # RADIX, Route B, v4: the setup's bounds polynomial in the RADIX row's explicit capacity

`RadSetupB3.RadSetupSpecB3` (RADB4) asks `need`, `bound`, `pipe` to be quasi-bounded in `n`
(`C·(n+2)^D·2^{K·L²}`). The RADIX row cannot meet that: its factor stages cost
`costC ≥ (4L_d+1)^{3·listBound D}·2^{3·listBound D}` (lists-machine `RowPopRec.costC`), Route B's record carries the
scrub capacity `R ≥ costC` in unary, and `listBound (thrCallD) = 4·Σ_{j<J} W_j + 1 ≥ 64·J·t = Θ(L²)`
(`W_j = ⌈8C₁(√(tB_*2^{-j})+t)⌉`, P3). As for the SYM POP rows (`PopSetup.PopSetupSpecB2`), the
bounds are polynomial in the row's explicit capacity, and the class link absorbs it through the THR load `Ψ_T`
(P3:3094-3108; the absorption lemma is `RadAbsorb`).

* **`radMeas`**: the RADIX row's explicit capacity measure at a call: Route B's `radX` (the digit lists' counting
  capacity `(8G+2)^{3·lb+1}` with `lb = listBound (thrCallD)`, `M`, `τ₀`, `G`, `Mlab`, `lb`, the table word's length,
  `p`, `b₀`), the digit tuples `(M+1)^{2τ₀}`, the request's length, `t`, `ℓ₀`, `J` and the digit program's measure;
* **`RadSetupSpecB4 x l F`**: `RadSetupSpecB3`'s run from `RsIn4` to `RadReadyB2`, with `need (radMeas …) ≤ cap`,
  the cost `≤ bound cap`, `q.bound ≤ pipe (radMeas …)`, and `need`, `bound`, `pipe` polynomial (`Kn(X+1)^Dn` …).

Paper quantity of the main type: the RADIX row's C2 request (`RadSetup.radReqOf`) with its row's capacities, within
the preprocessing class `2^{O(Ψ)}` (prim:runtime P3:3089-3108). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- **The RADIX row's explicit capacity measure** at prime `pr` and star row `row`. -/
noncomputable def radMeas (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) (row : ℕ) : ℕ :=
  RadSpec.radX (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ((4 * row + 4) * (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length)
      (ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation))
      (FinalPass.ListEval.levelWord (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W
        (FinalPass.ListEval.rowsOf (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
          (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length)).length pr.val 2 +
    ((thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length + 1) ^ (2 * thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) +
    ((thrReq n a' ha' Cs carriers translation).word ++ frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))).length +
    thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers + thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers +
    FinalPass.Digs.digsN ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) pr.val

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB4
