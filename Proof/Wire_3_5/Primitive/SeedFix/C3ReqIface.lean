import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase
import Proof.Wire_3_5.Primitive.SeedFix.C4Geo
import Proof.Wire_3_5.Compiler.MachinePoolContract2

/-! # The C3 request writer's interface: the compiler's fixed fields of a call, from the request

P3:1886-1906 (alg:compiler: the request is one framed record of framed fields), P3:1636-1664 (alg:pullback: "the
common pool" of the call's geometry, P3:1661-1664), P3:3034-3037 ("For each candidate child prefix, print its signed
equation expression [...] and sum the recovered integers"): per call, the compiler's fields other than the expression
are fixed, and C4's children assemble `frame (PRE ++ frame (exprWord V) ++ POST)` (`C4Iface.AsmStage`). This file fixes
the writer of `PRE` and `POST` from the request word and the four free numbers `h`, `Q'`, `m`, `pr` (in unary):

* `r0` (the call's request at the pool `gates`, `C4Sym.symR0`'s form, mode-generic), `preW`, `postW` (fields `0 … 7`
  and `9 … 10` of `c3Fields`, each framed), `preW_irrel`, `postW_irrel` (independent of `ψ`, `d`, `k`);
* `c3In`, `c3Out`, `C3Run` (the inputs kept, `frame PRE` on `preS`, `frame POST` on `postS`, residues within the budget,
  every head at `0`), `C3Stage`;
* **`C3ReqAt`** (SYM at `Records.symPool`, THR at `Records.thrPool`; the budget `c_W·classBound E_W .preprocessing` at the
  call, for every `h, Q', m, pr` with `1 ≤ h`, `CoefFit`, `h + Q' + m + pr ≤ c_N·(ψ(n) + 1)`), **`C3ReqLeaf`** (`c_N`,
  then `fe`, the floors `E_W`, `F`, `c_W`).

Paper quantities of the main type: the compiler's fixed fields `preW`/`postW` of the call's request (the pool records
`poolRecs`, the children table, the counts, the table's header and columns). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C3ReqIface
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-! ## The call's request and its fixed fields -/

section Req
variable (P : StarParams) (σ : P.Translation)

/-- **The call's compiler request at the pool `gates`** (`C4Sym.symR0`'s form, mode-generic): the pool of the call's
geometry, the expression empty (each child replaces it), the table's rows `dRow` and columns `cols`. -/
def r0 (gates : List (NormalizedThresholdGate P.n)) (h Q psi m d pr k : ℕ) : CompilerMachine.Req.C3Req :=
  ⟨C4Geo.poolReq P σ gates h Q psi, [], m, d, C4Geo.dRow P, C4Geo.cols P, pr, k, psi⟩

end Req

variable (a : DecompositionAlgorithm)

/-- **`PRE`**: the compiler's fields before the expression (`c3Fields` `0 … 7`), each framed. -/
def preW (R : CompilerMachine.Req.C3Req) : List Bool := ((CompilerMachine.Req.c3Fields a R).take 8).flatMap frame

/-- **`POST`**: the compiler's fields after the expression (`c3Fields` `9 … 10`), each framed. -/
def postW (R : CompilerMachine.Req.C3Req) : List Bool := ((CompilerMachine.Req.c3Fields a R).drop 9).flatMap frame

/-! ## The writer's run -/

/-- The writer's entry bank: `frame w` on `inS`, `1^h`, `1^Q'`, `1^m`, `1^pr` on their tapes, every other tape
blank. -/
def c3In {t : ℕ} (inS hS qS mS pS : Fin t) (w : List Bool) (h Q m pr : ℕ) : Fin t → List Bool :=
  fun i => if i = inS then frame w else if i = hS then List.replicate h true else if i = qS then List.replicate Q true
    else if i = mS then List.replicate m true else if i = pS then List.replicate pr true else []

/-- The writer's exit bank: the inputs kept, `frame pre` on `preS`, `frame post` on `postS`, the residue `J j` on
every other tape. -/
def c3Out {t : ℕ} (inS hS qS mS pS preS postS : Fin t) (w : List Bool) (h Q m pr : ℕ) (pre post : List Bool)
    (J : Fin t → List Bool) : Fin t → List Bool :=
  fun i => if i = preS then frame pre else if i = postS then frame post
    else if i = inS ∨ i = hS ∨ i = qS ∨ i = mS ∨ i = pS then c3In inS hS qS mS pS w h Q m pr i else J i

/-- **The writer's run** within `B` steps (residues at most `B`, every head at `0` at both ends). -/
def C3Run {t s : ℕ} (M : Machine t s) (B : ℕ) (inS hS qS mS pS preS postS : Fin t) (w : List Bool)
    (h Q m pr : ℕ) (pre post : List Bool) : Prop :=
  ∃ J : Fin t → List Bool, (∀ j, (J j).length ≤ B) ∧
    ClockJoin.ReadyRun M B (c3In inS hS qS mS pS w h Q m pr) (c3Out inS hS qS mS pS preS postS w h Q m pr pre post J)

/-- **A C3 request writer**: one machine, its request port, the four number ports and the two output ports. -/
structure C3Stage where
  t : ℕ
  s : ℕ
  M : Machine t s
  inS : Fin t
  hS : Fin t
  qS : Fin t
  mS : Fin t
  pS : Fin t
  preS : Fin t
  postS : Fin t
  distinct : [inS, hS, qS, mS, pS, preS, postS].Nodup

/-! ## The writer at the gate's call families -/

section At
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

end At

end NearCubicWires.WireExponent3_5.PrimT.C3ReqIface
