import Lean
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.Primitive.Writers.FiltSetupIface2
import Proof.Wire_3_5.Primitive.Writers.CellLoopD
import Proof.Wire_3_5.Primitive.Writers.SymDecBr
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase


noncomputable section
set_option maxRecDepth 4096


/-! # The THR unit's decode front: the contract between the decode (T3) and the unit machine (C6b)

P3:2543-2558 (the THR call's numbers once per call), P3:2019-2054 (the FILTER rows), P3:2585-2623 (the RADIX row);
the THR tape's units as in `SymFlat.symEmit (|carriers|+1) 0` (per entry `[true]`, per row `[true]`, the row's
request, `[false]`, then `[false]`; `thrEU nc = (nc+1)·3 + 2` units per entry). From the unit's fresh cell
`CellLoopD.blankCellD x w out j u` (the call's request word `w`, the counts `u` on `113`), the decode front leaves:

* at a RADIX request unit (row `r = nc`): register `rRadK ≠ 0`, `rFltK = 0`, and the RADIX setup's entry
  `RadSetupB3.RsIn4` at the unit's `(g, p, s, row)` (W6's words on `130 … 132`, the payloads on `133 … 136`);
* at a FILTER request unit (row `r < nc`): `rRadK = 0`, `rFltK ≠ 0`, and the FILTER setup's entry `FiltSetup.FsIn2` at
  the unit's seed and row slice (`FiltDock5.thrFilt_dock5`'s form);
* at every other unit: both registers `0`, the flags `150`, `151` blank and the unit's emission (a marker, or nothing
  past the call's units) printed: `CellUnit.DecOK`'s first disjunct;
* in every case: the request kept (head `0`) and the counter `1^j` (head `0`).

**`ThrDecFront x l F`**: one machine on the cell layout `LNS x` per gate, quasi-bounded capacity `need` and cost
`bound` in `n`, running at every THR call, every unit `j` and every capacity `≥ need n + j`.

Paper quantity of the main type: the THR call's rows (FILTER and RADIX) at each unit of the THR tape. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- The star rows per state: `N² = (2^{kh})²`. -/
noncomputable def thrN2 : ℕ := (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2

/-- The call's units: `thrNT · N² · thrEU |carriers|`. -/
noncomputable def thrTOT : ℕ :=
  Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs * thrN2 l F kclk coef A a ha hs *
    thrEU carriers.length

/-- The THR call's request word on the unit's cell (the request, then the fixed hash's bits, framed). -/
noncomputable def thrCallW : List Bool :=
  (thrReq n a' ha' Cs carriers translation).word ++
    frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
      ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))

/-- The THR call's counts on stream `113`: the sixteen numbers, then the carriers' sizes and the tuple's count. -/
noncomputable def thrCallU : List Bool :=
  Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
    (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
      ThrData.thrCounts Cs carriers)

/-- The request unit `(e, r)`'s printed body: row `r` of the THR batch's entry `e = (t, row)`. -/
noncomputable def thrCallUnit (e r _s : ℕ) : List Bool :=
  ((WriterIface.thrGrp (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation
    (e / thrN2 l F kclk coef A a ha hs) (e % thrN2 l F kclk coef A a ha hs)).getD r []).flatMap SymFlat.unitBody

/-- Unit `j`'s state index `t` and star row. -/
noncomputable def stOfU (j : ℕ) : ℕ := j / thrEU carriers.length / thrN2 l F kclk coef A a ha hs
noncomputable def rowOfS (j : ℕ) : ℕ := j / thrEU carriers.length % thrN2 l F kclk coef A a ha hs

/-- **What the decode front leaves at unit `j`**. -/
structure ThrDecOut (x : ℕ) (cap : ℕ) (σ : WState (LNS x) LNR) (out : List Bool) (j : ℕ) : Prop where
  s0 : σ.st (sk x 0) = frame (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
  h0 : σ.sh (sk x 0) = 0
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  rad : ∀ ht : stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs,
    IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j → rowOfU carriers.length j = carriers.length →
    σ.val rRadK ≠ 0 ∧ σ.val rFltK = 0 ∧
    RsIn4 x σ (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
      (thrCallU l F kclk coef A a ha hs Cs carriers)
      (radVals l F kclk coef A a ha hs Cs carriers
        (Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.1).val
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.2.1.val
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.2.2.val
        (rowOfS l F kclk coef A a ha hs carriers j))
      (Data.unaryList (primesList (callNums l F kclk coef A a ha hs Cs carriers).cut))
      (winRecs (thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A
        (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den))
      (frame (SignedSortKey.binary (callNums l F kclk coef A a ha hs Cs carriers).ell0
        (callNums l F kclk coef A a ha hs Cs carriers).pMod))
      carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨i.val, h⟩) else []) a'
  filt : ∀ ht : stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs,
    IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j → rowOfU carriers.length j < carriers.length →
    σ.val rRadK = 0 ∧ σ.val rFltK ≠ 0 ∧
    FiltSetup.FsIn2 x σ (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
      (thrCallU l F kclk coef A a ha hs Cs carriers)
      ((callInputs l F kclk coef A a ha).filterParams .thr n).len ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp
      (Enum.gapSeedEquiv ((callInputs l F kclk coef A a ha).filterParams .thr n)
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).1)
      (4 * rowOfS l F kclk coef A a ha hs carriers j)
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length
      (Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)
        (rowOfU carriers.length j))
      ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD
        (rowOfU carriers.length j) []).length
  idle : ¬ IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j →
    σ.val rRadK = 0 ∧ σ.val rFltK = 0 ∧
    σ.st (sk x 150) = [] ∧ σ.sh (sk x 150) = 0 ∧ σ.st (sk x 151) = [] ∧ σ.sh (sk x 151) = 0 ∧
    σ.st (sk x 1) = out ++ SymDec.unitE (thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
      (thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j ++ [false] ∧
    σ.sh (sk x 1) = (out ++ SymDec.unitE (thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
      (thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j).length

end Call

/-- **The THR unit's decode front** (#186; T3 builds it): one machine on the cell layout `LNS x` per gate, with
capacity `need` and cost `bound` quasi-bounded in `n`; at every THR call, every output `out`, unit `j` and capacity
`≥ need n + j`, from the unit's fresh cell to `ThrDecOut`. -/
structure ThrDecFront (x : ℕ) (l : Literals) (F : GateFree l) where
  s : ℕ
  M : Machine (LNS x + 2 + LNR) s
  need : ℕ → ℕ
  bound : ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  Kn : ℕ
  need_q : ∀ n, QuasiBounded (need n) n Cn Dn Kn
  Cb : ℕ
  Db : ℕ
  Kb : ℕ
  bound_q : ∀ n, QuasiBounded (bound n) n Cb Db Kb
  run : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (out : List Bool) (j cap : ℕ), need n + j ≤ cap →
    ∃ (σD : WState (LNS x) LNR) (m : ℕ),
      Step M m (wenc cap (CellLoopD.blankCellD x (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
          (thrCallU l F kclk coef A a ha hs Cs carriers))).H
        (wenc cap (CellLoopD.blankCellD x (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
          (thrCallU l F kclk coef A a ha hs Cs carriers))).A
        (wenc cap σD).H (wenc cap σD).A ∧ m ≤ bound n ∧
      ThrDecOut l F kclk coef A a ha hs ha' Cs carriers translation x cap σD out j

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDec

end
