import Lean
import Proof.Wire_3_5.UnionMachine.RadLink
import Proof.Wire_3_5.FinalPass.RadPre
import Proof.Wire_3_5.FinalPass.RadCaps
import Proof.Wire_3_5.FinalPass.RadBW6
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrSide7
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.RadCallBase


noncomputable section
set_option maxRecDepth 4096


/-! # RADIX: the setup at a THR call (stages 2 to 6 and the value links; P3:2585-2623, P3:2150-2157; #170,
#183)

At a THR call, from the setup's entry `RadSetupB3.RsIn4` (the request and the fixed hash's bits on `0`, W6's words on
`130 … 132`, the payloads on `133 … 136`, the twenty values in `410 …`), **`radixW`** = C1's digit program
(`RadDigs.digsP`, stage 2) ; `RadAsm.radixB` at the block writer `FinalPass.RadB.radBlockW3` (stages 3 to 6) ends in
**`RadSetupB3.RadReadyB2`** for Route B's request `qC = reqB (radReqOf …) G ((4row+4)G) (4S₁+1) (M+2+S₂+(J+1)G)`:

* the value links: the call's majorant `mpC` is W6's `thrMP M A B_* K` (`mpC_eq`), its level records are the window
  records, its seed word and rows are the table builder's (`HashSeed.revWord_eq`, `Hash4.rowF_eq`), the list data is
  `thrCallD = dataBits mpC hashBits`, `listBound = 4S₁+1`;
* the record (`RadLink.record_frame`), the admissibility (the `radPre`), the capacities (the `radCaps` with
  `RadBnd.thrDigs_caps` and the table word's length `lw`);
* `RunCaps` (the capacity premises of `RadAsm.radixB_run`, as one structure), **`radix_call`**.

Paper quantity of the main type: the RADIX row's C2 request `radReqOf … g pr s row` at Route B's capacities, on the
record stream (`RadReadyB2`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires.RepairOrdinary.SignedSortKey

/-! ## The capacity premises of stages 3 to 6, as one structure -/

/-! ## The setup at a THR call -/

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- The call's fixed-hash majorant parameters (its hash bits are drawn at these). -/
noncomputable abbrev mpC : MajorantParams :=
  thrMajorant ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)

/-- The call's hash bits. -/
noncomputable abbrev hbC : Fin (2 * (mpC l F kclk coef A a ha hs Cs carriers).t * (mpC l F kclk coef A a ha hs Cs carriers).ell0) → Bool :=
  FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)

/-- The pool size `G = |thrPool|`. -/
noncomputable abbrev gC : ℕ := (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length

/-- The level records as pairs `(pow W'_j, W'_j)`. -/
noncomputable abbrev prsC : List (ℕ × ℕ) :=
  (FinalPass.ListEval.levels (mpC l F kclk coef A a ha hs Cs carriers).J).map fun j =>
    (FinalPass.ListEval.pow (FinalPass.ListEval.topW (mpC l F kclk coef A a ha hs Cs carriers).J (mpC l F kclk coef A a ha hs Cs carriers).W j),
      FinalPass.ListEval.topW (mpC l F kclk coef A a ha hs Cs carriers).J (mpC l F kclk coef A a ha hs Cs carriers).W j)

/-- **Route B's request at the call.** -/
noncomputable abbrev qC (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
    (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) (s : ZMod pr.val) (row : ℕ) : RadSetupB.RadReqB :=
  reqB (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row) (gC l F kclk coef A a ha hs Cs carriers) ((4 * row + 4) * gC l F kclk coef A a ha hs Cs carriers)
    (4 * ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum + 1)
    ((mpC l F kclk coef A a ha hs Cs carriers).M + 2 + (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length + ((mpC l F kclk coef A a ha hs Cs carriers).J + 1) * gC l F kclk coef A a ha hs Cs carriers)

theorem mpC_eq : mpC l F kclk coef A a ha hs Cs carriers = thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den := by
  have ht : thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers = (callNums l F kclk coef A a ha hs Cs carriers).tt := by
    unfold thrCallT
    rw [← thrNumVals_A (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap]
    rfl
  have hJ : thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers = (callNums l F kclk coef A a ha hs Cs carriers).J := by
    unfold thrCallJ
    rw [← thrNumVals_A (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap]
    rfl
  show thrMajorant ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) = _
  rw [ht, hJ]
  exact thrNumVals_MP ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (callInputs l F kclk coef A a ha).D _

theorem sum_prsC : ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum = ∑ j ∈ Finset.range (mpC l F kclk coef A a ha hs Cs carriers).J, (mpC l F kclk coef A a ha hs Cs carriers).W j := by
  rw [← RadScan.sum_topW]
  unfold prsC
  rw [List.map_map]
  rfl

end Call

/-- The call's words for stages 3 to 6. -/
noncomputable abbrev lsC (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
    (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) : List (List ℕ) :=
  List.ofFn fun d => Records.thrDigGis ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) g pr d

section CallLemmas
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n)) (translation : List ℕ) (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
  (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) (s : ZMod pr.val) (row : ℕ)

theorem digs_lsC : (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).digs =
    (lsC l F kclk coef A a ha hs Cs carriers g pr).map fun gis => (gis.length, CompilerMachine.Pool.labsOf (gC l F kclk coef A a ha hs Cs carriers) row gis) := by
  unfold radReqOf Records.thrDigs lsC
  rw [List.map_ofFn]
  rfl

/-- **The framed request record is the cell's record stream.** -/
theorem qC_record : frame (qC l F kclk coef A a ha hs Cs carriers translation g pr s row).record =
    RadFieldsP.fieldsWordB ((1048576 * xOf (gC l F kclk coef A a ha hs Cs carriers) row (mpC l F kclk coef A a ha hs Cs carriers).M (lsC l F kclk coef A a ha hs Cs carriers g pr).length (mpC l F kclk coef A a ha hs Cs carriers).J pr.val ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length) ^ 40) ((1048576 * xOf (gC l F kclk coef A a ha hs Cs carriers) row (mpC l F kclk coef A a ha hs Cs carriers).M (lsC l F kclk coef A a ha hs Cs carriers g pr).length (mpC l F kclk coef A a ha hs Cs carriers).J pr.val ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length) ^ 40 + 1) (mpC l F kclk coef A a ha hs Cs carriers).M (lsC l F kclk coef A a ha hs Cs carriers g pr).length pr.val s.val ((1048576 * xOf (gC l F kclk coef A a ha hs Cs carriers) row (mpC l F kclk coef A a ha hs Cs carriers).M (lsC l F kclk coef A a ha hs Cs carriers g pr).length (mpC l F kclk coef A a ha hs Cs carriers).J pr.val ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length) ^ 45) ++
      (lsC l F kclk coef A a ha hs Cs carriers g pr).flatMap (fun gis => RadBlk.digBlocks (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
        gis (gC l F kclk coef A a ha hs Cs carriers) row) ++ [true, false, false] := by
  have hd := digs_lsC l F kclk coef A a ha hs Cs carriers translation g pr s row
  have hlen : (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).digs.length =
      (lsC l F kclk coef A a ha hs Cs carriers g pr).length := by rw [hd, List.length_map]
  rw [RadLink.record_frame _ _ _ _ _ (gC l F kclk coef A a ha hs Cs carriers) row (lsC l F kclk coef A a ha hs Cs carriers g pr) hd rfl]
  have eU : RadSpec.radU (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).D.M
      (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).digs.length (gC l F kclk coef A a ha hs Cs carriers) ((4 * row + 4) * gC l F kclk coef A a ha hs Cs carriers)
      (4 * ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum + 1)
      ((mpC l F kclk coef A a ha hs Cs carriers).M + 2 + (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length + ((mpC l F kclk coef A a ha hs Cs carriers).J + 1) * gC l F kclk coef A a ha hs Cs carriers)
      (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).p
      (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).b0 = (1048576 * xOf (gC l F kclk coef A a ha hs Cs carriers) row (mpC l F kclk coef A a ha hs Cs carriers).M (lsC l F kclk coef A a ha hs Cs carriers g pr).length (mpC l F kclk coef A a ha hs Cs carriers).J pr.val ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length) := by
    rw [hlen]
    rfl
  show RadFieldsP.fieldsWordB (RadSpec.radRB _) (RadSpec.radRB _ + 1) _ _ _ _ (RadSpec.radCapB _) ++ _ ++ _ = _
  rw [eU, hlen]
  rfl

/-- **The request is admissible and Route B's capacities meet the row's conditions.** -/
theorem qC_ready (ha' : a' ≤ 4) (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hrow : row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2) :
    (qC l F kclk coef A a ha hs Cs carriers translation g pr s row).r.Pre ∧ (qC l F kclk coef A a ha hs Cs carriers translation g pr s row).Caps := by
  have hpre := FinalPass.RadB.radPre l F kclk coef A a ha n hs a' ha' Cs carriers translation hcall g pr s row hrow
  refine ⟨hpre, FinalPass.RadB.radCaps _ _ _ _ _ hpre (by rw [RadScan.listBound_eq, sum_prsC]; rfl) ?_ ?_⟩
  · intro dg hdg
    exact RadBnd.thrDigs_caps ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg _ g pr row dg hdg
  · rw [RadScan.levelWord_length _ _ _ _ (gC l F kclk coef A a ha hs Cs carriers) (RadDig.rowsOf_len _ (gC l F kclk coef A a ha hs Cs carriers)), ← (RadScan.winRecs_eq (mpC l F kclk coef A a ha hs Cs carriers))]
    rfl

end CallLemmas

end NearCubicWires.WireExponent3_5.UnionMachine.RadCall

end
