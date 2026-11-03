import Lean
import Proof.Wire_3_5.UnionMachine.RadNeed
import Proof.Wire_3_5.UnionMachine.ThrUnitIface3
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SeamsUni
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrSide7
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.RadCall
import Proof.Wire_3_5.UnionMachine.RadSetupB4
import Proof.Wire_3_5.UnionMachine.RadSetupB5
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase


noncomputable section
set_option maxRecDepth 4096


/-! # RADIX, Route B: the `RadSetupSpecB5` instance (the setup at every THR call, need/bound/pipe polynomial)

"The RADIX row [...] its digit populations `v_{i,d}` [...] its C2 request" (row:radix P3:2585-2623) within the
preprocessing class (prim:runtime P3:3089-3108): the setup program `RadCall.radixW` (C1's digit program, then stages 3
to 6 with the block writer) runs from `RadSetupB3.RsIn4` to `RadSetupB3.RadReadyB2` for Route B's request
`RadCall.qC … g pr s row` at every capacity `cap ≥ needF (radMeas5 …)`, within `bnd cap`, and the request's pipe
bound is at most `pipeF (radMeas5 …)`; `needF`, `bnd`, `pipeF` are polynomial (`RadNeed`).

* `meas_ge`: the row's numbers are summands of `radMeas5` (`xOf` is its Route-B term);
* `bd_call`: the call's numbers meet `RadNeed.Bd` at `X = radMeas5`;
* `radix_run`: the run with its cost (`RadNeed.runCaps_of`, `RadNeed.cost_le`);
* **`radSetupSpecB5 x l F : RadSetupB5.RadSetupSpecB5 x l F`** (the machine `(radixW x).toProg.compile`);
* **`radStage l xF`**: the family as `Seams.StageU` (`ThrUnitOf3`'s RADIX argument; its exponents and coefficients
  depend on nothing).

Paper quantity of the main type: the RADIX row's C2 request `radReqOf … g pr s row` with Route B's capacities on the
record stream, within `2^{O(Ψ)}` (P3:3089-3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.UnionMachine.RadCall

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n)) (translation : List ℕ) (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
  (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) (row : ℕ)

/-- **The row's numbers are summands of the measure.** -/
theorem meas_ge :
    xOf (gC l F kclk coef A a ha hs Cs carriers) row (mpC l F kclk coef A a ha hs Cs carriers).M (lsC l F kclk coef A a ha hs Cs carriers g pr).length (mpC l F kclk coef A a ha hs Cs carriers).J pr.val ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length + ((thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length + 1) ^ (2 * thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) + ((thrReq n a' ha' Cs carriers translation).word ++ frame (List.ofFn (hbC l F kclk coef A a ha hs Cs carriers translation))).length + (mpC l F kclk coef A a ha hs Cs carriers).t + (mpC l F kclk coef A a ha hs Cs carriers).J + FinalPass.Digs.digsN ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) pr.val + row ≤ (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row) := by
  have e1 : (lsC l F kclk coef A a ha hs Cs carriers g pr).length = thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) := by simp [lsC]
  have e2 : ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) = 4 * ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum + 1 := by rw [RadScan.listBound_eq, sum_prsC]; rfl
  have e3 : (FinalPass.ListEval.levelWord (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W (FinalPass.ListEval.rowsOf (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length)).length =
      (mpC l F kclk coef A a ha hs Cs carriers).M + 2 + (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length + ((mpC l F kclk coef A a ha hs Cs carriers).J + 1) * (gC l F kclk coef A a ha hs Cs carriers) := by
    rw [RadScan.levelWord_length _ _ _ _ _ (RadDig.rowsOf_len _ _), ← RadScan.winRecs_eq (mpC l F kclk coef A a ha hs Cs carriers)]
    rfl
  unfold RadSetupB5.radMeas5 RadSetupB4.radMeas
  rw [e2, e3, e1]
  exact le_of_eq (by unfold xOf; rfl)

variable (s : ZMod pr.val)

/-- **The call's numbers meet `RadNeed.Bd`** at the measure `radMeas5`. -/
theorem bd_call :
    RadNeed.Bd (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row) (thrReq n a' ha' Cs carriers translation).word (List.ofFn (hbC l F kclk coef A a ha hs Cs carriers translation)) (mpC l F kclk coef A a ha hs Cs carriers).t (mpC l F kclk coef A a ha hs Cs carriers).ell0 (mpC l F kclk coef A a ha hs Cs carriers).refMod (mpC l F kclk coef A a ha hs Cs carriers).J
      (gC l F kclk coef A a ha hs Cs carriers) row (mpC l F kclk coef A a ha hs Cs carriers).M pr.val s.val (prsC l F kclk coef A a ha hs Cs carriers) (mpC l F kclk coef A a ha hs Cs carriers).W (lsC l F kclk coef A a ha hs Cs carriers g pr) (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (FinalPass.Hash4.coefsRev (FinalPass.MajorantBits.coefVal (mpC l F kclk coef A a ha hs Cs carriers) (hbC l F kclk coef A a ha hs Cs carriers translation))) := by
  have hm := meas_ge l F kclk coef A a ha hs ha' Cs carriers translation g pr row
  have hx := RadNeed.xOf_ge (gC l F kclk coef A a ha hs Cs carriers) row (mpC l F kclk coef A a ha hs Cs carriers).M (lsC l F kclk coef A a ha hs Cs carriers g pr).length (mpC l F kclk coef A a ha hs Cs carriers).J pr.val ((prsC l F kclk coef A a ha hs Cs carriers).map Prod.snd).sum (RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers)).length
  have hpr : 2 ≤ pr.val := (SupplierPrime.mem_primesUpTo.mp pr.property).1.two_le
  haveI : NeZero pr.val := ⟨by omega⟩
  have hcl := UnionMachine.PopPipeLe.clog_le (mpC l F kclk coef A a ha hs Cs carriers).M
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_, ZMod.val_lt s, by omega, ?_,
    (RadScan.winRecs_eq (mpC l F kclk coef A a ha hs Cs carriers)).symm, rfl, rfl, rfl, FinalPass.Hash4.rowF_eq (mpC l F kclk coef A a ha hs Cs carriers) (hbC l F kclk coef A a ha hs Cs carriers translation) (gC l F kclk coef A a ha hs Cs carriers),
    by rw [RadScan.listBound_eq, sum_prsC]; rfl, ?_, ?_⟩
  · unfold MajorantParams.ell0
    exact max_le (by omega) (by omega)
  · simp [FinalPass.Hash4.coefsRev]
  · simp only [lsC, List.length_ofFn]
    exact ThrSide.dig_pos l F kclk coef A a ha Cs hs
  · intro gis hg
    obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hg
    exact RadBnd.thrDigGis_length_le ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg _ g pr d
  · intro gis hg gi hgi
    obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hg
    exact RadBnd.thrDigGis_lt ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg _ g pr d gi hgi

/-- **The pipe's bound at the call.** -/
theorem pipe_call :
    (qC l F kclk coef A a ha hs Cs carriers translation g pr s row).bound ≤ RadNeed.pipeF (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row) := by
  have hm := meas_ge l F kclk coef A a ha hs ha' Cs carriers translation g pr row
  have hB := bd_call l F kclk coef A a ha hs ha' Cs carriers translation g pr row s
  apply RadNeed.bound_le
  · have e : (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).digs.length = thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) := by
      rw [digs_lsC l F kclk coef A a ha hs Cs carriers translation g pr s row, List.length_map]
      simp [lsC]
    show ((thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length + 1) ^ (2 * (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).digs.length) ≤ _
    rw [e]
    omega
  · have hr := congrArg List.length (qC_record l F kclk coef A a ha hs Cs carriers translation g pr s row)
    rw [frame_length] at hr
    simp only [List.length_append, List.length_cons, List.length_nil] at hr
    have := hB.lu_le
    omega

end Call

/-- **The RADIX setup at a THR call, with its cost**: from `RsIn4` at a capacity above `needF (radMeas5 …)`, the setup
program ends in `RadReadyB2` for Route B's request `qC … g pr s row`, within `bnd cap`. -/
theorem radix_run (x : ℕ) (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (s : ZMod pr.val) (row : ℕ) (hrow : row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2)
    (cap : ℕ) (out : List Bool) (j : ℕ) (u : List Bool) (σ : WState (LNS x) LNR)
    (hin : RadSetupB3.RsIn4 x σ ((thrReq n a' ha' Cs carriers translation).word ++
        frame (List.ofFn (hbC l F kclk coef A a ha hs Cs carriers translation))) out j u
      (radVals l F kclk coef A a ha hs Cs carriers ((Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg g).val) pr.val s.val row)
      (Data.unaryList (primesList (callNums l F kclk coef A a ha hs Cs carriers).cut))
      (winRecs (thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den))
      (frame (binary (callNums l F kclk coef A a ha hs Cs carriers).ell0 (callNums l F kclk coef A a ha hs Cs carriers).pMod))
      carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨i.val, h⟩) else []) a')
    (hneed : RadNeed.needF (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row) ≤ cap) :
    ∃ (σR : WState (LNS x) LNR) (c : ℕ), WExec cap (radixW x) σ σR c ∧ c ≤ RadNeed.bnd cap ∧
      RadSetupB3.RadReadyB2 x σR ((thrReq n a' ha' Cs carriers translation).word ++
        frame (List.ofFn (hbC l F kclk coef A a ha hs Cs carriers translation))) out j u (qC l F kclk coef A a ha hs Cs carriers translation g pr s row) := by
  have hB := bd_call l F kclk coef A a ha hs ha' Cs carriers translation g pr row s
  have hm := meas_ge l F kclk coef A a ha hs ha' Cs carriers translation g pr row
  have hN : FinalPass.Digs.digsN ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) pr.val ≤ (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row) := by omega
  have hdn : FinalPass.DigsBody.digsWImpl.need (FinalPass.Digs.digsN ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) pr.val) ≤ cap := by
    have h1 := FinalPass.DigsBody.digsWImpl.need_le (FinalPass.Digs.digsN ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) pr.val)
    have h2 : FinalPass.DigsBody.digsWImpl.C * (FinalPass.Digs.digsN ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) pr.val + 1) ^ FinalPass.DigsBody.digsWImpl.D ≤
        FinalPass.DigsBody.digsWImpl.C * ((RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row) + 1) ^ FinalPass.DigsBody.digsWImpl.D :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    unfold RadNeed.needF at hneed
    omega
  have hc := RadNeed.runCaps_of cap hB hneed
  have hne : ∀ a b : Fin 161, a ≠ b → sk x a ≠ sk x b := fun a b h e => h (sk_inj x e)
  have hmp := mpC_eq l F kclk coef A a ha hs Cs carriers
  have hpr : 2 ≤ pr.val := (SupplierPrime.mem_primesUpTo.mp pr.property).1.two_le
  haveI : NeZero pr.val := ⟨by omega⟩
  -- stage 2
  have e2 := RadDigs.digs_run (x := x) ((callInputs l F kclk coef A a ha).starParams n hs) ha' Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) g pr
    cap σ hin rfl rfl rfl rfl hdn
  set σ1 := σ.sets (sk x RadDigs.dgK) (FinalPass.Digs.digsWord (lsC l F kclk coef A a ha hs Cs carriers g pr)) with hσ1
  have k137 : ∀ k : Fin 161, k ≠ 137 → σ1.st (sk x k) = σ.st (sk x k) := fun k hk => by
    simp [σ1, Function.update_apply, hne k 137 hk, RadDigs.dgK]
  have v1 : ∀ r, σ1.val r = σ.val r := fun r => rfl
  have b : ∀ k : Fin 161, (k.val = 3 ∨ (138 ≤ k.val ∧ k.val ≤ 148) ∨ k.val = 150) →
      σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0 := fun k hk =>
    hin.blank k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hprs : RadScan.recsW (prsC l F kclk coef A a ha hs Cs carriers) =
      (FinalPass.ListEval.levels (mpC l F kclk coef A a ha hs Cs carriers).J).flatMap (FinalPass.Hash4.winRec (mpC l F kclk coef A a ha hs Cs carriers).J (mpC l F kclk coef A a ha hs Cs carriers).W) :=
    (RadScan.winRecs_eq (mpC l F kclk coef A a ha hs Cs carriers)).symm
  obtain ⟨σR, eR, r3, r3h, r150, r150h, KR⟩ := radixB_run' cap x FinalPass.RadB.radBlockW3 σ1
    (thrReq n a' ha' Cs carriers translation).word (List.ofFn (hbC l F kclk coef A a ha hs Cs carriers translation)) (mpC l F kclk coef A a ha hs Cs carriers).t (mpC l F kclk coef A a ha hs Cs carriers).ell0
    (mpC l F kclk coef A a ha hs Cs carriers).refMod (mpC l F kclk coef A a ha hs Cs carriers).J (gC l F kclk coef A a ha hs Cs carriers) row (mpC l F kclk coef A a ha hs Cs carriers).M pr.val s.val (prsC l F kclk coef A a ha hs Cs carriers) (mpC l F kclk coef A a ha hs Cs carriers).W (lsC l F kclk coef A a ha hs Cs carriers g pr)
    (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
    (FinalPass.Hash4.coefsRev (FinalPass.MajorantBits.coefVal (mpC l F kclk coef A a ha hs Cs carriers) (hbC l F kclk coef A a ha hs Cs carriers translation))) (RadNeed.Cb cap) (RadNeed.cdB cap)
    (by rw [k137 0 (by decide)]; exact hin.s0) hin.h0
    (by rw [k137 131 (by decide), ← RadScan.winRecs_eq, hmp]; exact hin.sWin) hin.hWin hprs
    (by rw [k137 132 (by decide), hmp]; exact hin.sMod) hin.hMod
    (by simp [σ1, RadDigs.dgK]; rfl) (by simp [σ1]; exact (hin.blank 137 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))).2)
    (fun k hk => by
      have hk' : k ≠ 137 := fun e => by subst e; simp at hk
      rw [k137 k hk']; simp only [σ1, WState.sets_sh]; exact b k hk)
    (hin.vals 4) (hin.vals 3) (by rw [v1, hmp]; exact hin.vals 13)
    (by rw [v1]; simp only [lsC, List.length_ofFn]; exact hin.vals 12)
    (by rw [v1, hmp]; exact hin.vals 16) (hin.vals 1) (hin.vals 2)
    (by rw [v1, hmp]; exact hin.vals 17) (by rw [v1, hmp]; exact hin.vals 18)
    (fun i => hin.zero _ (Or.inl (by rw [rQ_val]; omega)))
    (fun i => hin.zero _ (Or.inl (by rw [rF_val]; omega)))
    (fun i => hin.zero _ (Or.inl (by rw [rY_val]; omega)))
    (fun i => hin.zero _ (Or.inl (by rw [rT_val]; omega)))
    (fun i => hin.zero _ (Or.inl (by rw [rB_val]; omega)))
    (fun i => hin.zero _ (Or.inl (by rw [rZ_val]; omega)))
    (fun i => hin.zero _ (Or.inr (Or.inr (by rw [rG_val]; omega))))
    (by rw [List.length_ofFn]) (by unfold MajorantParams.ell0; omega)
    (FinalPass.HashSeed.revWord_eq (mpC l F kclk coef A a ha hs Cs carriers) (hbC l F kclk coef A a ha hs Cs carriers translation)) rfl rfl rfl
    (FinalPass.Hash4.rowF_eq (mpC l F kclk coef A a ha hs Cs carriers) (hbC l F kclk coef A a ha hs Cs carriers translation) (gC l F kclk coef A a ha hs Cs carriers))
    (by rw [RadScan.listBound_eq, sum_prsC]; rfl)
    (fun gis hg => by
      obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hg
      exact RadBnd.thrDigGis_length_le ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg _ g pr d)
    (by simp only [lsC, List.length_ofFn]; exact ThrSide.dig_pos l F kclk coef A a ha Cs hs)
    hpr (ZMod.val_lt s) hc
  refine ⟨σR, _, WExec.seq e2 eR, RadNeed.cost_le cap hB hneed _ hN, ?_⟩
  have kR : ∀ k : Fin 161, k.val < 130 → k.val ≠ 3 → σR.st (sk x k) = σ1.st (sk x k) ∧ σR.sh (sk x k) = σ1.sh (sk x k) :=
    fun k h1 h2 => KR.1 (sk x k) (by simp [sk_val]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk h0 h1 h2 h3 h113 => ?_, ?_, ?_⟩
  · rw [(kR 0 (by decide) (by decide)).1, k137 0 (by decide)]; exact hin.s0
  · rw [(kR 0 (by decide) (by decide)).2]; exact hin.h0
  · rw [(kR 1 (by decide) (by decide)).1, k137 1 (by decide)]; exact hin.s1
  · rw [(kR 1 (by decide) (by decide)).2]; exact hin.h1
  · rw [(kR 2 (by decide) (by decide)).1, k137 2 (by decide)]; exact hin.s2
  · rw [(kR 2 (by decide) (by decide)).2]; exact hin.h2
  · rw [r3, qC_record l F kclk coef A a ha hs Cs carriers translation g pr s row]
  · exact r3h
  · rw [(kR 113 (by decide) (by decide)).1, k137 113 (by decide)]; exact hin.s113
  · rw [(kR 113 (by decide) (by decide)).2]; exact hin.h113
  · exact r150
  · exact r150h
  · rw [(kR k hk h3).1, (kR k hk h3).2, k137 k (by omega)]
    exact hin.blank k h0 h1 h2 h113 (by omega) (by omega) (by omega) (Or.inl (by omega))
  · exact (qC_ready l F kclk coef A a ha hs Cs carriers translation g pr s row ha' hcall hrow).1
  · exact (qC_ready l F kclk coef A a ha hs Cs carriers translation g pr s row ha' hcall hrow).2

/-- **The RADIX row setup, Route B, v5** (`RadSetupB5.RadSetupSpecB5`): the setup program's machine, the need
`needF`, the bound `bnd`, the pipe bound `pipeF` (all polynomial, `RadNeed`). -/
noncomputable def radSetupSpecB5 (x : ℕ) (l : Literals) (F : GateFree l) : RadSetupB5.RadSetupSpecB5 x l F where
  s := (radixW x).toProg.size
  M := (radixW x).toProg.compile
  need := RadNeed.needF
  bound := RadNeed.bnd
  pipe := RadNeed.pipeF
  Kn := Classical.choose RadNeed.needF_poly
  Dn := Classical.choose (Classical.choose_spec RadNeed.needF_poly)
  need_le := Classical.choose_spec (Classical.choose_spec RadNeed.needF_poly)
  Kb := Classical.choose RadNeed.bnd_poly
  Db := Classical.choose (Classical.choose_spec RadNeed.bnd_poly)
  bound_le := Classical.choose_spec (Classical.choose_spec RadNeed.bnd_poly)
  Kp := Classical.choose RadNeed.pipeF_poly
  Dp := Classical.choose (Classical.choose_spec RadNeed.pipeF_poly)
  pipe_le := Classical.choose_spec (Classical.choose_spec RadNeed.pipeF_poly)
  run := by
    intro kclk coef A a ha n hs a' ha' Cs carriers translation hcall g pr s row hrow cap out j u σ hin hneed
    obtain ⟨σR, c, e, hc, hR⟩ := radix_run x l F kclk coef A a ha n hs a' ha' Cs carriers translation hcall g pr s row
      hrow cap out j u σ hin hneed
    exact ⟨σR, c, qC l F kclk coef A a ha hs Cs carriers translation g pr s row, Exec.step (WExec.exec cap e), hc, rfl,
      pipe_call l F kclk coef A a ha hs ha' Cs carriers translation g pr row s, hR⟩

/-- **The RADIX setups as a uniform family** (`Seams.StageU`, `ThrUnit.ThrUnitOf3`'s RADIX argument) at any stream
count `xF F`: the exponents and the coefficients are constants. -/
noncomputable def radStage (l : Literals) (xF : GateFree l → ℕ) :
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => RadSetupB5.RadSetupSpecB5 (xF F) l F) (fun R => ThrUnit.radDeg5 R)
      (fun R => ThrUnit.radCf5 R) :=
  fun _ => ⟨max (max (Classical.choose (Classical.choose_spec RadNeed.needF_poly))
      (Classical.choose (Classical.choose_spec RadNeed.bnd_poly))) (Classical.choose (Classical.choose_spec RadNeed.pipeF_poly)),
    ⟨0, 0, 0, 0, 0, 0, 0, 0⟩, 0, fun F _ _ _ =>
      ⟨Classical.choose RadNeed.needF_poly + Classical.choose RadNeed.bnd_poly + Classical.choose RadNeed.pipeF_poly,
        fun _ _ _ _ _ => ⟨radSetupSpecB5 (xF F) l F, le_rfl, le_rfl⟩⟩⟩

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupRun

end
