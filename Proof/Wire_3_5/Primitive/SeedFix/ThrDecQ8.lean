import Lean
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ7
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.GeoPack
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.ThrDecIface
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ8Base


noncomputable section
set_option maxRecDepth 120000


/-! # T3 THR decode front, packaging part 8: the run at a THR call

**`call_run`**: at every THR call of the gate, every output `out`, unit `j` and capacity `cap ≥ c₀(n)`, the decode
front `frontM` (the front end `TW l`, W6 `NW l`, the gate's `c_r` and `f_e`) runs from the unit's fresh cell to
`ThrDec.ThrDecOut`, in at most `fK·(c₀+1)^{fD}` steps, where `c₀(n) = cZero (Q_F) (L²) (aE l f_e)`.

Paper quantity of the main type: the THR call's rows (FILTER and RADIX) at each unit of the THR tape (P3:2543-2558,
2019-2054, 2585-2623). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.ThrDec

/-- The front's virtual capacity at length `n` (`Q_F`, `L²`, the exponent `aE l f_e`). -/
noncomputable def needT (l : Literals) (F : GateFree l) (n : ℕ) : ℕ :=
  cZero (qF l F) (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) (aE l F.filterErrDeg)

/-- The front's cost bound at length `n`. -/
noncomputable def boundT (l : Literals) (F : GateFree l) (n : ℕ) : ℕ :=
  fK (TW l) (NW l) * (needT l F n + 1) ^ fD (TW l) (NW l)

section Call
variable (x : ℕ) (l : Literals) (hx : dX (TW l) (NW l) ≤ x) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
  {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
  (translation : List ℕ) (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
  (hs : (callInputs l F kclk coef A a ha).StarAt n)
include hcall hs

set_option quotPrecheck false in
local notation "PP" => (callInputs l F kclk coef A a ha).starParams n hs
set_option quotPrecheck false in
local notation "FPT" => (callInputs l F kclk coef A a ha).filterParams Mode.thr n
set_option quotPrecheck false in
local notation "HS" => ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
  (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams Mode.thr n).cap
set_option quotPrecheck false in
local notation "KH" => ((callInputs l F kclk coef A a ha).starParams n hs).s *
  (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)
set_option quotPrecheck false in
local notation "VV" => PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
  (PrimT.W6.litAlg l) 1 carriers.length ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs
    carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D
    ((callInputs l F kclk coef A a ha).filterParams Mode.thr n).cap).getD 1 0)
set_option quotPrecheck false in
local notation "XS" => carriers.map List.length
set_option quotPrecheck false in
local notation "TOTC" => 2 ^ (FPT).seedBits * (HS).getD 2 0 * (HS).getD 6 0 * 2 ^ (2 * (KH)) *
  ((carriers.length + 1) * 3 + 2)

/-- **The RADIX clause of `ThrDecOut`** from the front's. -/
theorem rad_link (σD : WState (LNS x) LNR) (out : List Bool) (j cap : ℕ)
    (hrad : IsReqU (TOTC) carriers.length j → rowOfU carriers.length j = carriers.length →
      σD.val rRadK ≠ 0 ∧ σD.val rFltK = 0 ∧
      ∃ t, t < (PrimThrW.Joins.primesList (VV).cut).length ∧
        ((PrimThrW.Joins.primesList (VV).cut).take t).sum ≤ j / thrEU carriers.length / 2 ^ (2 * (KH)) % (HS).getD 6 0 ∧
        j / thrEU carriers.length / 2 ^ (2 * (KH)) % (HS).getD 6 0 < ((PrimThrW.Joins.primesList (VV).cut).take (t + 1)).sum ∧
        RadSetupB3.RsIn4 x σD (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
          (Data.unaryList (HS ++ (XS ++ [(PrimT.ThrTab.tupleG Cs).length])))
          (![j / thrEU carriers.length / 2 ^ (2 * (KH)) / (HS).getD 6 0 % (HS).getD 2 0,
            (PrimThrW.Joins.primesList (VV).cut).getD t 0,
            j / thrEU carriers.length / 2 ^ (2 * (KH)) % (HS).getD 6 0 - ((PrimThrW.Joins.primesList (VV).cut).take t).sum,
            j / thrEU carriers.length % 2 ^ (2 * (KH)),
            2 * ((XS).getD 0 0 + (XS).getD 1 0) + (HS).getD 8 0, 2 * ((XS).getD 0 0 + (XS).getD 1 0), (PP).n,
            (HS).getD 2 0, (HS).getD 3 0, (HS).getD 4 0, (HS).getD 5 0, (HS).getD 6 0, (HS).getD 7 0, (HS).getD 8 0,
            (HS).getD 9 0, (HS).getD 10 0, (HS).getD 11 0, (HS).getD 12 0, (HS).getD 14 0, (HS).getD 15 0] : Fin 20 → ℕ)
          (Data.unaryList (PrimThrW.Joins.primesList (VV).cut))
          (PrimThrW.Joins.winRecs (PrimThrW.Joins.thrMP (VV).M (VV).A (VV).Bs (VV).den))
          (frame (SignedSortKey.binary (VV).ell0 (VV).pMod)) carriers.length ((HS).getD 1 0)
          (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (PrimT.W6.litAlg l) (Cs ⟨i.val, h⟩) else [])
          (ReqBridge.thrCodes Cs).length) :
    ∀ ht : stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs,
      IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j → rowOfU carriers.length j = carriers.length →
      σD.val rRadK ≠ 0 ∧ σD.val rFltK = 0 ∧
      RadSetupB3.RsIn4 x σD (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
        (thrCallU l F kclk coef A a ha hs Cs carriers)
        (PrimThrW.RadSetup.radVals l F kclk coef A a ha hs Cs carriers
          (Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
            ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.1).val
          ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.2.1.val
          ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, ht⟩).2.2.2.val
          (rowOfS l F kclk coef A a ha hs carriers j))
        (Data.unaryList (PrimThrW.Joins.primesList (PrimThrW.RadSetup.callNums l F kclk coef A a ha hs Cs carriers).cut))
        (PrimThrW.Joins.winRecs (PrimThrW.Joins.thrMP (PrimThrW.RadSetup.callNums l F kclk coef A a ha hs Cs carriers).M
          (PrimThrW.RadSetup.callNums l F kclk coef A a ha hs Cs carriers).A
          (PrimThrW.RadSetup.callNums l F kclk coef A a ha hs Cs carriers).Bs
          (PrimThrW.RadSetup.callNums l F kclk coef A a ha hs Cs carriers).den))
        (frame (SignedSortKey.binary (PrimThrW.RadSetup.callNums l F kclk coef A a ha hs Cs carriers).ell0
          (PrimThrW.RadSetup.callNums l F kclk coef A a ha hs Cs carriers).pMod))
        carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
        (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨i.val, h⟩) else []) a' := by
  intro ht hreq hrow
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  rw [tot_eq] at hreq
  obtain ⟨hR, hF0, t', -, ht1, ht2, hRs⟩ := hrad hreq hrow
  refine ⟨hR, hF0, ?_⟩
  have est : stOfU l F kclk coef A a ha hs carriers j = j / thrEU carriers.length / 2 ^ (2 * (KH)) := by
    unfold stOfU; rw [n2_eq]
  have ers : rowOfS l F kclk coef A a ha hs carriers j = j / thrEU carriers.length % 2 ^ (2 * (KH)) := by
    unfold rowOfS; rw [n2_eq]
  rw [← est] at ht1 ht2 hRs
  obtain ⟨pv, sv⟩ := prime_val l F kclk coef A a ha hs Cs carriers _ ht t' ht1 ht2
  rw [rad_vec l F kclk coef A a ha hs Cs carriers hk2, sel_val l F kclk coef A a ha hs Cs carriers _ ht, sv, pv, ers]
  have e1 : (HS).getD 1 0 = (FPT).cap := rfl
  have e2 : PrimT.W6.litAlg l = (gate0 l F).alg := rfl
  rw [thrCodes_len] at hRs
  rw [e1, e2] at hRs ⊢
  have e3 : PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg 1
      carriers.length (FPT).cap = PrimThrW.RadSetup.callNums l F kclk coef A a ha hs Cs carriers := rfl
  have e4 : thrCallU l F kclk coef A a ha hs Cs carriers =
      Data.unaryList (HS ++ (XS ++ [(PrimT.ThrTab.tupleG Cs).length])) := rfl
  rw [e3] at hRs ⊢
  rw [e4]
  exact hRs

/-- **The FILTER clause of `ThrDecOut`** from the front's. -/
theorem filt_link (σD : WState (LNS x) LNR) (out : List Bool) (j cap : ℕ)
    (hfilt : IsReqU (TOTC) carriers.length j → rowOfU carriers.length j < carriers.length →
      σD.val rRadK = 0 ∧ σD.val rFltK ≠ 0 ∧
      FiltSetup.FsIn2 x σD (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
        (Data.unaryList (HS ++ (XS ++ [(PrimT.ThrTab.tupleG Cs).length]))) (FPT).len (FPT).cap (FPT).errExp
        (j / thrEU carriers.length / 2 ^ (2 * (KH)) / (HS).getD 6 0 / (HS).getD 2 0)
        (2 * (2 * (j / thrEU carriers.length % 2 ^ (2 * (KH)))))
        (2 * ((XS).getD 0 0 + (XS).getD 1 0) + (HS).getD 8 0)
        (SymDec.fbOff (rowOfU carriers.length j) ((XS).getD 0 0))
        (SymDec.fbL (rowOfU carriers.length j) ((XS).getD 0 0) ((XS).getD 1 0))) :
    ∀ ht : stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs,
      IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j → rowOfU carriers.length j < carriers.length →
      σD.val rRadK = 0 ∧ σD.val rFltK ≠ 0 ∧
      FiltSetup.FsIn2 x σD (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
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
          (rowOfU carriers.length j) []).length := by
  intro ht hreq hrow
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  rw [tot_eq] at hreq
  obtain ⟨hR0, hF1, hFs⟩ := hfilt hreq hrow
  refine ⟨hR0, hF1, ?_⟩
  have est : stOfU l F kclk coef A a ha hs carriers j = j / thrEU carriers.length / 2 ^ (2 * (KH)) := by
    unfold stOfU; rw [n2_eq]
  have e4 : 4 * rowOfS l F kclk coef A a ha hs carriers j =
      2 * (2 * (j / thrEU carriers.length % 2 ^ (2 * (KH)))) := by
    unfold rowOfS; rw [n2_eq]; ring
  have eu : thrCallU l F kclk coef A a ha hs Cs carriers =
      Data.unaryList (HS ++ (XS ++ [(PrimT.ThrTab.tupleG Cs).length])) := rfl
  rw [seed_val l F kclk coef A a ha hs Cs carriers _ ht, est, e4, eu,
    thr_pool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap hk2,
    thr_slice_off ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers _ hrow (by omega),
    thr_slice_len ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers _ hrow (by omega)]
  exact hFs

omit hcall in
/-- **The idle clause of `ThrDecOut`** from the front's. -/
theorem idle_link (σD : WState (LNS x) LNR) (out : List Bool) (j : ℕ)
    (hidle : ¬ IsReqU (TOTC) carriers.length j →
      IdleAt x σD (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out
        (SymDec.unitE (TOTC) (carriers.length + 1) 0 (thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j) j) :
    ¬ IsReqU (thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j →
      σD.val rRadK = 0 ∧ σD.val rFltK = 0 ∧
      σD.st (sk x 150) = [] ∧ σD.sh (sk x 150) = 0 ∧ σD.st (sk x 151) = [] ∧ σD.sh (sk x 151) = 0 ∧
      σD.st (sk x 1) = out ++ SymDec.unitE (thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
        (thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j ++ [false] ∧
      σD.sh (sk x 1) = (out ++ SymDec.unitE (thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
        (thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j).length := by
  intro hnot
  rw [tot_eq] at hnot ⊢
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, -⟩ := hidle hnot
  exact ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩

/-- **The front's run at the call** (`front_run` at the call's values, `FNeed` from `call_atoms`): the step bound and
`ThrDecOut`. -/
theorem call_run (out : List Bool) (j cap : ℕ) (hcap : needT l F n ≤ cap) :
    ∃ σD m, Step (frontM (TW l) (NW l) x hx F.cr F.filterErrDeg) m
        (wenc cap (CellLoopD.blankCellD x (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
          (thrCallU l F kclk coef A a ha hs Cs carriers))).H
        (wenc cap (CellLoopD.blankCellD x (thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
          (thrCallU l F kclk coef A a ha hs Cs carriers))).A (wenc cap σD).H (wenc cap σD).A ∧
      m ≤ boundT l F n ∧ ThrDecOut l F kclk coef A a ha hs ha' Cs carriers translation x cap σD out j := by
  have hAt := call_atoms l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hF := fneed_arith (NW l) hAt
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  have hKb : ∀ c ∈ ReqBridge.thrCodes Cs, natBitLength c ≤ (Data.reqW n true (ReqBridge.thrCodes Cs)
      (carriers.map Stars.Carrier.code) (RepairRepresentation.natListWord translation ++
        ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length := by
    intro c hc
    have h1 := (natWord_le_reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).1 c hc
    rw [Bindings.Williams14.natWord_length] at h1
    omega
  have hLs : (PrimThrW.Joins.primesList (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs)
      Cs (PrimT.W6.litAlg l) 1 (carriers.map List.length).length
      ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).cut).sum =
      (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0 := by
    rw [PrimT.W6.primesList_sum, hashNums_get6]
    rfl
  obtain ⟨σD, m, hstep, hm, s0, h0, s2, h2, hfilt, hrad, hidle⟩ := front_run (TW l) (NW l) x hx F.cr F.filterErrDeg cap (needT l F n) hcap
    ((callInputs l F kclk coef A a ha).starParams n hs) (PrimT.GeoPack.starParams_r l F kclk coef A a ha n hs) Cs
    (carriers.map Stars.Carrier.code)
    (RepairRepresentation.natListWord translation ++
      ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)
    _ hKb out j _ (carriers.map List.length) (PrimT.ThrTab.tupleG Cs).length
    (ThrData.hashNums_length _ _ _ _ _ _) (by rw [List.length_map]; exact hk2) (by rw [List.length_map]; rfl)
    (by rw [List.length_map, List.length_map]) ((callInputs l F kclk coef A a ha).filterParams .thr n) rfl rfl rfl
    (((gate0 l F).budget kclk coef A a ha).capOf_pos .thr n) hF hLs (PrimT.GeoPack.star_n_pos hs) ha'
    hcall.2.2.1 (thrCallUnit l F kclk coef A a ha hs Cs carriers translation)
  have ew : Data.reqW ((callInputs l F kclk coef A a ha).starParams n hs).n true
      (ReqBridge.thrCodes (n := ((callInputs l F kclk coef A a ha).starParams n hs).n) Cs)
      (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs) =
      thrCallW l F kclk coef A a ha hs ha' Cs carriers translation :=
    ReqBridge.reqW_thrReq ha' Cs carriers translation _
  rw [ew] at hstep s0 hfilt hrad hidle
  simp only [List.length_map] at hfilt hrad hidle
  refine ⟨σD, m, hstep, le_trans hm ?_, s0, h0, s2, h2,
    rad_link x l F kclk coef A a ha ha' Cs carriers translation hcall hs σD out j cap hrad,
    filt_link x l F kclk coef A a ha ha' Cs carriers translation hcall hs σD out j cap hfilt,
    idle_link x l F kclk coef A a ha ha' Cs carriers translation hs σD out j hidle⟩
  have hL : ∀ L : List ℕ, L.length ≤ (Data.unaryList L).length := fun L => by
    rw [SymDec.unaryList_length_le]; omega
  have cP := hF.tn.cP
  exact front_cost_le (TW l) (NW l) n (ReqBridge.thrCodes Cs).length (carriers.map Stars.Carrier.code).length
    (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length
    F.cr F.filterErrDeg (needT l F n) _
    (tV (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length n
      ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 1 0)
      (NW l).Cn (NW l).Dn)
    ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 1 0)
    ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 0 0)
    _ _ hAt.acodes hAt.acc (le_trans (by
      have := Nat.one_le_two_pow (n := natBitLength n)
      have := Nat.one_le_two_pow (n := natBitLength (ReqBridge.thrCodes Cs).length)
      have := Nat.one_le_two_pow (n := natBitLength (carriers.map Stars.Carrier.code).length)
      omega) cP) hF.tn.c3
    (le_trans (Nat.le_add_right _ 2) hF.tot) (le_trans (Nat.le_add_right _ 42) hF.preB) (hL _)
    (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ 2) hF.post))

end Call

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF

end
