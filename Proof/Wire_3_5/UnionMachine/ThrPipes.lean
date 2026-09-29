import Proof.Wire_3_5.UnionMachine.FiltLift
import Proof.Wire_3_5.UnionMachine.RadSetupRun

/-! # The THR unit's pipes and emissions: RADIX (398) and FILTER (399) at a THR request unit

The THR tape's unit `j` (entry `e = j / EU`, `EU = thrEU |carriers|`; a request unit when `IsReqU`): its printed body
is row `r = rowOfU j` of the THR entry `(stOfU j, rowOfS j)` (`SymDec.symEmit_req`, `WriterIface.thrGrp`,
`Records.thrGroups`): `r < |carriers|` a FILTER row, `r = |carriers|` the RADIX row.

* `emit_req`, `callUnit_rad`, `callUnit_filt`: the unit's emission at a RADIX / FILTER request unit;
* `stOfU_lt`, `rowOfS_lt`, `rowOfU_le`: the index decode's ranges;
* **`radP R`** = the RADIX setup `R.M` (`RadSetupSpecB5`) ; the RADIX pipe `RadPipe.radPipeM`; **`radP_ok`**: from
  `RsIn4` at `(g, pr, s, row)` and `R.need (radMeas5 …) ≤ cap`, the RADIX row's body printed within
  `R.bound cap + 1 + (R.pipe (radMeas5 …) + 2)` (`UnitG.PipeOK`).

Paper quantity of the main type: the THR entry's rows printed at their units (row:radix P3:2585-2623, row:matrix
P3:1523-1526). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrPipes
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup

/-! ## The index decode's ranges -/

theorem thrEU_eq (nc : ℕ) : ThrDec.thrEU nc = 3 * nc + 5 := by unfold ThrDec.thrEU; ring

theorem rowOfU_le (nc j : ℕ) (h : j % ThrDec.thrEU nc < ThrDec.thrEU nc - 1) : ThrDec.rowOfU nc j ≤ nc := by
  unfold ThrDec.rowOfU
  rw [thrEU_eq] at h ⊢
  omega

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n)) (translation : List ℕ)

theorem thrN2_pos : 0 < ThrDec.thrN2 l F kclk coef A a ha hs := by
  unfold ThrDec.thrN2; positivity

theorem stOfU_lt (j : ℕ) (hj : j < ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) :
    ThrDec.stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs := by
  unfold ThrDec.stOfU
  unfold ThrDec.thrTOT at hj
  rw [Nat.div_div_eq_div_mul]
  exact (Nat.div_lt_iff_lt_mul (by unfold ThrDec.thrEU; have := thrN2_pos l F kclk coef A a ha hs; positivity)).mpr
    (by rw [show Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs * (ThrDec.thrEU carriers.length *
      ThrDec.thrN2 l F kclk coef A a ha hs) = Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs *
      ThrDec.thrN2 l F kclk coef A a ha hs * ThrDec.thrEU carriers.length by ring]; exact hj)

theorem rowOfS_lt (j : ℕ) : ThrDec.rowOfS l F kclk coef A a ha hs carriers j < ThrDec.thrN2 l F kclk coef A a ha hs :=
  Nat.mod_lt _ (thrN2_pos l F kclk coef A a ha hs)

/-- **The emission at a request unit**: row `rowOfU j` of entry `j / EU`, target `0`. -/
theorem emit_req (j : ℕ) (hj : ThrDec.IsReqU (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j) :
    SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0 (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j =
      ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation (j / ThrDec.thrEU carriers.length) (ThrDec.rowOfU carriers.length j) 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hj
  unfold SymDec.unitE
  rw [if_pos h1]
  have e := SymDec.symEmit_req (carriers.length + 1) 0 (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j h2 (by
    unfold ThrDec.thrEU at h3; omega) (by unfold ThrDec.thrEU at h4; omega) (by unfold ThrDec.thrEU at h4; omega)
  rw [e]
  unfold ThrDec.rowOfU
  unfold ThrDec.thrEU at h4
  congr 1
  omega

/-- **A RADIX request unit's body**: the entry's RADIX row. -/
theorem callUnit_rad (e : ℕ) (he : e / ThrDec.thrN2 l F kclk coef A a ha hs < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) :
    ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation e carriers.length 0 =
      SymFlat.unitBody (Records.radRow ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨e / ThrDec.thrN2 l F kclk coef A a ha hs, he⟩).2.1 ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨e / ThrDec.thrN2 l F kclk coef A a ha hs, he⟩).2.2.1 ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨e / ThrDec.thrN2 l F kclk coef A a ha hs, he⟩).2.2.2 (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length
        (e % ThrDec.thrN2 l F kclk coef A a ha hs) n) := by
  unfold ThrDec.thrCallUnit WriterIface.thrGrp
  rw [dif_pos he]
  unfold Records.thrGroups
  rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, List.length_range]; exact le_rfl)]
  simp only [List.length_map, List.length_range]
  erw [Nat.sub_self]
  simp

/-- **A FILTER request unit's body**: the entry's FILTER row `r`. -/
theorem callUnit_filt (e r : ℕ) (he : e / ThrDec.thrN2 l F kclk coef A a ha hs < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (hr : r < carriers.length) :
    ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation e r 0 =
      SymFlat.unitBody (Records.filtRow (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((callInputs l F kclk coef A a ha).filterParams .thr n)
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨e / ThrDec.thrN2 l F kclk coef A a ha hs, he⟩).1 (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length (e % ThrDec.thrN2 l F kclk coef A a ha hs) n r) := by
  unfold ThrDec.thrCallUnit WriterIface.thrGrp
  rw [dif_pos he]
  unfold Records.thrGroups
  have hr' : r < ((List.range carriers.length).map fun jr => [Records.filtRow (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)
      ((callInputs l F kclk coef A a ha).filterParams .thr n) ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨e / ThrDec.thrN2 l F kclk coef A a ha hs, he⟩).1 (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length
      (e % ThrDec.thrN2 l F kclk coef A a ha hs) n jr]).length := by
    rw [List.length_map, List.length_range]; exact hr
  erw [List.getD_append _ _ _ _ hr', List.getD_eq_getElem _ _ hr']
  simp

end Call

/-! ## The RADIX pipe -/

section Rad
variable (cap : ℕ) {x : ℕ} {l : Literals} {F : GateFree l}

/-- **The THR unit's RADIX pipe**: the setup, then the row. -/
noncomputable def radP (R : RadSetupB5.RadSetupSpecB5 x l F) := Composition.machine R.M (PrimAsm.RadPipe.radPipeM x)

/-- **The RADIX pipe at a RADIX request unit** (`UnitG.PipeOK`). -/
theorem radP_ok (R : RadSetupB5.RadSetupSpecB5 x l F) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (s : ZMod pr.val) (row : ℕ) (hrow : row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2) (out : List Bool) (j : ℕ) (σ : WState (LNS x) LNR)
    (hin : RadSetupB3.RsIn4 x σ (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
      (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers)
      (radVals l F kclk coef A a ha hs Cs carriers ((Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg g).val) pr.val s.val row)
      (Data.unaryList (primesList (callNums l F kclk coef A a ha hs Cs carriers).cut))
      (winRecs (thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den))
      (frame (SignedSortKey.binary (callNums l F kclk coef A a ha hs Cs carriers).ell0 (callNums l F kclk coef A a ha hs Cs carriers).pMod))
      carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨i.val, h⟩) else []) a')
    (hneed : R.need (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row) ≤ cap) :
    UnitG.PipeOK cap (radP R) σ out
      (SymFlat.unitBody (Records.radRow ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) g pr s
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length row n))
      (R.bound cap + 1 + (R.pipe (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row) + 2)) := by
  obtain ⟨σR, m, q, hS, hm, hq, hqb, hR⟩ := R.run kclk coef A a ha n hs a' ha' Cs carriers translation hcall g pr s row
    hrow cap out j (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers) σ hin hneed
  obtain ⟨σF, m', sF, o1, o1h, keep, hm'⟩ := RadPipeB.radPipe_readyB cap σR _ out j _ q hR
  obtain ⟨k0, -⟩ := keep 0 (Or.inl rfl)
  obtain ⟨k2, k2h⟩ := keep 2 (Or.inr (Or.inl rfl))
  have hb : SymFlat.unitBody (Records.radRow ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) g pr s
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length row n) =
      (ListMachine.Row.radRefC q.r.D q.r.digs q.r.p q.r.b0 q.r.s).flatMap (fun t => true :: ListMachine.Rec.termWord t) := by
    rw [radRow_eq l F kclk coef A a ha hs Cs carriers translation g pr s row, hq]
    rfl
  refine ⟨σF, Step.seq (hS.enlarge hm) (sF.enlarge (by omega)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [k0, hR.s0, hin.s0]
    rfl
  · rw [o1, hb]
  · rw [o1h, hb]
  · rw [k2, hR.s2, hin.s2]
  · rw [k2h, hR.h2, hin.h2]

end Rad

end NearCubicWires.WireExponent3_5.UnionMachine.ThrPipes
