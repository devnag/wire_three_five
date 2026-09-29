import Proof.Wire_3_5.UnionMachine.ThrPipes

/-! # The THR unit machine at a gate and its run at every unit of a THR call (THRU3's `ok`)

`thrUnitM` = the decode front `D.M` ; branch on register `398` into the RADIX pipe `ThrPipes.radP R`
(`RadSetupSpecB5`), else on `399` into the lifted FILTER pipe `FiltLift.filtP W hx F5`, else nothing ; the counter
increment (`UnitG.unitMG`). At a THR call:

* **`measC`**: the call's measure: the decode's need and bound at `n`, the counts' length, the RADIX measures
  `radMeas5` over every prime and star row (`rSup`), the FILTER setup's arguments over every row and star row
  (`fSup`), and the FILTER pipeline's bound `Kf·(fSup+2)^(Df·(e+2))` (`FiltPipeLe2`);
* `needU X = X + K_R·(X+1)^D_R + C_F·(X+1)^D_F`, `nUU` (the decode, the pipes at the capacity, the counter);
* **`unit_ok`**: `Shell.UnitOK cap x thrUnitM (nUU (measC + cap)) …` at every unit `j` and every
  `cap ≥ needU (measC) + j` (THRU3's `ok`): the decode's exit (`ThrDec.ThrDecOut`) is `UnitG.DecOKG`: idle units print
  their marker, RADIX request units run `radP` (`ThrPipes.radP_ok`, `emit_req`, `callUnit_rad`), FILTER request units
  run `filtP` (`FiltLift.filtP_ok`, `callUnit_filt`).

Paper quantity of the main type: the THR tape's unit `j` printed by the unit machine (the batch's markers and rows,
row:radix P3:2585-2623, row:matrix P3:1523-1526). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnitRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimT.WalkBank

theorem pipeOK_mono {cap x s : ℕ} {P : Machine (PrimAsm.CellLoop.TT x) s} {σ : WState (LNS x) LNR} {out e : List Bool}
    {B B' : ℕ} (h : UnitG.PipeOK cap P σ out e B) (hB : B ≤ B') : UnitG.PipeOK cap P σ out e B' := by
  obtain ⟨σF, s1, h1⟩ := h
  exact ⟨σF, s1.enlarge hB, h1⟩

section Gate
variable {l : Literals} {F : GateFree l} {x : ℕ} {W : WalkBankProducer} (hx : W.x ≤ x) (D : ThrDec.ThrDecFront x l F)
  (R : RadSetupB5.RadSetupSpecB5 x l F) (F5 : FiltSetup.FiltSetupSpec5 W) (Kf Df : ℕ)

/-- **The THR unit machine** at a gate. -/
noncomputable def thrUnitM :=
  UnitG.unitMG D.M ThrDec.rRadK ThrDec.rFltK (ThrPipes.radP R) (FiltLift.filtP W hx F5)

/-- The pipes' bound at `Y` (`Y` covers the capacity and the call's measure). -/
def Bp (Y : ℕ) : ℕ :=
  R.Kb * (Y + 1) ^ R.Db + 1 + (R.Kp * (Y + 1) ^ R.Dp + 2) + (F5.Cb * (Y + 1) ^ F5.Db + 1 + Y)

/-- **The unit's need** at the call's measure. -/
def needU (X : ℕ) : ℕ := X + R.Kn * (X + 1) ^ R.Dn + F5.Cn * (X + 1) ^ F5.Dn

/-- **The unit's budget** at `Y = measure + capacity`. -/
def nUU (Y : ℕ) : ℕ := CellLoopD.cpCost Y + 1 + (Y + 1 + (Bp R F5 Y + 4) + 1 + (3 * Y + 3))

section Call
variable (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
  (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
  (translation : List ℕ)

/-- The FILTER setup's measure at row `jr` and star row `row`. -/
noncomputable def fArgs (jr row : ℕ) : ℕ :=
  ((callInputs l F kclk coef A a ha).filterParams .thr n).len + ((callInputs l F kclk coef A a ha).filterParams .thr n).cap + ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD jr []).length + 4 * row + (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length +
    Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) jr + Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams .thr n))

/-- The FILTER setup's measures, maximized. -/
noncomputable def fSup : ℕ :=
  (Finset.range carriers.length ×ˢ Finset.range (ThrDec.thrN2 l F kclk coef A a ha hs)).sup
    (fun p => fArgs kclk coef A a ha n hs a' Cs carriers p.1 p.2)

/-- The RADIX measures, maximized over the primes and the star rows. -/
noncomputable def rSup : ℕ :=
  ((Finset.univ : Finset (SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ×ˢ
    Finset.range (ThrDec.thrN2 l F kclk coef A a ha hs)).sup
    (fun p => RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation p.1 p.2)

/-- **The call's measure.** -/
noncomputable def measC : ℕ :=
  D.need n + D.bound n + (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers).length +
    rSup kclk coef A a ha n hs a' ha' Cs carriers translation + fSup kclk coef A a ha n hs a' Cs carriers +
    Kf * (fSup kclk coef A a ha n hs a' Cs carriers + 2) ^ (Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 2))

theorem rad_le (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (row : ℕ) (hrow : row < ThrDec.thrN2 l F kclk coef A a ha hs) :
    RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row ≤
      measC D Kf Df kclk coef A a ha n hs a' ha' Cs carriers translation := by
  have h := Finset.le_sup (f := fun p : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) × ℕ =>
      RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation p.1 p.2)
    (b := (pr, row)) (Finset.mem_product.mpr ⟨Finset.mem_univ pr, Finset.mem_range.mpr hrow⟩)
  unfold measC rSup
  simp only at h
  omega

theorem filt_le (jr row : ℕ) (hjr : jr < carriers.length) (hrow : row < ThrDec.thrN2 l F kclk coef A a ha hs) :
    fArgs kclk coef A a ha n hs a' Cs carriers jr row ≤ fSup kclk coef A a ha n hs a' Cs carriers :=
  Finset.le_sup (f := fun p : ℕ × ℕ => fArgs kclk coef A a ha n hs a' Cs carriers p.1 p.2)
    (b := (jr, row)) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hjr, Finset.mem_range.mpr hrow⟩)

/-- The emission at a RADIX request unit. -/
theorem emit_rad (j : ℕ) (hreq : ThrDec.IsReqU (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j)
    (hst : ThrDec.stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (heq : (ThrDec.rowOfU carriers.length j) = carriers.length) :
    (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0 (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j) = SymFlat.unitBody (Records.radRow ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.1 ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.2 (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) n) := by
  have hfin : (⟨ThrDec.stOfU l F kclk coef A a ha hs carriers j, hst⟩ :
      Fin (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) =
      ⟨j / ThrDec.thrEU carriers.length / ThrDec.thrN2 l F kclk coef A a ha hs, hst⟩ := rfl
  rw [ThrPipes.emit_req l F kclk coef A a ha hs Cs carriers translation j hreq, heq,
    ThrPipes.callUnit_rad l F kclk coef A a ha hs Cs carriers translation (j / ThrDec.thrEU carriers.length) hst, hfin]
  rfl

/-- The emission at a FILTER request unit. -/
theorem emit_filt (j : ℕ) (hreq : ThrDec.IsReqU (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j)
    (hst : ThrDec.stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (hlt : (ThrDec.rowOfU carriers.length j) < carriers.length) :
    (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0 (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j) = SymFlat.unitBody (Records.filtRow (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((callInputs l F kclk coef A a ha).filterParams .thr n) ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).1 (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) n (ThrDec.rowOfU carriers.length j)) := by
  rw [ThrPipes.emit_req l F kclk coef A a ha hs Cs carriers translation j hreq]
  exact ThrPipes.callUnit_filt l F kclk coef A a ha hs Cs carriers translation (j / ThrDec.thrEU carriers.length) _ hst hlt

/-- **A RADIX request unit's pipe** within the pipes' bound. -/
theorem dec_rad (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (out : List Bool) (j cap X : ℕ) (σD : WState (LNS x) LNR)
    (hst : ThrDec.stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (hrs : RadSetupB3.RsIn4 x σD (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
      (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers)
      (radVals l F kclk coef A a ha hs Cs carriers ((Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.1).val)
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1.val ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.2.val (ThrDec.rowOfS l F kclk coef A a ha hs carriers j))
      (Data.unaryList (primesList (callNums l F kclk coef A a ha hs Cs carriers).cut))
      (winRecs (thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A
        (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den))
      (frame (SignedSortKey.binary (callNums l F kclk coef A a ha hs Cs carriers).ell0
        (callNums l F kclk coef A a ha hs Cs carriers).pMod))
      carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf (gate0 l F).alg (Cs ⟨i.val, h⟩) else []) a')
    (hmX : (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)) ≤ X) (hN : needU R F5 X ≤ cap) :
    UnitG.PipeOK cap (ThrPipes.radP R) σD out
      (SymFlat.unitBody (Records.radRow ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
        ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.1 ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.2 (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) n)) (Bp R F5 (X + cap)) := by
  have hrow := ThrPipes.rowOfS_lt l F kclk coef A a ha hs carriers j
  have hneedR : R.need (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)) ≤ cap := by
    have h1 := R.need_le (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j))
    have h2 : R.Kn * ((RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)) + 1) ^ R.Dn ≤ R.Kn * (X + 1) ^ R.Dn := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    unfold needU at hN
    omega
  have hXc : X ≤ cap := by unfold needU at hN; omega
  refine pipeOK_mono (ThrPipes.radP_ok cap R kclk coef A a ha n hs a' ha' Cs carriers translation hcall ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.1
    ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.2 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) hrow out j σD hrs hneedR) ?_
  have hb1 := R.bound_le cap
  have hb2 := R.pipe_le (RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j))
  have hc1 : R.Kb * (cap + 1) ^ R.Db ≤ R.Kb * (X + cap + 1) ^ R.Db := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hc2 : R.Kp * ((RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)) + 1) ^ R.Dp ≤ R.Kp * (X + cap + 1) ^ R.Dp := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  unfold Bp
  omega

/-- **A FILTER request unit's pipe** within the pipes' bound. -/
theorem dec_filt
    (hKf : ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
      FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
        Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ Df * (L + 2) ^ (Df * (P.errExp + 1)))
    (out : List Bool) (j cap X : ℕ) (σD : WState (LNS x) LNR)
    (hst : ThrDec.stOfU l F kclk coef A a ha hs carriers j < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (hlt : (ThrDec.rowOfU carriers.length j) < carriers.length)
    (hfs : FiltSetup.FsIn2 x σD (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) out j
      (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers) ((callInputs l F kclk coef A a ha).filterParams .thr n).len ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp
      (Enum.gapSeedEquiv ((callInputs l F kclk coef A a ha).filterParams .thr n) ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).1) (4 * (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length (Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) (ThrDec.rowOfU carriers.length j)) ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD (ThrDec.rowOfU carriers.length j) []).length)
    (hfX : fSup kclk coef A a ha n hs a' Cs carriers + Kf * (fSup kclk coef A a ha n hs a' Cs carriers + 2) ^ (Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 2)) ≤ X)
    (hN : needU R F5 X ≤ cap) :
    UnitG.PipeOK cap (FiltLift.filtP W hx F5) σD out
      (SymFlat.unitBody (Records.filtRow (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) ((callInputs l F kclk coef A a ha).filterParams .thr n) ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).1 (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) n (ThrDec.rowOfU carriers.length j))) (Bp R F5 (X + cap)) := by
  have hrow := ThrPipes.rowOfS_lt l F kclk coef A a ha hs carriers j
  have hc1 : 1 ≤ ((callInputs l F kclk coef A a ha).filterParams .thr n).cap := ((gate0 l F).budget kclk coef A a ha).capOf_pos .thr n
  have hfa := filt_le kclk coef A a ha n hs a' Cs carriers (ThrDec.rowOfU carriers.length j) (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) hlt hrow
  have hXc : X ≤ cap := by unfold needU at hN; omega
  have hnp := F5.need_poly ((callInputs l F kclk coef A a ha).filterParams .thr n).len ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD (ThrDec.rowOfU carriers.length j) []).length (4 * (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length
    (Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) (ThrDec.rowOfU carriers.length j)) (Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams .thr n)))
  unfold ValidatorPolynomialDomination.PolyBounded at hnp
  have hpw : F5.Cn * (fArgs kclk coef A a ha n hs a' Cs carriers (ThrDec.rowOfU carriers.length j) (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) + 1) ^ F5.Dn ≤ F5.Cn * (X + 1) ^ F5.Dn :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hneedF : F5.need ((callInputs l F kclk coef A a ha).filterParams .thr n).len ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD (ThrDec.rowOfU carriers.length j) []).length (4 * (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length
      (Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) (ThrDec.rowOfU carriers.length j)) (Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams .thr n))) ≤ cap := by
    unfold fArgs at hpw
    unfold needU at hN
    omega
  refine pipeOK_mono (FiltLift.filtP_ok cap W hx F5 ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).1 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) n (ThrDec.rowOfU carriers.length j) _ out _ j σD hc1 hneedF hfs) ?_
  have hb5 := F5.bound_poly cap
  unfold ValidatorPolynomialDomination.PolyBounded at hb5
  have hkf := hKf ((callInputs l F kclk coef A a ha).filterParams .thr n) ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).1 ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD (ThrDec.rowOfU carriers.length j) []).length (4 * (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length (Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) (ThrDec.rowOfU carriers.length j)) hc1
  have hs1 : ((callInputs l F kclk coef A a ha).filterParams .thr n).len + ((callInputs l F kclk coef A a ha).filterParams .thr n).cap + ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD (ThrDec.rowOfU carriers.length j) []).length + 4 * (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) + (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length +
      Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) (ThrDec.rowOfU carriers.length j) + 2 ≤ fSup kclk coef A a ha n hs a' Cs carriers + 2 := by
    unfold fArgs at hfa; omega
  have hs2 : ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD (ThrDec.rowOfU carriers.length j) []).length + 2 ≤ fSup kclk coef A a ha n hs a' Cs carriers + 2 := by
    unfold fArgs at hfa; omega
  have hk2 : Kf * (((callInputs l F kclk coef A a ha).filterParams .thr n).len + ((callInputs l F kclk coef A a ha).filterParams .thr n).cap + ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD (ThrDec.rowOfU carriers.length j) []).length + 4 * (ThrDec.rowOfS l F kclk coef A a ha hs carriers j) + (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length +
      Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) (ThrDec.rowOfU carriers.length j) + 2) ^ Df * (((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD (ThrDec.rowOfU carriers.length j) []).length + 2) ^ (Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 1)) ≤
      Kf * (fSup kclk coef A a ha n hs a' Cs carriers + 2) ^ (Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 2)) := by
    rw [show Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 2) = Df + Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 1) by ring, pow_add, ← mul_assoc]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs1 _)) (Nat.pow_le_pow_left hs2 _)
  have hcb : F5.Cb * (cap + 1) ^ F5.Db ≤ F5.Cb * (X + cap + 1) ^ F5.Db :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  unfold Bp
  omega

/-- **The unit at every unit of a THR call** (THRU3's `ok`). -/
theorem unit_ok
    (hKf : ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
      FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
        Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ Df * (L + 2) ^ (Df * (P.errExp + 1)))
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (out : List Bool) (j cap : ℕ)
    (hcap : needU R F5 (measC D Kf Df kclk coef A a ha n hs a' ha' Cs carriers translation) + j ≤ cap) :
    PrimThrW.Shell.UnitOK cap x (thrUnitM hx D R F5)
      (nUU R F5 (measC D Kf Df kclk coef A a ha n hs a' ha' Cs carriers translation + cap))
      (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
      (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers)
      (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
        (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) j out := by
  obtain ⟨X, hX⟩ : ∃ X, X = measC D Kf Df kclk coef A a ha n hs a' ha' Cs carriers translation := ⟨_, rfl⟩
  rw [← hX] at hcap ⊢
  have hXd : D.need n + D.bound n + (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers).length +
      (fSup kclk coef A a ha n hs a' Cs carriers +
      Kf * (fSup kclk coef A a ha n hs a' Cs carriers + 2) ^ (Df * (((callInputs l F kclk coef A a ha).filterParams .thr n).errExp + 2))) ≤ X := by
    rw [hX]; unfold measC; omega
  have hN : needU R F5 X ≤ cap := by omega
  have hNx : X ≤ needU R F5 X := by unfold needU; omega
  obtain ⟨σD, m, hS, hm, hout⟩ := D.run kclk coef A a ha n hs a' ha' Cs carriers translation hcall out j cap (by omega)
  have hdec : UnitG.DecOKG cap ThrDec.rRadK ThrDec.rFltK (ThrPipes.radP R) (FiltLift.filtP W hx F5) σD out (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0 (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation) j)
      (Bp R F5 (X + cap)) := by
    by_cases hreq : ThrDec.IsReqU (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) carriers.length j
    · have hst := ThrPipes.stOfU_lt l F kclk coef A a ha hs Cs carriers j hreq.1
      have hrl := ThrPipes.rowOfU_le carriers.length j hreq.2.2.1
      rcases Nat.lt_or_ge (ThrDec.rowOfU carriers.length j) carriers.length with hlt | hge
      · obtain ⟨r0, r1, hfs⟩ := hout.filt hst hreq hlt
        rw [emit_filt kclk coef A a ha n hs a' Cs carriers translation j hreq hst hlt]
        exact Or.inr (Or.inr ⟨r0, r1, dec_filt hx R F5 Kf Df kclk coef A a ha n hs a' ha' Cs carriers translation hKf out
          j cap X σD hst hlt hfs (by omega) hN⟩)
      · have heq : (ThrDec.rowOfU carriers.length j) = carriers.length := by omega
        obtain ⟨r0, -, hrs⟩ := hout.rad hst hreq heq
        rw [emit_rad kclk coef A a ha n hs a' Cs carriers translation j hreq hst heq]
        have hrm := rad_le D Kf Df kclk coef A a ha n hs a' ha' Cs carriers translation ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨_, hst⟩).2.2.1 (ThrDec.rowOfS l F kclk coef A a ha hs carriers j)
          (ThrPipes.rowOfS_lt l F kclk coef A a ha hs carriers j)
        rw [← hX] at hrm
        exact Or.inr (Or.inl ⟨r0, dec_rad R F5 kclk coef A a ha n hs a' ha' Cs carriers translation hcall out j cap X σD
          hst hrs hrm hN⟩)
    · obtain ⟨r0, r1, -, -, -, -, o1, o1h⟩ := hout.idle hreq
      exact Or.inl ⟨r0, r1, o1, o1h⟩
  apply UnitG.unitOK_ofG
  refine ⟨σD, m, Bp R F5 (X + cap), hS, hdec, hout.s0, hout.s2, hout.h2, ?_⟩
  have hu : (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers).length ≤ X + cap := by omega
  have hmX : m ≤ X + cap := by omega
  unfold nUU CellLoopD.cpCost
  omega

end Call

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnitRun
