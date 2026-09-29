import Proof.Wire_3_5.UnionMachine.UnitG
import Proof.Wire_3_5.Primitive.ThresholdWriter.FiltDock5

/-! # The FILTER pipe of the THR unit, lifted from the walk bank's cell `W.x` to the unit's cell `x ≥ W.x`

C6's FILTER setup `FiltSetupSpec5 W` (a register program on `LNS W.x`) and PA's FILTER pipeline `FiltPipe.filtPipeM W`
(a machine on `LNS W.x`'s tapes) run on the walk bank's cell. The THR unit's cell has `x ≥ W.x` streams (the decode
front docks W6 and `topFront3` there). The sub-layout of the first `LNS W.x + 1` streams, all registers and the cell
is docked by PA's `DockW.dockW` (no extra tapes):

* `fsE` (the streams' embedding), **`restr σ`** (the sub-layout state), `liftM M`, **`lift_step`**, `updW`'s reads;
* `fsIn2_restr`: `FsIn2` on `LNS x` restricts to `FsIn2` on `LNS W.x` (the fixed streams, the producer's scratch
  streams, the values);
* **`filtP W F5 hx`** = the setup ; the pipeline, both lifted; **`filtP_ok`**: from `FsIn2` at a THR FILTER row, the
  lifted pipe prints the row's body (`SymFlat.unitBody (filtRow …)`) within `F5.bound cap + 1 + Bp`
  (`FiltDock5.thrFilt_dock5`, `UnitReady.filtPipe_ready`), keeping the request and the counter (`UnitG.PipeOK`).

Paper quantity of the main type: the THR FILTER row's printed expression (C2's `filtRefC`, the filter `F_e` of
filt:gap at the slice's labels) on the unit's cell. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FiltLift
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimT.WalkBank NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.RecoveryRootRound

variable (cap : ℕ) (W : WalkBankProducer) {x : ℕ} (hx : W.x ≤ x)

/-- The streams' embedding. -/
def fsE : Fin (LNS W.x + 1) → Fin (LNS x + 1) := Fin.castLE (by unfold LNS; omega)

/-- No extra tapes. -/
def em0 (x : ℕ) : Fin 0 → Fin (LNS x + 1) := Fin.elim0

theorem fsE_sk (k : Fin 161) : fsE W hx (sk W.x k) = sk x k := Fin.ext rfl

theorem fsE_sT (k : Fin W.x) : fsE W hx (sT W.x k) = sT x (Fin.castLE hx k) := Fin.ext rfl

theorem gs_cast (i : Fin (LNS W.x + 1)) : gs (fsE W hx) (em0 x) (Fin.castAdd 0 i) = fsE W hx i := by
  simp only [gs, Fin.addCases_left]

theorem gs_inj : Function.Injective (gs (fsE W hx) (em0 x)) := by
  intro a b h
  have ha : a = Fin.castAdd 0 a := rfl
  have hb : b = Fin.castAdd 0 b := rfl
  rw [ha, hb, gs_cast, gs_cast] at h
  exact Fin.ext (by have := congrArg Fin.val h; simpa [fsE] using this)

theorem addCases_zero {α : Type} {m : ℕ} (f : Fin m → α) (g : Fin 0 → α) :
    Fin.addCases (motive := fun _ => α) f g = f := by
  funext i
  exact Fin.addCases_left (motive := fun _ => α) (m := m) (n := 0) i

/-- **The sub-layout state**: the first `LNS W.x + 1` streams, every register, the cell. -/
def restr (σ : WState (LNS x) LNR) : WState (LNS W.x) LNR :=
  ⟨fun i => σ.sh (fsE W hx i), fun i => σ.st (fsE W hx i), σ.val, σ.cell⟩

/-- The state after a lifted run. -/
noncomputable def upd (σ : WState (LNS x) LNR) (y : WState (LNS W.x) LNR) : WState (LNS x) LNR :=
  updW (fsE W hx) id (em0 x) σ y Fin.elim0 Fin.elim0

/-- A machine of the walk bank's cell, lifted. -/
noncomputable def liftM {s : ℕ} (M : Machine (LNS W.x + 2 + LNR) s) : Machine (LNS x + 2 + LNR) s :=
  RecoveryFocus.machine (wq (fsE W hx) (id : Fin LNR → Fin LNR) (em0 x)) M

/-- **A lifted run.** -/
theorem lift_step {s n : ℕ} (M : Machine (LNS W.x + 2 + LNR) s) (σ : WState (LNS x) LNR)
    (y' : WState (LNS W.x) LNR)
    (h : Step M n (wenc cap (restr W hx σ)).H (wenc cap (restr W hx σ)).A (wenc cap y').H (wenc cap y').A) :
    Step (liftM W hx M) n (wenc cap σ).H (wenc cap σ).A (wenc cap (upd W hx σ y')).H (wenc cap (upd W hx σ y')).A := by
  have h' : Step M n
      (Fin.addCases (motive := fun _ => ℕ) (m := LNS W.x + 2 + LNR) (n := 0) (wenc cap (restr W hx σ)).H
        (Fin.elim0 : Fin 0 → ℕ))
      (Fin.addCases (motive := fun _ => List Bool) (m := LNS W.x + 2 + LNR) (n := 0) (wenc cap (restr W hx σ)).A
        (Fin.elim0 : Fin 0 → List Bool))
      (Fin.addCases (motive := fun _ => ℕ) (m := LNS W.x + 2 + LNR) (n := 0) (wenc cap y').H (Fin.elim0 : Fin 0 → ℕ))
      (Fin.addCases (motive := fun _ => List Bool) (m := LNS W.x + 2 + LNR) (n := 0) (wenc cap y').A
        (Fin.elim0 : Fin 0 → List Bool)) := by
    rw [addCases_zero, addCases_zero, addCases_zero, addCases_zero]
    exact h
  exact dockW cap (fsE W hx) id (em0 x) (gs_inj W hx) Function.injective_id σ (restr W hx σ) y' Fin.elim0 Fin.elim0
    Fin.elim0 Fin.elim0 h' (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (fun k => k.elim0) (fun k => k.elim0)

theorem upd_st (σ : WState (LNS x) LNR) (y : WState (LNS W.x) LNR) (i : Fin (LNS W.x + 1)) :
    (upd W hx σ y).st (fsE W hx i) = y.st i := by
  show install (gs (fsE W hx) (em0 x)) σ.st (Fin.addCases (motive := fun _ => List Bool) y.st Fin.elim0) (fsE W hx i) = _
  rw [← gs_cast W hx i, install_slot _ (gs_inj W hx), Fin.addCases_left]

theorem upd_sh (σ : WState (LNS x) LNR) (y : WState (LNS W.x) LNR) (i : Fin (LNS W.x + 1)) :
    (upd W hx σ y).sh (fsE W hx i) = y.sh i := by
  show dockH (gs (fsE W hx) (em0 x)) σ.sh (Fin.addCases (motive := fun _ => ℕ) y.sh Fin.elim0) (fsE W hx i) = _
  rw [← gs_cast W hx i, dockH_slot _ (gs_inj W hx), Fin.addCases_left]

theorem upd_val (σ : WState (LNS x) LNR) (y : WState (LNS W.x) LNR) : (upd W hx σ y).val = y.val := by
  funext r
  exact dockH_slot id Function.injective_id σ.val y.val r

theorem restr_upd (σ : WState (LNS x) LNR) (y : WState (LNS W.x) LNR) : restr W hx (upd W hx σ y) = y := by
  apply WState.eq
  · funext i; exact upd_sh W hx σ y i
  · funext i; exact upd_st W hx σ y i
  · exact upd_val W hx σ y
  · rfl

/-- ** `FsIn2` restricts to the walk bank's cell.** -/
theorem fsIn2_restr {σ : WState (LNS x) LNR} {w out : List Bool} {j : ℕ} {u : List Bool}
    {len cp err g r4 G off L : ℕ} (hd : FiltSetup.FsIn2 x σ w out j u len cp err g r4 G off L) :
    FiltSetup.FsIn2 W.x (restr W hx σ) w out j u len cp err g r4 G off L where
  s0 := by show σ.st (fsE W hx (sk W.x 0)) = _; rw [fsE_sk]; exact hd.s0
  s1 := by show σ.st (fsE W hx (sk W.x 1)) = _; rw [fsE_sk]; exact hd.s1
  h1 := by show σ.sh (fsE W hx (sk W.x 1)) = _; rw [fsE_sk]; exact hd.h1
  s2 := by show σ.st (fsE W hx (sk W.x 2)) = _; rw [fsE_sk]; exact hd.s2
  h2 := by show σ.sh (fsE W hx (sk W.x 2)) = _; rw [fsE_sk]; exact hd.h2
  s113 := by show σ.st (fsE W hx (sk W.x 113)) = _; rw [fsE_sk]; exact hd.s113
  blank := fun k h0 h1 h2 h3 => by
    show σ.st (fsE W hx (sk W.x k)) = [] ∧ σ.sh (fsE W hx (sk W.x k)) = 0
    rw [fsE_sk]; exact hd.blank k h0 h1 h2 h3
  blankT := fun k => by
    show σ.st (fsE W hx (sT W.x k)) = [] ∧ σ.sh (fsE W hx (sT W.x k)) = 0
    rw [fsE_sT]; exact hd.blankT _
  cell := hd.cell
  vLen := hd.vLen
  vCap := hd.vCap
  vErr := hd.vErr
  vSeed := hd.vSeed
  vR4 := hd.vR4
  vG := hd.vG
  vOff := hd.vOff
  vL := hd.vL
  zLow := hd.zLow
  zHigh := hd.zHigh
  h0 := by show σ.sh (fsE W hx (sk W.x 0)) = _; rw [fsE_sk]; exact hd.h0

/-- **The THR unit's FILTER pipe**: C6's setup, then PA's pipeline, both lifted to the unit's cell. -/
noncomputable def filtP (F5 : FiltSetup.FiltSetupSpec5 W) :=
  Composition.machine (liftM W hx F5.prog.toProg.compile) (liftM W hx (FiltPipe.filtPipeM W))

/-- **The lifted FILTER pipe at a THR FILTER row** (`UnitG.PipeOK`): from `FsIn2` at the seed `e`'s index and row
`jr`'s slice, the row's body printed within `F5.bound cap + 1 + Bp`. -/
theorem filtP_ok (F5 : FiltSetup.FiltSetupSpec5 W) (P : StarParams) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Stars.Carrier P.n)) (FP : GapParams)
    (e : GapSeed FP) (row nw jr : ℕ) (w out u : List Bool) (j : ℕ) (σ : WState (LNS x) LNR) (hcap1 : 1 ≤ FP.cap)
    (hneed : F5.need FP.len FP.cap FP.errExp ((Records.thrSlices P Cs carriers).getD jr []).length (4 * row)
      (Records.thrPool P Cs carriers).length (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
      (Fintype.card (GapSeed FP)) ≤ cap)
    (hd : FiltSetup.FsIn2 x σ w out j u FP.len FP.cap FP.errExp (Enum.gapSeedEquiv FP e) (4 * row)
      (Records.thrPool P Cs carriers).length (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
      ((Records.thrSlices P Cs carriers).getD jr []).length) :
    UnitG.PipeOK cap (filtP W hx F5) σ out
      (SymFlat.unitBody (Records.filtRow (Records.thrSlices P Cs carriers) FP e (Records.thrPool P Cs carriers).length
        row nw jr))
      (F5.bound cap + 1 + FiltPipe.filtPipeBound FP e ((Records.thrSlices P Cs carriers).getD jr []).length (4 * row)
        (Records.thrPool P Cs carriers).length (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
        (FiltSetup.rulerW FP) (FiltSetup.rulerW FP)) := by
  obtain ⟨τ, m, hx5, hm, hok, t0, t0h, t2, t2h⟩ := PrimThrW.FiltDock5.thrFilt_dock5 P Cs carriers W F5 cap FP e row nw jr
    w out u j (restr W hx σ) hcap1 hneed (fsIn2_restr W hx hd)
  obtain ⟨-, -, -, -, P', e', L', r4', G', off', Mlab, RW, LW, sample, hR, he, hb⟩ := hok
  obtain ⟨σF, mF, sF, oF, ohF, kF, bF⟩ := UnitReady.filtPipe_ready cap W τ out P' e' L' r4' G' off' Mlab RW LW sample hR
  have s1 := lift_step cap W hx F5.prog.toProg.compile σ τ (WExec.exec cap hx5).step
  have s2 := lift_step cap W hx (FiltPipe.filtPipeM W) (upd W hx σ τ) σF (by rw [restr_upd]; exact sF)
  obtain ⟨k0, k0h⟩ := kF 0 (Or.inl rfl)
  obtain ⟨k2, k2h⟩ := kF 2 (Or.inr rfl)
  refine ⟨upd W hx (upd W hx σ τ) σF, Step.seq (s1.enlarge hm) (s2.enlarge (bF.trans hb)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← fsE_sk W hx 0, upd_st, k0, t0, fsE_sk, hd.s0]
  · rw [← fsE_sk W hx 1, upd_st, oF, he]
  · rw [← fsE_sk W hx 1, upd_sh, ohF, he]
  · rw [← fsE_sk W hx 2, upd_st, k2, t2, fsE_sk, hd.s2]
  · rw [← fsE_sk W hx 2, upd_sh, k2h, t2h, fsE_sk, hd.h2]

end NearCubicWires.WireExponent3_5.UnionMachine.FiltLift
