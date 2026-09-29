import Proof.Wire_3_5.UnionMachine.ThrUnitMeas3

/-! # The producer statement v5, proved: `thrUnitOf5 l : ThrUnit.ThrUnitOf5 l`

From the walk bank `W`, the unit cells `xF F ≥ W.x`, the FILTER setup `FiltSetupSpec5 W`, its pipe bound
(`FiltPipeLe2`), the uniform decode fronts and RADIX setups (`RadSetupSpecB5`), the THR unit machines v4 in the
StageU order:

* the machine `ThrUnitRun.thrUnitM` (the decode ; RADIX 398 ; FILTER 399 ; the counter), the measure
  `2^{K_q·Ψ_T}` (`ThrMeas.Kq`: from `l`, `f_e`, the decode front's exponent bound, `D_f`, `D_t`), the need
  `needU (c·X)` and the budget `nUU (c·Y)` with the coefficient `c = C_n + C_b + 16K_t + 32 + K_f + 3` (after the gate);
* `need_le`, `nU_le` (explicit `K·(X+1)^D`, the exponents from the RADIX setup's and the FILTER setup's), `meas_le`
  (`K_m = K_q`, `D_m = 0`), **`ok`** (`ThrUnitRun.unit_ok` at `measC ≤ c·2^{K_q Ψ_T}`, `ThrMeas.measC_le`, the need and
  the budget monotone);
* **`thrUnitOf5 l`** (the family; floors `envMax` of the two families' and `C_D ≥ 1`; `K_t` from `ThrNumsPoly`, `K_f`, `D_f` from `FiltPipeLe2`).

Paper quantity of the main type: the THR tape's unit machines within the preprocessing class `2^{O(Ψ_T)}` (P3:3089-3108,
row:radix P3:2585-2623, row:matrix P3:1523-1526). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnitOf
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimT.WalkBank

/-! ## Monotone, polynomial -/

theorem unitOK_mono {cap x sU : ℕ} {U : Machine (PrimAsm.CellLoop.TT x) sU} {nU nU' : ℕ} {w u : List Bool}
    {emit : ℕ → List Bool} {j : ℕ} {out : List Bool} (h : PrimThrW.Shell.UnitOK cap x U nU w u emit j out)
    (hn : nU ≤ nU') : PrimThrW.Shell.UnitOK cap x U nU' w u emit j out := by
  obtain ⟨σE, mU, s, a1, a2, a3, a4, a5⟩ := h
  exact ⟨σE, mU, s, a1, a2, a3, a4, a5.trans hn⟩

theorem pw_le (c X d D : ℕ) (hd : d ≤ D) : (c * X + 1) ^ d ≤ (c + 1) ^ d * (X + 1) ^ D := by
  calc (c * X + 1) ^ d ≤ ((c + 1) * (X + 1)) ^ d := Nat.pow_le_pow_left (by nlinarith) d
    _ = (c + 1) ^ d * (X + 1) ^ d := mul_pow _ _ _
    _ ≤ (c + 1) ^ d * (X + 1) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd)

section Gate
variable {l : Literals} {F : GateFree l} {x : ℕ} {W : WalkBankProducer} (R : RadSetupB5.RadSetupSpecB5 x l F)
  (F5 : FiltSetup.FiltSetupSpec5 W)

theorem needU_mono {X X' : ℕ} (h : X ≤ X') : ThrUnitRun.needU R F5 X ≤ ThrUnitRun.needU R F5 X' := by
  unfold ThrUnitRun.needU; gcongr

theorem nUU_mono {Y Y' : ℕ} (h : Y ≤ Y') : ThrUnitRun.nUU R F5 Y ≤ ThrUnitRun.nUU R F5 Y' := by
  unfold ThrUnitRun.nUU ThrUnitRun.Bp CellLoopD.cpCost; gcongr

/-- The need's coefficient and exponent at the coefficient `c`. -/
def KnU (c : ℕ) : ℕ := c + R.Kn * (c + 1) ^ R.Dn + F5.Cn * (c + 1) ^ F5.Dn
def DnU : ℕ := 1 + R.Dn + F5.Dn

theorem needU_le (c X : ℕ) : ThrUnitRun.needU R F5 (c * X) ≤ KnU R F5 c * (X + 1) ^ DnU R F5 := by
  unfold ThrUnitRun.needU KnU DnU
  have h1 := pw_le c X R.Dn (1 + R.Dn + F5.Dn) (by omega)
  have h2 := pw_le c X F5.Dn (1 + R.Dn + F5.Dn) (by omega)
  have h3 : c * X ≤ c * (X + 1) ^ (1 + R.Dn + F5.Dn) := Nat.mul_le_mul_left _
    ((Nat.le_succ X).trans (by simpa using Nat.pow_le_pow_right (show 1 ≤ X + 1 by omega) (show 1 ≤ 1 + R.Dn + F5.Dn by omega)))
  have h4 := Nat.mul_le_mul_left R.Kn h1
  have h5 := Nat.mul_le_mul_left F5.Cn h2
  have e : (c + R.Kn * (c + 1) ^ R.Dn + F5.Cn * (c + 1) ^ F5.Dn) * (X + 1) ^ (1 + R.Dn + F5.Dn) =
      c * (X + 1) ^ (1 + R.Dn + F5.Dn) + R.Kn * ((c + 1) ^ R.Dn * (X + 1) ^ (1 + R.Dn + F5.Dn)) +
        F5.Cn * ((c + 1) ^ F5.Dn * (X + 1) ^ (1 + R.Dn + F5.Dn)) := by ring
  omega

/-- The budget's coefficient and exponent at the coefficient `c`. -/
def KuU (c : ℕ) : ℕ :=
  22 * c + 23 + R.Kb * (c + 1) ^ R.Db + R.Kp * (c + 1) ^ R.Dp + F5.Cb * (c + 1) ^ F5.Db
def DuU : ℕ := 1 + R.Db + R.Dp + F5.Db

theorem nUU_le (c Y : ℕ) : ThrUnitRun.nUU R F5 (c * Y) ≤ KuU R F5 c * (Y + 1) ^ DuU R F5 := by
  unfold ThrUnitRun.nUU ThrUnitRun.Bp CellLoopD.cpCost KuU DuU
  have h1 := pw_le c Y R.Db (1 + R.Db + R.Dp + F5.Db) (by omega)
  have h2 := pw_le c Y R.Dp (1 + R.Db + R.Dp + F5.Db) (by omega)
  have h3 := pw_le c Y F5.Db (1 + R.Db + R.Dp + F5.Db) (by omega)
  have hB : Y + 1 ≤ (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db) := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ Y + 1 by omega) (show 1 ≤ 1 + R.Db + R.Dp + F5.Db by omega)
  have hcY : c * Y ≤ c * (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db) := Nat.mul_le_mul_left _ ((Nat.le_succ Y).trans hB)
  have h4 := Nat.mul_le_mul_left R.Kb h1
  have h5 := Nat.mul_le_mul_left R.Kp h2
  have h6 := Nat.mul_le_mul_left F5.Cb h3
  have hone : 1 ≤ (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db) := Nat.one_le_pow _ _ (by omega)
  have e : (22 * c + 23 + R.Kb * (c + 1) ^ R.Db + R.Kp * (c + 1) ^ R.Dp + F5.Cb * (c + 1) ^ F5.Db) *
      (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db) = 22 * (c * (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db)) +
      23 * (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db) + R.Kb * ((c + 1) ^ R.Db * (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db)) +
      R.Kp * ((c + 1) ^ R.Dp * (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db)) +
      F5.Cb * ((c + 1) ^ F5.Db * (Y + 1) ^ (1 + R.Db + R.Dp + F5.Db)) := by ring
  omega

end Gate

/-! ## The unit machine at a gate -/

/-- The unit's coefficient: the decode front's, the data counts', the FILTER pipeline's. -/
def cU {x : ℕ} {l : Literals} {F : GateFree l} (D : ThrDec.ThrDecFront x l F) (Kt Kf : ℕ) : ℕ :=
  D.Cn + D.Cb + (16 * Kt + 32) + Kf + 3

/-- **The THR unit machine v4 at a gate.** -/
noncomputable def thrSpec {l : Literals} {F : GateFree l} {x : ℕ} {W : WalkBankProducer} (hx : W.x ≤ x)
    (D : ThrDec.ThrDecFront x l F) (R : RadSetupB5.RadSetupSpecB5 x l F) (F5 : FiltSetup.FiltSetupSpec5 W)
    (Kf Df Kt Dt D0 : ℕ) (hD0 : ThrUnit.decDeg D ≤ D0) (hCD : 1 ≤ F.CD)
    (hKf : ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
      FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
        Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ Df * (L + 2) ^ (Df * (P.errExp + 1)))
    (hKt : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
      {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)),
      a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) →
      ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap,
        v ≤ Kt * (n + 1) ^ Dt) :
    ThrUnit.ThrUnitSpec4 l F where
  x := x
  sU := _
  U := ThrUnitRun.thrUnitM hx D R F5
  meas := fun kclk coef A a ha n hs a' ha' Cs carriers translation =>
    2 ^ (ThrMeas.Kq l F.filterErrDeg D0 Df Dt * (loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n)))
  need := fun X => ThrUnitRun.needU R F5 (cU D Kt Kf * X)
  nU := fun Y => ThrUnitRun.nUU R F5 (cU D Kt Kf * Y)
  Kn := KnU R F5 (cU D Kt Kf)
  Dn := DnU R F5
  need_le := fun X => needU_le R F5 _ X
  Ku := KuU R F5 (cU D Kt Kf)
  Du := DuU R F5
  nU_le := fun Y => nUU_le R F5 _ Y
  Km := ThrMeas.Kq l F.filterErrDeg D0 Df Dt
  Dm := 0
  meas_le := fun kclk coef A a ha n hs a' ha' Cs carriers translation _ => by
    have h1 : 1 ≤ ThrMeas.Kq l F.filterErrDeg D0 Df Dt := by unfold ThrMeas.Kq; omega
    simp only [pow_zero, mul_one]
    exact Nat.le_mul_of_pos_left _ h1
  ok := fun kclk coef A a ha n hs a' ha' Cs carriers translation hcall out j cap h => by
    have hm := ThrMeas.measC_le l F kclk coef A a ha n a' ha' Cs carriers translation hcall hs D D0 hD0 hCD Kf Df Kt Dt
      (hKt kclk coef A a ha n hs Cs carriers ha' hcall.2.2.2.1 (fun i => hcall.2.2.1 i))
    have hc1 : 1 ≤ cU D Kt Kf := by unfold cU; omega
    have hN := needU_mono R F5 hm
    have h' : ThrUnitRun.needU R F5 ((D.Cn + D.Cb + (16 * Kt + 32) + Kf + 3) *
        2 ^ (ThrMeas.Kq l F.filterErrDeg D0 Df Dt * (loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n)))) + j ≤ cap := h
    have hU := ThrUnitRun.unit_ok hx D R F5 Kf Df kclk coef A a ha n hs a' ha' Cs carriers translation hKf hcall out j cap
      (by omega)
    refine unitOK_mono hU (nUU_mono R F5 ?_)
    have e : cU D Kt Kf * (2 ^ (ThrMeas.Kq l F.filterErrDeg D0 Df Dt * (loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n))) + cap) =
        cU D Kt Kf * 2 ^ (ThrMeas.Kq l F.filterErrDeg D0 Df Dt * (loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n))) + cU D Kt Kf * cap := by ring
    have hcap : cap ≤ cU D Kt Kf * cap := Nat.le_mul_of_pos_left _ hc1
    unfold cU at hm e hcap ⊢
    omega

/-! ## The family -/

/-- `FiltPipeLe2`'s constants. -/
noncomputable def kfOf (hfp : BudgetIface.FiltPipeLe2) : ℕ := Classical.choose hfp
noncomputable def dfOf (hfp : BudgetIface.FiltPipeLe2) : ℕ := Classical.choose (Classical.choose_spec hfp)

theorem hKf_of (hfp : BudgetIface.FiltPipeLe2) : ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
    FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
      kfOf hfp * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ dfOf hfp * (L + 2) ^ (dfOf hfp * (P.errExp + 1)) :=
  Classical.choose_spec (Classical.choose_spec hfp)

/-- The THR numbers' exponent (at the cap's exponent `capZR l`, before the gate). -/
noncomputable def dtOf (l : Literals) : ℕ := Classical.choose (PrimT.W6.thrNumsPoly l (CallIndexR.capZR l))

/-- The THR numbers' coefficient (after the gate). -/
noncomputable def ktOf (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (PrimT.W6.thrNumsPoly l (CallIndexR.capZR l))
    (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F)

theorem hKt_of (l : Literals) (F : GateFree l) : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)), a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) →
    ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap,
      v ≤ ktOf l F * (n + 1) ^ dtOf l := by
  intro kclk coef A a ha n hs a' Cs carriers h1 h2 h3 v hv
  have hc : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤
      (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) * (n + 1) ^ CallIndexR.capZR l := by
    have h := CallIndexR.cap_leR l F.cr .thr n
    have h2' : (n + 2) ^ CallIndexR.capZR l ≤ 2 ^ CallIndexR.capZR l * (n + 1) ^ CallIndexR.capZR l := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    calc ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l := h
      _ ≤ CallIndexR.capK F.cr * (2 ^ CallIndexR.capZR l * (n + 1) ^ CallIndexR.capZR l) := Nat.mul_le_mul_left _ h2'
      _ = _ := by ring
  exact Classical.choose_spec (Classical.choose_spec (PrimT.W6.thrNumsPoly l (CallIndexR.capZR l))
    (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F) kclk coef A a ha n hs Cs carriers _ h1 h2 h3 hc v hv

theorem pow_mono2 {a b d e : ℕ} (hab : a ≤ b) (hde : d ≤ e) : (a + 1) ^ d ≤ (b + 1) ^ e :=
  (Nat.pow_le_pow_left (by omega) d).trans (Nat.pow_le_pow_right (by omega) hde)

/-- The family's coefficient (after the gate). -/
def C0 (Cd0 Cr0 Dr0 Kt Kf : ℕ) {W : WalkBankProducer} (F5 : FiltSetup.FiltSetupSpec5 W) : ℕ :=
  (Cd0 + (16 * Kt + 32) + Kf + 3) + Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 +
      F5.Cn * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ F5.Dn +
    (22 * (Cd0 + (16 * Kt + 32) + Kf + 3) + 23 + Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 +
      Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 + F5.Cb * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ F5.Db)

theorem spec_cf {l : Literals} {F : GateFree l} {x : ℕ} {W : WalkBankProducer} (hx : W.x ≤ x)
    (D : ThrDec.ThrDecFront x l F) (R : RadSetupB5.RadSetupSpecB5 x l F) (F5 : FiltSetup.FiltSetupSpec5 W)
    (Kf Df Kt Dt D0 : ℕ) (hD0 : ThrUnit.decDeg D ≤ D0) (hCD : 1 ≤ F.CD) (hKf) (hKt) (Cd0 Cr0 Dr0 : ℕ)
    (hCd : ThrUnit.decCf D ≤ Cd0) (hCr : ThrUnit.radCf5 R ≤ Cr0) (hDr : ThrUnit.radDeg5 R ≤ Dr0) :
    (thrSpec hx D R F5 Kf Df Kt Dt D0 hD0 hCD hKf hKt).cf4 ≤ C0 Cd0 Cr0 Dr0 Kt Kf F5 := by
  show KnU R F5 (cU D Kt Kf) + KuU R F5 (cU D Kt Kf) ≤ _
  unfold ThrUnit.decCf at hCd
  unfold ThrUnit.radCf5 at hCr
  unfold ThrUnit.radDeg5 at hDr
  have hc : cU D Kt Kf ≤ Cd0 + (16 * Kt + 32) + Kf + 3 := by unfold cU; omega
  have hRn : R.Dn ≤ Dr0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hDr
  have hRb : R.Db ≤ Dr0 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hDr
  have hRp : R.Dp ≤ Dr0 := le_trans (le_max_right _ _) hDr
  have p1 := pow_mono2 hc hRn
  have p2 := pow_mono2 hc hRb
  have p3 := pow_mono2 hc hRp
  have p4 := pow_mono2 hc (le_refl F5.Dn)
  have p5 := pow_mono2 hc (le_refl F5.Db)
  have q1 : R.Kn * (cU D Kt Kf + 1) ^ R.Dn ≤ Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 :=
    Nat.mul_le_mul (by omega) p1
  have q2 : R.Kb * (cU D Kt Kf + 1) ^ R.Db ≤ Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 :=
    Nat.mul_le_mul (by omega) p2
  have q3 : R.Kp * (cU D Kt Kf + 1) ^ R.Dp ≤ Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 :=
    Nat.mul_le_mul (by omega) p3
  have q4 := Nat.mul_le_mul_left F5.Cn p4
  have q5 := Nat.mul_le_mul_left F5.Cb p5
  unfold KnU KuU C0
  omega

/-- **The producer statement v5, proved.** -/
noncomputable def thrUnitOf5 (l : Literals) : ThrUnit.ThrUnitOf5 l :=
  fun W xF hxF F5 hfp dec rad fe =>
    ⟨max (max (1 + (rad fe).1 + F5.Dn) (1 + (rad fe).1 + (rad fe).1 + F5.Db))
        (max 0 (ThrMeas.Kq l fe (dec fe).1 (dfOf hfp) (dtOf l))),
      envMax (dec fe).2.1 (rad fe).2.1, max (max (dec fe).2.2.1 (rad fe).2.2.1) 1,
      fun F hF hE hCD =>
        ⟨C0 ((dec fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
              (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCD)).1
            ((rad fe).2.2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE)
              (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCD)).1 (rad fe).1 (ktOf l F) (kfOf hfp) F5,
          fun kclk coef A a ha =>
            ⟨thrSpec (hxF F)
                (((dec fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
                  (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCD)).2 kclk coef A a ha).1
                (((rad fe).2.2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE)
                  (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCD)).2 kclk coef A a ha).1 F5
                (kfOf hfp) (dfOf hfp) (ktOf l F) (dtOf l) (dec fe).1
                (((dec fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
                  (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCD)).2 kclk coef A a ha).2.1
                (le_trans (le_max_right _ _) hCD) (hKf_of hfp) (hKt_of l F),
              by
                have hR := (((rad fe).2.2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE)
                  (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCD)).2 kclk coef A a ha).2.1
                unfold ThrUnit.radDeg5 at hR
                show max (max (DnU _ F5) (DuU _ F5)) (max 0 (ThrMeas.Kq l F.filterErrDeg (dec fe).1 (dfOf hfp) (dtOf l))) ≤ _
                rw [hF]
                unfold DnU DuU
                have h1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
                have h2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
                have h3 := le_trans (le_max_right _ _) hR
                exact max_le_max (max_le_max (by omega) (by omega)) le_rfl,
              spec_cf (hxF F) _ _ F5 _ _ _ _ _ _ _ _ _ _ _ _
                (((dec fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
                  (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCD)).2 kclk coef A a ha).2.2
                (((rad fe).2.2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE)
                  (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCD)).2 kclk coef A a ha).2.2
                (((rad fe).2.2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE)
                  (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCD)).2 kclk coef A a ha).2.1⟩⟩⟩

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnitOf
