import Proof.Wire_3_5.UnionMachine.RadAbsorb
import Proof.Wire_3_5.UnionMachine.ThrUnitIface3

/-! # The THR unit machine's contract, v4: the measure absorbed by the THR load `Ψ_T` alone

`ThrUnit.ThrUnitSpec3` (THRU3) bounds the per-call measure by `2^{K·psiOf n}`, `psiOf = max(Ψ_T, Ψ_S, Ψ_aux)`
(P3:3106-3107); the THR shell (THRTAIL) dimensions its counters in-machine, so the SYM and auxiliary loads would enter
its dimension stage. Every term of the THR unit's measure is a THR quantity: the RADIX list bound is absorbed through
`ThrSide.loadThr_le` (`RadAbsorb.lb_absorb`'s own chain), the decode's `2^{K·L²}` through `L² ≤ C_D·L² ≤ Ψ_T`, the
THR cap `B_T` through `√(B_T·L) ≤ Ψ_T`. So the bound is stated against **the THR load**
`Ψ_T = loadThr C_D k L B_T` (P3:3094-3100, `k = kOf n`, `L = ⌈log₂(n+2)⌉`, `B_T = capOf .thr n`):

* `loadThr_le'`, **`lb_absorbT`**: the RADIX row's list bound times `L` below `cAb l · Ψ_T`;
* **`ThrUnitSpec4 l F`**: `ThrUnitSpec3` with `meas_le` against `Ψ_T`; `ThrUnitSpec4.toSpec3` (`Ψ_T ≤ psiOf`);
* `deg4`, `cf4`, **`ThrUnitU4 l`**, **`ThrLeafOfU4 l`**, **`ThrUnitOf5 l`** (the producer statement), `nU_tail`.

Paper quantity of the main type: the THR tape's units within the preprocessing class `2^{O(Ψ_T)}` (P3:3089-3108). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.Stars

/-! ## The RADIX list bound against the THR load -/

theorem loadThr_le' (CD k L BT : ℕ) :
    CD * CD * ((k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L)) ≤ loadThr CD k L BT := by
  unfold loadThr sqrtUp
  have e : CD * CD * ((k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L)) =
      CD * ((k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + L ^ 2))) := by ring
  rw [e]
  apply Nat.mul_le_mul_left
  have : (k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + L ^ 2)) ≤ (k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + 1 + L ^ 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  omega

/-- **The RADIX row's list bound times `L` below `cAb l · Ψ_T`** (`RadAbsorb.lb_absorb`'s chain, stopped at `Ψ_T`). -/
theorem lb_absorbT (l : Literals) (F : GateFree l) (hCD : 1 ≤ F.CD) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) * Nat.clog 2 (n + 2) ≤
      RadAbsorb.cAb l * loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
        (((gate0 l F).budget kclk coef A a ha).capOf .thr n) := by
  set L := Nat.clog 2 (n + 2) with hLd
  set BT := ((gate0 l F).budget kclk coef A a ha).capOf .thr n with hBT
  set t := thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers with ht
  set J := thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers with hJ
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by
    rw [hLd]; exact (Nat.clog_pos (by norm_num) (by omega)).ne')
  have hJle : J ≤ ThrSide.eJ l * L := ThrSide.thrCallJ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have htle : t ≤ (2 * ThrSide.eJ l + 1) * L :=
    ThrSide.thrCallT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  -- B_*
  set Bs := (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W 0 with hBs0
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hBst : a' * (4096 * ((carriers.length + 1) * (4096 * BT))) ≤ 201326592 * BT := by
    have h1 : a' * (4096 * ((carriers.length + 1) * (4096 * BT))) ≤ 4 * (4096 * (3 * (4096 * BT))) :=
      Nat.mul_le_mul ha' (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
    omega
  -- the windows
  have hW : ∀ j, (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W j ≤
      16 * t + 20 * (Nat.sqrt (t * (a' * (4096 * ((carriers.length + 1) * (4096 * BT))))) + 1 + 1) := by
    intro j
    show 16 * t + 20 * ((Nat.sqrt (t * (a' * (4096 * ((carriers.length + 1) * (4096 * BT))))) + 1) / 2 ^ (j / 2) + 1) ≤ _
    have := Nat.div_le_self (Nat.sqrt (t * (a' * (4096 * ((carriers.length + 1) * (4096 * BT))))) + 1) (2 ^ (j / 2))
    omega
  have hsq : Nat.sqrt (t * (a' * (4096 * ((carriers.length + 1) * (4096 * BT))))) ≤
      RadAbsorb.cSq l * (Nat.sqrt (BT * L) + 1) := by
    apply ThrSide.sqrt_le_mul
    have e1 : t * (a' * (4096 * ((carriers.length + 1) * (4096 * BT)))) ≤ ((2 * ThrSide.eJ l + 1) * L) * (201326592 * BT) :=
      Nat.mul_le_mul htle hBst
    have e2 : ((2 * ThrSide.eJ l + 1) * L) * (201326592 * BT) ≤ RadAbsorb.cSq l * RadAbsorb.cSq l * (BT * L) := by
      unfold RadAbsorb.cSq
      have : (2 * ThrSide.eJ l + 1) * 201326592 ≤ (2 * ThrSide.eJ l + 1) * 14190 * ((2 * ThrSide.eJ l + 1) * 14190) := by
        nlinarith
      nlinarith [Nat.zero_le (BT * L)]
    exact e1.trans e2
  -- the sum
  have hsum : ∑ j ∈ Finset.range J, (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W j ≤
      J * (16 * t + 20 * (RadAbsorb.cSq l * (Nat.sqrt (BT * L) + 1) + 1) + 20) := by
    have h := Finset.sum_le_card_nsmul (Finset.range J) (fun j => (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers
      translation).W j) (16 * t + 20 * (RadAbsorb.cSq l * (Nat.sqrt (BT * L) + 1) + 1) + 20) (fun j _ => by
        have := hW j; omega)
    rw [Finset.card_range, smul_eq_mul] at h
    exact h
  have hlb := RadScan.listBound_eq (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
  have hDJ : (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J = J := rfl
  rw [hDJ] at hlb
  -- the load
  have hload := loadThr_le' F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) L BT
  have hkL : L * L * (Nat.sqrt (BT * L) + L * L) ≤
      F.CD * F.CD * ((((gate0 l F).budget kclk coef A a ha).kOf n + L) * (((gate0 l F).budget kclk coef A a ha).kOf n + L) * (Nat.sqrt (BT * L) + L * L)) := by
    have h1 : 1 ≤ F.CD * F.CD := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 : L * L ≤ (((gate0 l F).budget kclk coef A a ha).kOf n + L) * (((gate0 l F).budget kclk coef A a ha).kOf n + L) := Nat.mul_le_mul (by omega) (by omega)
    calc L * L * (Nat.sqrt (BT * L) + L * L) ≤ (((gate0 l F).budget kclk coef A a ha).kOf n + L) * (((gate0 l F).budget kclk coef A a ha).kOf n + L) * (Nat.sqrt (BT * L) + L * L) :=
          Nat.mul_le_mul_right _ h2
      _ ≤ F.CD * F.CD * ((((gate0 l F).budget kclk coef A a ha).kOf n + L) * (((gate0 l F).budget kclk coef A a ha).kOf n + L) * (Nat.sqrt (BT * L) + L * L)) := Nat.le_mul_of_pos_left _ h1
  have hfin : (4 * (ThrSide.eJ l * L * (16 * ((2 * ThrSide.eJ l + 1) * L) + 20 * (RadAbsorb.cSq l * (Nat.sqrt (BT * L) + 1) + 1) +
      20)) + 1) * L ≤ RadAbsorb.cAb l * (L * L * (Nat.sqrt (BT * L) + L * L)) :=
    RadAbsorb.absorb_arith (ThrSide.eJ l) (RadAbsorb.cSq l) L (Nat.sqrt (BT * L)) hL1
  have hstep : ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) ≤
      4 * (ThrSide.eJ l * L * (16 * ((2 * ThrSide.eJ l + 1) * L) + 20 * (RadAbsorb.cSq l * (Nat.sqrt (BT * L) + 1) + 1) + 20)) +
        1 := by
    rw [hlb]
    have h1 : J * (16 * t + 20 * (RadAbsorb.cSq l * (Nat.sqrt (BT * L) + 1) + 1) + 20) ≤
        ThrSide.eJ l * L * (16 * ((2 * ThrSide.eJ l + 1) * L) + 20 * (RadAbsorb.cSq l * (Nat.sqrt (BT * L) + 1) + 1) + 20) :=
      Nat.mul_le_mul hJle (by omega)
    omega
  calc ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) * L
      ≤ (4 * (ThrSide.eJ l * L * (16 * ((2 * ThrSide.eJ l + 1) * L) + 20 * (RadAbsorb.cSq l * (Nat.sqrt (BT * L) + 1) + 1) +
          20)) + 1) * L := Nat.mul_le_mul_right _ hstep
    _ ≤ RadAbsorb.cAb l * (L * L * (Nat.sqrt (BT * L) + L * L)) := hfin
    _ ≤ RadAbsorb.cAb l * loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) L BT :=
      Nat.mul_le_mul_left _ (hkL.trans hload)

/-! ## THRU4 -/

/-- **The THR unit machine at a gate, v4**: as `ThrUnitSpec3`, the measure absorbed by the THR load `Ψ_T`. -/
structure ThrUnitSpec4 (l : Literals) (F : GateFree l) where
  x : ℕ
  sU : ℕ
  U : Machine (PrimAsm.CellLoop.TT x) sU
  meas : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ), ℕ
  need : ℕ → ℕ
  nU : ℕ → ℕ
  Kn : ℕ
  Dn : ℕ
  need_le : ∀ X, need X ≤ Kn * (X + 1) ^ Dn
  Ku : ℕ
  Du : ℕ
  nU_le : ∀ X, nU X ≤ Ku * (X + 1) ^ Du
  Km : ℕ
  Dm : ℕ
  meas_le : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    meas kclk coef A a ha n hs a' ha' Cs carriers translation ≤
      Km * (n + 2) ^ Dm * 2 ^ (Km * loadThr F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
        (((gate0 l F).budget kclk coef A a ha).capOf .thr n))
  ok : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (out : List Bool) (j cap : ℕ), need (meas kclk coef A a ha n hs a' ha' Cs carriers translation) + j ≤ cap →
    PrimThrW.Shell.UnitOK cap x U (nU (meas kclk coef A a ha n hs a' ha' Cs carriers translation + cap))
      (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
      (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers)
      (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
        (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) j out

/-- The unit's exponents (with the envelope: from `(l, fe)` only). -/
def ThrUnitSpec4.deg4 {l : Literals} {F : GateFree l} (U : ThrUnitSpec4 l F) : ℕ :=
  max (max U.Dn U.Du) (max U.Dm U.Km)

/-- The unit's coefficients (after `F`). -/
def ThrUnitSpec4.cf4 {l : Literals} {F : GateFree l} (U : ThrUnitSpec4 l F) : ℕ := U.Kn + U.Ku

/-- **The unit machines v4 in `ThrLeafJ2`'s order of choice** (`Seams.StageU`). -/
abbrev ThrUnitU4 (l : Literals) : Type :=
  FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrUnitSpec4 l F) (fun U => U.deg4) (fun U => U.cf4)

/-- **The THR writer's leaf from the unit machines, v4** (THRTAIL: the flattening, the emission, the shell over the v4 data stage dimensioned by the THR load, the class link through `meas_le`, `ThrWriterAtJ`). -/
abbrev ThrLeafOfU4 (l : Literals) : Type :=
  ThrData.ThrStage4U l → ThrUnitU4 l → WritersJoin.ThrLeafJ2 l

/-- **The producer statement, v5**: the uniform decode fronts and RADIX setups (v5) on the unit cells `xF F`, the
FILTER setup and its pipe bound give the unit machines v4. -/
abbrev ThrUnitOf5 (l : Literals) : Type :=
  ∀ (W : PrimT.WalkBank.WalkBankProducer) (xF : GateFree l → ℕ), (∀ F, W.x ≤ xF F) →
    FiltSetup.FiltSetupSpec5 W → BudgetIface.FiltPipeLe2 →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrDec.ThrDecFront (xF F) l F) (fun D => decDeg D)
      (fun D => decCf D) →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => RadSetupB5.RadSetupSpecB5 (xF F) l F) (fun R => radDeg5 R)
      (fun R => radCf5 R) →
    ThrUnitU4 l

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
