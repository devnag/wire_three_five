import Proof.Wire_3_5.Primitive.Writers.NumsXT

/-! # (HASH (c)): the HASH writer's dimension stage at `mOfH KL KH P = mOfT KL P + KH·L³`

The HASH tape's units are FILTER rows of the auxiliary filter (P3:2220-2226) at the error exponent `e = listE …`
(`thrCallE`, `Θ(Dexp·L²)`); their pipeline costs `2^{Θ(Dexp·L³)}` (the table's degree `3·(128·walkLen)+1`), above the THR
shell's `2^{mOfT KL P}` (`KL·L²`) and inside the preprocessing class (`Ψ_aux = C_D[k+L²+(k+L³)L²(k+L)]`, P3:3101-3102;
`scratchpad/pa2/hash_aux_check.py`). The HASH writer's loop and scrub are dimensioned by `2^{mOfH KL KH P}`: the THR
dimension program (`NumsXT.numsWT`) with one more stage before the source, `m += ((L·KH)·L)·L`.

* `mOfH`, `khW` (the extra stage), **`numsWH`**, **`numsWH_spec`** (from the filled state: the source
  `srcWord (mOfH KL KH P)`, the request and the fill count kept, within `numsCostH`);
* `numsPH`, **`numsMH`** (the stage, every head back at `0`), `numsStageCostH`, **`nums_stepH`**.

Paper quantity of the main type: the dimension `2^{mOf P + KL·L² + KH·L³}` of the HASH writer (the auxiliary filter's
rows inside `2^{O(Ψ_aux)}`, prim:runtime P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.NumsXH
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.NumsX
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimAsm.NumsXT

/-! ## The program -/

/-- **The HASH writer's dimension** `mOfT KL P + KH·L³`. -/
def mOfH (KL KH : ℕ) (P : Shared.StarParams) : ℕ := PrimThrW.Shell2.mOfT KL P + KH * Nat.clog 2 (P.n + 2) ^ 3

/-- `rQ := rQ + rB·L` (`L` in `rA`). -/
def mBQ : Fin 5 ↪ Fin NR := ⟨![rB, rA, rQ, rX, rY], by decide⟩

/-- `rM := rM + rQ·L`. -/
def mMQ : Fin 5 ↪ Fin NR := ⟨![rQ, rA, rM, rX, rY], by decide⟩

/-- The extra stage: `rB := L·KH`, `rQ := (L·KH)·L`, `m += ((L·KH)·L)·L`. -/
def khW (KH : ℕ) : WM NS NR :=
  .seq (WM.clear rQ) (.seq (WM.clear rB) (.seq (StarNums.incN rQ KH) (.seq (mulAddW mLK) (.seq (WM.clear rQ)
    (.seq (mulAddW mBQ) (mulAddW mMQ))))))

/-- The HASH dimension program: `n`, the star numbers, `m = 2·kh + L`, `m += KL·L²`, `m += KH·L³`, the source. -/
def numsWH (KL KH cr : ℕ) : WM NS NR :=
  .seq (readNatM true xIN rF rC (SN 0) rP rT) (.seq (StarNums.starNumsM cr 0 SN) (.seq mW (.seq (klW KL)
    (.seq (khW KH) srcW))))

/-- The program's cost bound. -/
def numsCostH (n cr KL KH W : ℕ) : ℕ :=
  numsCostT n cr KL W + 60 * (KH * (n + 2) * (n + 2) * (n + 2)) + 8 * UnaryPow.sq (2 * W + 2)

theorem mOfH_eq (KL KH : ℕ) (P : Shared.StarParams) :
    PrimThrW.Shell2.mOfT KL P + (0 + ((0 + Nat.clog 2 (P.n + 2) * KH) * Nat.clog 2 (P.n + 2))) *
      Nat.clog 2 (P.n + 2) = mOfH KL KH P := by
  unfold mOfH
  ring

theorem numsWH_spec (KL KH cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 16 + KL * (P.n + 2) ^ 2 + KH * (P.n + 2) ^ 3 ≤ W) :
    ∃ σF c, WExec (2 * W + 2) (numsWH KL KH cr) (σN w W) σF c ∧ σF.st xOUT = srcWord (mOfH KL KH P) ∧
      σF.st xIN = RepairOrdinary.frame w ∧ σF.st xCT = List.replicate W true ∧ c ≤ numsCostH P.n cr KL KH W := by
  set cap := 2 * W + 2 with hcap
  have hpow := CopyNat.two_pow_natBitLength_le P.n
  have hkh := kh2_le P
  have hL := clog_le P.n
  have hmo := mOf_le P
  have hsq := UnaryPow.sq_ge cap
  have hL1 : 1 ≤ Nat.clog 2 (P.n + 2) := Nat.clog_pos (by norm_num) (by omega)
  have hp2 : KL * (P.n + 2) ^ 2 = KL * (P.n + 2) * (P.n + 2) := by ring
  have hKL1 : KL ≤ KL * (P.n + 2) * (P.n + 2) := by
    have : 1 ≤ (P.n + 2) * (P.n + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc KL = KL * 1 := (mul_one _).symm
      _ ≤ KL * ((P.n + 2) * (P.n + 2)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have hLK : Nat.clog 2 (P.n + 2) * KL ≤ KL * (P.n + 2) * (P.n + 2) := by
    have h1 : Nat.clog 2 (P.n + 2) * KL ≤ (P.n + 2) * KL := Nat.mul_le_mul_right _ hL
    have h2 : (P.n + 2) * KL ≤ KL * (P.n + 2) * (P.n + 2) := by nlinarith
    omega
  have hLKL : Nat.clog 2 (P.n + 2) * KL * Nat.clog 2 (P.n + 2) ≤ KL * (P.n + 2) * (P.n + 2) := by
    have h1 : Nat.clog 2 (P.n + 2) * KL * Nat.clog 2 (P.n + 2) ≤ (P.n + 2) * KL * (P.n + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hL) hL
    have h2 : (P.n + 2) * KL * (P.n + 2) = KL * (P.n + 2) * (P.n + 2) := by ring
    omega
  have hp3 : KH * (P.n + 2) ^ 3 = KH * (P.n + 2) * (P.n + 2) * (P.n + 2) := by ring
  have hLKH : Nat.clog 2 (P.n + 2) * KH ≤ KH * (P.n + 2) * (P.n + 2) * (P.n + 2) := by
    have h1 : Nat.clog 2 (P.n + 2) * KH ≤ (P.n + 2) * KH := Nat.mul_le_mul_right _ hL
    have hh : 1 ≤ (P.n + 2) * (P.n + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 : (P.n + 2) * KH ≤ KH * (P.n + 2) * (P.n + 2) * (P.n + 2) :=
      calc (P.n + 2) * KH = KH * (P.n + 2) * 1 := by ring
        _ ≤ KH * (P.n + 2) * ((P.n + 2) * (P.n + 2)) := Nat.mul_le_mul_left _ hh
        _ = _ := by ring
    omega
  have hLKH2 : Nat.clog 2 (P.n + 2) * KH * Nat.clog 2 (P.n + 2) ≤ KH * (P.n + 2) * (P.n + 2) * (P.n + 2) := by
    have h1 : Nat.clog 2 (P.n + 2) * KH * Nat.clog 2 (P.n + 2) ≤ (P.n + 2) * KH * (P.n + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hL) hL
    have hh : 1 ≤ P.n + 2 := by omega
    have h2 : (P.n + 2) * KH * (P.n + 2) ≤ KH * (P.n + 2) * (P.n + 2) * (P.n + 2) :=
      calc (P.n + 2) * KH * (P.n + 2) = KH * (P.n + 2) * (P.n + 2) * 1 := by ring
        _ ≤ KH * (P.n + 2) * (P.n + 2) * (P.n + 2) := Nat.mul_le_mul_left _ hh
    omega
  have hLKH3 : Nat.clog 2 (P.n + 2) * KH * Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2) ≤
      KH * (P.n + 2) * (P.n + 2) * (P.n + 2) := by
    have h1 : Nat.clog 2 (P.n + 2) * KH * Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2) ≤
        (P.n + 2) * KH * (P.n + 2) * (P.n + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ hL) hL) hL
    have h2 : (P.n + 2) * KH * (P.n + 2) * (P.n + 2) = KH * (P.n + 2) * (P.n + 2) * (P.n + 2) := by ring
    omega
  have hKH1 : KH ≤ KH * (P.n + 2) * (P.n + 2) * (P.n + 2) := by
    have : 1 ≤ (P.n + 2) * (P.n + 2) * (P.n + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc KH = KH * 1 := (mul_one _).symm
      _ ≤ KH * ((P.n + 2) * (P.n + 2) * (P.n + 2)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  -- 1: `n` into `SN 0`
  have r1 := readNatM_spec cap true xIN rF rC (SN 0) rP rT (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) P.n [] (marks sfx ++ [false]) (σN w W)
    (by simp only [σN, if_pos rfl]; rw [hw]; exact frame_split _ _) (by rfl) rfl rfl rfl rfl
    (by simp only [σN]; rw [pow_succ]; omega)
  set σ1 := ((σN w W).seth xIN (([] : List Bool).length + stp true * (RepairRepresentation.natWord P.n).length)).setv
    (SN 0) ((σN w W).val (SN 0) + P.n) with hσ1
  have v1 : ∀ r : Fin NR, r ≠ SN 0 → σ1.val r = 0 := by
    intro r hr
    simp [hσ1, Function.update_apply, hr, σN]
  have v10 : σ1.val (SN 0) = P.n := by simp [hσ1, σN]
  -- 2: the star numbers
  have r2 := StarNums.starNums_spec cap cr 0 SN P hrP σ1 v10
    (fun i hi => v1 _ (fun e => hi (SN.injective e))) (by omega)
  set σ2 := StarNums.starOut σ1 SN P 0 with hσ2
  obtain ⟨o1, -, -, -, -, -, o8, -, -⟩ := StarNums.starOut_val σ1 SN P 0
  -- 3: `m`
  have r3 := mW_spec cap σ2 (P.s * (P.r / 2)) (Nat.clog 2 (P.n + 2)) o8 o1
    (by rw [hσ2, starOut_hi _ _ _ _ (by decide)]; exact v1 _ (SN_ne 0 rM (by decide)).symm)
    (by rw [hσ2, starOut_hi _ _ _ _ (by decide)]; exact v1 _ (SN_ne 0 rT (by decide)).symm) (by omega)
  set σ3 := σ2.setv rM (2 * (P.s * (P.r / 2)) + Nat.clog 2 (P.n + 2)) with hσ3
  have v3 : ∀ r : Fin NR, 20 ≤ r.val → r ≠ rM → σ3.val r = 0 := by
    intro r hr hrm
    rw [hσ3]
    simp only [WState.setv_val, Function.update_apply, if_neg hrm]
    rw [hσ2, starOut_hi _ _ _ _ hr]
    exact v1 _ (fun e => by rw [e, SN_val] at hr; simp at hr)
  -- 3b: `m += (L·KL)·L`
  set L := Nat.clog 2 (P.n + 2) with hLd
  have o1' : σ3.val (SN 1) = L := by
    rw [hσ3, WState.setv_val, Function.update_of_ne (SN_ne 1 rM (by decide))]; exact o1
  have o3m : σ3.val rM = mOf P := by rw [hσ3, WState.setv_val, Function.update_self]; rfl
  have hn0 : (0 + L * KL) * L = L * KL * L := by ring
  have ka := SparseNum.copy1 cap (SN 1) rA rT (by decide) (by decide) (by decide) L σ3 o1'
    (v3 rA (by decide) (by decide)) (v3 rT (by decide) (by decide)) (by omega)
  obtain ⟨σa, hσa⟩ : ∃ y, y = σ3.setv rA L := ⟨_, rfl⟩
  rw [← hσa] at ka
  have va : ∀ r : Fin NR, r ≠ rA → σa.val r = σ3.val r := fun r h => by
    rw [hσa, WState.setv_val, Function.update_of_ne h]
  have kb := SparseNum.incN0 cap rQ KL σa (by rw [va _ (by decide)]; exact v3 rQ (by decide) (by decide)) (by omega)
  obtain ⟨σb, hσb⟩ : ∃ y, y = σa.setv rQ KL := ⟨_, rfl⟩
  rw [← hσb] at kb
  have vb : ∀ r : Fin NR, r ≠ rQ → σb.val r = σa.val r := fun r h => by
    rw [hσb, WState.setv_val, Function.update_of_ne h]
  have kc := SparseNum.mulAdd1 cap mLK L KL 0 σb
    (show σb.val (SN 1) = L by rw [vb _ (by decide), va _ (by decide)]; exact o1')
    (show σb.val rQ = KL by rw [hσb, WState.setv_val, Function.update_self])
    (show σb.val rB = 0 by rw [vb _ (by decide), va _ (by decide)]; exact v3 rB (by decide) (by decide))
    (show σb.val rX = 0 by rw [vb _ (by decide), va _ (by decide)]; exact v3 rX (by decide) (by decide))
    (show σb.val rY = 0 by rw [vb _ (by decide), va _ (by decide)]; exact v3 rY (by decide) (by decide))
    (by omega) (by omega) (by omega)
  obtain ⟨σc, hσc⟩ : ∃ y, y = σb.setv rB (0 + L * KL) := ⟨_, rfl⟩
  have kc' : WExec cap (mulAddW mLK) σb σc (UnaryPow.sq cap) := by rw [hσc]; exact kc
  have vc : ∀ r : Fin NR, r ≠ rB → σc.val r = σb.val r := fun r h => by
    rw [hσc, WState.setv_val, Function.update_of_ne h]
  have kd := SparseNum.mulAdd1 cap mML (0 + L * KL) L (mOf P) σc
    (show σc.val rB = 0 + L * KL by rw [hσc, WState.setv_val, Function.update_self])
    (show σc.val rA = L by rw [vc _ (by decide), vb _ (by decide), hσa, WState.setv_val, Function.update_self])
    (show σc.val rM = mOf P by rw [vc _ (by decide), vb _ (by decide), va _ (by decide)]; exact o3m)
    (show σc.val rX = 0 by rw [vc _ (by decide), vb _ (by decide), va _ (by decide)]; exact v3 rX (by decide) (by decide))
    (show σc.val rY = 0 by rw [vc _ (by decide), vb _ (by decide), va _ (by decide)]; exact v3 rY (by decide) (by decide))
    (by omega) (by omega) (by omega)
  obtain ⟨σd, hσd⟩ : ∃ y, y = σc.setv rM (mOf P + (0 + L * KL) * L) := ⟨_, rfl⟩
  have kd' : WExec cap (mulAddW mML) σc σd (UnaryPow.sq cap) := by rw [hσd]; exact kd
  have vd : ∀ r : Fin NR, r ≠ rM → σd.val r = σc.val r := fun r h => by
    rw [hσd, WState.setv_val, Function.update_of_ne h]
  have dz : ∀ r : Fin NR, 20 ≤ r.val → r ≠ rM → r ≠ rA → r ≠ rQ → r ≠ rB → σd.val r = 0 := by
    intro r h1 h2 h3 h4 h5
    rw [vd _ h2, vc _ h5, vb _ h4, va _ h3]
    exact v3 r h1 h2
  have hmT : mOf P + (0 + L * KL) * L = PrimThrW.Shell2.mOfT KL P := mOfT_eq KL P
  have hmT' : PrimThrW.Shell2.mOfT KL P ≤ 2 * P.n + 2 + KL * (P.n + 2) * (P.n + 2) := by
    rw [← hmT]
    have : (0 + L * KL) * L = L * KL * L := by ring
    omega
  -- 3c: `m += ((L·KH)·L)·L`
  have vdQ : σd.val rQ = KL := by rw [vd _ (by decide), vc _ (by decide), hσb, WState.setv_val, Function.update_self]
  have vdB : σd.val rB = 0 + L * KL := by rw [vd _ (by decide), hσc, WState.setv_val, Function.update_self]
  have vdA : σd.val rA = L := by
    rw [vd _ (by decide), vc _ (by decide), vb _ (by decide), hσa, WState.setv_val, Function.update_self]
  have vdM : σd.val rM = PrimThrW.Shell2.mOfT KL P := by rw [hσd, WState.setv_val, Function.update_self]; exact hmT
  have vdS : σd.val (SN 1) = L := by
    rw [vd _ (by decide), vc _ (by decide), vb _ (by decide), va _ (by decide)]; exact o1'
  have ke1 := SparseNum.clear1 cap rQ KL σd vdQ (by omega)
  obtain ⟨σe1, hσe1⟩ : ∃ y, y = σd.setv rQ 0 := ⟨_, rfl⟩
  rw [← hσe1] at ke1
  have ke2 := SparseNum.clear1 cap rB (0 + L * KL) σe1 (by rw [hσe1, WState.setv_val, Function.update_of_ne (by decide)]; exact vdB)
    (by omega)
  obtain ⟨σe2, hσe2⟩ : ∃ y, y = σe1.setv rB 0 := ⟨_, rfl⟩
  rw [← hσe2] at ke2
  have ke3 := SparseNum.incN0 cap rQ KH σe2 (by rw [hσe2, WState.setv_val, Function.update_of_ne (by decide), hσe1,
    WState.setv_val, Function.update_self]) (by omega)
  obtain ⟨σe3, hσe3⟩ : ∃ y, y = σe2.setv rQ KH := ⟨_, rfl⟩
  rw [← hσe3] at ke3
  have ve3 : ∀ r : Fin NR, r ≠ rQ → r ≠ rB → σe3.val r = σd.val r := fun r h1 h2 => by
    rw [hσe3, WState.setv_val, Function.update_of_ne h1, hσe2, WState.setv_val, Function.update_of_ne h2, hσe1,
      WState.setv_val, Function.update_of_ne h1]
  have ke4 := SparseNum.mulAdd1 cap mLK L KH 0 σe3
    (show σe3.val (SN 1) = L by rw [ve3 _ (by decide) (by decide)]; exact vdS)
    (show σe3.val rQ = KH by rw [hσe3, WState.setv_val, Function.update_self])
    (show σe3.val rB = 0 by rw [hσe3, WState.setv_val, Function.update_of_ne (by decide), hσe2, WState.setv_val,
      Function.update_self])
    (show σe3.val rX = 0 by rw [ve3 _ (by decide) (by decide)]; exact dz rX (by decide) (by decide) (by decide) (by decide) (by decide))
    (show σe3.val rY = 0 by rw [ve3 _ (by decide) (by decide)]; exact dz rY (by decide) (by decide) (by decide) (by decide) (by decide))
    (by omega) (by omega) (by omega)
  obtain ⟨σe4, hσe4⟩ : ∃ y, y = σe3.setv rB (0 + L * KH) := ⟨_, rfl⟩
  have ke4' : WExec cap (mulAddW mLK) σe3 σe4 (UnaryPow.sq cap) := by rw [hσe4]; exact ke4
  have ke5 := SparseNum.clear1 cap rQ KH σe4 (by rw [hσe4, WState.setv_val, Function.update_of_ne (by decide), hσe3,
    WState.setv_val, Function.update_self]) (by omega)
  obtain ⟨σe5, hσe5⟩ : ∃ y, y = σe4.setv rQ 0 := ⟨_, rfl⟩
  rw [← hσe5] at ke5
  have ve5 : ∀ r : Fin NR, r ≠ rQ → r ≠ rB → σe5.val r = σd.val r := fun r h1 h2 => by
    rw [hσe5, WState.setv_val, Function.update_of_ne h1, hσe4, WState.setv_val, Function.update_of_ne h2]
    exact ve3 r h1 h2
  have hs0 : 0 + L * KH = L * KH := by ring
  have hs1 : (0 + L * KH) * L = L * KH * L := by ring
  have hs2 : (0 + (0 + L * KH) * L) * L = L * KH * L * L := by ring
  have hs3 : 0 + (0 + L * KH) * L = L * KH * L := by ring
  have ke6 := SparseNum.mulAdd1 cap mBQ (0 + L * KH) L 0 σe5
    (show σe5.val rB = 0 + L * KH by rw [hσe5, WState.setv_val, Function.update_of_ne (by decide), hσe4,
      WState.setv_val, Function.update_self])
    (show σe5.val rA = L by rw [ve5 _ (by decide) (by decide)]; exact vdA)
    (show σe5.val rQ = 0 by rw [hσe5, WState.setv_val, Function.update_self])
    (show σe5.val rX = 0 by rw [ve5 _ (by decide) (by decide)]; exact dz rX (by decide) (by decide) (by decide) (by decide) (by decide))
    (show σe5.val rY = 0 by rw [ve5 _ (by decide) (by decide)]; exact dz rY (by decide) (by decide) (by decide) (by decide) (by decide))
    (by omega) (by omega) (by omega)
  obtain ⟨σe6, hσe6⟩ : ∃ y, y = σe5.setv rQ (0 + (0 + L * KH) * L) := ⟨_, rfl⟩
  have ke6' : WExec cap (mulAddW mBQ) σe5 σe6 (UnaryPow.sq cap) := by rw [hσe6]; exact ke6
  have ve6 : ∀ r : Fin NR, r ≠ rQ → r ≠ rB → σe6.val r = σd.val r := fun r h1 h2 => by
    rw [hσe6, WState.setv_val, Function.update_of_ne h1]; exact ve5 r h1 h2
  have ke7 := SparseNum.mulAdd1 cap mMQ (0 + (0 + L * KH) * L) L (PrimThrW.Shell2.mOfT KL P) σe6
    (show σe6.val rQ = 0 + (0 + L * KH) * L by rw [hσe6, WState.setv_val, Function.update_self])
    (show σe6.val rA = L by rw [ve6 _ (by decide) (by decide)]; exact vdA)
    (show σe6.val rM = PrimThrW.Shell2.mOfT KL P by rw [ve6 _ (by decide) (by decide)]; exact vdM)
    (show σe6.val rX = 0 by rw [ve6 _ (by decide) (by decide)]; exact dz rX (by decide) (by decide) (by decide) (by decide) (by decide))
    (show σe6.val rY = 0 by rw [ve6 _ (by decide) (by decide)]; exact dz rY (by decide) (by decide) (by decide) (by decide) (by decide))
    (by omega) (by omega) (by omega)
  obtain ⟨σe7, hσe7⟩ : ∃ y, y = σe6.setv rM (PrimThrW.Shell2.mOfT KL P + (0 + (0 + L * KH) * L) * L) := ⟨_, rfl⟩
  have ke7' : WExec cap (mulAddW mMQ) σe6 σe7 (UnaryPow.sq cap) := by rw [hσe7]; exact ke7
  have ve7 : ∀ r : Fin NR, r ≠ rQ → r ≠ rB → r ≠ rM → σe7.val r = σd.val r := fun r h1 h2 h3 => by
    rw [hσe7, WState.setv_val, Function.update_of_ne h3]; exact ve6 r h1 h2
  have ez : ∀ r : Fin NR, 20 ≤ r.val → r ≠ rM → r ≠ rA → r ≠ rQ → r ≠ rB → σe7.val r = 0 := by
    intro r h1 h2 h3 h4 h5
    rw [ve7 r h4 h5 h2]
    exact dz r h1 h2 h3 h4 h5
  have hmH : PrimThrW.Shell2.mOfT KL P + (0 + (0 + L * KH) * L) * L = mOfH KL KH P := mOfH_eq KL KH P
  have hmH' : mOfH KL KH P ≤ 2 * P.n + 2 + KL * (P.n + 2) * (P.n + 2) + KH * (P.n + 2) * (P.n + 2) * (P.n + 2) := by
    rw [← hmH]
    have : (0 + (0 + L * KH) * L) * L = L * KH * L * L := by ring
    omega
  -- 4: the source
  have hst : σe7.st = σ3.st := by rw [hσe7, hσe6, hσe5, hσe4, hσe3, hσe2, hσe1, hσd, hσc, hσb, hσa]; rfl
  have hsh : σe7.sh = σ3.sh := by rw [hσe7, hσe6, hσe5, hσe4, hσe3, hσe2, hσe1, hσd, hσc, hσb, hσa]; rfl
  have r4 := srcW_spec cap σe7 (mOfH KL KH P) (by rw [hσe7, WState.setv_val, Function.update_self]; exact hmH)
    (ez rK (by decide) (by decide) (by decide) (by decide) (by decide))
    (ez rT (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hst]; simp [hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN, xCT, xAUX])
    (by rw [hsh]; simp [hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN])
    (ez rOP (by decide) (by decide) (by decide) (by decide) (by decide)) (by omega)
  refine ⟨_, _, WExec.seq r1 (WExec.seq r2 (WExec.seq r3 (WExec.seq (WExec.seq ka (WExec.seq kb (WExec.seq kc' kd')))
    (WExec.seq (WExec.seq ke1 (WExec.seq ke2 (WExec.seq ke3 (WExec.seq ke4' (WExec.seq ke5 (WExec.seq ke6' ke7'))))))
    r4)))), ?_, ?_, ?_, ?_⟩
  · simp [hst, hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN, xCT, xAUX]
  · simp [hst, hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN, Function.update_apply]
  · simp [hst, hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN, xCT, Function.update_apply]
  · have hce : UnaryPow.sq cap = UnaryPow.sq (2 * W + 2) := rfl
    unfold numsCostH numsCostT numsCost
    have e1 : 18 * (P.s * (P.r / 2)) + 3 + 1 + (18 * (P.s * (P.r / 2)) + 3 + 1 + (18 * Nat.clog 2 (P.n + 2) + 3)) ≤
        18 * P.n + 18 * (P.n + 2) + 11 := by omega
    have e2 : 8 + 1 + (18 * mOfH KL KH P + 3 + 1 + (mOfH KL KH P * 12 + 1) + 1 + (8 + 1 +
        (18 * mOfH KL KH P + 3 + 1 + (mOfH KL KH P * 12 + 1) + 1 + 8))) ≤
        60 * (2 * P.n + 2) + 60 * (KL * (P.n + 2) * (P.n + 2)) + 60 * (KH * (P.n + 2) * (P.n + 2) * (P.n + 2)) + 38 := by
      omega
    omega

/-! ## The stage as one run -/

/-- The stage before its teardown: the fill, then the program. -/
noncomputable def numsPH (KL KH cr : ℕ) := Composition.machine fillX.compile (numsWH KL KH cr).toProg.compile

/-- **The HASH dimension stage** (every head back at `0`). -/
noncomputable def numsMH (KL KH cr : ℕ) := MaskedReset.machine (numsPH KL KH cr) (fun _ => true)

/-- The stage's cost before the teardown. -/
def numsStageCostH (n cr KL KH W : ℕ) : ℕ := 11 * W + 20 + 1 + 1 + 1 + numsCostH n cr KL KH W

/-- **The HASH dimension stage's run**: from `frame w` (`w = natWord n ++ sfx`) and `1^W`, every head back at `0`, the
output stream holds the CapReader source `srcWord (mOfH KL KH P)`; the request and the fill count stay. -/
theorem nums_stepH (KL KH cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 16 + KL * (P.n + 2) ^ 2 + KH * (P.n + 2) ^ 3 ≤ W) :
    ∃ (tout : Fin (NS + 2 + NR) → List Bool) (m : ℕ),
      Step (numsMH KL KH cr) (2 * numsStageCostH P.n cr KL KH W + 2) (fun _ => 0)
        (Fin.addCases (rawInX w W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => 0)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape xOUT) = srcWord (mOfH KL KH P) ∧ tout (sTape xIN) = RepairOrdinary.frame w ∧
      tout (sTape xCT) = List.replicate W true := by
  have s0 := Exec.step (fillX_exec w W)
  obtain ⟨σF, c, hx, o, i, ct, hc⟩ := numsWH_spec KL KH cr W P hrP sfx w hw hW
  have s1 := Exec.step (WExec.exec (2 * W + 2) hx)
  have core : Step (numsPH KL KH cr) (numsStageCostH P.n cr KL KH W) (fun _ => 0) (rawInX w W) (wenc (2 * W + 2) σF).H
      (wenc (2 * W + 2) σF).A := (s0.seq s1).enlarge (by unfold numsStageCostH; omega)
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (NS + 2 + NR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc (2 * W + 2) σF).H i)
      (fun _ : Fin 1 => 0) : Fin (NS + 2 + NR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  refine ⟨(wenc (2 * W + 2) σF).A, m, (hm.congr_in eh rfl).congr eh' rfl, ?_, ?_, ?_⟩
  · rw [wenc_A_s, o]
  · rw [wenc_A_s, i]
  · rw [wenc_A_s, ct]

end NearCubicWires.WireExponent3_5.PrimAsm.NumsXH
