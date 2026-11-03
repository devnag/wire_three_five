import Proof.MachineModel.RuntimeShape
import Proof.MachineModel.P1ClosureCompactCost
import Proof.SourceAssembly.SourceBundle

/-! # R1 class lemmas: which class each producer budget summand lives in

Paper: `paper.tex:1111-1112` (preprocessing "added to, and never multiplied by, the `2^{q-K}`
enumeration"), `:1205-1207` (external rows multiply both one-row charges by `q^{h_D}` once);
plan.md §12.1 "three cost classes". Consumer: the `bound` field of `RuntimeShape.Split`.
Charged to: `rowBudget` (`Proof/Assembly/RowProduction.lean`) and `packetBudget`
(`Proof/Assembly/Production.lean`). Every admission fact is an explicit, named
hypothesis (`h_*`); those are the open T1 obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RuntimeShape
open SupplierEstimator
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation
open SourceInterfaces P1Closure CloseoutRowsEstimator
open RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ1fef9807c6954e94_Native
open ExtDecompositionBatch

/-! ## 1. The classes and their closure laws -/

/-- Table class: `(q+1)^h * 2^(q-K)` with `K = normalizedLiveCount q L` (= `2^residual`). -/
abbrev tableClass (L h q : ℕ) : ℕ := (q+1)^h*2^(q-normalizedLiveCount q L)
/-- Small (additive preprocessing) class: `(q+1)^h * 2^(q/m)`. -/
abbrev smallClass (m h q : ℕ) : ℕ := (q+1)^h*2^(q/m)

theorem residual_eq (a : DecompositionAlgorithm) (r : Request) :
    Packets.residual (r.family a) = r.q-normalizedLiveCount r.q r.liveScale := rfl

theorem tableClass_mono {L h h' q : ℕ} (hh : h ≤ h') : tableClass L h q ≤ tableClass L h' q :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos q) hh)

theorem smallClass_mono {m h h' q : ℕ} (hh : h ≤ h') : smallClass m h q ≤ smallClass m h' q :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos q) hh)

theorem one_le_smallClass (m h q : ℕ) : 1 ≤ smallClass m h q :=
  Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity))

/-! ## 2. Entry into the small class -/

/-! ## 3. The row budget -/

theorem input_poly (q n inputC inputE : ℕ) (h : n ≤ inputC*(q+1)^inputE) :
    q+n+1 ≤ (inputC+2)*(q+1)^(inputE+1) := by
  have hbase : q+1 ≤ (q+1)^(inputE+1) := Nat.le_self_pow (by omega) _
  have hpow : (q+1)^inputE ≤ (q+1)^(inputE+1) := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith [Nat.mul_le_mul_left inputC hpow]

/-- **`rowBudget` by class.** The residual-table summand is table class with exponent
`(inputE+1)*d` (row degree `d` fixed before `L`); `copyCap` (`= 2*Driver.value+1` in §12.1)
carries its own table part; `smallSize^d`, `headerFuel`, `C` and the constant are small. -/
theorem rowBudget_classes (a : DecompositionAlgorithm) (c d : ℕ) (r : Request) (C : ℕ)
    (caps : RowCaps) (m inputC inputE smallC smallE headerC headerE capC capE
      copyTC copyTE copySC copySE : ℕ)
    (h_input : (r.input a).length ≤ inputC*(r.q+1)^inputE)
    (h_small : (r.smallSize a)^d ≤ smallC*smallClass m smallE r.q)
    (h_header : caps.headerFuel ≤ headerC*smallClass m headerE r.q)
    (h_cap : C ≤ capC*smallClass m capE r.q)
    (h_copy : caps.copyCap ≤
      copyTC*tableClass r.liveScale copyTE r.q+copySC*smallClass m copySE r.q) :
    rowBudget a c d r C caps ≤
      (c*((inputC+2)^d+copyTC))*tableClass r.liveScale ((inputE+1)*d+copyTE) r.q+
      (c*(smallC+headerC+capC+copySC+1))*smallClass m (smallE+headerE+capE+copySE) r.q := by
  set T := tableClass r.liveScale ((inputE+1)*d+copyTE) r.q with hT
  set S := smallClass m (smallE+headerE+capE+copySE) r.q with hS
  have hrow : 2^(Packets.residual (r.family a))*(r.q+(r.input a).length+1)^d ≤
      (inputC+2)^d*T := by
    rw [residual_eq]
    have hin := Nat.pow_le_pow_left (input_poly r.q _ inputC inputE h_input) d
    rw [mul_pow, ← pow_mul] at hin
    calc 2^(r.q-normalizedLiveCount r.q r.liveScale)*(r.q+(r.input a).length+1)^d
        ≤ 2^(r.q-normalizedLiveCount r.q r.liveScale)*
            ((inputC+2)^d*(r.q+1)^((inputE+1)*d)) := Nat.mul_le_mul_left _ hin
      _ = (inputC+2)^d*tableClass r.liveScale ((inputE+1)*d) r.q := by
          simp only [tableClass]; ring
      _ ≤ (inputC+2)^d*T :=
          Nat.mul_le_mul_left _ (tableClass_mono (Nat.le_add_right _ _))
  have s1 := Nat.mul_le_mul_left smallC (smallClass_mono (m := m) (q := r.q)
    (show smallE ≤ smallE+headerE+capE+copySE by omega))
  have s2 := Nat.mul_le_mul_left headerC (smallClass_mono (m := m) (q := r.q)
    (show headerE ≤ smallE+headerE+capE+copySE by omega))
  have s3 := Nat.mul_le_mul_left capC (smallClass_mono (m := m) (q := r.q)
    (show capE ≤ smallE+headerE+capE+copySE by omega))
  have s4 := Nat.mul_le_mul_left copySC (smallClass_mono (m := m) (q := r.q)
    (show copySE ≤ smallE+headerE+capE+copySE by omega))
  have t4 := Nat.mul_le_mul_left copyTC (tableClass_mono (L := r.liveScale) (q := r.q)
    (show copyTE ≤ (inputE+1)*d+copyTE by omega))
  have hone := one_le_smallClass m (smallE+headerE+capE+copySE) r.q
  rw [← hS] at s1 s2 s3 s4 hone
  rw [← hT] at t4
  have inner : (r.smallSize a)^d+caps.headerFuel+C+caps.copyCap+
      2^(Packets.residual (r.family a))*(r.q+(r.input a).length+1)^d+1 ≤
      ((inputC+2)^d+copyTC)*T+(smallC+headerC+capC+copySC+1)*S := by
    have e1 : ((inputC+2)^d+copyTC)*T = (inputC+2)^d*T+copyTC*T := Nat.add_mul _ _ _
    have e2 : (smallC+headerC+capC+copySC+1)*S = smallC*S+headerC*S+capC*S+copySC*S+S := by
      ring
    omega
  unfold rowBudget
  calc c*((r.smallSize a)^d+caps.headerFuel+C+caps.copyCap+
        2^(Packets.residual (r.family a))*(r.q+(r.input a).length+1)^d+1)
      ≤ c*(((inputC+2)^d+copyTC)*T+(smallC+headerC+capC+copySC+1)*S) :=
        Nat.mul_le_mul_left c inner
    _ = (c*((inputC+2)^d+copyTC))*T+(c*(smallC+headerC+capC+copySC+1))*S := by ring

/-! ## 4. The packet budget -/

/-- **`packetBudget` is small class.** It is never multiplied by `2^residual`; it needs the
row count polynomial and `smallSize^d` in the small envelope. -/
theorem packetBudget_classes (a : DecompositionAlgorithm) (c d : ℕ) (r : Request)
    (m rowsC rowsE smallC smallE : ℕ)
    (h_rows : (r.family a).rows.length+1 ≤ rowsC*(r.q+1)^rowsE)
    (h_small : (r.smallSize a)^d ≤ smallC*smallClass m smallE r.q) :
    packetBudget a c d r ≤ (c*rowsC*smallC)*smallClass m (rowsE+smallE) r.q := by
  unfold packetBudget
  calc c*((r.family a).rows.length+1)*(r.smallSize a)^d
      ≤ c*(rowsC*(r.q+1)^rowsE)*(smallC*smallClass m smallE r.q) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c h_rows) h_small
    _ = (c*rowsC*smallC)*smallClass m (rowsE+smallE) r.q := by
        simp only [smallClass, pow_add]; ring

/-! ## 5. The complete table term, from the existing `SourceTableFactor` -/


end NearCubicWires.RuntimeShape
