import Proof.Wire_3_5.Primitive.Writers.ThrSide1

/-! # c4 THR block, piece 6 part 2: the THR majorant's numbers below `2^{cL}`, uniformly in `F`

P3:2121-2157 (filt:majorant: `M`, `A`, `B_*`, `J`, `t`, `ℓ₀`), P3:2551-2558 (the cutoff, the digits), P3:1189 (`4c_r ≤ k`,
so `2c_r + 2 ≤ n + 2`): at a THR call of the gate, with `L = ⌈log₂(n+2)⌉`, the fixed hash's numbers are
`J, t ≤ e_J·L`, `ℓ₀ ≤ (e_J + 28)·L`, the digit count `≤ (10X + 32)·L`, the occurrences `M ≤ 4(n+1)^{26}` and
`B_* ≤ 2^{28 + (48+Z)L}`; the constants depend on `l` only (`X = algX l`, `Z = capZR l`), not on `F` (the cap's
`capK(c_r) ≤ 2^{48L}` because `c_r ≤ n`). Hence the hash bits' count `2t·ℓ₀` is `O(L²)` uniformly.

* `eJ`; `capT_le2`, `den_le2`, `dig_le2`, `A_le2`, `Bs_le2`, **`thrCallJ_le`**, **`thrCallT_le`**, `occ_le`,
  **`ell0_le`**, **`hbC_le`**.

Paper quantities of the main types: the fixed hash's `J`, `t`, `ℓ₀` and its seed length `s_h = 2tℓ₀`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (cK pow_N_le one_le_L n2_le_L kh_two cr_le_k pow_mono_mul)

/-- The exponent of `J` and `t` (`X = algX l`, `Z = capZR l`). -/
noncomputable def eJ (l : Literals) : ℕ := 28 * CallIndex.algX l + 152 + CallIndexR.capZR l

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
  (hs : (callInputs l F kclk coef A a ha).StarAt n)
include hcall hs

/-- The THR cap below `2^{(48+Z)L}`, uniformly in `F`. -/
theorem capT_le2 : ((gate0 l F).budget kclk coef A a ha).capOf .thr n ≤
    2 ^ ((48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)) := by
  have hc := CallIndexR.cap_leR l F.cr .thr n
  have hcr := cr_le_k l F kclk coef A a ha hs
  have hkq : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n := hcall.2.2.2.2.2.2.kq
  have hn2 := n2_le_L n
  have hK1 : CallIndexR.capK F.cr ≤ 2 ^ (48 * Nat.clog 2 (n + 2)) := by
    show (2 * F.cr + 2) ^ 48 ≤ _
    exact pow_mono_mul 48 (by omega)
  have hZ := pow_N_le n (CallIndexR.capZR l)
  calc ((gate0 l F).budget kclk coef A a ha).capOf .thr n ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l := hc
    _ ≤ 2 ^ (48 * Nat.clog 2 (n + 2)) * 2 ^ (CallIndexR.capZR l * Nat.clog 2 (n + 2)) := Nat.mul_le_mul hK1 hZ
    _ = _ := by rw [← pow_add, ← Nat.add_mul]

/-- The THR denominator `8(|𝒢|+1)n` below `2^{4 + (4X+1)L}`. -/
theorem den_le2 : thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
    2 ^ (4 + (4 * CallIndex.algX l + 1) * Nat.clog 2 (n + 2)) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hq := CallIndex.thrEq_le l F kclk coef A a ha n hs ha' Cs hd
  have hN := pow_N_le n (CallIndex.algX l * 4)
  have hn2 := n2_le_L n
  have hD : (callInputs l F kclk coef A a ha).D = 1 := rfl
  rw [ThrQ.thrCallDen_eq, hD, pow_one]
  obtain ⟨G, hG⟩ : ∃ G, G = Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) :=
    ⟨_, rfl⟩
  rw [← hG] at hq ⊢
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hN hn2 ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = CallIndex.algX l := ⟨_, rfl⟩
  rw [← hX] at hq hN ⊢
  have h1 : G + 1 ≤ 2 * 2 ^ (X * 4 * L) := by
    have := Nat.one_le_two_pow (n := X * 4 * L)
    omega
  have h2 : n ≤ 2 ^ L := by omega
  calc 8 * (G + 1) * n ≤ 8 * (2 * 2 ^ (X * 4 * L)) * 2 ^ L :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    _ = 2 ^ (4 + (4 * X + 1) * L) := by
        rw [show 4 + (4 * X + 1) * L = 3 + 1 + X * 4 * L + L by ring, pow_add, pow_add, pow_add]; ring

/-- The digit count below `(10X + 32)L`. -/
theorem dig_le2 : thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤
    (10 * CallIndex.algX l + 32) * Nat.clog 2 (n + 2) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hc := CallIndex.cut_le l F kclk coef A a ha n hs ha' Cs hd
  have hN := pow_N_le n (10 * CallIndex.algX l + 32)
  exact Nat.clog_le_of_le_pow (hc.trans hN)

/-- `A = |𝒢|·|primes|·τ₀·2` below `2^{(24X+65)L + 2}`. -/
theorem A_le2 : thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
    2 ^ ((24 * CallIndex.algX l + 65) * Nat.clog 2 (n + 2) + 2) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hq := CallIndex.thrEq_le l F kclk coef A a ha n hs ha' Cs hd
  have hc := CallIndex.cut_le l F kclk coef A a ha n hs ha' Cs hd
  have hdig := dig_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hNq := pow_N_le n (CallIndex.algX l * 4)
  have hNc := pow_N_le n (10 * CallIndex.algX l + 32)
  have hA : thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs =
      Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) *
        ((SupplierPrime.primesUpTo (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))).card *
        (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * 2)) := by
    rw [← PrimThrW.Joins.thrNumVals_A (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers.length
      ((callInputs l F kclk coef A a ha).filterParams .thr n).cap]
    rfl
  rw [hA]
  have hpr := RepairOrdinary.CloseoutFinalC10WireEnvelope.primesUpTo_card_le
    (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hNq hNc hdig ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = CallIndex.algX l := ⟨_, rfl⟩
  rw [← hX] at hq hc hNq hNc hdig ⊢
  have g1 : Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) ≤
      2 ^ (X * 4 * L) := hq.trans hNq
  have g2 : (SupplierPrime.primesUpTo (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))).card ≤ 2 ^ ((10 * X + 32) * L + 1) := by
    have := Nat.one_le_two_pow (n := (10 * X + 32) * L)
    rw [pow_succ]; omega
  have g3 : thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * 2 ≤ 2 ^ ((10 * X + 32) * L + 1) := by
    have := (Nat.lt_two_pow_self (n := (10 * X + 32) * L)).le
    rw [pow_succ]; omega
  calc _ ≤ 2 ^ (X * 4 * L) * (2 ^ ((10 * X + 32) * L + 1) * 2 ^ ((10 * X + 32) * L + 1)) :=
        Nat.mul_le_mul g1 (Nat.mul_le_mul g2 g3)
    _ = 2 ^ ((24 * X + 64) * L + 2) := by rw [← pow_add, ← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- `B_* = a·4096·(|carriers|+1)·4096·cap_T` below `2^{28 + (48+Z)L}`. -/
theorem Bs_le2 : thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a') ≤
    2 ^ (28 + (48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)) := by
  have hcT := capT_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  unfold thrCallBs
  rw [pow_add]
  have h1 : a' * (4096 * ((carriers.length + 1) * (4096 * ((gate0 l F).budget kclk coef A a ha).capOf .thr n))) ≤
      4 * (4096 * (3 * (4096 * ((gate0 l F).budget kclk coef A a ha).capOf .thr n))) :=
    Nat.mul_le_mul ha' (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
  have h2 : 4 * (4096 * (3 * (4096 * ((gate0 l F).budget kclk coef A a ha).capOf .thr n))) =
      201326592 * ((gate0 l F).budget kclk coef A a ha).capOf .thr n := by omega
  have h3 : (201326592 : ℕ) ≤ 2 ^ 28 := by norm_num
  calc _ ≤ 201326592 * ((gate0 l F).budget kclk coef A a ha).capOf .thr n := h1.trans (le_of_eq h2)
    _ ≤ 2 ^ 28 * 2 ^ ((48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)) := Nat.mul_le_mul h3 hcT

/-- **`J ≤ e_J·L`**, uniformly in `F`. -/
theorem thrCallJ_le : thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers ≤
    eJ l * Nat.clog 2 (n + 2) := by
  have hK := den_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hA := A_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hB := Bs_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 := one_le_L n
  show Nat.clog 2 (8 * thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs *
    thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs *
    thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a') + 1) ≤ _
  apply Nat.clog_le_of_le_pow
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hK hA hB hL1 ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = CallIndex.algX l := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = CallIndexR.capZR l := ⟨_, rfl⟩
  rw [← hX] at hK hA
  rw [← hZ] at hB
  have hP := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hK) hA) hB
  have e1 : 8 * 2 ^ (4 + (4 * X + 1) * L) * 2 ^ ((24 * X + 65) * L + 2) * 2 ^ (28 + (48 + Z) * L) =
      2 ^ (37 + (28 * X + 114 + Z) * L) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [e1] at hP
  have h2 : 2 ^ (37 + (28 * X + 114 + Z) * L) + 1 ≤ 2 ^ (eJ l * L) := by
    have e2 : eJ l * L = (37 + (28 * X + 114 + Z) * L) + (1 + (L - 1) * 38) := by
      unfold eJ; rw [← hX, ← hZ]
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    rw [e2, pow_add 2 (37 + (28 * X + 114 + Z) * L)]
    have h3 : 2 ≤ 2 ^ (1 + (L - 1) * 38) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 := Nat.one_le_two_pow (n := 37 + (28 * X + 114 + Z) * L)
    nlinarith
  omega

/-- **`t ≤ (2e_J + 1)·L`**, uniformly in `F`. -/
theorem thrCallT_le : thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers ≤
    (2 * eJ l + 1) * Nat.clog 2 (n + 2) := by
  have hK := den_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hA := A_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hJ := thrCallJ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 := one_le_L n
  show Nat.clog 2 (8 * thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs *
    thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs *
    thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers + 1) + 1 ≤ _
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hK hA hJ hL1 ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = CallIndex.algX l := ⟨_, rfl⟩
  rw [← hX] at hK hA
  have hJ2 : thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers ≤ 2 ^ (eJ l * L) :=
    hJ.trans (Nat.lt_two_pow_self).le
  have hP := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hK) hA) hJ2
  have e1 : 8 * 2 ^ (4 + (4 * X + 1) * L) * 2 ^ ((24 * X + 65) * L + 2) * 2 ^ (eJ l * L) =
      2 ^ (9 + (28 * X + 66) * L + eJ l * L) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [e1] at hP
  have hle : 28 * X + 66 + 10 ≤ eJ l := by unfold eJ; rw [← hX]; omega
  have h2 : 2 ^ (9 + (28 * X + 66) * L + eJ l * L) + 1 ≤ 2 ^ (2 * eJ l * L) := by
    have e2 : 2 * eJ l * L = (9 + (28 * X + 66) * L + eJ l * L) + ((eJ l - (28 * X + 66)) * L - 9) := by
      have h5 : 10 * L ≤ (eJ l - (28 * X + 66)) * L := Nat.mul_le_mul_right _ (by omega)
      have e3 : (eJ l - (28 * X + 66)) * L + (28 * X + 66) * L = eJ l * L := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      have e4 : 2 * eJ l * L = eJ l * L + eJ l * L := by ring
      omega
    rw [e2, pow_add 2 (9 + (28 * X + 66) * L + eJ l * L)]
    have h3 : 2 ≤ 2 ^ ((eJ l - (28 * X + 66)) * L - 9) := by
      have h5 : 10 * L ≤ (eJ l - (28 * X + 66)) * L := Nat.mul_le_mul_right _ (by omega)
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 := Nat.one_le_two_pow (n := 9 + (28 * X + 66) * L + eJ l * L)
    nlinarith
  have hc := Nat.clog_le_of_le_pow (show 8 * thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs *
    thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs *
    thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers + 1 ≤ 2 ^ (2 * eJ l * L) by omega)
  have e5 : (2 * eJ l + 1) * L = 2 * eJ l * L + L := by ring
  omega

/-- The occurrences: `M ≤ 4(n+1)^{26}`. -/
theorem occ_le : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length ≤ 4 * (n + 1) ^ 26 := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have h := PrimT.C4GateSym.tupleG_len_le Cs _ hd
  have e : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length = (PrimT.ThrTab.tupleG Cs).length := by
    rw [← List.length_map (f := fun o => o.gate), PrimT.ThrTab.thrOccs_gates]; rfl
  rw [e]
  exact h.trans (Nat.mul_le_mul_right _ ha')

/-- **`ℓ₀ ≤ (e_J + 28)·L`**: the fixed hash's field dimension. -/
theorem ell0_le : (thrMajorant ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
    ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)).ell0 ≤
    (eJ l + 28) * Nat.clog 2 (n + 2) := by
  have hJ := thrCallJ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hM := occ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 := one_le_L n
  have hN := pow_N_le n 26
  have hM2 : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length ≤
      2 ^ (26 * Nat.clog 2 (n + 2) + 2) := by
    have h26 : (n + 1) ^ 26 ≤ (n + 2) ^ 26 := Nat.pow_le_pow_left (by omega) 26
    rw [pow_add]; omega
  have hcM := Nat.clog_le_of_le_pow hM2
  show max (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers + 1)
    (Nat.clog 2 (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length) ≤ _
  have e : (eJ l + 28) * Nat.clog 2 (n + 2) = eJ l * Nat.clog 2 (n + 2) + 28 * Nat.clog 2 (n + 2) := by ring
  rw [e]
  exact max_le (by omega) (by omega)

/-- The hash bits' constant: `|frame hb| ≤ c_H·L²`. -/
noncomputable def cH (l : Literals) : ℕ := 4 * ((2 * eJ l + 1) * (eJ l + 28)) + 1

/-- **The framed hash bits are `O(L²)`**, uniformly in `F`. -/
theorem hbC_le : (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length ≤
    cH l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := by
  have hT := thrCallT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have h0 := ell0_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 := one_le_L n
  unfold ThrCap.hbC
  rw [SymDec.frame_length, List.length_ofFn]
  show 2 * (2 * thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers *
    (thrMajorant ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
    ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)).ell0) + 1 ≤ _
  have hp := Nat.mul_le_mul hT h0
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hp hL1 ⊢
  have e : (2 * eJ l + 1) * L * ((eJ l + 28) * L) = (2 * eJ l + 1) * (eJ l + 28) * (L * L) := by ring
  rw [e] at hp
  have hLL : 1 ≤ L * L := Nat.mul_pos hL1 hL1
  have e2 : cH l * (L * L) = 4 * ((2 * eJ l + 1) * (eJ l + 28) * (L * L)) + L * L := by unfold cH; ring
  rw [e2]
  have e3 : 2 * (2 * thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers *
      (thrMajorant ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)).ell0) =
      4 * (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers *
      (thrMajorant ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)).ell0) := by ring
  rw [e3]
  omega

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
