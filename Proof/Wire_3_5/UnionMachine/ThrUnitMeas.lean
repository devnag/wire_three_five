import Proof.Wire_3_5.FinalPass.ThrSz3
import Proof.Wire_3_5.Primitive.Writers.ThrBud2
import Proof.Wire_3_5.UnionMachine.ThrUnitIface5
import Proof.Wire_3_5.UnionMachine.ThrUnitRun

/-! # The THR unit's measure absorbed by the THR load `Ψ_T` (THRU4's `meas_le`), part 1: the RADIX measure

At a THR call, with `L = ⌈log₂(n+2)⌉` and `Y = L²`, every number of the RADIX row's measure `radMeas5` (P3:2585-2623)
is `2^{O(L²)}` uniformly in the gate (PA's THR side bounds: `occ_le`, `thrPool_le`, `dig_le2`, `thrCallJ_le`,
`thrCallT_le`, `Bs_le2`, `hbC_le`; `thr_ell_le`'s `k_h ≤ bsq n`; `ThrSz.levelWord_le`, `majW_le`, `payOf_le`;
`CallSize.wordBound_poly`), except the digit lists' counting capacity `(8G+2)^{3·lb+1}`, `lb = listBound(thrCallD)`,
which is `2^{(3·lb+1)(26L+7)}`:

* the atoms: `lw_le` (the table word), `word_le` (the request and the hash bits), `pw_le` (`(M+1)^{2τ₀}`),
  `digsN_le` (the digit program's measure), `mlab_le`, `row_le`;
* **`radMeas5_le`**: `radMeas5 … pr row ≤ 2^{(3·lb+1)(26L+7) + K_R·L² + 8}` at every prime and star row;
* `KR l` (the constant, from `l` only).

Paper quantity: the RADIX row's explicit capacity, within `2^{O(Ψ_T)}` (P3:3094-3108) once `lb·L ≤ c·Ψ_T`
(`ThrUnit.lb_absorbT`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (pow_N_le one_le_L n2_le_L pow_mono_mul)

/-! ## Arithmetic -/

theorem nbl_le_L (n : ℕ) : natBitLength n ≤ Nat.clog 2 (n + 2) := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.log_zero_right, zero_add]; exact one_le_L 0
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) (show n < 2 ^ Nat.clog 2 (n + 2) from
      lt_of_lt_of_le (by omega) (n2_le_L n))
    omega

theorem le_two_pow_self (x : ℕ) : x ≤ 2 ^ x := (Nat.lt_two_pow_self).le

theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem mul_le_two_pow (c x : ℕ) : c * x ≤ 2 ^ (c * x) := le_two_pow_self _

/-- The word bound's polynomial constants. -/
noncomputable def cW : ℕ := Classical.choose CallSize.wordBound_poly
noncomputable def dW : ℕ := Classical.choose (Classical.choose_spec CallSize.wordBound_poly)

theorem wordBound_le (n : ℕ) : CallSize.wordBound 26 26 2 n ≤ cW * (n + 1) ^ dW :=
  (Classical.choose_spec (Classical.choose_spec CallSize.wordBound_poly)).2 n

/-- **The RADIX measure's constant** (from `l` only). -/
noncomputable def KR (l : Literals) : ℕ :=
  200 * (10 * CallIndex.algX l + 32) + 64 * (48 + CallIndexR.capZR l) + 64 * ThrSide.eJ l + ThrSide.cH l + dW +
    Nat.clog 2 cW + 64 * CallIndex.algX l + 1000

/-- The row: at most `N² ≤ 2^{8L²}`. -/
theorem sq_le (kh L : ℕ) (hkh : kh ≤ (L + 1) ^ 2) (hL : 1 ≤ L) : (2 ^ kh) ^ 2 ≤ 2 ^ (8 * (L * L)) := by
  rw [← pow_mul]
  apply two_pow_mono
  have e : (L + 1) ^ 2 = L * L + 2 * L + 1 := by ring
  have : L ≤ L * L := Nat.le_mul_of_pos_left L hL
  omega

/-- **The digit lists' counting capacity and the numbers**: `radX` below `2^{(3lb+1)(26L+7) + E + 4}`. -/
theorem radX_le (M τ G Mlab lb lw p L E : ℕ) (hG8 : 8 * G + 2 ≤ 2 ^ (26 * L + 7)) (hM : M ≤ 2 ^ E) (hτ : τ ≤ 2 ^ E)
    (hG : G ≤ 2 ^ E) (hMl : Mlab ≤ 2 ^ E) (hlw : lw ≤ 2 ^ E) (hp : p ≤ 2 ^ E) :
    RadSpec.radX M τ G Mlab lb lw p 2 ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7) + E + 4) := by
  unfold RadSpec.radX
  have h1 := pow_mono_mul (3 * lb + 1) hG8
  have h2 : lb ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7)) := by
    have := le_two_pow_self lb
    exact this.trans (two_pow_mono (by nlinarith))
  have a1 : 2 ^ ((3 * lb + 1) * (26 * L + 7)) ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7) + E) := two_pow_mono (by omega)
  have a2 : 2 ^ E ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7) + E) := two_pow_mono (by omega)
  have a3 : 2 ^ ((3 * lb + 1) * (26 * L + 7) + E + 4) = 16 * 2 ^ ((3 * lb + 1) * (26 * L + 7) + E) := by
    rw [pow_add]; ring
  have a4 : 1 ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7) + E) := Nat.one_le_two_pow
  omega

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
  (hs : (callInputs l F kclk coef A a ha).StarAt n)
include hcall hs

theorem pool_le : (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 2 ^ (26 * Nat.clog 2 (n + 2) + 3) := by
  have hG := ThrSide.thrPool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have h26 : (n + 1) ^ 26 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) :=
    (Nat.pow_le_pow_left (by omega) 26).trans (pow_N_le n 26)
  rw [pow_add]; omega

theorem occ_le' : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length ≤ 2 ^ (26 * Nat.clog 2 (n + 2) + 2) := by
  have hM := ThrSide.occ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have h26 : (n + 1) ^ 26 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) :=
    (Nat.pow_le_pow_left (by omega) 26).trans (pow_N_le n 26)
  rw [pow_add]; omega

theorem row_le : ThrDec.thrN2 l F kclk coef A a ha hs ≤ 2 ^ (8 * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := by
  have hkh := (ThrBud.thr_ell_le l F kclk coef A a ha ha' Cs carriers translation hcall hs).2.2.2
  have hbsq : PrimT.C4Cap.bsq n ≤ (Nat.clog 2 (n + 2) + 1) ^ 2 := by
    show (natBitLength n + 1) ^ 2 ≤ _
    exact Nat.pow_le_pow_left (by have := nbl_le_L n; omega) 2
  exact sq_le _ _ (hkh.trans hbsq) (one_le_L n)

/-- The digit count, below `2^{(10X+32)L}`. -/
theorem dig_le' : (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) ≤ 2 ^ ((10 * CallIndex.algX l + 32) * Nat.clog 2 (n + 2)) :=
  (ThrSide.dig_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs).trans (le_two_pow_self _)

/-- **The table word at the pool** (`levelWord` at `G = |thrPool|`). -/
theorem lw_le :
    (FinalPass.ListEval.levelWord (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W (FinalPass.ListEval.rowsOf (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length)).length ≤
      2 ^ (KR l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 3) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLd ▸ one_le_L n
  have hLY : L ≤ L * L := Nat.le_mul_of_pos_left L hL1
  have hJ := ThrSide.thrCallJ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hT := ThrSide.thrCallT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hB := ThrSide.Bs_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hG := pool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hM := occ_le' l F kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [← hLd] at hJ hT hB hG hM ⊢
  obtain ⟨T, hTd⟩ : ∃ T, T = thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a') := ⟨_, rfl⟩
  have hW : ∀ j, (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W j ≤ 16 * T + 20 * (T * B + 2) := fun j => by
    rw [hTd, hBd]; exact FinalPass.ThrSz.majW_le _ j
  have hR : ∀ j, (FinalPass.ListEval.rowsOf (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length j).length ≤ (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := fun j => by
    rw [RadDig.rowsOf_len]
  have h := FinalPass.ThrSz.levelWord_le (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W (FinalPass.ListEval.rowsOf (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length) _ _ hW hR
  rw [← hTd] at hT
  rw [← hBd] at hB
  -- the exponents, as multiples of `L²`
  obtain ⟨eJ, heJ⟩ : ∃ e, e = ThrSide.eJ l := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ z, z = CallIndexR.capZR l := ⟨_, rfl⟩
  rw [← heJ] at hJ hT
  rw [← hZ] at hB
  have hK : 64 * eJ + 64 * (48 + Z) + 1000 ≤ KR l := by rw [heJ, hZ]; unfold KR; omega
  have hTp : T ≤ 2 ^ ((2 * eJ + 1) * L) := hT.trans (le_two_pow_self _)
  have hJp : (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J + 1 ≤ 2 ^ (eJ * L + 1) := by
    have h1 := le_two_pow_self (eJ * L)
    have h0 : 1 ≤ 2 ^ (eJ * L) := Nat.one_le_two_pow
    have : (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J = thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers := rfl
    rw [pow_add]; omega
  have hTB : T * B ≤ 2 ^ ((2 * eJ + 1) * L + (28 + (48 + Z) * L)) := by
    rw [pow_add]; exact Nat.mul_le_mul hTp hB
  obtain ⟨e1, he1⟩ : ∃ e, e = (2 * eJ + 1) * L + (28 + (48 + Z) * L) := ⟨_, rfl⟩
  rw [← he1] at hTB
  have hTe : 2 ^ ((2 * eJ + 1) * L) ≤ 2 ^ e1 := two_pow_mono (by rw [he1]; omega)
  have hWm : 16 * T + 20 * (T * B + 2) ≤ 2 ^ (e1 + 6) := by
    have : 2 ^ (e1 + 6) = 64 * 2 ^ e1 := by rw [pow_add]; ring
    have : 2 ^ 1 ≤ 2 ^ e1 := two_pow_mono (by rw [he1]; omega)
    have : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hGe : 2 ^ (26 * L + 3) ≤ 2 ^ (e1 + 26 * L + 3) := two_pow_mono (by omega)
  have hIn : 5 * (16 * T + 20 * (T * B + 2)) + 5 + (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 2 ^ (e1 + 26 * L + 10) := by
    have h6 : 2 ^ (e1 + 6) ≤ 2 ^ (e1 + 26 * L + 6) := two_pow_mono (by omega)
    have : 2 ^ (e1 + 26 * L + 10) = 16 * 2 ^ (e1 + 26 * L + 6) := by rw [show e1 + 26 * L + 10 = e1 + 26 * L + 6 + 4 by ring, pow_add]; ring
    have : 2 ^ (e1 + 26 * L + 6) = 8 * 2 ^ (e1 + 26 * L + 3) := by rw [show e1 + 26 * L + 6 = e1 + 26 * L + 3 + 3 by ring, pow_add]; ring
    have : 1 ≤ 2 ^ (e1 + 26 * L + 3) := Nat.one_le_two_pow
    omega
  have hProd : ((Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J + 1) * (5 * (16 * T + 20 * (T * B + 2)) + 5 + (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length) ≤ 2 ^ (eJ * L + 1 + (e1 + 26 * L + 10)) := by
    rw [pow_add]; exact Nat.mul_le_mul hJp hIn
  obtain ⟨e2, he2⟩ : ∃ e, e = eJ * L + 1 + (e1 + 26 * L + 10) := ⟨_, rfl⟩
  rw [← he2] at hProd
  have hDM : (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M = (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length := rfl
  have hMe : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length + 2 ≤ 2 ^ e2 := by
    have : 2 ^ (26 * L + 2) + 2 ≤ 2 ^ (26 * L + 3) := by
      have e : 2 ^ (26 * L + 3) = 2 * 2 ^ (26 * L + 2) := by ring
      have : 2 ≤ 2 ^ (26 * L + 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (26 * L + 2) := two_pow_mono (by omega)
      omega
    exact (by omega : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length + 2 ≤ 2 ^ (26 * L + 3)).trans (two_pow_mono (by rw [he2]; omega))
  -- `e₂ + 1 ≤ K_R·L² + 3`
  have hmulL : eJ * L ≤ eJ * (L * L) := Nat.mul_le_mul_left _ hLY
  have hmulL2 : (2 * eJ + 1) * L ≤ (2 * eJ + 1) * (L * L) := Nat.mul_le_mul_left _ hLY
  have hmulL3 : (48 + Z) * L ≤ (48 + Z) * (L * L) := Nat.mul_le_mul_left _ hLY
  have hKY : (64 * eJ + 64 * (48 + Z) + 1000) * (L * L) ≤ KR l * (L * L) := Nat.mul_le_mul_right _ hK
  have eK : (64 * eJ + 64 * (48 + Z) + 1000) * (L * L) =
      64 * (eJ * (L * L)) + 64 * ((48 + Z) * (L * L)) + 1000 * (L * L) := by ring
  have e2' : (2 * eJ + 1) * (L * L) = 2 * (eJ * (L * L)) + L * L := by ring
  have hE : e2 + 1 ≤ KR l * (L * L) + 3 := by rw [he2, he1]; omega
  have hfin : 2 ^ e2 + 2 ^ e2 ≤ 2 ^ (KR l * (L * L) + 3) := by
    have : 2 ^ e2 + 2 ^ e2 = 2 ^ (e2 + 1) := by rw [pow_add]; ring
    rw [this]; exact two_pow_mono hE
  omega

/-- **The request word and the framed hash bits.** -/
theorem word_le :
    ((thrReq n a' ha' Cs carriers translation).word ++ ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs
      carriers translation hs).length ≤ 2 ^ (KR l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 3) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLd ▸ one_le_L n
  have hLY : L ≤ L * L := Nat.le_mul_of_pos_left L hL1
  have hw := (CallSize.gate_word_length_le l F kclk coef A a ha _ hcall).trans (wordBound_le n)
  have hH := ThrSide.hbC_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [← hLd] at hH ⊢
  have hn : (n + 1) ^ dW ≤ 2 ^ (dW * L) := by
    have := pow_N_le n dW; rw [← hLd] at this
    exact (Nat.pow_le_pow_left (by omega) dW).trans this
  have hc : cW ≤ 2 ^ Nat.clog 2 cW := Nat.le_pow_clog (by norm_num) _
  have h1 : cW * (n + 1) ^ dW ≤ 2 ^ (Nat.clog 2 cW + dW * L) := by rw [pow_add]; exact Nat.mul_le_mul hc hn
  have h2 : ThrSide.cH l * (L * L) ≤ 2 ^ (ThrSide.cH l * (L * L)) := mul_le_two_pow _ _
  have hK : Nat.clog 2 cW + dW + ThrSide.cH l ≤ KR l := by unfold KR; omega
  have hKY : (Nat.clog 2 cW + dW + ThrSide.cH l) * (L * L) ≤ KR l * (L * L) := Nat.mul_le_mul_right _ hK
  have e : (Nat.clog 2 cW + dW + ThrSide.cH l) * (L * L) =
      Nat.clog 2 cW * (L * L) + dW * (L * L) + ThrSide.cH l * (L * L) := by ring
  have m1 : dW * L ≤ dW * (L * L) := Nat.mul_le_mul_left _ hLY
  have m2 : Nat.clog 2 cW ≤ Nat.clog 2 cW * (L * L) := Nat.le_mul_of_pos_right _ (by positivity)
  have p1 : 2 ^ (Nat.clog 2 cW + dW * L) ≤ 2 ^ (KR l * (L * L)) := two_pow_mono (by omega)
  have p2 : 2 ^ (ThrSide.cH l * (L * L)) ≤ 2 ^ (KR l * (L * L)) := two_pow_mono (by omega)
  have p3 : 2 ^ (KR l * (L * L) + 3) = 8 * 2 ^ (KR l * (L * L)) := by rw [pow_add]; ring
  rw [List.length_append]
  omega

/-- **The digit tuples' count** `(M+1)^{2τ₀}`. -/
theorem pw_le : ((thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length + 1) ^ (2 * (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤ 2 ^ (KR l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 3) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLd ▸ one_le_L n
  have hM := occ_le' l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hτ := ThrSide.dig_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [← hLd] at hM hτ ⊢
  have hM1 : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length + 1 ≤ 2 ^ (29 * L) := by
    have : 2 ^ (26 * L + 3) ≤ 2 ^ (29 * L) := two_pow_mono (by omega)
    have : 2 ^ (26 * L + 2) + 1 ≤ 2 ^ (26 * L + 3) := by
      have e : 2 ^ (26 * L + 3) = 2 * 2 ^ (26 * L + 2) := by ring
      have : 1 ≤ 2 ^ (26 * L + 2) := Nat.one_le_two_pow
      omega
    omega
  have h1 := pow_mono_mul (2 * (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) hM1
  refine h1.trans (two_pow_mono ?_)
  obtain ⟨X, hX⟩ : ∃ x, x = CallIndex.algX l := ⟨_, rfl⟩
  rw [← hX] at hτ
  have hK : 58 * (10 * X + 32) ≤ KR l := by rw [hX]; unfold KR; omega
  have hKY : 58 * (10 * X + 32) * (L * L) ≤ KR l * (L * L) := Nat.mul_le_mul_right _ hK
  have m : 2 * (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) * (29 * L) ≤ 2 * ((10 * X + 32) * L) * (29 * L) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hτ)
  have e : 2 * ((10 * X + 32) * L) * (29 * L) = 58 * (10 * X + 32) * (L * L) := by ring
  omega

/-- **The digit program's measure** `Σ|payOf| + p + τ₀ + thrOff`. -/
theorem digsN_le (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) :
    FinalPass.Digs.digsN ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) pr.val ≤ 2 ^ (KR l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 3) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLd ▸ one_le_L n
  have hLY : L ≤ L * L := Nat.le_mul_of_pos_left L hL1
  have hG := pool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hτ := dig_le' l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hpr : pr.val ≤ 2 ^ (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) := Primitive.prime_le_two_pow _ _ _ _ pr
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  rw [← hLd] at hG hτ ⊢
  obtain ⟨X, hX⟩ : ∃ x, x = CallIndex.algX l := ⟨_, rfl⟩
  rw [← hX] at hτ
  have hpr' : pr.val ≤ 2 ^ ((10 * X + 32) * L) := hpr.trans (two_pow_mono (by
    have := ThrSide.dig_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
    rw [← hLd, ← hX] at this; exact this))
  have h26 : (n + 1) ^ 26 ≤ 2 ^ (26 * L) := by
    have := pow_N_le n 26; rw [← hLd] at this
    exact (Nat.pow_le_pow_left (by omega) 26).trans this
  have hX2 : (n + 2) ^ X ≤ 2 ^ (X * L) := by have := pow_N_le n X; rw [← hLd] at this; exact this
  have hpay : ∀ i : Fin a', (PrimThrW.TopFront.payOf (gate0 l F).alg (Cs i)).length ≤ 2 ^ ((26 + X) * L + 5) := by
    intro i
    have h1 := FinalPass.ThrSz.payOf_le (gate0 l F).alg (Cs i) ((n + 1) ^ 26) (hd i)
    have h2 := CallIndex.scb_le l n
    have hg : (gate0 l F).alg = Endpoint.gateAlg l := rfl
    rw [hg] at h1 ⊢
    rw [← hX] at h2
    have a1 : 2 ^ (26 * L) ≤ 2 ^ ((26 + X) * L) := two_pow_mono (Nat.mul_le_mul_right _ (by omega))
    have a2 : 2 ^ (X * L) ≤ 2 ^ ((26 + X) * L) := two_pow_mono (Nat.mul_le_mul_right _ (by omega))
    have a3 : 2 ^ ((26 + X) * L + 5) = 32 * 2 ^ ((26 + X) * L) := by rw [pow_add]; ring
    have a4 : 1 ≤ 2 ^ ((26 + X) * L) := Nat.one_le_two_pow
    omega
  have hsum : (∑ i : Fin a', (PrimThrW.TopFront.payOf (gate0 l F).alg (Cs i)).length) ≤ 4 * 2 ^ ((26 + X) * L + 5) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i : Fin a' => (PrimThrW.TopFront.payOf (gate0 l F).alg (Cs i)).length)
      (2 ^ ((26 + X) * L + 5)) (fun i _ => hpay i)
    rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ ha')
  have hoff : Records.thrOff ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers ≤ (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := by
    rw [RadBnd.thrPool_length]; omega
  have hK : 64 * X + 200 * (10 * X + 32) + 1000 ≤ KR l := by rw [hX]; unfold KR; omega
  have hKY : (64 * X + 200 * (10 * X + 32) + 1000) * (L * L) ≤ KR l * (L * L) := Nat.mul_le_mul_right _ hK
  have eK : (64 * X + 200 * (10 * X + 32) + 1000) * (L * L) = 64 * (X * (L * L)) + 200 * ((10 * X + 32) * (L * L)) + 1000 * (L * L) := by ring
  have m1 : X * L ≤ X * (L * L) := Nat.mul_le_mul_left _ hLY
  have m2 : (10 * X + 32) * L ≤ (10 * X + 32) * (L * L) := Nat.mul_le_mul_left _ hLY
  have e26 : (26 + X) * L = 26 * L + X * L := by ring
  have e10 : (10 * X + 32) * (L * L) = 10 * (X * (L * L)) + 32 * (L * L) := by ring
  obtain ⟨E, hE⟩ : ∃ e, e = KR l * (L * L) := ⟨_, rfl⟩
  rw [← hE] at hKY ⊢
  have q1 : 2 ^ ((26 + X) * L + 5) ≤ 2 ^ E := two_pow_mono (by omega)
  have q2 : 2 ^ ((10 * X + 32) * L) ≤ 2 ^ E := two_pow_mono (by omega)
  have q3 : 2 ^ (26 * L + 3) ≤ 2 ^ E := two_pow_mono (by omega)
  have q4 : 2 ^ (E + 3) = 8 * 2 ^ E := by rw [pow_add]; ring
  show (∑ i : Fin a', (PrimThrW.TopFront.payOf (gate0 l F).alg (Cs i)).length) + pr.val + (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) +
    Records.thrOff ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers ≤ _
  omega

/-- **The RADIX measure at a THR call**, at every prime and star row. -/
theorem radMeas5_le (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    (row : ℕ) (hrow : row < ThrDec.thrN2 l F kclk coef A a ha hs) :
    RadSetupB5.radMeas5 l F kclk coef A a ha hs ha' Cs carriers translation pr row ≤
      2 ^ ((3 * ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) + 1) * (26 * Nat.clog 2 (n + 2) + 7) + KR l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 8) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLd ▸ one_le_L n
  have hLY : L ≤ L * L := Nat.le_mul_of_pos_left L hL1
  have hG := pool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hM := occ_le' l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hN2 := row_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hτ := dig_le' l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hpr : pr.val ≤ 2 ^ (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) := Primitive.prime_le_two_pow _ _ _ _ pr
  have hlw := lw_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hw := word_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hpw := pw_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hdg := digsN_le l F kclk coef A a ha ha' Cs carriers translation hcall hs pr
  have hJ := ThrSide.thrCallJ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hT := ThrSide.thrCallT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [← hLd] at hG hM hN2 hτ hlw hw hpw hdg hJ hT ⊢
  obtain ⟨E, hE⟩ : ∃ e, e = KR l * (L * L) + 3 := ⟨_, rfl⟩
  have hKc : 10 * CallIndex.algX l + 32 + 64 * ThrSide.eJ l + 100 ≤ KR l := by unfold KR; omega
  have hKY : (10 * CallIndex.algX l + 32 + 64 * ThrSide.eJ l + 100) * (L * L) ≤ KR l * (L * L) :=
    Nat.mul_le_mul_right _ hKc
  have eK : (10 * CallIndex.algX l + 32 + 64 * ThrSide.eJ l + 100) * (L * L) =
      (10 * CallIndex.algX l + 32) * (L * L) + 64 * (ThrSide.eJ l * (L * L)) + 100 * (L * L) := by ring
  have m1 : (10 * CallIndex.algX l + 32) * L ≤ (10 * CallIndex.algX l + 32) * (L * L) := Nat.mul_le_mul_left _ hLY
  have m2 : ThrSide.eJ l * L ≤ ThrSide.eJ l * (L * L) := Nat.mul_le_mul_left _ hLY
  have m3 : (2 * ThrSide.eJ l + 1) * L ≤ 2 * (ThrSide.eJ l * (L * L)) + L * L := by
    have := Nat.mul_le_mul_left (2 * ThrSide.eJ l + 1) hLY
    have e : (2 * ThrSide.eJ l + 1) * (L * L) = 2 * (ThrSide.eJ l * (L * L)) + L * L := by ring
    omega
  have p0 : ∀ c, c ≤ E → 2 ^ c ≤ 2 ^ E := fun c hc => two_pow_mono hc
  have x1 : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length ≤ 2 ^ E := hM.trans (p0 _ (by omega))
  have x2 : (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) ≤ 2 ^ E := hτ.trans (p0 _ (by omega))
  have x3 : (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 2 ^ E := hG.trans (p0 _ (by omega))
  have x4 : pr.val ≤ 2 ^ E := hpr.trans ((two_pow_mono (ThrSide.dig_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs)).trans
    (by rw [← hLd]; exact p0 _ (by omega)))
  have x5 : (4 * row + 4) * (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 2 ^ E := by
    have r1 : 4 * row + 4 ≤ 2 ^ (8 * (L * L) + 3) := by
      have : 2 ^ (8 * (L * L) + 3) = 8 * 2 ^ (8 * (L * L)) := by rw [pow_add]; ring
      omega
    have r2 := Nat.mul_le_mul r1 hG
    rw [← pow_add] at r2
    exact r2.trans (p0 _ (by omega))
  have x6 : 8 * (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length + 2 ≤ 2 ^ (26 * L + 7) := by
    have : 2 ^ (26 * L + 7) = 16 * 2 ^ (26 * L + 3) := by rw [show 26 * L + 7 = 26 * L + 3 + 4 by ring, pow_add]; ring
    have : 1 ≤ 2 ^ (26 * L + 3) := Nat.one_le_two_pow
    omega
  have hX := radX_le (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ((4 * row + 4) * (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length) (ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation))
    (FinalPass.ListEval.levelWord (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).J (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).W (FinalPass.ListEval.rowsOf (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length)).length pr.val L E x6 x1 x2 x3 x5
    (by rw [hE]; exact hlw) x4
  obtain ⟨E0, hE0⟩ : ∃ e, e = (3 * ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) + 1) * (26 * L + 7) := ⟨_, rfl⟩
  rw [← hE0] at hX ⊢
  have y1 : thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers ≤ 2 ^ E :=
    hT.trans ((le_two_pow_self _).trans (p0 _ (by omega)))
  have y2 : thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers ≤ 2 ^ E :=
    hJ.trans ((le_two_pow_self _).trans (p0 _ (by omega)))
  have y3 : row ≤ 2 ^ E := by have := p0 (8 * (L * L)) (by omega); omega
  have z1 : 2 ^ E ≤ 2 ^ (E0 + E) := two_pow_mono (by omega)
  have z2 : 2 ^ (E0 + E + 4) = 16 * 2 ^ (E0 + E) := by rw [pow_add]; ring
  have z3 : 2 ^ (E0 + (E - 3) + 8) = 32 * 2 ^ (E0 + E) := by
    rw [show E0 + (E - 3) + 8 = E0 + E + 5 by omega, pow_add]; ring
  show RadSetupB4.radMeas l F kclk coef A a ha hs ha' Cs carriers translation pr row + row ≤ _
  unfold RadSetupB4.radMeas
  rw [show KR l * (L * L) = E - 3 by omega]
  have hw' : ((thrReq n a' ha' Cs carriers translation).word ++ frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n)
      (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))).length ≤ 2 ^ E := by
    rw [hE]; exact hw
  rw [← hE] at hpw hdg
  omega

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
