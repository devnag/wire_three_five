import Proof.Wire_3_5.FinalPass.HashShape
import Proof.Wire_3_5.FinalPass.SymDeg
import Proof.Wire_3_5.FinalPass.ThrSz1

/-! # The HASH call's sizes, part 1: the majorant's numbers, F-free

At a THR call of the gate (`L = ⌈log₂(n+2)⌉`, `a = algX l`, `Z = capZR l`), every number of the fixed hash's majorant
(P3:2221-2279, `list_params_bound`'s choice `J, t, e`, P3:2238-2251) is `2^{O(L)}` or `O(L)` with constants of the
literals only: the THR cap `≤ 2^{(48+Z)L}` (`2c_r + 2 ≤ n + 2`, so `capK(c_r) ≤ 2^{48L}`: no constant of `F`), `|𝒢|`,
the cutoff, `A`, `K = den`, `B_*`, `J ≤ c_J(L+1)`, `t ≤ c_t(L+1)`, `M ≤ 2^{28(L+1)}`. These fix the HASH free
numbers' constants before `F` (the recovery range `Q' = O(k + L³)`, P3:2291-2296).

* `capT_le`, `eq_le`, `cut_le'`, `primes_le`, **`A_le`**, **`den_le`**, **`Bs_le`**, **`J_le`**, **`t_le`**, **`M_le`**.

Paper quantities of the main types: the fixed hash's majorant parameters at a THR call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr

/-- The majorant constants of the literals. -/
noncomputable def cJ (l : Literals) : ℕ := 40 + 28 * CallIndex.algX l + 113 + CallIndexR.capZR l
noncomputable def cT (l : Literals) : ℕ := 12 + 28 * CallIndex.algX l + 65 + cJ l

theorem n1_le_L (n : ℕ) : n + 1 ≤ 2 ^ Nat.clog 2 (n + 2) := by have := n2_le_L n; omega

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The THR cap** `≤ 2^{(48+Z)L}`. -/
theorem capT_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (((gate0 l F).budget kclk coef A a ha).capOf .thr n) ≤ 2 ^ ((48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) := by
  have hc : (((gate0 l F).budget kclk coef A a ha).capOf .thr n) ≤ CallIndexR.capK F.cr * (n + 2) ^ (CallIndexR.capZR l) := CallIndexR.cap_leR l F.cr .thr n
  have hcr := cr_le_k l F kclk coef A a ha hs
  have hkq : (((gate0 l F).budget kclk coef A a ha).kOf n) ≤ n := hcall.2.2.2.2.2.2.kq
  have hn2 := n2_le_L n
  have hK1 : CallIndexR.capK F.cr ≤ 2 ^ (48 * (Nat.clog 2 (n + 2))) := by
    show (2 * F.cr + 2) ^ 48 ≤ _
    exact pow_mono_mul 48 (by omega)
  have hZ := pow_N_le n (CallIndexR.capZR l)
  calc (((gate0 l F).budget kclk coef A a ha).capOf .thr n) ≤ 2 ^ (48 * (Nat.clog 2 (n + 2))) * 2 ^ ((CallIndexR.capZR l) * (Nat.clog 2 (n + 2))) := hc.trans (Nat.mul_le_mul hK1 hZ)
    _ = 2 ^ ((48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) := by rw [← pow_add]; congr 1; ring

theorem eq_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)) ≤ 2 ^ (4 * (CallIndex.algX l) * (Nat.clog 2 (n + 2))) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have h := CallIndex.thrEq_le l F kclk coef A a ha n hs ha' Cs hd
  refine h.trans ((pow_N_le n _).trans (Nat.pow_le_pow_right (by norm_num) (le_of_eq (by ring))))

theorem cut_le' (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) ≤ 2 ^ ((10 * (CallIndex.algX l) + 32) * (Nat.clog 2 (n + 2))) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  exact (CallIndex.cut_le l F kclk coef A a ha n hs ha' Cs hd).trans (pow_N_le n _)

theorem primes_le (c : ℕ) : Fintype.card (SupplierPrime.PrimeIndex c) ≤ c + 1 := by
  rw [Fintype.card_coe]
  unfold SupplierPrime.primesUpTo
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- **The populations' count** `A ≤ 2^{(24a+64)L + 2}`. -/
theorem A_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) := by
  have h1 := eq_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have h2 := cut_le' l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hp := primes_le (Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
  have hd : Primitive.thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤ (Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)) := by
    unfold Primitive.thrDigits; exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  unfold Primitive.thrCallA
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  obtain ⟨E, hE⟩ : ∃ E, E = (10 * (CallIndex.algX l) + 32) * (Nat.clog 2 (n + 2)) := ⟨_, rfl⟩
  rw [← hE] at h2
  have hE1 : (1 : ℕ) ≤ 2 ^ E := Nat.one_le_two_pow
  have hp2 : Fintype.card (SupplierPrime.PrimeIndex (Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤ 2 * 2 ^ E := by omega
  have e : (2 : ℕ) ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) = 2 ^ (4 * (CallIndex.algX l) * (Nat.clog 2 (n + 2))) * (2 * 2 ^ E) * 2 ^ E * 2 := by
    rw [hE, show (24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2 = 4 * (CallIndex.algX l) * (Nat.clog 2 (n + 2)) + 1 + (10 * (CallIndex.algX l) + 32) * (Nat.clog 2 (n + 2)) +
      (10 * (CallIndex.algX l) + 32) * (Nat.clog 2 (n + 2)) + 1 by ring, pow_add, pow_add, pow_add, pow_add]
    ring
  rw [e]
  have key : (Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)) * Fintype.card (SupplierPrime.PrimeIndex (Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) * Primitive.thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * 2 ≤
      2 ^ (4 * (CallIndex.algX l) * (Nat.clog 2 (n + 2))) * (2 * 2 ^ E) * 2 ^ E * 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul h1 hp2) (hd.trans h2))
  calc (Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)) * (Fintype.card (SupplierPrime.PrimeIndex (Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) * (Primitive.thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * 2))
        = (Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)) * Fintype.card (SupplierPrime.PrimeIndex (Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) * Primitive.thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * 2 := by ring
    _ ≤ _ := key

/-- **The prime surrogate's denominator** `K = den ≤ 2^{(4a+1)L + 4}`. -/
theorem den_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 ^ ((4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4) := by
  have h1 := eq_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hn := n1_le_L n
  have hD : (callInputs l F kclk coef A a ha).D = 1 := rfl
  unfold Primitive.thrCallDen
  rw [hD, pow_one]
  have h2 : (Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)) + 1 ≤ 2 * 2 ^ (4 * (CallIndex.algX l) * (Nat.clog 2 (n + 2))) := by have := Nat.one_le_two_pow (n := 4 * (CallIndex.algX l) * (Nat.clog 2 (n + 2))); omega
  have e : (2 : ℕ) ^ ((4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4) = 8 * (2 * 2 ^ (4 * (CallIndex.algX l) * (Nat.clog 2 (n + 2)))) * 2 ^ (Nat.clog 2 (n + 2)) := by
    rw [show (4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4 = 4 * (CallIndex.algX l) * (Nat.clog 2 (n + 2)) + (Nat.clog 2 (n + 2)) + 4 by ring, pow_add, pow_add]; ring
  rw [e]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) (by omega)

/-- **`B_*`** `≤ 2^{28 + (48+Z)L}`. -/
theorem Bs_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a')) ≤ 2 ^ (28 + (48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) := by
  have hc := capT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  unfold Primitive.thrCallBs
  have h1 : a' * (4096 * ((carriers.length + 1) * (4096 * (((gate0 l F).budget kclk coef A a ha).capOf .thr n)))) ≤ 4 * (4096 * (3 * (4096 * (((gate0 l F).budget kclk coef A a ha).capOf .thr n)))) :=
    Nat.mul_le_mul ha' (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
  refine h1.trans ?_
  rw [pow_add]
  have := Nat.mul_le_mul_left (2 ^ 28) hc
  norm_num at this ⊢
  omega

/-- **The levels** `J ≤ c_J(L+1)`. -/
theorem J_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ cJ l * ((Nat.clog 2 (n + 2)) + 1) := by
  have hA := A_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hK := den_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hB := Bs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  unfold Primitive.thrCallJ Primitive.listJ
  apply Nat.clog_le_of_le_pow
  have hm : 8 * (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a')) ≤ 2 ^ 3 * 2 ^ ((4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4) * 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) *
      2 ^ (28 + (48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hK) hA) hB
  have e : (2 : ℕ) ^ 3 * 2 ^ ((4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4) * 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) *
      2 ^ (28 + (48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) = 2 ^ (37 + (28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [e] at hm
  have h2 : (2 : ℕ) ^ (37 + (28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) + 1 ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1)) := by
    have hle : 38 + (28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2)) ≤ cJ l * ((Nat.clog 2 (n + 2)) + 1) := by
      unfold cJ
      have e2 : (40 + 28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) * ((Nat.clog 2 (n + 2)) + 1) = (28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2)) + 40 * (Nat.clog 2 (n + 2)) +
          (40 + 28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) := by ring
      rw [e2]; omega
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hle
    rw [show 38 + (28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2)) = (37 + (28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) + 1 by ring, pow_succ] at this
    have h1 : 1 ≤ (2 : ℕ) ^ (37 + (28 * (CallIndex.algX l) + 113 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) := Nat.one_le_two_pow
    omega
  omega

/-- **The moment count** `t ≤ c_t(L+1)`. -/
theorem t_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ cT l * ((Nat.clog 2 (n + 2)) + 1) := by
  have hA := A_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hK := den_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hJ := J_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  unfold Primitive.thrCallT Primitive.listT
  have hJ2 : (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1)) := hJ.trans (Nat.lt_two_pow_self).le
  have hm : 8 * (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ 3 * 2 ^ ((4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4) * 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) *
      2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hK) hA) hJ2
  have e : (2 : ℕ) ^ 3 * 2 ^ ((4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4) * 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) *
      2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1)) = 2 ^ (9 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + cJ l * ((Nat.clog 2 (n + 2)) + 1)) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [e] at hm
  have hc : Nat.clog 2 (8 * (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * Primitive.listJ (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a')) (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) + 1) ≤
      10 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + cJ l * ((Nat.clog 2 (n + 2)) + 1) := by
    apply Nat.clog_le_of_le_pow
    have h1 : 1 ≤ (2 : ℕ) ^ (9 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + cJ l * ((Nat.clog 2 (n + 2)) + 1)) := Nat.one_le_two_pow
    rw [show 10 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + cJ l * ((Nat.clog 2 (n + 2)) + 1) = (9 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + cJ l * ((Nat.clog 2 (n + 2)) + 1)) + 1
      by ring, pow_succ]
    have : Primitive.listJ (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a')) (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) = (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
    rw [this]
    omega
  unfold cT
  have e2 : (12 + 28 * (CallIndex.algX l) + 65 + cJ l) * ((Nat.clog 2 (n + 2)) + 1) = 11 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + cJ l * ((Nat.clog 2 (n + 2)) + 1) +
      (12 * (Nat.clog 2 (n + 2)) + (28 * (CallIndex.algX l) + 65) + 1) := by ring
  rw [e2]
  omega

/-- **The occurrences** `M ≤ 2^{28(L+1)}`. -/
theorem M_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 ^ (28 * ((Nat.clog 2 (n + 2)) + 1)) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have h := ThrSz.occs_len ((callInputs l F kclk coef A a ha).starParams n hs) ha' Cs ((n + 1) ^ 26) hd
  have hn : (n + 1) ^ 26 ≤ 2 ^ (26 * (Nat.clog 2 (n + 2))) := pow_mono_mul 26 (n1_le_L n)
  unfold Primitive.thrCallM
  calc (Primitive.thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length ≤ 4 * 2 ^ (26 * (Nat.clog 2 (n + 2))) := h.trans (Nat.mul_le_mul_left _ hn)
    _ ≤ 2 ^ (28 * ((Nat.clog 2 (n + 2)) + 1)) := by
      rw [show 28 * ((Nat.clog 2 (n + 2)) + 1) = 2 + 26 * (Nat.clog 2 (n + 2)) + (2 * (Nat.clog 2 (n + 2)) + 26) by ring, pow_add, pow_add]
      have : 1 ≤ (2 : ℕ) ^ (2 * (Nat.clog 2 (n + 2)) + 26) := Nat.one_le_two_pow
      norm_num
      nlinarith

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
