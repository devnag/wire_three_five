import Lean
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.ThrSz3
import Proof.Wire_3_5.FinalPass.SymCap2Base
import Proof.Wire_3_5.Primitive.Writers.BShape1
import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.HashSz1Base


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH call's sizes, part 2: the field, the weights, the aux seeds, the pool (F-free)

At a THR call of the gate (`L = ⌈log₂(n+2)⌉`, `X = L + 1`), the fixed hash's remaining numbers (P3:2221-2279,
filt:aux-precision P3:2291-2296) have constants of the literals only: the field dimension `ℓ₀ ≤ c_ℓ X`, every weight
`W_j ≤ 2^{c_W X}`, so `∏_j W_j^{2t} ≤ 2^{c_Π X³}` (`log Δ₀ = O(L³)`), the aux error exponent `e ≤ c_E X²`, the aux
seeds `n_E ≤ 2^{c_N X²}` (`s_aux = O(log M + log U + e)`, P3:2029-2030), the pool `|𝒢| ≤ 2^{3+26L}` and the modulus
`refMod < 2^{ℓ₀+1}`.

* `cL0`, `cW`, `cPW`, `cE`, `cN`; `t_pos`, **`ell0_le`**, **`W_le`**, **`prodW_le`**, **`E_le`**, **`nE_le`**,
  **`G_le`**, `refMod_lt`, `sumX_le`.

Paper quantities of the main types: the fixed hash's `ℓ₀`, `W_j`, `Δ₀`'s weight product, `e`, `n_E = 2^{s_aux}`, `|𝒢|`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr

/-- The field's constant. -/
noncomputable def cL0 (l : Literals) : ℕ := cJ l + 29
/-- The weights' constant. -/
noncomputable def cW (l : Literals) : ℕ := cT l + 48 + CallIndexR.capZR l + 35
/-- The weight product's constant. -/
noncomputable def cPW (l : Literals) : ℕ := 2 * cT l * cJ l * cW l
/-- The aux error exponent's constant. -/
noncomputable def cE (l : Literals) : ℕ := 56 * cT l + cJ l + 28 * CallIndex.algX l + 77
/-- The aux seeds' constant. -/
noncomputable def cN (l : Literals) : ℕ := 6000 * (cE l + CallIndexR.capZR l + 92)

section Gate
variable (l : Literals) (F : GateFree l)

theorem t_pos (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : 1 ≤ (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := by
  have := hcall.2.2.2.1
  unfold Primitive.thrCallT Primitive.listT; omega

/-- **The field dimension** `ℓ₀ ≤ c_ℓ X`. -/
theorem ell0_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ cL0 l * ((Nat.clog 2 (n + 2)) + 1) := by
  have hJ := J_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hM := M_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hc : Nat.clog 2 (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ≤ 28 * ((Nat.clog 2 (n + 2)) + 1) := Nat.clog_le_of_le_pow hM
  show max ((Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) (Nat.clog 2 (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs)) ≤ _
  have e : cL0 l * ((Nat.clog 2 (n + 2)) + 1) = cJ l * ((Nat.clog 2 (n + 2)) + 1) + 29 * ((Nat.clog 2 (n + 2)) + 1) := by unfold cL0; ring
  rw [e]
  exact max_le (by omega) (by omega)

/-- **Every weight** `W_j ≤ 2^{c_W X}`. -/
theorem W_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (j : ℕ) : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.W j ≤ 2 ^ (cW l * ((Nat.clog 2 (n + 2)) + 1)) := by
  have h := ThrSz.majW_le (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP j
  have ht := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hB := Bs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hB' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.Bstar = (Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a')) := rfl
  rw [ht', hB'] at h
  have ht2 : (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ (cT l * ((Nat.clog 2 (n + 2)) + 1)) := ht.trans (Nat.lt_two_pow_self).le
  obtain ⟨x, hx⟩ : ∃ x, x = cT l * ((Nat.clog 2 (n + 2)) + 1) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = 28 + (48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2)) := ⟨_, rfl⟩
  rw [← hx] at ht2
  rw [← hy] at hB
  have hxy : (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a')) ≤ 2 ^ x * 2 ^ y := Nat.mul_le_mul ht2 hB
  have hr : (128 : ℕ) ≤ 2 ^ (55 + (CallIndexR.capZR l) + 35 * (Nat.clog 2 (n + 2))) :=
    calc (128 : ℕ) = 2 ^ 7 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : (2 : ℕ) ^ (cW l * ((Nat.clog 2 (n + 2)) + 1)) = 2 ^ x * 2 ^ y * 2 ^ (55 + (CallIndexR.capZR l) + 35 * (Nat.clog 2 (n + 2))) := by
    rw [hx, hy, ← pow_add, ← pow_add]; congr 1; unfold cW; ring
  rw [e]
  have h1 : 2 ^ x * 2 ^ y * 128 ≤ 2 ^ x * 2 ^ y * 2 ^ (55 + (CallIndexR.capZR l) + 35 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul_left _ hr
  have h2 : 2 ^ x ≤ 2 ^ x * 2 ^ y := Nat.le_mul_of_pos_right _ (by positivity)
  have h3 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  omega

/-- **The weight product** `∏_{j<J} W_j^{2t} ≤ 2^{c_Π X³}` (`log Δ₀ = O(L³)`, P3:2291-2296). -/
theorem prodW_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : SeedFix.prodW (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP ≤ 2 ^ (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have hJ := J_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have ht := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hJ' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J = (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have ht' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  unfold SeedFix.prodW
  calc ∏ j ∈ Finset.range (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J, (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.W j ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t)
      ≤ ∏ _j ∈ Finset.range (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.J, (2 ^ (cW l * ((Nat.clog 2 (n + 2)) + 1))) ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun j _ => Nat.pow_le_pow_left (W_le l F kclk coef A a ha ha' Cs carriers translation hcall hs j) _)
    _ = 2 ^ (cW l * ((Nat.clog 2 (n + 2)) + 1) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) * (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) := by
        rw [Finset.prod_const, Finset.card_range, ← pow_mul, ← pow_mul, hJ', ht']
        ring
    _ ≤ 2 ^ (cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
        apply Nat.pow_le_pow_right (by norm_num)
        calc cW l * ((Nat.clog 2 (n + 2)) + 1) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) * (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ cW l * ((Nat.clog 2 (n + 2)) + 1) * (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1))) * (cJ l * ((Nat.clog 2 (n + 2)) + 1)) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht)) hJ
          _ = cPW l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cPW; ring

/-- **The aux error exponent** `e ≤ c_E X²` (`listE`, `M^{2t}` with `t = O(L)`, `M = 2^{O(L)}`). -/
theorem E_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
  have hA := A_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hK := den_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hJ := J_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hM := M_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have ht := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have ht1 := t_pos l F kclk coef A a ha ha' Cs carriers translation hcall hs
  unfold Primitive.thrCallE Primitive.listE
  have hJe : Primitive.listJ (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a')) (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) = (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  have hTe : Primitive.listT (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a')) (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) = (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  rw [hJe, hTe]
  have h8 : 8 * (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 ^ (9 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2))) := by
    have hm : 8 * (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 ^ 3 * 2 ^ ((4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4) * 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hK) hA
    have e : (2 : ℕ) ^ 3 * 2 ^ ((4 * (CallIndex.algX l) + 1) * (Nat.clog 2 (n + 2)) + 4) * 2 ^ ((24 * (CallIndex.algX l) + 64) * (Nat.clog 2 (n + 2)) + 2) =
        2 ^ (9 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2))) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    rw [e] at hm; exact hm
  have hJ2 : (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ (cJ l * ((Nat.clog 2 (n + 2)) + 1)) := hJ.trans (Nat.lt_two_pow_self).le
  have hMt : (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 2 ^ (28 * ((Nat.clog 2 (n + 2)) + 1) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))) :=
    (Nat.pow_le_pow_left hM _).trans (le_of_eq (pow_mul 2 (28 * ((Nat.clog 2 (n + 2)) + 1)) (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))).symm)
  obtain ⟨u, hu⟩ : ∃ u, u = cJ l * ((Nat.clog 2 (n + 2)) + 1) + 28 * ((Nat.clog 2 (n + 2)) + 1) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) := ⟨_, rfl⟩
  have hM2 : (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 ^ u := hM.trans (Nat.pow_le_pow_right (by norm_num) (by
    rw [hu]; have : 28 * ((Nat.clog 2 (n + 2)) + 1) ≤ 28 * ((Nat.clog 2 (n + 2)) + 1) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) := Nat.le_mul_of_pos_right _ (by omega)
    omega))
  have hJM : (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 2 ^ u := by
    rw [hu, pow_add]; exact Nat.mul_le_mul hJ2 hMt
  have hsum : (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) + (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 2 ^ (u + 1) := by rw [pow_succ]; omega
  have hp : 8 * (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * ((Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) + (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))) ≤ 2 ^ (9 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + (u + 1)) := by
    rw [pow_add]; exact Nat.mul_le_mul h8 hsum
  have hc : Nat.clog 2 (8 * (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * (Primitive.thrCallA (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) * ((Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) + (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) * (Primitive.thrCallM (callInputs l F kclk coef A a ha) hs Cs) ^ (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))) + 1) ≤
      9 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + (u + 1) + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    have : 1 ≤ (2 : ℕ) ^ (9 + (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) + (u + 1)) := Nat.one_le_two_pow
    omega
  have hX1 : 1 ≤ ((Nat.clog 2 (n + 2)) + 1) := by omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have i1 : (28 * (CallIndex.algX l) + 65) * (Nat.clog 2 (n + 2)) ≤ (28 * (CallIndex.algX l) + 65) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (by omega)
  have i2 : cJ l * ((Nat.clog 2 (n + 2)) + 1) ≤ cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ hXX
  have i3 : 28 * ((Nat.clog 2 (n + 2)) + 1) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 56 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    calc 28 * ((Nat.clog 2 (n + 2)) + 1) * (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 28 * ((Nat.clog 2 (n + 2)) + 1) * (2 * (cT l * ((Nat.clog 2 (n + 2)) + 1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht)
      _ = 56 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by ring
  have e : cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = 56 * (cT l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) + cJ l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) +
      (28 * (CallIndex.algX l) + 65) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 12 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by unfold cE; ring
  rw [e]
  omega

theorem sumX_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) : (carriers.map List.length).sum ≤ 2 * 2 ^ (26 * (Nat.clog 2 (n + 2))) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hs := BShape.sum_map_le_card carriers List.length ((n + 1) ^ 26) (fun X hX => (hcall.2.1 X hX).1)
  have hn := n26_le n
  calc (carriers.map List.length).sum ≤ carriers.length * (n + 1) ^ 26 := hs
    _ ≤ 2 * 2 ^ (26 * (Nat.clog 2 (n + 2))) := Nat.mul_le_mul hnc hn

/-- **The aux seeds** `n_E = 2^{s_aux} ≤ 2^{c_N X²}`. -/
theorem nE_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : (PrimAsm.WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ (cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
  have hsb := Filters.seedBits_le (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
  have he := E_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hsx := sumX_le l F kclk coef A a ha ha' Cs carriers translation hcall
  have hc := capT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  show Fintype.card (Filters.GapSeed (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ _
  rw [Filters.card_gapSeed]
  apply Nat.pow_le_pow_right (by norm_num)
  refine hsb.trans ?_
  have hlen : (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len = 2 * (carriers.map List.length).sum := rfl
  have hcap : (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap = (carriers.length + 1) * (4096 * (((gate0 l F).budget kclk coef A a ha).capOf .thr n)) := rfl
  have hee : (PrimAsm.WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp = (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := rfl
  rw [hlen, hcap, hee]
  have h1 : Nat.clog 2 (2 * (carriers.map List.length).sum + 1) ≤ 3 + 26 * (Nat.clog 2 (n + 2)) := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    have : 1 ≤ (2 : ℕ) ^ (26 * (Nat.clog 2 (n + 2))) := Nat.one_le_two_pow
    omega
  have h2 : Nat.clog 2 ((carriers.length + 1) * (4096 * (((gate0 l F).budget kclk coef A a ha).capOf .thr n)) + 1) ≤ 14 + (48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2)) := by
    apply Nat.clog_le_of_le_pow
    have hm : (carriers.length + 1) * (4096 * (((gate0 l F).budget kclk coef A a ha).capOf .thr n)) ≤ 3 * (4096 * 2 ^ ((48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2)))) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hc)
    rw [pow_add]
    have : 1 ≤ (2 : ℕ) ^ ((48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2))) := Nat.one_le_two_pow
    norm_num
    omega
  have hXX : ((Nat.clog 2 (n + 2)) + 1) ≤ ((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have i1 : (48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2)) + 26 * (Nat.clog 2 (n + 2)) ≤ ((CallIndexR.capZR l) + 74) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := by
    have : ((CallIndexR.capZR l) + 74) * (Nat.clog 2 (n + 2)) ≤ ((CallIndexR.capZR l) + 74) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) := Nat.mul_le_mul_left _ (by omega)
    have e : (48 + (CallIndexR.capZR l)) * (Nat.clog 2 (n + 2)) + 26 * (Nat.clog 2 (n + 2)) = ((CallIndexR.capZR l) + 74) * (Nat.clog 2 (n + 2)) := by ring
    omega
  have e : cN l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) = 6000 * (cE l * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + ((CallIndexR.capZR l) + 74) * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1)) + 18 * (((Nat.clog 2 (n + 2)) + 1) * ((Nat.clog 2 (n + 2)) + 1))) := by
    unfold cN; ring
  rw [e]
  omega

/-- **The pool** `|𝒢| = 2Σ|X_j| + M ≤ 2^{3+26L}`. -/
theorem G_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 2 ^ (3 + 26 * (Nat.clog 2 (n + 2))) := by
  have hsx := sumX_le l F kclk coef A a ha ha' Cs carriers translation hcall
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have ho := ThrSz.occs_len ((callInputs l F kclk coef A a ha).starParams n hs) ha' Cs ((n + 1) ^ 26) hd
  have hn := n26_le n
  have hpl : (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length = 2 * (carriers.map List.length).sum + (Primitive.thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length := by
    unfold PrimAsm.Records.thrPool PrimAsm.Records.thrSlices
    rw [List.flatten_append, List.length_append, PrimAsm.Records.prefix_length]
    simp
    rfl
  rw [hpl, pow_add]
  have := Nat.mul_le_mul_left 4 hn
  omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
