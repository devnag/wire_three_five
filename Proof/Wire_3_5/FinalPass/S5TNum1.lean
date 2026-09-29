import Proof.Wire_3_5.FinalPass.S5TJoin2
import Proof.Wire_3_5.Primitive.SeedFix.TS4K

/-! # S5-THR, part 35: the stage's costs below one power (P3:3105-3115)

Every piece of the THR stage's cost at arguments `≤ Z` (one bound for the request's sizes and numbers, `Z` a power of
the padded count base): a polynomially bounded piece of degree `≤ H` and coefficient `≤ Z` costs at most
`Z^{2H+1}` (**`pw_Z`**, **`pb_Z`**); the parse `≤ 6000·Z²` (**`parse_le`**); the first docks (the prep, W6)
`≤ Z^{2H+2}` (**`chainA_le`**); the next docks (the top front, the data stage) `≤ Z^{2H+2}` (**`chainB_le`**); the
tail `≤ 19062·Z⁵` (**`tail_le`**); the whole THR stage `≤ Z^{2H+3}` (**`stageThr_le`**).

Paper quantity of the main type: the front's running time as a power of the call's size, the powers fixed before
the gate (P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.SupplierPipeline

section Calc

/-- **A bounded power** `C·m^d` at `m ≤ 5Z`, `C ≤ Z`, `d ≤ H` is at most `Z^{2H+1}`. -/
theorem pw_Z {v C d m Z H : ℕ} (hZ : 5 ≤ Z) (h : v ≤ C * m ^ d) (hm : m ≤ 5 * Z) (hC : C ≤ Z) (hd : d ≤ H) :
    v ≤ Z ^ (2 * H + 1) := by
  have h1 : m ≤ Z ^ 2 := by nlinarith
  have h2 : m ^ d ≤ (Z ^ 2) ^ H :=
    (Nat.pow_le_pow_left h1 d).trans (Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) hd)
  calc v ≤ C * m ^ d := h
    _ ≤ Z * (Z ^ 2) ^ H := Nat.mul_le_mul hC h2
    _ = Z ^ (2 * H + 1) := by ring

/-- **A polynomially bounded piece** at a measure `≤ 4Z`: at most `Z^{2H+1}`. -/
theorem pb_Z {v m C d Z H : ℕ} (hZ : 5 ≤ Z) (h : ValidatorPolynomialDomination.PolyBounded v m C d) (hm : m ≤ 4 * Z)
    (hC : C ≤ Z) (hd : d ≤ H) : v ≤ Z ^ (2 * H + 1) :=
  pw_Z hZ h (by omega) hC hd

/-- One more power absorbs a factor `c ≤ Z`. -/
theorem mul_pow_le {Z e c : ℕ} (hc : c ≤ Z) : c * Z ^ e ≤ Z ^ (e + 1) := by
  rw [pow_succ, Nat.mul_comm (Z ^ e) Z]; exact Nat.mul_le_mul_right _ hc

end Calc

section Pieces

/-- **The parse's cost** at `n + 3 ≤ Z`, `a ≤ 4`, `c ≤ Z`. -/
theorem parse_le (n a c Z : ℕ) (hn : n + 3 ≤ Z) (ha : a ≤ 4) (hc : c ≤ Z) : parseCost n a c ≤ 6000 * Z ^ 2 := by
  unfold parseCost
  have h1 := PrimT.TS4.a1_le n Z hn
  have h2 := PrimT.TS4.a2_le a ha
  have h3 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **The tail's cost** at arguments `≤ Z`. -/
theorem tail_le (m t ℓ w M J nall o a x y Z : ℕ) (h1 : 1 ≤ Z) (hm : m ≤ Z) (ht : t ≤ Z) (hl : ℓ ≤ Z) (hw : w ≤ Z)
    (hM : M ≤ Z) (hJ : J ≤ Z) (hn : nall ≤ Z) (ho : o ≤ Z) (ha : a ≤ Z) (hx : x ≤ Z) (hy : y ≤ Z) :
    tailCost m t ℓ w M J nall o a x y ≤ 19062 * Z ^ 5 := by
  have e1 : tailCost m t ℓ w M J nall o a x y ≤ tailCost Z Z Z Z Z Z Z Z Z Z Z := by
    unfold tailCost tailACost seedCost zfrCost Hash4.buildCost Hash4.levelCost Hash4.stepCost Hash4.hornerCost
      Hash4.recCost mulStepCost
    gcongr
  refine e1.trans ?_
  have p1 : Z ≤ Z ^ 5 := Nat.le_self_pow (by norm_num) _
  have p2 : Z ^ 2 ≤ Z ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
  have p3 : Z ^ 3 ≤ Z ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
  have p4 : Z ^ 4 ≤ Z ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
  have p0 : 1 ≤ Z ^ 5 := Nat.one_le_pow _ _ h1
  unfold tailCost tailACost seedCost zfrCost Hash4.buildCost Hash4.levelCost Hash4.stepCost Hash4.hornerCost
    Hash4.recCost mulStepCost
  ring_nf
  nlinarith

variable (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ)

/-- **The first docks' cost** (the prep, W6) at `n, W_p, (n+1)^{26}, cap_T ≤ Z`. -/
theorem chainA_le (l : Literals) (cr n a nc Wp Z H : ℕ) (hZ : 30 ≤ Z) (hH : 1 ≤ H) (ha : a ≤ 4) (hnc : nc ≤ 2) (hn : n ≤ Z)
    (hW : Wp ≤ Z) (h26 : (n + 1) ^ 26 ≤ Z) (hcap : PrimT.TS4.capTL l cr n ≤ Z) (hKp : PrimT.TS4.Kp l cr ≤ Z)
    (hDp : PrimT.TS4.Dp l ≤ H) (hC6 : (PrimT.W6.numsW6 alg Dexp).Cc ≤ Z) (hD6 : (PrimT.W6.numsW6 alg Dexp).Dc ≤ H) :
    chainACost alg Dexp l cr n a nc Wp ≤ Z ^ (2 * H + 2) := by
  unfold chainACost
  have hp := pw_Z (by omega) (PrimT.TS4.p0Stage_le l cr n Wp a nc ha hnc) (by omega) hKp hDp
  have h6 := pb_Z (by omega) ((PrimT.W6.numsW6 alg Dexp).cost_poly (n + (Wp + (n + 1) ^ 26) + PrimT.TS4.capTL l cr n))
    (by omega) hC6 hD6
  have hz : Z ^ 2 ≤ Z ^ (2 * H + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz2 : 30 * Z ≤ Z ^ 2 := by nlinarith
  have hs : 30 * Z ^ (2 * H + 1) ≤ Z ^ (2 * H + 2) := mul_pow_le (by omega)
  omega

/-- **The next docks' cost** (the top front, the data stage) at `V ≤ 4Z`, `K + n + L + W_t ≤ 4Z`. -/
theorem chainB_le {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (V L Wt K Z H : ℕ) (hZ : 100 ≤ Z) (hH : 1 ≤ H) (hV : V ≤ 4 * Z) (hn : n ≤ Z)
    (hC3 : (PrimThrW.TF3Cost.topFront3 alg).Cc ≤ Z) (hD3 : (PrimThrW.TF3Cost.topFront3 alg).Dc ≤ H)
    (htd : ValidatorPolynomialDomination.PolyBounded (PrimAsm.ThrData.thrDataStage2.cost a' Cs carriers L Wt)
      (K + n + L + Wt) PrimAsm.ThrData.thrDataStage2.Cc PrimAsm.ThrData.thrDataStage2.Dc)
    (hm : K + n + L + Wt ≤ 4 * Z) (hCd : PrimAsm.ThrData.thrDataStage2.Cc ≤ Z)
    (hDd : PrimAsm.ThrData.thrDataStage2.Dc ≤ H) :
    chainBCost alg Cs carriers V L Wt ≤ Z ^ (2 * H + 2) := by
  unfold chainBCost
  have h3 := pb_Z (by omega) ((PrimThrW.TF3Cost.topFront3 alg).cost_poly V) hV hC3 hD3
  have hd := pb_Z (by omega) htd hm hCd hDd
  have hz : Z ^ 2 ≤ Z ^ (2 * H + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz2 : 100 * Z ≤ Z ^ 2 := by nlinarith
  have hs : 30 * Z ^ (2 * H + 1) ≤ Z ^ (2 * H + 2) := mul_pow_le (by omega)
  omega

/-- **The THR stage's cost**: the parse, the branch, the path, below `Z^{2H+3}`. -/
theorem stageThr_le (p cA cB tl Z H : ℕ) (hZ : 30000 ≤ Z) (hH : 2 ≤ H) (hp : p ≤ 6000 * Z ^ 2)
    (hA : cA ≤ Z ^ (2 * H + 2)) (hB : cB ≤ Z ^ (2 * H + 2)) (ht : tl ≤ 19062 * Z ^ 5) :
    p + 1 + (1 + (cA + 1 + (cB + 1 + tl))) ≤ Z ^ (2 * H + 3) := by
  have z2 : Z ^ 2 ≤ Z ^ (2 * H + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have z5 : Z ^ 5 ≤ Z ^ (2 * H + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have z0 : 1 ≤ Z ^ (2 * H + 2) := Nat.one_le_pow _ _ (by omega)
  have hs : 30000 * Z ^ (2 * H + 2) ≤ Z ^ (2 * H + 2 + 1) := mul_pow_le hZ
  have e : 2 * H + 2 + 1 = 2 * H + 3 := by omega
  rw [e] at hs
  omega

end Pieces

end NearCubicWires.WireExponent3_5.FinalPass.S5T
