import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ4
import Proof.Wire_3_5.UnionMachine.ThrUnitMeasBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPolyBase
import Proof.Wire_3_5.Primitive.SeedFix.W6L
import Proof.Wire_3_5.Primitive.SeedFix.GeoPackBase
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrBBase
import Proof.Wire_3_5.FinalPass.SymSz1Base

/-! # T3 THR decode front, packaging part 5: the call's atom bounds

At a THR call of the gate (`Call`, `StarAt n`), with `L = ⌈log₂(n+2)⌉`, `Y = L²`: every register value of the front is
at most `Q_F·2^{A·Y}` (`Atoms`): the request `|thrCallW| ≤ 2^{K_R Y + 3}` (`ThrMeas.word_le`), the THR numbers
`≤ K_t(F)·(n+1)^{D_t}` (`W6.thrNumsPoly` at the cap's degree `48 + Z`, `ThrSide.capT_le2`), the carriers' sizes and the
tuple's gates `≤ 8(n+1)^{26}`, the THR filter's seed length `≤ 6000(80 + Z + f_e)·Y` (`Filters.seedBits_le`), `2k_h = k ≤
L²` (`SymFr.kh_two`, `k_le_L2`), `c_r ≤ k/4`, the numbers machine's need constants. The exponent `A = A(l, f_e)` is
fixed before the gate; `Q_F = K_t(F) + 1` after it.

* `capD`, `capC`, `dT`, `kT`, `NW`, `TW`, `aE`, `qF`; **`call_atoms`**.

Paper quantity of the main type: the THR call's sizes within `2^{O(L²)}` (P3:2543-2558, 2597-2599). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine




theorem pow_le_L (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ (d * Nat.clog 2 (n + 2)) := by
  have h : n + 1 ≤ 2 ^ Nat.clog 2 (n + 2) := by have := Nat.le_pow_clog (b := 2) (by norm_num) (n + 2); omega
  calc (n + 1) ^ d ≤ (2 ^ Nat.clog 2 (n + 2)) ^ d := Nat.pow_le_pow_left h d
    _ = 2 ^ (d * Nat.clog 2 (n + 2)) := by rw [← pow_mul, Nat.mul_comm]

theorem Y_ge (n : ℕ) : 1 ≤ Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) := by
  have := FinalPass.SymFr.one_le_L n; nlinarith

theorem L_le_Y (n : ℕ) : Nat.clog 2 (n + 2) ≤ Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) := by
  have := FinalPass.SymFr.one_le_L n; nlinarith

theorem two_le_QY {Q Y A e : ℕ} (hQ : 1 ≤ Q) (h : e ≤ A * Y) : 2 ^ e ≤ QY Q Y 0 A := by
  unfold QY; simp only [pow_zero, one_mul]; exact Nat.pow_le_pow_right (by norm_num) h

theorem le_two_QY {Q Y A x e : ℕ} (hQ : 1 ≤ Q) (hx : x ≤ 2 ^ e) (h : e ≤ A * Y) : x ≤ QY Q Y 0 A :=
  hx.trans (two_le_QY hQ h)

theorem x_le_two_pow (x : ℕ) : x ≤ 2 ^ x := (Nat.lt_two_pow_self).le

/-- A value below `2^e` with `e ≤ A·Y` is below `QY Q Y 0 A` (any `Q ≥ 1`). -/
theorem qy0_of {Q Y A x e : ℕ} (hQ : 1 ≤ Q) (hx : x ≤ 2 ^ e) (he : e ≤ A * Y) : x ≤ QY Q Y 0 A :=
  le_two_QY hQ hx he

/-- The THR filter's seed length (`Filters.seedBits_le` at the THR cap `≤ 2^{(48+Z)L}`). -/
theorem sbT_core (fe Z L capT len sb : ℕ) (hL : 1 ≤ L) (hlen : Nat.clog 2 (len + 1) ≤ 26 * L + 2)
    (hcap : Nat.clog 2 (capT + 1) ≤ (48 + Z) * L + 1)
    (h : sb ≤ 6000 * (Nat.clog 2 (len + 1) + Nat.clog 2 (capT + 1) + fe * L + 1)) :
    sb + 64 ≤ (6000 * (80 + Z + fe) + 64) * (L * L) := by
  have hLL : L ≤ L * L := Nat.le_mul_of_pos_left L hL
  have e1 : (48 + Z) * L = 48 * L + Z * L := by ring
  have e2 : (6000 * (80 + Z + fe) + 64) * (L * L) = 480064 * (L * L) + 6000 * (Z * (L * L)) + 6000 * (fe * (L * L)) := by
    ring
  have z1 : Z * L ≤ Z * (L * L) := Nat.mul_le_mul_left _ hLL
  have z2 : fe * L ≤ fe * (L * L) := Nat.mul_le_mul_left _ hLL
  rw [e2]; rw [e1] at hcap
  omega

section Nums
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (D capT : ℕ)

theorem hashNums_get5 : (ThrData.hashNums P Cs carriers alg D capT).getD 5 0 =
    (SupplierPrime.primesUpTo (PrimThrW.Joins.thrNumVals P Cs alg D carriers.length capT).cut).card := by
  simp [ThrData.hashNums, ThrData.thrNumList, PrimThrW.Joins.ThrNumVals.get, PrimThrW.Joins.thrNumVals]

theorem hashNums_get6 : (ThrData.hashNums P Cs carriers alg D capT).getD 6 0 =
    ThrQ.primeSum (PrimThrW.Joins.thrNumVals P Cs alg D carriers.length capT).cut := by
  simp [ThrData.hashNums, ThrData.thrNumList, PrimThrW.Joins.ThrNumVals.get, PrimThrW.Joins.thrNumVals]

end Nums

/-- `c·L + c ≤ E·L²` once `2c ≤ E` (`L ≥ 1`). -/
theorem lin_le_aY {c L E : ℕ} (hL : 1 ≤ L) (hE : 2 * c ≤ E) : c * L + c ≤ E * (L * L) := by
  have h1 : c * L + c ≤ 2 * c * L := by nlinarith
  have h2 : 2 * c * L ≤ 2 * c * (L * L) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left L hL)
  have h3 : 2 * c * (L * L) ≤ E * (L * L) := Nat.mul_le_mul_right _ hE
  omega

/-- The `n`-atoms below `QY Q Y 0 A` (`A ≥ 64`). -/
theorem n_atoms (Q E n : ℕ) (hQ : 1 ≤ Q) (hE : 64 ≤ E) :
    n + 3 ≤ QY Q (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) 0 E ∧
    (n + 1) ^ 26 * 2 ≤ QY Q (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) 0 E ∧
    8 * (n + 1) ^ 26 ≤ QY Q (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) 0 E ∧
    2 * (n + 1) ^ 26 + 8 ≤ QY Q (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) 0 E := by
  have hL1 := FinalPass.SymFr.one_le_L n
  have hn := FinalPass.SymFr.n2_le_L n
  have hp := pow_le_L n 26
  have e26 : 26 * Nat.clog 2 (n + 2) + 26 ≤ E * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := lin_le_aY hL1 (by omega)
  have e1 : 1 * Nat.clog 2 (n + 2) + 1 ≤ E * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := lin_le_aY hL1 (by omega)
  have t0 := Nat.one_le_two_pow (n := 26 * Nat.clog 2 (n + 2))
  have p1 : 2 ^ (Nat.clog 2 (n + 2) + 1) = 2 ^ Nat.clog 2 (n + 2) * 2 := pow_succ _ _
  have p2 : 2 ^ (26 * Nat.clog 2 (n + 2) + 1) = 2 ^ (26 * Nat.clog 2 (n + 2)) * 2 := pow_succ _ _
  have p3 : 2 ^ (26 * Nat.clog 2 (n + 2) + 3) = 2 ^ (26 * Nat.clog 2 (n + 2)) * 8 := by rw [pow_add]; norm_num
  have p4 : 2 ^ (26 * Nat.clog 2 (n + 2) + 4) = 2 ^ (26 * Nat.clog 2 (n + 2)) * 16 := by rw [pow_add]; norm_num
  refine ⟨qy0_of hQ (e := Nat.clog 2 (n + 2) + 1) (by omega) (by omega),
    qy0_of hQ (e := 26 * Nat.clog 2 (n + 2) + 1) (by omega) (by omega),
    qy0_of hQ (e := 26 * Nat.clog 2 (n + 2) + 3) (by omega) (by omega),
    qy0_of hQ (e := 26 * Nat.clog 2 (n + 2) + 4) (by omega) (by omega)⟩

section Star

end Star

section Call

end Call


end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
