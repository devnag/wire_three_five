import Proof.Wire_3_5.Primitive.Writers.HashBud1
import Proof.Wire_3_5.Primitive.Writers.HashFit3

/-! # c4 HASH budget (C), part 2: the cell and the kept words writer at rate `4`

P3:3105-3115 (`c₄` after `F`): at every THR call, with the cell's digit bound `B_m` within the cell's capacity (the premise) and `S_m` within it (`CellFit.cc`), the HASH cell's steps `HashCell.callCost` and the kept words writer's
`Wk.cost` are at most `K·U⁴`, `U = 2^{⌊n/8⌋ + c_U}`: the populations' cost is quartic in `q + cap + 1`
(**`pops_arith`**, **`pops_le`**), the cell's other terms quadratic in the capacity or polynomial in `n`
(**`call_arith`**), the writer's size `kwS` quadratic and its numbers `kwT ≤ 9q` quasi-polynomial (**`kwT_le`**,
**`wk_arith`**); hence **`hX_ex`**: `∃ c_X, … Ex n 7 c_X (callCost + Wk.cost)`.

Paper quantity of the main type: the HASH setup's cell and writer steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashBud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Bud

/-- The populations' cost, as a polynomial in its atoms. -/
theorem pops_arith (Z g p u d B S : ℕ) (hZ : 1 ≤ Z) (hg : g ≤ Z) (hp : p ≤ Z) (hu : u ≤ Z * Z) (hd : d ≤ Z)
    (hB : B ≤ Z) (hS : S ≤ Z) :
    g * (p * ((11 * u + 7) + 1 + ((B + 1 + (18 * d + 3 + 1 + (d * (46 * S + 69 + 4) + 1)) + 1 + (7 * S + 1)) + 1 +
      (3 * u + 1)) + 2) + 1 + 1 + (5 * u + 1 + 1 + 3) + 4) + 1 + 1 + 7 ≤ 256 * (Z * Z * Z * Z) := by
  obtain ⟨Z2, hZ2⟩ : ∃ x, x = Z * Z := ⟨_, rfl⟩
  obtain ⟨Z3, hZ3⟩ : ∃ x, x = Z2 * Z := ⟨_, rfl⟩
  obtain ⟨Z4, hZ4⟩ : ∃ x, x = Z3 * Z := ⟨_, rfl⟩
  have e4 : Z * Z * Z * Z = Z4 := by rw [hZ4, hZ3, hZ2]
  rw [e4]
  rw [← hZ2] at hu
  have l1 : Z ≤ Z2 := by rw [hZ2]; exact Nat.le_mul_of_pos_left Z hZ
  have l2 : Z2 ≤ Z3 := by rw [hZ3]; exact Nat.le_mul_of_pos_right Z2 hZ
  have l3 : Z3 ≤ Z4 := by rw [hZ4]; exact Nat.le_mul_of_pos_right Z3 hZ
  have h1 : d * (46 * S + 69 + 4) ≤ Z * (119 * Z) := Nat.mul_le_mul hd (by omega)
  have e1 : Z * (119 * Z) = 119 * Z2 := by rw [hZ2]; ring
  have h2 : p * ((11 * u + 7) + 1 + ((B + 1 + (18 * d + 3 + 1 + (d * (46 * S + 69 + 4) + 1)) + 1 + (7 * S + 1)) + 1 +
      (3 * u + 1)) + 2) ≤ Z * (200 * Z2) := Nat.mul_le_mul hp (by omega)
  have e2 : Z * (200 * Z2) = 200 * Z3 := by rw [hZ3]; ring
  have h3 : g * (p * ((11 * u + 7) + 1 + ((B + 1 + (18 * d + 3 + 1 + (d * (46 * S + 69 + 4) + 1)) + 1 + (7 * S + 1)) +
      1 + (3 * u + 1)) + 2) + 1 + 1 + (5 * u + 1 + 1 + 3) + 4) ≤ Z * (240 * Z3) := Nat.mul_le_mul hg (by omega)
  have e3 : Z * (240 * Z3) = 240 * Z4 := by rw [hZ4]; ring
  omega

section Call
variable {kclk : ℕ} {Ev : Envelope} {B : TimeBudget kclk Ev} (alg : RepairRepresentation.DecompositionAlgorithm)
  (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)

/-- **The populations' cost** is quartic in `q + cap + 1`. -/
theorem pops_le (Bm Sm q cap : ℕ) (hG : HashPops.hNG alg Cs ≤ q)
    (hc : thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) ≤ q)
    (hd : thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) ≤ q) (hB : Bm ≤ cap) (hS : Sm ≤ cap) :
    HashCell.popsCost alg I hs Cs Bm Sm ≤ 256 * ((q + cap + 1) * (q + cap + 1) * (q + cap + 1) * (q + cap + 1)) := by
  have hp : (HashPops.hPrimes alg I hs Cs).length ≤ q + cap + 1 := by
    have : (HashPops.hPrimes alg I hs Cs).length ≤ thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) + 1 := by
      unfold HashPops.hPrimes PrimThrW.Joins.primesList
      exact (List.length_filter_le _ _).trans (by simp)
    omega
  have hu : (PrimAsm.Data.unaryList (HashPops.hPrimes alg I hs Cs)).length ≤ (q + cap + 1) * (q + cap + 1) :=
    le_trans (FinalPass.ThrSz.primesWord_le _) (Nat.mul_le_mul (by omega) (by omega))
  unfold HashCell.popsCost HashPops.pCost HashPops.cRow
  exact pops_arith (q + cap + 1) _ _ _ _ _ _ (by omega) (by omega) hp hu (by omega) (by omega) (by omega)

end Call

/-- The cell's cost, as a polynomial in its atoms (`U` bounds the capacity scale, `n + 3`, `c_r` and the ports). -/
theorem call_arith (U W n cr wl tC nC pC : ℕ) (hU : 1 ≤ U) (hW : W ≤ U) (hn : n + 3 ≤ U) (hcr : cr ≤ U)
    (hT : tC ≤ U) (hN : nC ≤ U) (hP : pC ≤ 400000 * (U * U * U * U)) :
    HashCell.cellCost W (HashCell.cACost (2 * W + 2) n wl cr) (tC + 1 + nC)
      (HashCell.cBCost (2 * W + 2) + 1 + pC) ≤ 1000000000 * (U * U * U * U) := by
  obtain ⟨U2, hU2⟩ : ∃ x, x = U * U := ⟨_, rfl⟩
  obtain ⟨U4, hU4⟩ : ∃ x, x = U * U * U * U := ⟨_, rfl⟩
  have l1 : U ≤ U2 := by rw [hU2]; exact Nat.le_mul_of_pos_left U hU
  have l2 : U2 ≤ U4 := by
    rw [hU4, hU2]
    calc U * U = U * U * 1 * 1 := by ring
      _ ≤ U * U * U * U := Nat.mul_le_mul (Nat.mul_le_mul_left _ hU) hU
  rw [← hU4] at hP ⊢
  have hsq : UnaryPow.sq (2 * W + 2) = 200 * ((2 * W + 2 + 2) * (2 * W + 2 + 2)) := by unfold UnaryPow.sq; ring
  have hs1 : (2 * W + 2 + 2) * (2 * W + 2 + 2) ≤ (6 * U) * (6 * U) := Nat.mul_le_mul (by omega) (by omega)
  have es : (6 * U) * (6 * U) = 36 * U2 := by rw [hU2]; ring
  have hbl := PrimAsm.CopyNat.natBitLength_le_self_succ n
  have hpw := PrimAsm.CopyNat.two_pow_natBitLength_le n
  have ht1 : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ U * (120 * U) := Nat.mul_le_mul (by omega) (by omega)
  have et : U * (120 * U) = 120 * U2 := by rw [hU2]; ring
  have hst : StarNums.starCost n cr 0 ≤ 400 * U2 + 30 * U := by
    unfold StarNums.starCost
    have : (n + 2) * (n + 2) ≤ U * U := Nat.mul_le_mul (by omega) (by omega)
    have e0 : 400 * (n + 2) * (n + 2) = 400 * ((n + 2) * (n + 2)) := by ring
    rw [hU2]
    omega
  unfold HashCell.cellCost HashCell.cACost HashCell.cBCost SymDec.hACost
  rw [hsq]
  omega

/-- The kept words writer's cost from its size and numbers. -/
theorem wk_arith (Wk : PrimT.C4KW.KWW) (D : PrimT.C4H.HashData) (cap U : ℕ) (hU : 1 ≤ U)
    (hS : PrimT.C4KW.kwS D cap + 1 ≤ 13 * (U * U)) (hT : (PrimT.C4KW.kwT D + 1) ^ Wk.Dg ≤ U) :
    Wk.cost D cap ≤ (170 * Wk.K) * (U * U * U * U) := by
  have h := Wk.cost_le D cap
  have h1 : (PrimT.C4KW.kwS D cap + 1) ^ 2 ≤ (13 * (U * U)) ^ 2 := Nat.pow_le_pow_left hS 2
  have e1 : (13 * (U * U)) ^ 2 = 169 * (U * U * U * U) := by ring
  have hU4 : U ≤ U * U * U * U := by
    calc U = U * 1 * 1 * 1 := by ring
      _ ≤ U * U * U * U := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hU) hU) hU
  have h2 : Wk.K * (PrimT.C4KW.kwS D cap + 1) ^ 2 ≤ Wk.K * (169 * (U * U * U * U)) :=
    Nat.mul_le_mul_left _ (e1 ▸ h1)
  have h3 : Wk.K * (PrimT.C4KW.kwT D + 1) ^ Wk.Dg ≤ Wk.K * (U * U * U * U) := Nat.mul_le_mul_left _ (hT.trans hU4)
  have e2 : 170 * Wk.K * (U * U * U * U) = Wk.K * (169 * (U * U * U * U)) + Wk.K * (U * U * U * U) := by ring
  omega

/-- `K·U⁴` at `U = 2^{⌊n/8⌋ + c_U}` is at rate `7`. -/
theorem ex_U (n cU K X : ℕ) (h : X ≤ K * (2 ^ (n / 8 + cU) * 2 ^ (n / 8 + cU) * 2 ^ (n / 8 + cU) * 2 ^ (n / 8 + cU))) :
    Ex n 7 (Nat.clog 2 K + 4 * cU) X := by
  unfold Ex
  have hK : K ≤ 2 ^ Nat.clog 2 K := Nat.le_pow_clog (by norm_num) K
  have e : 2 ^ (n / 8 + cU) * 2 ^ (n / 8 + cU) * 2 ^ (n / 8 + cU) * 2 ^ (n / 8 + cU) = 2 ^ (4 * (n / 8) + 4 * cU) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [e] at h
  calc X ≤ 2 ^ Nat.clog 2 K * 2 ^ (4 * (n / 8) + 4 * cU) := h.trans (Nat.mul_le_mul_right _ hK)
    _ = 2 ^ (Nat.clog 2 K + (4 * (n / 8) + 4 * cU)) := (pow_add 2 _ _).symm
    _ ≤ 2 ^ (7 * (n / 8) + (Nat.clog 2 K + 4 * cU)) := Nat.pow_le_pow_right (by norm_num) (by omega)

end NearCubicWires.WireExponent3_5.PrimAsm.HashBud
