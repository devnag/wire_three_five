import Proof.Wire_3_5.Primitive.Writers.ShellTRun
import Proof.Wire_3_5.Primitive.Writers.NumsXT
import Proof.MachineModel.BlockPolyBound

/-! # for THR: the THR writer shell, v2 (`PrimThrW.Shell2.ThrShellX2`)

P3:2621-2623 (row:radix: a RADIX row prints `2^{Θ(L²)}` terms) and THR's `ThrShellX2`: the THR writer shell
dimensioned by `n' = 2^{mOfT KL P}`, `mOfT KL P = mOf P + KL·L²`. The run is `ShellTRun.shell_runG` (ONE proof, generic
in the dimension stage, build-once) at the THR dimension stage `NumsXT.numsMT KL cr`:

* **`dimOK_numsT`**: `numsMT KL cr` meets `ShellTBoot.DimOK` at `mOfT KL P` (ShellX's `x2_step` with `nums_stepT`);
* `costT` (the budget `2·shellCostG + 2` with the per-unit budget capped at the scrub `R`, `shellCostG_len`), `EcT`,
  `KcT`, **`costT_le`** (the budget is `Kc(|w|+n+cc+2)^Ec + Kc(2^m+1)^Ec + b·(2nU + 2R + 10)`);
* **`thrShellX2 : ThrShellX2 S x U D C D2 C2 Dv Cv cr DL CL KL`** (THR's structure: the stage, the cost with its
  bound, and the run).

Paper quantity of the main type: the THR writer's output tape `(List.range b).flatMap emit ++ [false]` at the dimension
`2^{mOf P + KL·L²}` (lem:primitive P3:3068-3084). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires.WireExponent3_5.PrimAsm.ShellX NearCubicWires.SupplierPipeline

section Dim

end Dim

/-! ## The budget -/

/-- `shellCostG` reads the request word only through its length. -/
theorem shellCostG_len (w : List Bool) (n D C D2 C2 cc Dv Cv c2 m DL CL nU : ℕ) :
    shellCostG w n D C D2 C2 cc Dv Cv c2 m DL CL nU =
      shellCostG (List.replicate w.length false) n D C D2 C2 cc Dv Cv c2 m DL CL nU := by
  simp [shellCostG, bootXCostG, preCost, bootCost]

/-- **The v2 shell's budget**: `2·shellCostG + 2` at the request length, with the per-unit budget capped at the scrub
capacity `R = C(2^m+1)^D` (the run has `nU + 1 ≤ R`, so it is the run's budget there). -/
def costT (D C D2 C2 Dv Cv cr DL CL KL : ℕ) (lw n cc nU m : ℕ) : ℕ :=
  2 * shellCostG (List.replicate lw false) n D C D2 C2 cc Dv Cv
    (2 * NumsXT.numsStageCostT n cr KL (UnaryCalc.value Dv Cv n) + 2) m DL CL
    (min nU (UnaryCalc.value D C (2 ^ m))) + 2

/-- The budget's exponent. -/
def EcT (D D2 Dv DL : ℕ) : ℕ := D + D2 + 3 * Dv + DL + 4

/-- The request-side coefficient. -/
def KAT (C2 D2 Cv Dv cr KL : ℕ) : ℕ :=
  2 * (100 + UnaryCalc.polyCoefficient D2 C2 + (2 * C2 + 6) + 2 + UnaryCalc.polyCoefficient Dv Cv +
    (22 * Cv + 6000 + 480 * KL + 1600 * ((2 * Cv + 4) * (2 * Cv + 4)) + 60 * cr)) + 60

/-- The dimension-side coefficient. -/
def KBT (D C DL CL : ℕ) : ℕ :=
  2 * (92 + UnaryCalc.polyCoefficient DL CL + (2 * CL + 3) + (UnaryCalc.polyCoefficient D C + 4 * C + 12)) +
    (4 * C * CL + 10 * CL) + 40

/-- The budget's coefficient. -/
def KcT (D C D2 C2 Dv Cv cr DL CL KL : ℕ) : ℕ := KAT C2 D2 Cv Dv cr KL + KBT D C DL CL

theorem capCost_le (m PY : ℕ) (h : 2 ^ m + 1 ≤ PY) : capCost m ≤ 92 * PY := by
  have := Nat.lt_two_pow_self (n := m)
  unfold capCost
  generalize 2 ^ m = T at h this ⊢
  omega

/-- **The v2 budget's bound** (`ThrShellX2.cost_le`): polynomial in the request side `|w| + n + cc` and in the
dimension `2^m`, plus the loop's `b·(2nU + 2R + 10)`. -/
theorem costT_le (D C D2 C2 Dv Cv cr DL CL KL : ℕ) (lw n cc nU m : ℕ) :
    costT D C D2 C2 Dv Cv cr DL CL KL lw n cc nU m ≤
      KcT D C D2 C2 Dv Cv cr DL CL KL * (lw + n + cc + 2) ^ EcT D D2 Dv DL +
      KcT D C D2 C2 Dv Cv cr DL CL KL * (2 ^ m + 1) ^ EcT D D2 Dv DL +
      UnaryCalc.value DL CL (2 ^ m) * (2 * nU + 2 * UnaryCalc.value D C (2 ^ m) + 10) := by
  obtain ⟨E, hE⟩ : ∃ e, e = EcT D D2 Dv DL := ⟨_, rfl⟩
  have hE4 : D + D2 + 3 * Dv + DL + 4 = E := by rw [hE]; rfl
  obtain ⟨PX, hPX⟩ : ∃ p, p = (lw + n + cc + 2) ^ E := ⟨_, rfl⟩
  obtain ⟨PY, hPY⟩ : ∃ p, p = (2 ^ m + 1) ^ E := ⟨_, rfl⟩
  rw [← hE, ← hPX, ← hPY]
  have hX1 : 1 ≤ lw + n + cc + 2 := by omega
  have pw : ∀ d, d ≤ E → (n + 1) ^ d ≤ PX := fun d hd => by
    rw [hPX]; exact le_trans (Nat.pow_le_pow_left (by omega) d) (Nat.pow_le_pow_right hX1 hd)
  have pX : lw + n + cc + 2 ≤ PX := by
    rw [hPX]
    calc lw + n + cc + 2 = (lw + n + cc + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hX1 (by omega)
  have pX1 : 1 ≤ PX := by rw [hPX]; exact Nat.one_le_pow _ _ (by omega)
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hY1 : 1 ≤ 2 ^ m + 1 := by omega
  have pY : ∀ d, d ≤ E → (2 ^ m + 1) ^ d ≤ PY := fun d hd => by
    rw [hPY]; exact Nat.pow_le_pow_right hY1 hd
  have pYY : 2 ^ m + 1 ≤ PY := by
    have := pY 1 (by omega); rwa [pow_one] at this
  have pY1 : 1 ≤ PY := by rw [hPY]; exact Nat.one_le_pow _ _ (by omega)
  have hm2 : m + 1 ≤ 2 ^ m + 1 := by have := Nat.lt_two_pow_self (n := m); omega
  clear hPX hPY
  -- the request side
  have hbn := CopyNat.natBitLength_le_self_succ n
  have hpw := CopyNat.two_pow_natBitLength_le n
  have Q : (n + 1) * (n + 1) ≤ PX := by have := pw 2 (by omega); rwa [sq] at this
  have f1 : bootCost (List.replicate lw false) n 0 0 ≤ 100 * PX := by
    have b00 := UnaryCalc.poly_cost_polyBounded 0 0 n
    unfold ValidatorPolynomialDomination.PolyBounded at b00
    have e00 : UnaryCalc.polyCoefficient 0 0 * (n + 1) ^ (0 + 1) = 13 * (n + 1) := by
      simp [UnaryCalc.polyCoefficient]
    have v00 : UnaryCalc.value 0 0 n = 0 := by simp [UnaryCalc.value]
    unfold bootCost
    rw [v00, List.length_replicate]
    omega
  have f2 : PCPSerializerCapacity.Power.budget D2 C2 n ≤ UnaryCalc.polyCoefficient D2 C2 * PX := by
    have b := UnaryCalc.poly_cost_polyBounded D2 C2 n
    unfold ValidatorPolynomialDomination.PolyBounded at b
    exact le_trans b (Nat.mul_le_mul_left _ (pw _ (by omega)))
  have f3 : UnaryCalc.value D2 C2 n ≤ C2 * PX := Nat.mul_le_mul_left _ (pw _ (by omega))
  have f5 : PCPSerializerCapacity.Power.budget Dv Cv n ≤ UnaryCalc.polyCoefficient Dv Cv * PX := by
    have b := UnaryCalc.poly_cost_polyBounded Dv Cv n
    unfold ValidatorPolynomialDomination.PolyBounded at b
    exact le_trans b (Nat.mul_le_mul_left _ (pw _ (by omega)))
  have fW : UnaryCalc.value Dv Cv n ≤ Cv * PX := Nat.mul_le_mul_left _ (pw _ (by omega))
  have fS : (2 * UnaryCalc.value Dv Cv n + 2 + 2) * (2 * UnaryCalc.value Dv Cv n + 2 + 2) ≤
      (2 * Cv + 4) * (2 * Cv + 4) * PX := by
    have p1 : 1 ≤ (n + 1) ^ Dv := Nat.one_le_pow _ _ (by omega)
    have h1 : 2 * UnaryCalc.value Dv Cv n + 2 + 2 ≤ (2 * Cv + 4) * (n + 1) ^ Dv := by
      unfold UnaryCalc.value
      have : (2 * Cv + 4) * (n + 1) ^ Dv = 2 * (Cv * (n + 1) ^ Dv) + 4 * (n + 1) ^ Dv := by ring
      omega
    have h2 := Nat.mul_le_mul h1 h1
    have h3 : (2 * Cv + 4) * (n + 1) ^ Dv * ((2 * Cv + 4) * (n + 1) ^ Dv) =
        (2 * Cv + 4) * (2 * Cv + 4) * (n + 1) ^ (Dv + Dv) := by rw [pow_add]; ring
    have h4 := Nat.mul_le_mul_left ((2 * Cv + 4) * (2 * Cv + 4)) (pw (Dv + Dv) (by omega))
    omega
  have fK : KL * (n + 2) * (n + 2) ≤ 4 * (KL * PX) := by
    have h1 : (n + 2) * (n + 2) ≤ 4 * ((n + 1) * (n + 1)) := by nlinarith
    have h2 : KL * (n + 2) * (n + 2) ≤ KL * (4 * ((n + 1) * (n + 1))) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h1
    have h3 : KL * (4 * ((n + 1) * (n + 1))) ≤ KL * (4 * PX) := Nat.mul_le_mul_left _ (by omega)
    have h4 : KL * (4 * PX) = 4 * (KL * PX) := by ring
    omega
  have fB : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 360 * ((n + 1) * (n + 1)) := by
    have := Nat.mul_le_mul (show natBitLength n + 2 ≤ 3 * (n + 1) by omega)
      (show 40 * 2 ^ natBitLength n + 40 ≤ 120 * (n + 1) by omega)
    have e : 3 * (n + 1) * (120 * (n + 1)) = 360 * ((n + 1) * (n + 1)) := by ring
    omega
  have fN : (n + 2) * (n + 2) ≤ 4 * ((n + 1) * (n + 1)) := by nlinarith
  have fcr : cr ≤ cr * PX := Nat.le_mul_of_pos_right _ pX1
  have f6 : 2 * NumsXT.numsStageCostT n cr KL (UnaryCalc.value Dv Cv n) + 2 ≤
      22 * (Cv * PX) + 6000 * PX + 480 * (KL * PX) + 1600 * ((2 * Cv + 4) * (2 * Cv + 4) * PX) + 60 * (cr * PX) := by
    unfold NumsXT.numsStageCostT NumsXT.numsCostT NumsX.numsCost StarNums.starCost UnaryPow.sq
    have e1 : 400 * (n + 2) * (n + 2) = 400 * ((n + 2) * (n + 2)) := by ring
    have e2 : 200 * (2 * UnaryCalc.value Dv Cv n + 2 + 2) * (2 * UnaryCalc.value Dv Cv n + 2 + 2) =
        200 * ((2 * UnaryCalc.value Dv Cv n + 2 + 2) * (2 * UnaryCalc.value Dv Cv n + 2 + 2)) := by ring
    have e3 : 25 * 0 * (n + 2) = 0 := by ring
    rw [e1, e2, e3]
    generalize (2 * UnaryCalc.value Dv Cv n + 2 + 2) * (2 * UnaryCalc.value Dv Cv n + 2 + 2) = sW at fS ⊢
    generalize UnaryCalc.value Dv Cv n = W at fW ⊢
    generalize (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) = nb at fB ⊢
    generalize (n + 2) * (n + 2) = n2 at fN ⊢
    generalize (n + 1) * (n + 1) = n1 at Q fB fN ⊢
    generalize KL * (n + 2) * (n + 2) = kn at fK ⊢
    generalize (2 * Cv + 4) * (2 * Cv + 4) * PX = sP at fS ⊢
    omega
  clear fS fK fB fN fcr fW Q hbn hpw
  -- the dimension side
  have g1 : capCost m ≤ 92 * PY := capCost_le m PY pYY
  have g2 : PCPSerializerCapacity.Power.budget DL CL (2 ^ m) ≤ UnaryCalc.polyCoefficient DL CL * PY := by
    have b := UnaryCalc.poly_cost_polyBounded DL CL (2 ^ m)
    unfold ValidatorPolynomialDomination.PolyBounded at b
    exact le_trans b (Nat.mul_le_mul_left _ (pY _ (by omega)))
  have g3 : UnaryCalc.value DL CL (2 ^ m) ≤ CL * PY := Nat.mul_le_mul_left _ (pY _ (by omega))
  have g4 : Scrub.entryCost D C (2 ^ m) ≤ UnaryCalc.polyCoefficient D C * PY + 4 * (C * PY) + 12 * PY := by
    have b := PolyBound.entryCost_polyBounded D C (2 ^ m)
    unfold ValidatorPolynomialDomination.PolyBounded at b
    have h := le_trans b (Nat.mul_le_mul_left (UnaryCalc.polyCoefficient D C + 4 * C + 12) (pY (D + 1) (by omega)))
    have e : (UnaryCalc.polyCoefficient D C + 4 * C + 12) * PY =
        UnaryCalc.polyCoefficient D C * PY + 4 * (C * PY) + 12 * PY := by ring
    omega
  have g5 : UnaryCalc.value DL CL (2 ^ m) * (4 * UnaryCalc.value D C (2 ^ m) + 10) ≤
      4 * (C * CL * PY) + 10 * (CL * PY) := by
    unfold UnaryCalc.value
    have h1 : CL * (2 ^ m + 1) ^ DL * (4 * (C * (2 ^ m + 1) ^ D) + 10) =
        4 * (C * CL * (2 ^ m + 1) ^ (DL + D)) + 10 * (CL * (2 ^ m + 1) ^ DL) := by rw [pow_add]; ring
    have h2 := Nat.mul_le_mul_left (C * CL) (pY (DL + D) (by omega))
    have h3 := Nat.mul_le_mul_left CL (pY DL (by omega))
    generalize (2 ^ m + 1) ^ (DL + D) = y1 at h1 h2
    generalize (2 ^ m + 1) ^ DL = y2 at h1 h3
    generalize (2 ^ m + 1) ^ D = y3 at h1
    omega
  -- the loop
  unfold costT shellCostG bootXCostG preCost
  obtain ⟨R, hR⟩ : ∃ r, r = UnaryCalc.value D C (2 ^ m) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ r, r = UnaryCalc.value DL CL (2 ^ m) := ⟨_, rfl⟩
  rw [← hR] at g5 ⊢
  rw [← hb] at g3 g5 ⊢
  have hmin1 : min nU R ≤ nU := min_le_left _ _
  have hmin2 : min nU R ≤ R := min_le_right _ _
  have hl1 : 2 * ((2 * min nU R + 2 + 1 + (2 * R + 4)) + 3) ≤ (2 * nU + 2 * R + 10) + (4 * R + 10) := by omega
  have hl2 := Nat.mul_le_mul_left b hl1
  have hl3 : b * (2 * ((2 * min nU R + 2 + 1 + (2 * R + 4)) + 3)) =
      2 * (b * ((2 * min nU R + 2 + 1 + (2 * R + 4)) + 3)) := by ring
  have hl4 : b * ((2 * nU + 2 * R + 10) + (4 * R + 10)) = b * (2 * nU + 2 * R + 10) + b * (4 * R + 10) := by ring
  -- the coefficients
  have eA : KAT C2 D2 Cv Dv cr KL * PX = 2 * (100 * PX + UnaryCalc.polyCoefficient D2 C2 * PX +
      (2 * (C2 * PX) + 6 * PX) + 2 * PX + UnaryCalc.polyCoefficient Dv Cv * PX + (22 * (Cv * PX) + 6000 * PX +
      480 * (KL * PX) + 1600 * ((2 * Cv + 4) * (2 * Cv + 4) * PX) + 60 * (cr * PX))) + 60 * PX := by
    unfold KAT; ring
  have eB : KBT D C DL CL * PY = 2 * (92 * PY + UnaryCalc.polyCoefficient DL CL * PY + (2 * (CL * PY) + 3 * PY) +
      (UnaryCalc.polyCoefficient D C * PY + 4 * (C * PY) + 12 * PY)) + (4 * (C * CL * PY) + 10 * (CL * PY)) +
      40 * PY := by
    unfold KBT; ring
  have eK1 : KcT D C D2 C2 Dv Cv cr DL CL KL * PX = KAT C2 D2 Cv Dv cr KL * PX + KBT D C DL CL * PX := by
    unfold KcT; ring
  have eK2 : KcT D C D2 C2 Dv Cv cr DL CL KL * PY = KAT C2 D2 Cv Dv cr KL * PY + KBT D C DL CL * PY := by
    unfold KcT; ring
  generalize bootCost (List.replicate lw false) n 0 0 = t1 at f1 ⊢
  generalize PCPSerializerCapacity.Power.budget D2 C2 n = t2 at f2 ⊢
  generalize UnaryCalc.value D2 C2 n = t3 at f3 ⊢
  generalize PCPSerializerCapacity.Power.budget Dv Cv n = t5 at f5 ⊢
  generalize NumsXT.numsStageCostT n cr KL (UnaryCalc.value Dv Cv n) = t6 at f6 ⊢
  generalize capCost m = u1 at g1 ⊢
  generalize PCPSerializerCapacity.Power.budget DL CL (2 ^ m) = u2 at g2 ⊢
  generalize Scrub.entryCost D C (2 ^ m) = u4 at g4 ⊢
  generalize b * ((2 * min nU R + 2 + 1 + (2 * R + 4)) + 3) = L1 at hl3 ⊢
  generalize b * (2 * ((2 * min nU R + 2 + 1 + (2 * R + 4)) + 3)) = L2 at hl2 hl3
  generalize b * ((2 * nU + 2 * R + 10) + (4 * R + 10)) = L3 at hl2 hl4
  generalize b * (2 * nU + 2 * R + 10) = L4 at hl4 ⊢
  generalize b * (4 * R + 10) = L5 at hl4 g5
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
