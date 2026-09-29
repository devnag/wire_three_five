import Proof.Wire_3_5.Primitive.Writers.ShellH4Run

/-! # THRTAIL T-B, part 1: the v4 shell's budget at one master bound

`shell_runH4`'s budget `2·shellCostG w n D C D₂ C₂ cc D_v C_v c₂ m D_L C_L n_U + 2`, bounded at ONE master bound
`Y ≥ 2^m + 1, n + 1, |w|` (playbook): with every exponent `D, D₂, D_v, D_L` below `E - 1` and the data stage's cost
`cc`, the dimension stage's cost `c₂` and the unit budget `n_U` below `K·Y^E`, the budget is at most
`128·K²·Y^E·Y^E` (**`costG_le`**).

Paper quantity of the main type: the THR writer's time within a polynomial of its dimension `2^{m_T}` (P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX

/-- The base coefficient the shell's constants need. -/
def kShell (D C D2 C2 Dv Cv DL CL : ℕ) : ℕ :=
  UnaryCalc.polyCoefficient D2 C2 + UnaryCalc.polyCoefficient Dv Cv + UnaryCalc.polyCoefficient DL CL +
    UnaryCalc.polyCoefficient D C + 4 * C + C2 + CL + 200

/-- **The v4 shell's budget at one master bound.** -/
theorem costG_le (w : List Bool) (n D C D2 C2 cc Dv Cv c2 m DL CL nU Y E K : ℕ)
    (hY : 2 ^ m + 1 ≤ Y) (hn : n + 1 ≤ Y) (hw : w.length ≤ Y)
    (hE : D + 1 ≤ E) (hE2 : D2 + 1 ≤ E) (hEv : Dv + 1 ≤ E) (hEL : DL + 1 ≤ E)
    (hK : kShell D C D2 C2 Dv Cv DL CL ≤ K)
    (hcc : cc ≤ K * Y ^ E) (hc2 : c2 ≤ K * Y ^ E) (hnU : nU ≤ K * Y ^ E) :
    2 * ShellT.shellCostG w n D C D2 C2 cc Dv Cv c2 m DL CL nU + 2 ≤ 128 * (K * K * (Y ^ E * Y ^ E)) := by
  obtain ⟨PY, hPY⟩ : ∃ p, p = Y ^ E := ⟨_, rfl⟩
  rw [← hPY] at hcc hc2 hnU ⊢
  have hY1 : 1 ≤ Y := by omega
  have pw : ∀ a, a ≤ E → Y ^ a ≤ PY := fun a ha => by rw [hPY]; exact Nat.pow_le_pow_right hY1 ha
  have pm : ∀ a, a ≤ E → (2 ^ m + 1) ^ a ≤ PY := fun a ha => le_trans (Nat.pow_le_pow_left hY a) (pw a ha)
  have pn : ∀ a, a ≤ E → (n + 1) ^ a ≤ PY := fun a ha => le_trans (Nat.pow_le_pow_left hn a) (pw a ha)
  have pY : Y ≤ PY := by have := pw 1 (by omega); rwa [pow_one] at this
  have pP1 : 1 ≤ PY := le_trans hY1 pY
  have hK200 : 200 ≤ K := le_trans (by unfold kShell; omega) hK
  -- the request side
  have hbn := CopyNat.natBitLength_le_self_succ n
  have f1 : bootCost w n 0 0 ≤ 200 * PY := by
    have b00 := UnaryCalc.poly_cost_polyBounded 0 0 n
    unfold ValidatorPolynomialDomination.PolyBounded at b00
    have e00 : UnaryCalc.polyCoefficient 0 0 * (n + 1) ^ (0 + 1) = 13 * (n + 1) := by
      simp [UnaryCalc.polyCoefficient]
    have v00 : UnaryCalc.value 0 0 n = 0 := by simp [UnaryCalc.value]
    unfold bootCost
    rw [v00]
    omega
  have f2 : PCPSerializerCapacity.Power.budget D2 C2 n ≤ UnaryCalc.polyCoefficient D2 C2 * PY := by
    have b := UnaryCalc.poly_cost_polyBounded D2 C2 n
    unfold ValidatorPolynomialDomination.PolyBounded at b
    exact le_trans b (Nat.mul_le_mul_left _ (pn _ hE2))
  have f3 : UnaryCalc.value D2 C2 n ≤ C2 * PY := Nat.mul_le_mul_left _ (pn _ (by omega))
  have f5 : PCPSerializerCapacity.Power.budget Dv Cv n ≤ UnaryCalc.polyCoefficient Dv Cv * PY := by
    have b := UnaryCalc.poly_cost_polyBounded Dv Cv n
    unfold ValidatorPolynomialDomination.PolyBounded at b
    exact le_trans b (Nat.mul_le_mul_left _ (pn _ hEv))
  -- the dimension side
  have g1 : capCost m ≤ 92 * PY := ShellT.capCost_le m PY (le_trans hY pY)
  have g2 : PCPSerializerCapacity.Power.budget DL CL (2 ^ m) ≤ UnaryCalc.polyCoefficient DL CL * PY := by
    have b := UnaryCalc.poly_cost_polyBounded DL CL (2 ^ m)
    unfold ValidatorPolynomialDomination.PolyBounded at b
    exact le_trans b (Nat.mul_le_mul_left _ (pm _ hEL))
  have g3 : UnaryCalc.value DL CL (2 ^ m) ≤ CL * PY := Nat.mul_le_mul_left _ (pm _ (by omega))
  have g4 : Scrub.entryCost D C (2 ^ m) ≤ (UnaryCalc.polyCoefficient D C + 4 * C + 12) * PY := by
    have b := PolyBound.entryCost_polyBounded D C (2 ^ m)
    unfold ValidatorPolynomialDomination.PolyBounded at b
    exact le_trans b (Nat.mul_le_mul_left _ (pm _ hE))
  have g5 : UnaryCalc.value D C (2 ^ m) ≤ C * PY := Nat.mul_le_mul_left _ (pm _ (by omega))
  -- everything at `K·PY`
  have eK : (UnaryCalc.polyCoefficient D C + 4 * C + 12) * PY ≤ K * PY := Nat.mul_le_mul_right _ (by unfold kShell at hK; omega)
  have eK2 : UnaryCalc.polyCoefficient D2 C2 * PY ≤ K * PY := Nat.mul_le_mul_right _ (by unfold kShell at hK; omega)
  have eK3 : C2 * PY ≤ K * PY := Nat.mul_le_mul_right _ (by unfold kShell at hK; omega)
  have eK5 : UnaryCalc.polyCoefficient Dv Cv * PY ≤ K * PY := Nat.mul_le_mul_right _ (by unfold kShell at hK; omega)
  have eKL : UnaryCalc.polyCoefficient DL CL * PY ≤ K * PY := Nat.mul_le_mul_right _ (by unfold kShell at hK; omega)
  have eCL : CL * PY ≤ K * PY := Nat.mul_le_mul_right _ (by unfold kShell at hK; omega)
  have eC : C * PY ≤ K * PY := Nat.mul_le_mul_right _ (by unfold kShell at hK; omega)
  have ePY : 200 * PY ≤ K * PY := Nat.mul_le_mul_right _ (by omega)
  -- the loop
  obtain ⟨b, hb⟩ : ∃ r, r = UnaryCalc.value DL CL (2 ^ m) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ r, r = UnaryCalc.value D C (2 ^ m) := ⟨_, rfl⟩
  rw [← hb] at g3
  rw [← hR] at g5
  have hbK : b ≤ K * PY := by omega
  have hin : (2 * nU + 2 + 1 + (2 * R + 4)) + 3 ≤ 14 * (K * PY) := by
    have : 1 ≤ K * PY := le_trans (by omega) (Nat.mul_le_mul hK200 pP1)
    omega
  have hloop : b * ((2 * nU + 2 + 1 + (2 * R + 4)) + 3) ≤ 14 * (K * K * (PY * PY)) := by
    calc b * ((2 * nU + 2 + 1 + (2 * R + 4)) + 3) ≤ (K * PY) * (14 * (K * PY)) := Nat.mul_le_mul hbK hin
      _ = 14 * (K * K * (PY * PY)) := by ring
  have hlin : K * PY ≤ K * K * (PY * PY) := by
    have h1 : 1 ≤ K * PY := le_trans (by omega) (Nat.mul_le_mul hK200 pP1)
    calc K * PY = K * PY * 1 := (mul_one _).symm
      _ ≤ K * PY * (K * PY) := Nat.mul_le_mul_left _ h1
      _ = K * K * (PY * PY) := by ring
  unfold ShellT.shellCostG ShellT.bootXCostG preCost
  rw [← hb, ← hR]
  generalize bootCost w n 0 0 = t1 at f1 ⊢
  generalize PCPSerializerCapacity.Power.budget D2 C2 n = t2 at f2 ⊢
  generalize UnaryCalc.value D2 C2 n = t3 at f3 ⊢
  generalize PCPSerializerCapacity.Power.budget Dv Cv n = t5 at f5 ⊢
  generalize capCost m = u1 at g1 ⊢
  generalize PCPSerializerCapacity.Power.budget DL CL (2 ^ m) = u2 at g2 ⊢
  generalize Scrub.entryCost D C (2 ^ m) = u4 at g4 ⊢
  generalize b * ((2 * nU + 2 + 1 + (2 * R + 4)) + 3) = LL at hloop ⊢
  generalize K * K * (PY * PY) = Z at hloop hlin ⊢
  generalize K * PY = KP at hlin eK eK2 eK3 eK5 eKL eCL eC ePY hbK hcc hc2 hnU
  omega

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
