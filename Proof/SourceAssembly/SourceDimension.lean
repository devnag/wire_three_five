import Proof.SourceAssembly.SourceCleanupClass
import Proof.MachineModel.OrdinaryMatrixUnaryDifference
import Proof.PCP.ProjectionDimensionTemplate

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.Dimension
noncomputable section

/-! ## 1. Zero-head docking -/

/-! ## 2. The local layout -/

/-- First free tape after the `hR` polynomial block: `Rc`'s output. -/
def o1 (hR : ℕ) : ℕ := 64 + 2*hR
/-- `V`'s output. -/
def o2 (hR hV : ℕ) : ℕ := o1 hR + 15 + 2*hV
/-- The local universe. -/
def P (hR hV : ℕ) : ℕ := o2 hR hV + 2

variable (hR hV : ℕ)

theorem P_ge : 66 ≤ P hR hV := by unfold P o2 o1; omega

def aV (i : ℕ) : ℕ := i
def lcV (j : ℕ) : ℕ := if j = 0 then 1 else 2 + j
def cV' (i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then 27 else if i = 2 then 29 else 30
def dV (i : ℕ) : ℕ := if i = 0 then 29 else if i = 1 then 31 else 32
def eV (j : ℕ) : ℕ := if j = 0 then 31 else 32 + j
def fV (i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then 49 else 50
def gV (j : ℕ) : ℕ := if j = 0 then 49 else 50 + j
def hVal (i : ℕ) : ℕ :=
  if i = 0 then 53 + 2*hR else if i = 1 then 45 else if i = 2 then o1 hR else o1 hR + 1
def iV (j : ℕ) : ℕ := if j = 0 then 49 else o1 hR + 1 + j
def jV (i : ℕ) : ℕ :=
  if i = 0 then o1 hR + 4 + 2*hV else if i = 1 then 45 else if i = 2 then o2 hR hV else o2 hR hV + 1

/-- Unfold the layout values and close an index (in)equality. -/
macro "lay" : tactic => `(tactic| (
  simp only [aV, lcV, cV', dV, eV, fV, gV, hVal, iV, jV, o1, o2, P,
    BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at *
  try split_ifs at *
  all_goals omega))

def aSl : Fin 3 → Fin (P hR hV) := fun i => ⟨aV i.val, by have := i.isLt; lay⟩
def lcSl : Fin 27 → Fin (P hR hV) := fun j => ⟨lcV j.val, by have := j.isLt; lay⟩
def cSl : Fin 4 → Fin (P hR hV) := fun i => ⟨cV' i.val, by have := i.isLt; lay⟩
def dSl : Fin 3 → Fin (P hR hV) := fun i => ⟨dV i.val, by have := i.isLt; lay⟩
def eSl : Fin 17 → Fin (P hR hV) := fun j => ⟨eV j.val, by have := j.isLt; lay⟩
def fSl : Fin 3 → Fin (P hR hV) := fun i => ⟨fV i.val, by have := i.isLt; lay⟩
def gSl : Fin (BlockPlatform.UnaryCalc.tapes hR) → Fin (P hR hV) :=
  fun j => ⟨gV j.val, by have := j.isLt; lay⟩
def hSl : Fin 4 → Fin (P hR hV) := fun i => ⟨hVal hR i.val, by have := i.isLt; lay⟩
def iSl : Fin (BlockPlatform.UnaryCalc.tapes hV) → Fin (P hR hV) :=
  fun j => ⟨iV hR j.val, by have := j.isLt; lay⟩
def jSl : Fin 4 → Fin (P hR hV) := fun i => ⟨jV hR hV i.val, by have := i.isLt; lay⟩

macro "injv" : tactic => `(tactic| (
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [aSl, lcSl, cSl, dSl, eSl, fSl, gSl, hSl, iSl, jSl] at hv
  apply Fin.ext
  lay))


/-! ## 3. The machine and its cost -/

/-- The cheap prefix: stages A-G and I (all `poly(q)` or `O(q·2^(q-K))`). -/
def prefixMachine (L C cVc : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine (aSl hR hV) (UWalkUnary.machine true false))
    (RecoveryFocus.machine (lcSl hR hV) (PCJ6e421fabe2aa4155_SourceLiveCount.machine L)))
    (RecoveryFocus.machine (cSl hR hV) MatrixUnaryDifference.resetMachine))
    (RecoveryFocus.machine (dSl hR hV) (UWalkUnary.machine false false)))
    (RecoveryFocus.machine (eSl hR hV) RepairSource.CloseoutCapacity.Power.machine))
    (RecoveryFocus.machine (fSl hR hV) (UWalkUnary.machine false false)))
    (RecoveryFocus.machine (gSl hR hV) (PCPSerializerCapacity.Power.machine hR C)))
    (RecoveryFocus.machine (iSl hR hV) (PCPSerializerCapacity.Power.machine hV cVc))

/-- The whole pipeline: the cheap prefix, then the two exact products H (`Rc`) and J (`V`). -/
def machine (L C cVc : ℕ) :=
  Composition.machine (Composition.machine (prefixMachine hR hV L C cVc)
    (RecoveryFocus.machine (hSl hR hV) ClockUnaryProduct.machine))
    (RecoveryFocus.machine (jSl hR hV) ClockUnaryProduct.machine)

/-- The residual `q - K`. -/
abbrev res (L q : ℕ) : ℕ := q - normalizedLiveCount q L

/-- The prefix's cost: every stage but the two final products. -/
def prefixCost (L C cVc q : ℕ) : ℕ :=
  let r := res L q
  (((((((2*q+6)+1+PCJ6e421fabe2aa4155_SourceLiveCount.budget q L)+1+(2*q+8))+1+(2*r+6))+1+
    RepairSource.CloseoutCapacity.Power.budget r)+1+(2*q+6))+1+PCPSerializerCapacity.Power.budget hR C q)+1+
    PCPSerializerCapacity.Power.budget hV cVc q

def cost (L C cVc q : ℕ) : ℕ :=
  let r := res L q
  (prefixCost hR hV L C cVc q+1+(2*((C*(q+1)^hR)*(2*2^r+3)+2)+2))+1+
    (2*((cVc*(q+1)^hV)*(2*2^r+3)+2)+2)

/-! ## 4. The ten stages, each an exact `Step` on its own tapes (heads `0` in and out) -/

/-! ## 5. Bookkeeping: where each stage writes -/

macro "slv" : tactic => `(tactic| (
  intro j
  have hj := j.isLt
  simp only [aSl, lcSl, cSl, dSl, eSl, fSl, gSl, hSl, iSl, jSl] at *
  lay))



/-! ## 6. The named outputs -/

def pR : Fin (P hR hV) := ⟨o1 hR, by unfold P o2; omega⟩
def pV : Fin (P hR hV) := ⟨o2 hR hV, by unfold P; omega⟩

/-! ## 7. The pipeline run -/

/-! ## 8. Budget class, and the erasure condition -/

theorem liveCount_poly (q L : ℕ) :
    PCJ6e421fabe2aa4155_SourceLiveCount.budget q L ≤ (400 + 20*L) * (q+1)^2 := by
  simp only [PCJ6e421fabe2aa4155_SourceLiveCount.budget, PCJ6e421fabe2aa4155_SourceLog.budget,
    RepairSource.CloseoutSchedule.Clog.budget]
  have hlg := SourceConstruction.logScale_le q
  have hK := normalizedLiveCount_le q L
  have hm : L * logScale q ≤ L * (q+1) := Nat.mul_le_mul_left L hlg
  have hq : q + 1 ≤ (q+1)^2 := Nat.le_self_pow (by decide) _
  have hLq : L * (q+1) ≤ L * (q+1)^2 := Nat.mul_le_mul_left L hq
  have hL : L ≤ L * (q+1)^2 := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos q))
  have e : q + 2 - 1 = q + 1 := by omega
  rw [e]
  have e2 : (400 + 20*L) * (q+1)^2 = 400*(q+1)^2 + 20*(L*(q+1)^2) := by ring
  have e3 : L * (2 * logScale q + 3) = 2*(L*logScale q) + 3*L := by ring
  rw [e2, e3]
  have e4 : (q+1)^2 = q*q + 2*q + 1 := by ring
  rw [e4] at hq hLq hL ⊢
  nlinarith

/-- The prefix cost in two pieces: a polynomial of degree `hR+1` and ONE table `(q+1)·2^(q-K)`. -/
theorem prefixCost_split (L C cVc q : ℕ) (h2 : 2 ≤ hR) (hVR : hV + 1 ≤ hR) :
    q + 3 + prefixCost hR hV L C cVc q ≤
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc) * (q+1)^(hR+1) +
      300 * ((q+1) * 2^(q - normalizedLiveCount q L)) := by
  have hlc := liveCount_poly q L
  have hpw := SourceConstruction.power_class L q
  simp only [RuntimeShape.tableClass, pow_one] at hpw
  have hpR := BlockPlatform.UnaryCalc.poly_cost_polyBounded hR C q
  have hpV := BlockPlatform.UnaryCalc.poly_cost_polyBounded hV cVc q
  unfold ValidatorPolynomialDomination.PolyBounded at hpR hpV
  have hK := normalizedLiveCount_le q L
  have y1 : q + 1 ≤ (q+1)^(hR+1) := Nat.le_self_pow (by omega) _
  have y2 : (q+1)^2 ≤ (q+1)^(hR+1) := Nat.pow_le_pow_right (Nat.succ_pos q) (by omega)
  have yV : (q+1)^(hV+1) ≤ (q+1)^(hR+1) := Nat.pow_le_pow_right (Nat.succ_pos q) (by omega)
  have m2 := Nat.mul_le_mul_left (400 + 20*L) y2
  have mV := Nat.mul_le_mul_left (BlockPlatform.UnaryCalc.polyCoefficient hV cVc) yV
  have m1 := Nat.mul_le_mul_left 50 y1
  have e : (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc) * (q+1)^(hR+1) =
      50*(q+1)^(hR+1) + (400 + 20*L)*(q+1)^(hR+1) +
      BlockPlatform.UnaryCalc.polyCoefficient hR C * (q+1)^(hR+1) +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc * (q+1)^(hR+1) := by ring
  dsimp only [prefixCost, res]
  rw [e]
  omega

/-- **Once, table class.** The whole pipeline costs `≤ c·tableClass L (hR+1) q` whenever
`hV < hR`, `2 ≤ hR`; the coefficient is explicit and `L`-free in its exponent. -/
theorem cost_class (L C cVc q : ℕ) (h2 : 2 ≤ hR) (hVR : hV + 1 ≤ hR) :
    cost hR hV L C cVc q ≤
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2) *
        RuntimeShape.tableClass L (hR+1) q := by
  have hs := prefixCost_split hR hV L C cVc q h2 hVR
  set T := RuntimeShape.tableClass L (hR+1) q with hTd
  have hT1 : 1 ≤ 2^(q - normalizedLiveCount q L) := Nat.one_le_two_pow
  have hpow : (q+1)^(hR+1) ≤ T := Nat.le_mul_of_pos_right _ hT1
  have htab : (q+1)*2^(q - normalizedLiveCount q L) ≤ T := by
    have : (q+1) ≤ (q+1)^(hR+1) := Nat.le_self_pow (by omega) _
    exact Nat.mul_le_mul_right _ this
  have hR' : (q+1)^hR*2^(q - normalizedLiveCount q L) ≤ T :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos q) (by omega))
  have hV' : (q+1)^hV*2^(q - normalizedLiveCount q L) ≤ T :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos q) (by omega))
  have hone : 1 ≤ T := SourceConstruction.one_le_tableClass L (hR+1) q
  have pH : 2*((C*(q+1)^hR)*(2*2^(q - normalizedLiveCount q L)+3)+2)+2 ≤ (10*C+6)*T := by
    have hd : C*(q+1)^hR*2^(q - normalizedLiveCount q L) ≤ C*T := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hR'
    have hd' : C*(q+1)^hR ≤ C*T := by
      calc C*(q+1)^hR ≤ C*((q+1)^hR*2^(q - normalizedLiveCount q L)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hT1)
        _ ≤ C*T := Nat.mul_le_mul_left _ hR'
    have e : 2*((C*(q+1)^hR)*(2*2^(q - normalizedLiveCount q L)+3)+2)+2 =
        4*(C*(q+1)^hR*2^(q - normalizedLiveCount q L)) + 6*(C*(q+1)^hR) + 6 := by ring
    have e2 : (10*C+6)*T = 10*(C*T) + 6*T := by ring
    rw [e, e2]
    omega
  have pJ : 2*((cVc*(q+1)^hV)*(2*2^(q - normalizedLiveCount q L)+3)+2)+2 ≤ (10*cVc+6)*T := by
    have hd : cVc*(q+1)^hV*2^(q - normalizedLiveCount q L) ≤ cVc*T := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hV'
    have hd' : cVc*(q+1)^hV ≤ cVc*T := by
      calc cVc*(q+1)^hV ≤ cVc*((q+1)^hV*2^(q - normalizedLiveCount q L)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hT1)
        _ ≤ cVc*T := Nat.mul_le_mul_left _ hV'
    have e : 2*((cVc*(q+1)^hV)*(2*2^(q - normalizedLiveCount q L)+3)+2)+2 =
        4*(cVc*(q+1)^hV*2^(q - normalizedLiveCount q L)) + 6*(cVc*(q+1)^hV) + 6 := by ring
    have e2 : (10*cVc+6)*T = 10*(cVc*T) + 6*T := by ring
    rw [e, e2]
    omega
  have m1 := Nat.mul_le_mul_left (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc) hpow
  have m2 := Nat.mul_le_mul_left 300 htab
  have e : (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2) * T =
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc) * T + 300*T + (10*C+6)*T + (10*cVc+6)*T + 2*T := by
    ring
  dsimp only [cost, res]
  rw [e]
  omega

end
end NearCubicWires.SourceConstruction.Dimension
end
