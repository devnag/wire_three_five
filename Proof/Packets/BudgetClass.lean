import Proof.Packets.BudgetCycFuel
import Proof.Packets.BudgetFamilyAt

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape
noncomputable section

theorem exactWord_pos {q : ℕ} (g : ExactThresholdGate q) : 1 ≤ (exactWord g).length := by
  unfold exactWord intWord
  simp only [List.length_append, List.length_cons]
  omega

/-- A gate list is no longer than its word. -/
theorem gs_le_word {q : ℕ} (gs : List (ExactThresholdGate q)) : gs.length ≤ (exactListWord gs).length := by
  have h : gs.length ≤ (gs.flatMap exactWord).length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := exactWord_pos g
      omega
  unfold exactListWord
  simp only [List.length_append]
  omega

/-- **The cold cache of an admitted request is small class**, from POOL-8's polynomial `hcold`, AD's radix bound and one
`small_poly` fact. -/
theorem cold_small (a : DecompositionAlgorithm) {den degree target : ℕ} (hden : 1 ≤ den) (r : Request)
    (hr : RequestAdmitted den degree target r) (cc dc : ℕ)
    (hcold : ∀ (q : ℕ) (x : BinaryCacheColdJoin.Args q), BinaryCacheColdRun.budget x ≤
      cc * ((exactListWord x.gs).length + x.gs.length + q + 2^x.live.card + 1)^dc)
    (m sC sE : ℕ) (hsm : (r.smallSize a)^((betaE a degree + 1)*dc) ≤ sC*smallClass m sE r.q) :
    BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) ≤
      (cc*(2*betaC a degree + 2)^dc*2^((betaE a degree + 1)*dc)*sC) * smallClass m sE r.q := by
  set Lw := (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length with hLw
  have h0 := hcold r.q (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a))
  have hrad0 := RequestAdmitted.radix_le hden a r hr
  have hrad : Lw + 1 ≤ betaPoly a degree r.q := hrad0
  have hbeta := betaPoly_le a degree r.q
  have hgs := gs_le_word (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs
  -- `q`, `2^K` and `1` are summands of `smallSize`
  have hq_le : r.q ≤ r.smallSize a := by
    have key : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℕ, x1 ≤ x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + 1 := by
      intros; omega
    unfold Request.smallSize
    exact key _ _ _ _ _ _ _ _
  have hK_le : 2^(PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).live.card ≤ r.smallSize a := by
    have key : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℕ, x3 ≤ x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + 1 := by
      intros; omega
    unfold Request.smallSize
    exact key _ _ _ _ _ _ _ _
  have hS1 : 1 ≤ r.smallSize a := by
    have key : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℕ, 1 ≤ x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + 1 := by
      intros; omega
    unfold Request.smallSize
    exact key _ _ _ _ _ _ _ _
  -- `q+1 ≤ (r.smallSize a)+1`
  have hqS : (r.q+1)^betaE a degree ≤ ((r.smallSize a)+1)^betaE a degree := Nat.pow_le_pow_left (by omega) _
  have hX : Lw + (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs.length + r.q +
      2^(PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).live.card + 1 ≤
      (2*betaC a degree + 2)*((r.smallSize a)+1)^(betaE a degree + 1) := by
    have h1 : ((r.smallSize a)+1)^betaE a degree ≤ ((r.smallSize a)+1)^(betaE a degree + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (r.smallSize a) + 1 ≤ ((r.smallSize a)+1)^(betaE a degree + 1) := Nat.le_self_pow (by omega) _
    have h3 : betaC a degree * (r.q+1)^betaE a degree ≤ betaC a degree * ((r.smallSize a)+1)^(betaE a degree + 1) :=
      Nat.mul_le_mul_left _ (hqS.trans h1)
    have e : (2*betaC a degree + 2)*((r.smallSize a)+1)^(betaE a degree + 1) =
        2*(betaC a degree * ((r.smallSize a)+1)^(betaE a degree + 1)) + 2*((r.smallSize a)+1)^(betaE a degree + 1) := by ring
    generalize 2^(PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).live.card = t at hK_le ⊢
    omega
  have hpow : ((r.smallSize a)+1)^((betaE a degree + 1)*dc) ≤ 2^((betaE a degree + 1)*dc) * (r.smallSize a)^((betaE a degree + 1)*dc) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  calc BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a))
      ≤ cc * (Lw + (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs.length + r.q +
          2^(PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).live.card + 1)^dc := h0
    _ ≤ cc * ((2*betaC a degree + 2)*((r.smallSize a)+1)^(betaE a degree + 1))^dc := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX dc)
    _ = cc*(2*betaC a degree + 2)^dc * ((r.smallSize a)+1)^((betaE a degree + 1)*dc) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ cc*(2*betaC a degree + 2)^dc * (2^((betaE a degree + 1)*dc) * (r.smallSize a)^((betaE a degree + 1)*dc)) :=
        Nat.mul_le_mul_left _ hpow
    _ ≤ cc*(2*betaC a degree + 2)^dc * (2^((betaE a degree + 1)*dc) * (sC*smallClass m sE r.q)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsm)
    _ = (cc*(2*betaC a degree + 2)^dc*2^((betaE a degree + 1)*dc)*sC) * smallClass m sE r.q := by ring

/-- **`cycFuel_inClasses`'s `hcold`** (small class, any `dP hT n`). -/
theorem cold_inClasses (a : DecompositionAlgorithm) {den degree target : ℕ} (hden : 1 ≤ den) (r : Request)
    (hr : RequestAdmitted den degree target r) (cc dc : ℕ)
    (hcold : ∀ (q : ℕ) (x : BinaryCacheColdJoin.Args q), BinaryCacheColdRun.budget x ≤
      cc * ((exactListWord x.gs).length + x.gs.length + q + 2^x.live.card + 1)^dc)
    (m sC sE : ℕ) (hsm : (r.smallSize a)^((betaE a degree + 1)*dc) ≤ sC*smallClass m sE r.q) (dP hT n : ℕ) :
    InClasses dP hT sE m r.liveScale n r.q 0 0 (cc*(2*betaC a degree + 2)^dc*2^((betaE a degree + 1)*dc)*sC)
      (BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a))) :=
  InClasses.small (cold_small a hden r hr cc dc hcold m sC sE hsm)

end
end NearCubicWires.SourceBudget
end

