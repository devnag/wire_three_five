import Proof.Wire_3_5.Selection.MathDefs

/-! # C1.1, the math reductions R1–R6 as residuals, and their composition (P3:1337-1362)

Paper: `star:selection`, "it remains to compute each candidate's objective. Enumerate its `2^k` error rows. For each
gate and row, the four threshold predicates have integer scores of the form `a_j(z_L)+b_j(z_R)`, `1 ≤ j ≤ 4` [...]
Enumerate each half's score vectors. For each of the sixteen corner patterns, count pairs satisfying its four weak
inequalities [...] The pattern determines whether the mixed residual is nonzero. Sum its exact count with the rational
population weights, over gates and rows. There are `2^k` candidate cosets [...] Select a minimum objective"
(P3:1339-1360).

The consumer is `C1Run` (the plan's run residual): the machine's output must be `cosetWord (selArgmin R)`. The
machine computes the objective the way the paper does, and this module states, as explicit residual propositions,
the six reductions from `selArgmin` to what the machine computes, then proves the two consumer-facing theorems from
them:
* **`selArgmin_eq_fold_of`** (R1, R2): the selected coset is the counter's strict-`<` running minimum of the exact
  objective key `objKey` under the cross-multiplied compare;
* **`gateRows_eq_gateJoin_of`** (R3–R6 and the key transfer): a gate's row counts at a partition are `gateJoin`, the
  sorted `<`-joins of the pooled points' offset-binary keys (a null point for a half outside the coset), for ANY
  enumeration of the halves.

Paper quantities: the selected coset `selArgmin R` and each gate's row count `gateRows P σ g` (the number of
`(center, error row)` pairs with a nonzero mixed residual). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine

/-! ## The residuals R1–R6 -/

/-- **R1, the argmin order**: over `allCodes s r` (the counter's digit order) from `replicate r 0`, the first
minimizer of `f` is the counter's strict-`<` running minimum under any key whose strict order is `f`'s. -/
def R1Fold : Prop :=
  ∀ (s r : ℕ) (f : List ℕ → ℚ) {κ : Type} (lt : κ → κ → Bool) (key : ℕ → κ),
    (∀ N, N < 2 ^ (s * r) → ∀ N', N' < 2 ^ (s * r) →
      (f (codesOfIdx s r N) < f (codesOfIdx s r N') ↔ lt (key N) (key N') = true)) →
    StarParams.argminFold f (List.replicate r 0) (StarParams.allCodes s r) =
      codesOfIdx s r (argminIdx lt key (2 ^ (s * r)))

/-- **R2, the objective compare**: for nonnegative weights, the exact objectives of two cosets compare as their
keys `Σ_X p_X · T_X` under the cross-multiplied compare (the common factor `2^{-n}` and the denominators cancel). -/
def R2Objective : Prop :=
  ∀ (R : SelectionReq) (h : ParamsOk R), (∀ X ∈ R.pops, 0 ≤ X.2) → ∀ l l' : List ℕ,
    (selObjective R l < selObjective R l' ↔ ratLt (objKey R h l) (objKey R h l') = true)

/-- **R3, pooling**: a gate's row counts over all error rows are the number of pairs of pooled points whose corner
pattern has a nonzero mixed difference. The machine enumerates EVERY `(u, z_L)` and every `(v, z_R)` and writes the
half point when the half lies in the coset and the null point `(0, 0)` otherwise (`ptLz`, `ptRz`). -/
def R3Pool : Prop :=
  ∀ (P : StarParams) (σ : P.Translation) (g : NormalizedThresholdGate P.n)
    (Ls : List (P.Errors × (P.SideL → Bool))) (Rs : List (P.Errors × (P.SideR → Bool))),
    Enumerates Ls (fun _ => True) → Enumerates Rs (fun _ => True) →
      gateRows P σ g = pairCount g.threshold (Ls.map (ptLz P σ g)) (Rs.map (ptRz P σ g))

/-- **R3b, the key range**: under `KeyBound g V`, the threshold, every left value `θ − a` and every right value `b`
have absolute value below `2^V`. -/
def R3Bound : Prop :=
  ∀ (P : StarParams) (g : NormalizedThresholdGate P.n) (V : ℕ), KeyBound g V →
    g.threshold.natAbs < 2 ^ V ∧ (∀ xL : P.SideL → Bool, (g.threshold - P.halfScoreL g xL).natAbs < 2 ^ V) ∧
      ∀ xR : P.SideR → Bool, (P.halfScoreR g xR).natAbs < 2 ^ V

/-- **R4, the J-form**: with `J = [min(θ−a, θ−a'), max(θ−a, θ−a'))`, `[Δ ≠ 0] = [b ∈ J] + [b' ∈ J] − 2·[b, b' ∈ J]`,
summed over the pairs. -/
def R4JForm : Prop :=
  ∀ (θ : ℤ) (L R : List (ℤ × ℤ)),
    pairCount θ L R + 2 * dom2 (L.map fun p => (loOf θ p, hiOf θ p)) (R.map fun q => (min q.1 q.2, max q.1 q.2)) =
      inCount (L.map fun p => (loOf θ p, hiOf θ p)) (R.map Prod.fst ++ R.map Prod.snd)

/-- **R5, the 1-d terms**: `Σ_J #{y ∈ J} + J<(Y; lo) = J<(Y; hi)`. -/
def R5OneDim : Prop :=
  ∀ (I : List (ℕ × ℕ)) (Y : List ℕ), (∀ J ∈ I, J.1 ≤ J.2) →
    inCount I Y + joinLt Y (I.map Prod.fst) = joinLt Y (I.map Prod.snd)

/-- **R6, the 2-d term by most-significant-bit levels** on keys below `2^W`:
`dom2 + Σ_ℓ J<(K2_ℓ; K1_ℓ) = Σ_ℓ J<(K2_ℓ; K3_ℓ)`. -/
def R6Levels : Prop :=
  ∀ (W : ℕ) (I D : List (ℕ × ℕ)), (∀ J ∈ I, J.1 < 2 ^ W ∧ J.2 < 2 ^ W) → (∀ d ∈ D, d.1 < 2 ^ W ∧ d.2 < 2 ^ W) →
    dom2 I D + ((List.range W).map fun ℓ => joinLt (lvlK2 W ℓ D) (lvlK1 W ℓ I)).sum =
      ((List.range W).map fun ℓ => joinLt (lvlK2 W ℓ D) (lvlK3 W ℓ I)).sum

/-- **The key transfer**: on values of absolute value below `2^V`, the offset-binary key is below `2^(V+1)` and
preserves and reflects `<` and `≤`. -/
def RKey : Prop :=
  ∀ (V : ℕ) (z z' : ℤ), z.natAbs < 2 ^ V → z'.natAbs < 2 ^ V →
    keyOf V z < 2 ^ (V + 1) ∧ (keyOf V z < keyOf V z' ↔ z < z') ∧ (keyOf V z ≤ keyOf V z' ↔ z ≤ z')

/-! ## Composition: R1, R2 give the fold -/

/-- `selObjective` at an admissible request is the reference objective at the coset's translation. -/
theorem selObjective_eq (R : SelectionReq) (h : ParamsOk R) (l : List ℕ) :
    selObjective R l = (starParamsOf R h).starObjectiveRef ((starParamsOf R h).translationOfCodes l) (popsOf R) := by
  unfold selObjective; rw [dif_pos h]

/-- **The selected coset is the counter's running minimum of `objKey`** (from R1, R2). -/
theorem selArgmin_eq_fold_of (r1 : R1Fold) (r2 : R2Objective) (R : SelectionReq) (h : ParamsOk R)
    (hp : ∀ X ∈ R.pops, 0 ≤ X.2) :
    selArgmin R = codesOfIdx R.s R.r (argminIdx ratLt (fun N => objKey R h (codesOfIdx R.s R.r N)) (2 ^ R.k)) := by
  have hk : R.k = R.s * R.r := Nat.mul_comm _ _
  rw [hk]
  unfold selArgmin
  rw [dif_pos h]
  exact r1 R.s R.r _ ratLt _ (fun N _ N' _ => by
    rw [← selObjective_eq R h, ← selObjective_eq R h]; exact r2 R h hp _ _)

/-! ## Composition: R3–R6 and the key transfer give the joins -/

theorem inCount_map {α β : Type} [LinearOrder α] [LinearOrder β] (k : α → β) (I : List (α × α)) (Y : List α)
    (hk : ∀ J ∈ I, ∀ y ∈ Y, (k J.1 ≤ k y ↔ J.1 ≤ y) ∧ (k y < k J.2 ↔ y < J.2)) :
    inCount (I.map fun J => (k J.1, k J.2)) (Y.map k) = inCount I Y := by
  unfold inCount
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro J hJ
  simp only [Function.comp_apply, List.countP_map]
  apply List.countP_congr
  intro y hy
  have := hk J hJ y hy
  simp only [Function.comp_apply, decide_eq_true_eq, this.1, this.2]

theorem dom2_map {α β : Type} [LinearOrder α] [LinearOrder β] (k : α → β) (I D : List (α × α))
    (hk : ∀ J ∈ I, ∀ d ∈ D, (k J.1 ≤ k d.1 ↔ J.1 ≤ d.1) ∧ (k d.2 < k J.2 ↔ d.2 < J.2)) :
    dom2 (I.map fun J => (k J.1, k J.2)) (D.map fun d => (k d.1, k d.2)) = dom2 I D := by
  unfold dom2
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro J hJ
  simp only [Function.comp_apply, List.countP_map]
  apply List.countP_congr
  intro d hd
  have := hk J hJ d hd
  simp only [Function.comp_apply, decide_eq_true_eq, this.1, this.2]

theorem natAbs_min_lt {V : ℕ} {a b : ℤ} (ha : a.natAbs < 2 ^ V) (hb : b.natAbs < 2 ^ V) :
    (min a b).natAbs < 2 ^ V := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

theorem natAbs_max_lt {V : ℕ} {a b : ℤ} (ha : a.natAbs < 2 ^ V) (hb : b.natAbs < 2 ^ V) :
    (max a b).natAbs < 2 ^ V := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

/-- **The pair count is the joins' difference** (from R4, R5, R6 and the key transfer), for values below `2^V`. -/
theorem pairCount_eq_gateJoin_of (r4 : R4JForm) (r5 : R5OneDim) (r6 : R6Levels) (rk : RKey) (V : ℕ) (θ : ℤ)
    (L R : List (ℤ × ℤ)) (hL : ∀ p ∈ L, (θ - p.1).natAbs < 2 ^ V ∧ (θ - p.2).natAbs < 2 ^ V)
    (hR : ∀ q ∈ R, q.1.natAbs < 2 ^ V ∧ q.2.natAbs < 2 ^ V) :
    pairCount θ L R = gateJoin V θ L R := by
  set I : List (ℤ × ℤ) := L.map fun p => (loOf θ p, hiOf θ p) with hI
  set D : List (ℤ × ℤ) := R.map fun q => (min q.1 q.2, max q.1 q.2) with hD
  set Y : List ℤ := R.map Prod.fst ++ R.map Prod.snd with hY
  have hIb : ∀ J ∈ I, J.1.natAbs < 2 ^ V ∧ J.2.natAbs < 2 ^ V := by
    intro J hJ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hJ
    exact ⟨natAbs_min_lt (hL p hp).1 (hL p hp).2, natAbs_max_lt (hL p hp).1 (hL p hp).2⟩
  have hDb : ∀ d ∈ D, d.1.natAbs < 2 ^ V ∧ d.2.natAbs < 2 ^ V := by
    intro d hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
    exact ⟨natAbs_min_lt (hR q hq).1 (hR q hq).2, natAbs_max_lt (hR q hq).1 (hR q hq).2⟩
  have hYb : ∀ y ∈ Y, y.natAbs < 2 ^ V := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact (hR q hq).1
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact (hR q hq).2
  -- the ℕ keys
  set I' : List (ℕ × ℕ) := I.map fun J => (keyOf V J.1, keyOf V J.2) with hI'
  set D' : List (ℕ × ℕ) := D.map fun d => (keyOf V d.1, keyOf V d.2) with hD'
  set Y' : List ℕ := Y.map (keyOf V) with hY'
  have e4 := r4 θ L R
  rw [← hI, ← hD, ← hY] at e4
  have eIn : inCount I' Y' = inCount I Y :=
    inCount_map (keyOf V) I Y fun J hJ y hy =>
      ⟨(rk V _ _ (hIb J hJ).1 (hYb y hy)).2.2, (rk V _ _ (hYb y hy) (hIb J hJ).2).2.1⟩
  have eDom : dom2 I' D' = dom2 I D :=
    dom2_map (keyOf V) I D fun J hJ d hd =>
      ⟨(rk V _ _ (hIb J hJ).1 (hDb d hd).1).2.2, (rk V _ _ (hDb d hd).2 (hIb J hJ).2).2.1⟩
  have e5 := r5 I' Y' (by
    intro J hJ
    obtain ⟨J0, hJ0, rfl⟩ := List.mem_map.mp hJ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hJ0
    exact (rk V _ _ (hIb _ hJ0).1 (hIb _ hJ0).2).2.2.mpr (by simp only [loOf, hiOf]; exact min_le_max))
  have e6 := r6 (V + 1) I' D'
    (by intro J hJ; obtain ⟨J0, hJ0, rfl⟩ := List.mem_map.mp hJ
        exact ⟨(rk V _ _ (hIb J0 hJ0).1 (hIb J0 hJ0).1).1, (rk V _ _ (hIb J0 hJ0).2 (hIb J0 hJ0).2).1⟩)
    (by intro d hd; obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
        exact ⟨(rk V _ _ (hDb d0 hd0).1 (hDb d0 hd0).1).1, (rk V _ _ (hDb d0 hd0).2 (hDb d0 hd0).2).1⟩)
  -- the definitions' lists are these lists
  have hYd : R.map (fun q => keyOf V q.1) ++ R.map (fun q => keyOf V q.2) = Y' := by
    simp only [hY', hY, List.map_append, List.map_map]; rfl
  have hHi : L.map (fun p => keyOf V (hiOf θ p)) = I'.map Prod.snd := by
    simp only [hI', hI, List.map_map]; rfl
  have hLo : L.map (fun p => keyOf V (loOf θ p)) = I'.map Prod.fst := by
    simp only [hI', hI, List.map_map]; rfl
  have hDd : R.map (fun q => (keyOf V (min q.1 q.2), keyOf V (max q.1 q.2))) = D' := by
    simp only [hD', hD, List.map_map]; rfl
  have hId : L.map (fun p => (keyOf V (loOf θ p), keyOf V (hiOf θ p))) = I' := by
    simp only [hI', hI, List.map_map]; rfl
  unfold gateJoin joinPlus joinMinus
  rw [hYd, hHi, hLo, hDd, hId]
  omega

/-- **A gate's row counts are the joins of its pooled points** (from R3–R6 and the key transfer), for any
enumeration of the halves and any key width meeting `KeyBound`. -/
theorem gateRows_eq_gateJoin_of (r3 : R3Pool) (r3b : R3Bound) (r4 : R4JForm) (r5 : R5OneDim) (r6 : R6Levels)
    (rk : RKey) (P : StarParams) (σ : P.Translation) (g : NormalizedThresholdGate P.n)
    (Ls : List (P.Errors × (P.SideL → Bool))) (Rs : List (P.Errors × (P.SideR → Bool)))
    (hLs : Enumerates Ls (fun _ => True)) (hRs : Enumerates Rs (fun _ => True)) (V : ℕ) (hV : KeyBound g V) :
    gateRows P σ g = gateJoin V g.threshold (Ls.map (ptLz P σ g)) (Rs.map (ptRz P σ g)) := by
  rw [r3 P σ g Ls Rs hLs hRs]
  obtain ⟨bθ, bL, bR⟩ := r3b P g V hV
  apply pairCount_eq_gateJoin_of r4 r5 r6 rk
  · intro p hp
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
    unfold ptLz
    split_ifs
    · exact ⟨bL _, bL _⟩
    · simp only [sub_zero]; exact ⟨bθ, bθ⟩
  · intro q hq
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hq
    unfold ptRz
    split_ifs
    · exact ⟨bR _, bR _⟩
    · simp


end NearCubicWires.WireExponent3_5.SelectionMachine.Math
