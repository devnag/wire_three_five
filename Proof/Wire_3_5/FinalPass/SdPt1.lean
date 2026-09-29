import Proof.Wire_3_5.FinalPass.SdLay

/-! # S4 (the seeds phase), part 4: the call's mask at a sampled point (P3:2019-2025, 3074-3080, 3170-3178)

"Write `M(e,x)` for their product" (P3:3078-3080): the call's mask is the product of its (at most two, `Call`)
carriers' factors. `carF … k`: carrier `k`'s factor (`true` when there is no carrier `k`); **`all_le2`**: a list of at
most two entries is `all`-ed by its first two. On the body's layout: `CarOK` (carrier `k`'s streams: its mask table,
formatted accumulators and scratch, the seed's table, the capacity), `MaskCom` (the point, the sign, the threshold, the
heads, the mask registers). **`maskStep_spec`**: `if rP k then maskK k else rM k += 1` adds carrier `k`'s factor to
`rM k`; **`maskAll_spec`**: both steps leave `rM 0 = [carF 0]`, `rM 1 = [carF 1]`, every other register, every head,
the cell and every stream but the carriers' accumulators and corner words as they were, and `CarOK` again.

Paper quantity of the main type: the carriers' factors of the call's mask `M(e,x)` (`maskBits`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.SupplierWalk (majorityThreshold)

/-! ## The factors -/

/-- Carrier `k`'s factor of the mask at `(c, u, v)` (`true` without a carrier `k`). -/
def carF (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (c u v : BitInput n)
    (k : ℕ) : Bool :=
  if h : k < carriers.length then
    filterBits FP e (popBits true (cornerWord ((maskGates (carriers.get ⟨k, h⟩)).map NormalizedThresholdGate.eval)
      c u v))
  else true

theorem all_le2 {α : Type} (f : α → Bool) : ∀ (l : List α), l.length ≤ 2 →
    l.all f = ((if h0 : 0 < l.length then f (l.get ⟨0, h0⟩) else true) &&
      (if h1 : 1 < l.length then f (l.get ⟨1, h1⟩) else true))
  | [], _ => rfl
  | [x], _ => by simp
  | [x, y], _ => by simp
  | _ :: _ :: _ :: _, h => by simp at h

/-- **The call's mask is the product of the two factors.** -/
theorem all_carF (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n))
    (hlen : carriers.length ≤ 2) (c u v : BitInput n) :
    (carriers.all fun X => filterBits FP e (popBits true (cornerWord ((maskGates X).map NormalizedThresholdGate.eval)
      c u v))) = (carF FP e carriers c u v 0 && carF FP e carriers c u v 1) := by
  rw [all_le2 _ carriers hlen]
  rfl

/-! ## Carrier `k`'s streams -/

section Lay
variable {nw nn nsc nrs : ℕ}

/-- The fixed streams are distinct when their indices are. -/
theorem bst_ne {i j : ℕ} {hi : i < 47} {hj : j < 47} (h : i ≠ j) :
    (bst i hi : Fin (bns nw nsc + 1)) ≠ bst j hj := fun e => h (congrArg Fin.val e)

theorem brg_ne {i j : ℕ} {hi : i < 220} {hj : j < 220} (h : i ≠ j) :
    (brg i hi : Fin (bnr nn nrs)) ≠ brg j hj := fun e => h (congrArg Fin.val e)

/-- Distinct fixed streams or registers of the body layout. -/
macro "bne" : tactic =>
  `(tactic| ((try (simp only [tN, tC, tU, tV, tSp, tD0, tD1, tD2, tT, tPos, tNeg, tX, tZ, tG, tThr, rM, rP])); first | (apply bst_ne; omega) | (apply brg_ne; omega)))

/-- **Carrier `k`'s streams at a seed**: its mask table, its accumulators and corner word formatted, its population
blank, the seed's table at its length, and the capacity its mask needs. -/
structure CarOK (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (X : Stars.Carrier n) (k : Fin 2)
    (ω : BS nw nn nsc nrs) : Prop where
  G : ω.st (tG k) = gatesW (PrimT.tabH X) (maskGates X)
  acc : ∃ A B : ℕ, ∃ ys : List Bool, ω.st (tPos k) = frameP (binary (PrimT.tabH X) A) ++ [false] ∧
    ω.st (tNeg k) = frameP (binary (PrimT.tabH X) B) ++ [false] ∧ ω.st (tX k) = ys ++ [false] ∧
    ys.length = 8 * (maskGates X).length
  Z : ω.st (tZ k) = List.replicate (2 * (maskGates X).length + 1) false
  T : ω.st (tT k) = tableWord (filterTable FP e (maskGates X).length)
  cap : MkCap cap (PrimT.tabH X) n (maskGates X).length (filterTable FP e (maskGates X).length)
    (majorityThreshold FP.walkLen)

/-- **The mask's common entry**: the point, the sign, the threshold, every head but the sampled pairs' at `0`, the
mask registers `0`. -/
structure MaskCom (cap : ℕ) (FP : GapParams) {n : ℕ} (c u v : BitInput n) (ω : BS nw nn nsc nrs) : Prop where
  C : ω.st tC = frame (List.ofFn c)
  U : ω.st tU = frame (List.ofFn u)
  V : ω.st tV = frame (List.ofFn v)
  Sp : ω.st tSp = [true]
  Thr : ω.st tThr = ListEval.unary (majorityThreshold FP.walkLen)
  sh : ∀ i, i ≠ tI → ω.sh i = 0
  ms : ∀ (j : ℕ) (hj : j < 14), ω.val (brg (122 + j) (by omega)) = 0
  cap2 : 2 ≤ cap

theorem carOK_frame (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (X : Stars.Carrier n) (k k' : Fin 2)
    (hk : k' ≠ k) (ω ω' : BS nw nn nsc nrs) (h : CarOK cap FP e X k' ω)
    (hst : ∀ i, i ≠ tPos k → i ≠ tNeg k → i ≠ tX k → ω'.st i = ω.st i) : CarOK cap FP e X k' ω' := by
  have hk' : k'.val ≠ k.val := fun e => hk (Fin.ext e)
  have := k.isLt
  have := k'.isLt
  have f : ∀ j (hj : j < 47), (j = 32 + k'.val ∨ j = 10 + 4 * k'.val ∨ j = 11 + 4 * k'.val ∨ j = 12 + 4 * k'.val ∨
      j = 13 + 4 * k'.val ∨ j = 8 + k'.val) → ω'.st (bst j hj) = ω.st (bst j hj) := by
    intro j hj hj'
    apply hst <;> bne
  obtain ⟨A, B, ys, h1, h2, h3, h4⟩ := h.acc
  exact ⟨by rw [show tG k' = bst (32 + k'.val) _ from rfl, f _ _ (by omega)]; exact h.G,
    ⟨A, B, ys, by rw [show tPos k' = bst (10 + 4 * k'.val) _ from rfl, f _ _ (by omega)]; exact h1,
      by rw [show tNeg k' = bst (11 + 4 * k'.val) _ from rfl, f _ _ (by omega)]; exact h2,
      by rw [show tX k' = bst (12 + 4 * k'.val) _ from rfl, f _ _ (by omega)]; exact h3, h4⟩,
    by rw [show tZ k' = bst (13 + 4 * k'.val) _ from rfl, f _ _ (by omega)]; exact h.Z,
    by rw [show tT k' = bst (8 + k'.val) _ from rfl, f _ _ (by omega)]; exact h.T, h.cap⟩

/-! ## One carrier's step -/

/-- Carrier `k`'s step: its factor into `rM k`, or `rM k := 1` without a carrier `k`. -/
def maskStep (k : Fin 2) : BP nw nn nsc nrs := .ifr (rP k) (maskK k) (.inc (rM k))

/-- Carrier `k`'s step cost. -/
def mkC (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (k : ℕ) : ℕ :=
  if h : k < carriers.length then
    mkCost (PrimT.tabH (carriers.get ⟨k, h⟩)) n (maskGates (carriers.get ⟨k, h⟩)).length
      (tableWord (filterTable FP e (maskGates (carriers.get ⟨k, h⟩)).length)).length (majorityThreshold FP.walkLen)
  else 3

theorem maskStep_spec (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n))
    (c u v : BitInput n) (k : Fin 2) (ω : BS nw nn nsc nrs) (hcom : MaskCom cap FP c u v ω)
    (hcar : ∀ (k' : Fin 2) (h : k'.val < carriers.length), CarOK cap FP e (carriers.get ⟨k'.val, h⟩) k' ω)
    (hM : ω.val (rM k) = 0) (hP : ω.val (rP k) = if k.val < carriers.length then 1 else 0) :
    ∃ ω', WExec cap (maskStep k) ω ω' (mkC FP e carriers k.val + 1) ∧ MaskCom cap FP c u v ω' ∧
      (∀ (k' : Fin 2) (h : k'.val < carriers.length), CarOK cap FP e (carriers.get ⟨k'.val, h⟩) k' ω') ∧
      (∀ i, i ≠ tPos k → i ≠ tNeg k → i ≠ tX k → ω'.st i = ω.st i) ∧ ω'.sh = ω.sh ∧
      ω'.val = Function.update ω.val (rM k) (carF FP e carriers c u v k.val).toNat ∧ ω'.cell = ω.cell := by
  have hk2 := k.isLt
  have hMms : ∀ (j : ℕ) (hj : j < 14), (brg (122 + j) (by omega) : Fin (bnr nn nrs)) ≠ rM k := fun j hj => by
    bne
  by_cases hk : k.val < carriers.length
  · -- a carrier `k`
    have hc := hcar k hk
    obtain ⟨A, B, ys, h1, h2, h3, h4⟩ := hc.acc
    obtain ⟨ω', A', B', e1, x1, p1, n1, o1, s1, v1, k1⟩ := maskK_spec cap k FP e (carriers.get ⟨k.val, hk⟩) c u v
      A B ys ω hc.G hcom.C hcom.U hcom.V h1 h2 h3 h4 hc.Z hcom.Sp hc.T hcom.Thr
      (fun i => hcom.sh _ (fsM_ne_tI k i)) hcom.ms hc.cap
      (by rw [hM]; have := hcom.cap2; omega)
    have hne : ∀ i, (i = tC ∨ i = tU ∨ i = tV ∨ i = tSp ∨ i = tThr) → ω'.st i = ω.st i := by
      intro i hi
      apply o1 <;> (rcases hi with rfl | rfl | rfl | rfl | rfl <;> bne)
    refine ⟨ω', WExec.ifrT (by rw [hP, if_pos hk]; omega) (by unfold mkC; rw [dif_pos hk]; exact e1), ?_, ?_,
      o1, s1, ?_, k1⟩
    · exact ⟨by rw [hne _ (by simp)]; exact hcom.C, by rw [hne _ (by simp)]; exact hcom.U,
        by rw [hne _ (by simp)]; exact hcom.V, by rw [hne _ (by simp)]; exact hcom.Sp,
        by rw [hne _ (by simp)]; exact hcom.Thr, fun i hi => by rw [s1]; exact hcom.sh i hi,
        fun j hj => by rw [v1, Function.update_of_ne (hMms j hj)]; exact hcom.ms j hj, hcom.cap2⟩
    · intro k' h'
      by_cases hkk : k' = k
      · subst hkk
        have hc' := hcar k' h'
        refine ⟨?_, ⟨A', B', frameP (cornerWord ((maskGates (carriers.get ⟨k'.val, h'⟩)).map
          NormalizedThresholdGate.eval) c u v), p1, n1, x1, ?_⟩, ?_, ?_, hc'.cap⟩
        · rw [o1 _ (by bne) (by bne)
            (by bne)]
          exact hc'.G
        · rw [frameP_length, cornerWord_length, List.length_map]
          ring
        · rw [o1 _ (by bne) (by bne)
            (by bne)]
          exact hc'.Z
        · rw [o1 _ (by bne) (by bne)
            (by bne)]
          exact hc'.T
      · exact carOK_frame cap FP e _ k k' hkk ω ω' (hcar k' h') o1
    · rw [v1, hM, Nat.zero_add]
      unfold carF
      rw [dif_pos hk]
  · -- no carrier `k`
    have hc0 : ω.val (rP k) = 0 := by rw [hP, if_neg hk]
    refine ⟨ω.setv (rM k) (ω.val (rM k) + 1),
      WExec.ifrF hc0 (by unfold mkC; rw [dif_neg hk]; exact WExec.inc (rM k) ω (by rw [hM]; have := hcom.cap2; omega)),
      ?_, fun k' h' => ?_, fun i _ _ _ => rfl, rfl, ?_, rfl⟩
    · exact ⟨hcom.C, hcom.U, hcom.V, hcom.Sp, hcom.Thr, hcom.sh,
        fun j hj => by simp only [WState.setv_val]; rw [Function.update_of_ne (hMms j hj)]; exact hcom.ms j hj,
        hcom.cap2⟩
    · exact carOK_frame cap FP e _ k k' (fun h => hk (h ▸ h')) ω _ (hcar k' h') (fun i _ _ _ => rfl)
    · simp only [WState.setv_val]
      rw [hM]
      unfold carF
      rw [dif_neg hk]
      rfl

/-! ## Both carriers -/

/-- **The call's mask factors**: carrier `0`'s step, then carrier `1`'s. -/
def maskAll : BP nw nn nsc nrs := .seq (maskStep 0) (maskStep 1)

theorem maskAll_spec (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n))
    (c u v : BitInput n) (ω : BS nw nn nsc nrs) (hcom : MaskCom cap FP c u v ω)
    (hcar : ∀ (k : Fin 2) (h : k.val < carriers.length), CarOK cap FP e (carriers.get ⟨k.val, h⟩) k ω)
    (hM : ∀ k, ω.val (rM k) = 0) (hP : ∀ k : Fin 2, ω.val (rP k) = if k.val < carriers.length then 1 else 0) :
    ∃ ω', WExec cap maskAll ω ω' (mkC FP e carriers 0 + 1 + 1 + (mkC FP e carriers 1 + 1)) ∧
      MaskCom cap FP c u v ω' ∧
      (∀ (k : Fin 2) (h : k.val < carriers.length), CarOK cap FP e (carriers.get ⟨k.val, h⟩) k ω') ∧
      (∀ i, (∀ k : Fin 2, i ≠ tPos k ∧ i ≠ tNeg k ∧ i ≠ tX k) → ω'.st i = ω.st i) ∧ ω'.sh = ω.sh ∧
      ω'.val = Function.update (Function.update ω.val (rM 0) (carF FP e carriers c u v 0).toNat) (rM 1)
        (carF FP e carriers c u v 1).toNat ∧ ω'.cell = ω.cell := by
  have h01 : (rM 0 : Fin (bnr nn nrs)) ≠ rM 1 := by bne
  obtain ⟨ω1, e1, c1, k1, o1, s1, v1, l1⟩ := maskStep_spec cap FP e carriers c u v 0 ω hcom hcar (hM 0) (hP 0)
  obtain ⟨ω2, e2, c2, k2, o2, s2, v2, l2⟩ := maskStep_spec cap FP e carriers c u v 1 ω1 c1 k1
    (by rw [v1, Function.update_of_ne h01.symm]; exact hM 1)
    (by rw [v1, Function.update_of_ne (show (rP 1 : Fin (bnr nn nrs)) ≠ rM 0 by bne)]; exact hP 1)
  refine ⟨ω2, WExec.seq e1 e2, c2, k2, fun i hi => ?_, by rw [s2, s1], by rw [v2, v1]; rfl, by rw [l2, l1]⟩
  rw [o2 i (hi 1).1 (hi 1).2.1 (hi 1).2.2, o1 i (hi 0).1 (hi 0).2.1 (hi 0).2.2]

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
