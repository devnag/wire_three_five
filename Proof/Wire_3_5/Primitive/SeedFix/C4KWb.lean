import Proof.Wire_3_5.Primitive.SeedFix.C4KWa

/-! # C4KW, part 2: the ruler arithmetic and the erasure

Word programs over streams on marker rulers (`mk a = false :: 1^a`, head at the marker):
* **`cp_spec`** (`cpApp X Z`: append `1^x` to `Z`, `X` kept);
* **`mkM_spec`** (a raw count `1^a` into a ruler `mk a`);
* **`apM_spec`** (`mk (x + y + e)` from rulers `x`, `y` and a constant `e`);
* **`mulM_spec`** (`mk (x·y)` from rulers `x`, `y`);
* **`eraseM_spec`** (a ruler overwritten by falses).

Paper quantities of the main types: the Hb printer's derived sizes `2t`, `2tℓ₀`, `L = 2t + 2tℓ₀`, `N²`, `2tℓ₀(2ℓ₀+1)`
(P3:2253-2290, the elimination's register sizes). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

variable {ns nr : ℕ} (cap : ℕ)

theorem apd_end (τ : WState ns nr) (d : Fin (ns + 1)) (x : List Bool) : (apd τ d x).sh d = ((apd τ d x).st d).length := by
  rw [apd_sh_d, apd_st_d, List.length_append]

/-! ## Appending a ruler's count -/

/-- Append `1^x` (the ones of the ruler `X`) to `Z`; `X` back at its marker. -/
def cpApp (X Z : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd X) (.seq (.whs X (.seq (wlist Z [true]) (.fwd X))) (rewM X))

def cpCost (x : ℕ) : ℕ := 11 * x + 12

theorem cp_spec (X Z : Fin (ns + 1)) (hXZ : X ≠ Z) (x : ℕ) (σ : WState ns nr) (hX : σ.st X = mk x)
    (hX0 : σ.sh X = 0) (hZ : σ.sh Z = (σ.st Z).length) :
    WExec cap (cpApp X Z) σ (apd σ Z (List.replicate x true)) (cpCost x) := by
  have t0 := WExec.fwd (cap := cap) X σ
  rw [hX0] at t0
  have hZ1 : (σ.seth X (0 + 1)).sh Z = ((σ.seth X (0 + 1)).st Z).length := by
    simp only [WState.seth_sh, WState.seth_st]; rw [Function.update_of_ne (Ne.symm hXZ)]; exact hZ
  have t1 := apd_loop cap X Z hXZ (wlist Z [true]) [true] 4 (fun _ => True) (fun τ _ h => wlist_spec cap Z [true] τ h)
    (fun _ _ => trivial) (fun _ _ _ => trivial) (mk x) 1 (x + 1)
    (fun q h1 h2 => by rw [rd_mk]; simp only [decide_eq_true_eq]; omega)
    (by rw [rd_mk]; simp only [decide_eq_false_iff_not]; omega) x (σ.seth X (0 + 1)) (by simp [hX])
    (by simp only [WState.seth_sh, Function.update_self]; omega) (by simp) trivial hZ1
  rw [apd_seth _ X Z hXZ, seth_seth', repW_single] at t1
  have t2 := rew_spec cap X x (x + 1) ((apd σ Z (List.replicate x true)).seth X (x + 1))
    (by simp [apd_st_ne σ Z X hXZ, hX]) (by simp) (by omega) (Or.inl le_rfl)
  rw [seth_seth', seth_same _ X 0 (by rw [apd_sh_ne σ Z X hXZ, hX0])] at t2
  exact WExec.cast cap (WExec.seq t0 (WExec.seq t1 t2)) rfl (by unfold cpCost; omega)

/-! ## A raw count into a ruler -/

/-- The raw count `1^a` on `A` (head `0`) into the blank ruler stream `R`. -/
def mkM (A R : Fin (ns + 1)) : WM ns nr :=
  .seq (wlist R [false]) (.seq (.whs A (.seq (wlist R [true]) (.fwd A))) (rewM R))

def mkCost (a : ℕ) : ℕ := 11 * a + 14

theorem mkM_spec (A R : Fin (ns + 1)) (hAR : A ≠ R) (a : ℕ) (σ : WState ns nr) (hA : σ.st A = List.replicate a true)
    (hA0 : σ.sh A = 0) (hR : σ.st R = []) (hR0 : σ.sh R = 0) :
    WExec cap (mkM A R) σ (((apd σ R (mk a)).seth R 0).seth A a) (mkCost a) := by
  have t0 := wlist_spec cap R [false] σ (by rw [hR, hR0]; rfl)
  have hA1 : (apd σ R [false]).st A = List.replicate a true := by rw [apd_st_ne σ R A hAR, hA]
  have hA1' : (apd σ R [false]).sh A = 0 := by rw [apd_sh_ne σ R A hAR, hA0]
  have hR1 : (apd σ R [false]).sh R = ((apd σ R [false]).st R).length := by
    rw [apd_sh_d, apd_st_d, List.length_append]
  have t1 := apd_loop cap A R hAR (wlist R [true]) [true] 4 (fun _ => True) (fun τ _ h => wlist_spec cap R [true] τ h)
    (fun _ _ => trivial) (fun _ _ _ => trivial) (List.replicate a true) 0 a
    (fun q _ h2 => by
      simp only [readTapeBit]; rw [List.getD_eq_getElem _ _ (by simp only [List.length_replicate]; omega)]; simp)
    (by simp [readTapeBit]) a (apd σ R [false]) hA1 (by omega) (by omega) trivial hR1
  rw [apd_apd, repW_single] at t1
  have hmk : [false] ++ List.replicate a true = mk a := rfl
  rw [hmk] at t1
  have t2 := rew_spec cap R a (a + 1) ((apd σ R (mk a)).seth A a)
    (by simp only [WState.seth_st]; rw [apd_st_d, hR]; rfl)
    (by simp only [WState.seth_sh]; rw [Function.update_of_ne (Ne.symm hAR), apd_sh_d, hR, mk_length]; simp)
    (by omega) (Or.inl le_rfl)
  rw [seth_comm _ A R hAR] at t2
  exact WExec.cast cap (WExec.seq t0 (WExec.seq t1 t2)) rfl (by unfold mkCost; simp; omega)

/-! ## Sums and products of rulers -/

/-- `Z := mk (x + y + e)` from the rulers `X`, `Y` (possibly the same) and the constant `e`. -/
def apM (X Y Z : Fin (ns + 1)) (e : ℕ) : WM ns nr :=
  .seq (wlist Z [false]) (.seq (cpApp X Z) (.seq (cpApp Y Z) (.seq (wlist Z (List.replicate e true)) (rewM Z))))

def apCost (x y e : ℕ) : ℕ := 14 * (x + y) + 7 * e + 40

theorem apM_spec (X Y Z : Fin (ns + 1)) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) (x y e : ℕ) (σ : WState ns nr)
    (hX : σ.st X = mk x) (hX0 : σ.sh X = 0) (hY : σ.st Y = mk y) (hY0 : σ.sh Y = 0) (hZ : σ.st Z = [])
    (hZ0 : σ.sh Z = 0) :
    WExec cap (apM X Y Z e) σ ((apd σ Z (mk (x + y + e))).seth Z 0) (apCost x y e) := by
  have t0 := wlist_spec cap Z [false] σ (by rw [hZ, hZ0]; rfl)
  set σ1 := apd σ Z [false] with hσ1
  have t1 := cp_spec cap X Z hXZ x σ1 (by rw [hσ1, apd_st_ne σ Z X hXZ, hX]) (by rw [hσ1, apd_sh_ne σ Z X hXZ, hX0])
    (apd_end σ Z [false])
  set σ2 := apd σ1 Z (List.replicate x true) with hσ2
  have t2 := cp_spec cap Y Z hYZ y σ2 (by rw [hσ2, apd_st_ne _ Z Y hYZ, hσ1, apd_st_ne σ Z Y hYZ, hY])
    (by rw [hσ2, apd_sh_ne _ Z Y hYZ, hσ1, apd_sh_ne σ Z Y hYZ, hY0]) (apd_end σ1 Z _)
  set σ3 := apd σ2 Z (List.replicate y true) with hσ3
  have t3 := wlist_spec cap Z (List.replicate e true) σ3 (apd_end σ2 Z _)
  have hw : [false] ++ (List.replicate x true ++ (List.replicate y true ++ List.replicate e true)) = mk (x + y + e) := by
    rw [mk, List.replicate_add, List.replicate_add]; simp only [List.singleton_append, List.append_assoc]
  have e3 : apd σ3 Z (List.replicate e true) = apd σ Z (mk (x + y + e)) := by
    rw [hσ3, hσ2, hσ1, apd_apd, apd_apd, apd_apd, ← hw]
  rw [e3] at t3
  have t4 := rew_spec cap Z (x + y + e) (x + y + e + 1) (apd σ Z (mk (x + y + e))) (by rw [apd_st_d, hZ]; rfl)
    (by rw [apd_sh_d, hZ, mk_length]; simp) (by omega) (Or.inl le_rfl)
  refine WExec.cast cap (WExec.seq t0 (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4)))) rfl ?_
  simp only [List.length_replicate, List.length_singleton]
  unfold apCost cpCost; omega

/-- `Z := mk (x·y)` from the distinct rulers `X`, `Y`. -/
def mulM (X Y Z : Fin (ns + 1)) : WM ns nr :=
  .seq (wlist Z [false]) (.seq (.fwd X) (.seq (.whs X (.seq (cpApp Y Z) (.fwd X))) (.seq (rewM X) (rewM Z))))

def mulCost (x y : ℕ) : ℕ := x * (11 * y + 16) + 3 * (x * y) + 3 * x + 30

theorem mulM_spec (X Y Z : Fin (ns + 1)) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) (x y : ℕ) (σ : WState ns nr)
    (hX : σ.st X = mk x) (hX0 : σ.sh X = 0) (hY : σ.st Y = mk y) (hY0 : σ.sh Y = 0) (hZ : σ.st Z = [])
    (hZ0 : σ.sh Z = 0) :
    WExec cap (mulM X Y Z) σ ((apd σ Z (mk (x * y))).seth Z 0) (mulCost x y) := by
  have t0 := wlist_spec cap Z [false] σ (by rw [hZ, hZ0]; rfl)
  set σ1 := apd σ Z [false] with hσ1
  have t1 := WExec.fwd (cap := cap) X σ1
  have hX1 : σ1.sh X = 0 := by rw [hσ1, apd_sh_ne σ Z X hXZ, hX0]
  rw [hX1] at t1
  set σ2 := σ1.seth X (0 + 1) with hσ2
  let I : WState ns nr → Prop := fun τ => τ.st Y = mk y ∧ τ.sh Y = 0
  have hI2 : I σ2 := by
    refine ⟨?_, ?_⟩
    · rw [hσ2]; simp only [WState.seth_st]; rw [hσ1, apd_st_ne σ Z Y hYZ, hY]
    · rw [hσ2]; simp only [WState.seth_sh]; rw [Function.update_of_ne (Ne.symm hXY), hσ1, apd_sh_ne σ Z Y hYZ, hY0]
  have hZ2 : σ2.sh Z = (σ2.st Z).length := by
    rw [hσ2]; simp only [WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (Ne.symm hXZ), hσ1, apd_sh_d, apd_st_d, List.length_append]
  have t2 := apd_loop cap X Z hXZ (cpApp Y Z) (List.replicate y true) (cpCost y) I
    (fun τ hτ h => cp_spec cap Y Z hYZ y τ hτ.1 hτ.2 h)
    (fun τ hτ => ⟨by rw [apd_st_ne τ Z Y hYZ, hτ.1], by rw [apd_sh_ne τ Z Y hYZ, hτ.2]⟩)
    (fun τ v hτ => ⟨by simp only [WState.seth_st]; exact hτ.1,
      by simp only [WState.seth_sh]; rw [Function.update_of_ne (Ne.symm hXY)]; exact hτ.2⟩)
    (mk x) 1 (x + 1) (fun q h1 h2 => by rw [rd_mk]; simp only [decide_eq_true_eq]; omega)
    (by rw [rd_mk]; simp only [decide_eq_false_iff_not]; omega) x σ2
    (by rw [hσ2]; simp only [WState.seth_st]; rw [hσ1, apd_st_ne σ Z X hXZ, hX])
    (by rw [hσ2]; simp only [WState.seth_sh, Function.update_self]; omega)
    (by rw [hσ2]; simp only [WState.seth_sh, Function.update_self]; omega) hI2 hZ2
  rw [repW_rep, hσ2, apd_seth _ X Z hXZ, seth_seth', hσ1, apd_apd] at t2
  have hw : [false] ++ List.replicate (x * y) true = mk (x * y) := rfl
  rw [hw] at t2
  have t3 := rew_spec cap X x (x + 1) ((apd σ Z (mk (x * y))).seth X (x + 1))
    (by simp [apd_st_ne σ Z X hXZ, hX]) (by simp) (by omega) (Or.inl le_rfl)
  rw [seth_seth', seth_same _ X 0 (by rw [apd_sh_ne σ Z X hXZ, hX0])] at t3
  have t4 := rew_spec cap Z (x * y) (x * y + 1) (apd σ Z (mk (x * y))) (by rw [apd_st_d, hZ]; rfl)
    (by rw [apd_sh_d, hZ, mk_length]; simp) (by omega) (Or.inl le_rfl)
  refine WExec.cast cap (WExec.seq t0 (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4)))) rfl ?_
  unfold mulCost cpCost
  simp only [List.length_singleton]
  have : x * (11 * y + 12 + 4) = x * (11 * y + 16) := by ring
  omega

/-! ## Erasing a ruler -/

theorem write_run (q k : ℕ) :
    writeTapeBit (List.replicate q false ++ List.replicate (k + 1) true) q false =
      List.replicate (q + 1) false ++ List.replicate k true := by
  induction q with
  | zero => rfl
  | succ q ih =>
    show writeTapeBit (false :: (List.replicate q false ++ List.replicate (k + 1) true)) (q + 1) false = _
    rw [writeTapeBit, ih]; rfl

/-- Overwrite a ruler's ones by falses (its marker is already `false`). -/
def eraseM (R : Fin (ns + 1)) : WM ns nr := .seq (.fwd R) (.whs R (.seq (.wr R false) (.fwd R)))

theorem erase_loop (R : Fin (ns + 1)) : ∀ (k q : ℕ) (σ : WState ns nr),
    σ.st R = List.replicate q false ++ List.replicate k true → σ.sh R = q →
    WExec cap (.whs R (.seq (.wr R false) (.fwd R))) σ
      ((σ.sets R (List.replicate (q + k) false)).seth R (q + k)) (5 * k + 1)
  | 0, q, σ, hs, hq => by
    have e : (σ.sets R (List.replicate (q + 0) false)).seth R (q + 0) = σ := by
      apply WState.eq
      · funext j; by_cases hj : j = R
        · subst hj; simp [WState.seth, hq]
        · simp [WState.seth, Function.update_of_ne hj]
      · funext j; by_cases hj : j = R
        · subst hj; simp [WState.sets, hs]
        · simp [WState.sets, Function.update_of_ne hj]
      · rfl
      · rfl
    rw [e]
    exact WExec.whsF (by show readTapeBit _ _ = false; rw [hs, hq]; simp [readTapeBit])
  | k + 1, q, σ, hs, hq => by
    have hb : wbit σ R = true := by
      show readTapeBit _ _ = true
      rw [hs, hq]; simp [readTapeBit, List.getD_append_right, List.replicate_succ]
    have t1 := WExec.wr (cap := cap) R false σ
    rw [hs, hq, write_run] at t1
    have t2 := WExec.fwd (cap := cap) R (σ.sets R (List.replicate (q + 1) false ++ List.replicate k true))
    have ih := erase_loop R k (q + 1) ((σ.sets R (List.replicate (q + 1) false ++ List.replicate k true)).seth R
      ((σ.sets R (List.replicate (q + 1) false ++ List.replicate k true)).sh R + 1)) (by simp) (by simp [hq])
    have e : (((σ.sets R (List.replicate (q + 1) false ++ List.replicate k true)).seth R
        ((σ.sets R (List.replicate (q + 1) false ++ List.replicate k true)).sh R + 1)).sets R
          (List.replicate (q + 1 + k) false)).seth R (q + 1 + k) =
        (σ.sets R (List.replicate (q + (k + 1)) false)).seth R (q + (k + 1)) := by
      apply WState.eq
      · funext j; by_cases hj : j = R
        · subst hj; simp [WState.seth, WState.sets]; omega
        · simp [WState.seth, WState.sets, Function.update_of_ne hj]
      · funext j; by_cases hj : j = R
        · subst hj; simp only [WState.sets_st, WState.seth_st, Function.update_self]
          rw [show q + 1 + k = q + (k + 1) by omega]
        · simp [WState.sets, Function.update_of_ne hj]
      · rfl
      · rfl
    rw [e] at ih
    exact WExec.cast cap (WExec.whsT hb (WExec.seq t1 t2) ih) rfl (by omega)

theorem eraseM_spec (R : Fin (ns + 1)) (a : ℕ) (σ : WState ns nr) (hR : σ.st R = mk a) (hR0 : σ.sh R = 0) :
    WExec cap (eraseM R) σ ((σ.sets R (List.replicate (a + 1) false)).seth R (a + 1)) (5 * a + 3) := by
  have t0 := WExec.fwd (cap := cap) R σ
  rw [hR0] at t0
  have t1 := erase_loop cap R a 1 (σ.seth R (0 + 1)) (by simp [hR, mk]) (by simp)
  have e : ((σ.seth R (0 + 1)).sets R (List.replicate (1 + a) false)).seth R (1 + a) =
      (σ.sets R (List.replicate (a + 1) false)).seth R (a + 1) := by
    apply WState.eq
    · funext j; by_cases hj : j = R
      · subst hj; simp [WState.seth, WState.sets]; omega
      · simp [WState.seth, WState.sets, Function.update_of_ne hj]
    · funext j; by_cases hj : j = R
      · subst hj; simp only [WState.sets_st, WState.seth_st, Function.update_self]
        rw [Nat.add_comm]
      · simp [WState.sets, Function.update_of_ne hj]
    · rfl
    · rfl
  rw [e] at t1
  exact WExec.cast cap (WExec.seq t0 t1) rfl (by omega)

end NearCubicWires.WireExponent3_5.PrimT.C4KW
