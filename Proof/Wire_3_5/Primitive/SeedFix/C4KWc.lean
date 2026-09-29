import Proof.Wire_3_5.Primitive.SeedFix.C4KWb

/-! # C4KW, part 3: the special emitters

Word programs over streams on marker rulers, each appending a framed word to an output:
* **`decM_spec`**: `frame [decide (a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0)]` (the Hb printer's flag `[0 < n]`, its cell count a product);
* **`bin1M_spec`**: `frame (bin1W ℓ)`, with `bin1W ℓ = frame (binary ℓ 1)` (`bin1W_eq`);
* **`padM_spec`**: `frame (1^x ++ 0^{c − x})` (the elimination's padded constraint ruler `pad c 1^x`).

Paper quantity of the main types: the Hb printer's static words (P3:2253-2290). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

variable {ns nr : ℕ} (cap : ℕ)

theorem wbit_mk1 (σ : WState ns nr) (R : Fin (ns + 1)) (a : ℕ) (h : σ.st R = mk a) (h1 : σ.sh R = 1) :
    wbit σ R = decide (a ≠ 0) := by
  show readTapeBit _ _ = _
  rw [h, h1, rd_mk]; simp only [decide_eq_decide]; omega

theorem wbit_mk (σ : WState ns nr) (R : Fin (ns + 1)) (a p : ℕ) (h : σ.st R = mk a) (hp : σ.sh R = p) :
    wbit σ R = decide (1 ≤ p ∧ p ≤ a) := by
  show readTapeBit _ _ = _
  rw [h, hp, rd_mk]

theorem apd_end' (τ : WState ns nr) (d : Fin (ns + 1)) (x : List Bool) : (apd τ d x).sh d = ((apd τ d x).st d).length := by
  rw [apd_sh_d, apd_st_d, List.length_append]

theorem seth_end (τ : WState ns nr) (R O : Fin (ns + 1)) (hRO : R ≠ O) (v : ℕ) (h : τ.sh O = (τ.st O).length) :
    (τ.seth R v).sh O = ((τ.seth R v).st O).length := by
  simp only [WState.seth_sh, WState.seth_st]; rw [Function.update_of_ne (Ne.symm hRO)]; exact h

/-! ## The flag -/

/-- `frame [a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0]` from three distinct rulers. -/
def decM (R1 R2 R3 O : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd R1) (.seq (.fwd R2) (.seq (.fwd R3) (.seq (.ifs R1 (.ifs R2 (.ifs R3 (wlist O [true, true])
    (wlist O [true, false])) (wlist O [true, false])) (wlist O [true, false])) (.seq (wlist O [false])
      (.seq (.bwd R1) (.seq (.bwd R2) (.bwd R3)))))))

theorem decM_spec (R1 R2 R3 O : Fin (ns + 1)) (h12 : R1 ≠ R2) (h13 : R1 ≠ R3) (h23 : R2 ≠ R3) (h1O : R1 ≠ O)
    (h2O : R2 ≠ O) (h3O : R3 ≠ O) (a1 a2 a3 : ℕ) (σ : WState ns nr) (hR1 : σ.st R1 = mk a1) (hR2 : σ.st R2 = mk a2)
    (hR3 : σ.st R3 = mk a3) (h10 : σ.sh R1 = 0) (h20 : σ.sh R2 = 0) (h30 : σ.sh R3 = 0)
    (hO : σ.sh O = (σ.st O).length) :
    WExec cap (decM R1 R2 R3 O) σ (apd σ O (frame [decide (a1 ≠ 0 ∧ a2 ≠ 0 ∧ a3 ≠ 0)])) 40 := by
  set σ' := ((σ.seth R1 1).seth R2 1).seth R3 1 with hσ'
  have t1 := WExec.fwd (cap := cap) R1 σ
  have t2 := WExec.fwd (cap := cap) R2 (σ.seth R1 (σ.sh R1 + 1))
  have t3 := WExec.fwd (cap := cap) R3 ((σ.seth R1 (σ.sh R1 + 1)).seth R2 ((σ.seth R1 (σ.sh R1 + 1)).sh R2 + 1))
  have e3 : ((σ.seth R1 (σ.sh R1 + 1)).seth R2 ((σ.seth R1 (σ.sh R1 + 1)).sh R2 + 1)).seth R3
      (((σ.seth R1 (σ.sh R1 + 1)).seth R2 ((σ.seth R1 (σ.sh R1 + 1)).sh R2 + 1)).sh R3 + 1) = σ' := by
    rw [hσ']; simp only [WState.seth_sh]
    rw [Function.update_of_ne (Ne.symm h12), Function.update_of_ne (Ne.symm h23), Function.update_of_ne (Ne.symm h13),
      h10, h20, h30]
  rw [e3] at t3
  have s1 : σ'.st R1 = mk a1 := by rw [hσ']; simp [hR1]
  have s2 : σ'.st R2 = mk a2 := by rw [hσ']; simp [hR2]
  have s3 : σ'.st R3 = mk a3 := by rw [hσ']; simp [hR3]
  have b1 : wbit σ' R1 = decide (a1 ≠ 0) := wbit_mk1 σ' R1 a1 s1 (by rw [hσ']; simp [Function.update_of_ne h13,
    Function.update_of_ne h12])
  have b2 : wbit σ' R2 = decide (a2 ≠ 0) := wbit_mk1 σ' R2 a2 s2 (by rw [hσ']; simp [Function.update_of_ne h23])
  have b3 : wbit σ' R3 = decide (a3 ≠ 0) := wbit_mk1 σ' R3 a3 s3 (by rw [hσ']; simp)
  have hO' : σ'.sh O = (σ'.st O).length := by
    rw [hσ']; simp only [WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (Ne.symm h3O), Function.update_of_ne (Ne.symm h2O), Function.update_of_ne (Ne.symm h1O)]
    exact hO
  set b := decide (a1 ≠ 0 ∧ a2 ≠ 0 ∧ a3 ≠ 0) with hb
  have tI : WExec cap (.ifs R1 (.ifs R2 (.ifs R3 (wlist O [true, true]) (wlist O [true, false]))
      (wlist O [true, false])) (wlist O [true, false])) σ' (apd σ' O [true, b]) 11 := by
    have wT := wlist_spec cap O [true, true] σ' hO'
    have wF := wlist_spec cap O [true, false] σ' hO'
    by_cases c1 : a1 ≠ 0
    · by_cases c2 : a2 ≠ 0
      · by_cases c3 : a3 ≠ 0
        · have : b = true := by rw [hb]; simp [c1, c2, c3]
          rw [this]
          exact WExec.cast cap (WExec.ifsT (by rw [b1]; simp [c1]) (WExec.ifsT (by rw [b2]; simp [c2])
            (WExec.ifsT (by rw [b3]; simp [c3]) wT))) rfl (by simp)
        · have : b = false := by rw [hb]; simp [c3]
          rw [this]
          exact WExec.cast cap (WExec.ifsT (by rw [b1]; simp [c1]) (WExec.ifsT (by rw [b2]; simp [c2])
            (WExec.ifsF (by rw [b3]; simp [c3]) wF))) rfl (by simp)
      · have : b = false := by rw [hb]; simp [c2]
        rw [this]
        exact WExec.cast cap (WExec.ifsT (by rw [b1]; simp [c1]) (WExec.ifsF (by rw [b2]; simp [c2]) wF)) rfl
          (by simp)
    · have : b = false := by rw [hb]; simp [c1]
      rw [this]
      exact WExec.cast cap (WExec.ifsF (by rw [b1]; simp [c1]) wF) rfl (by simp)
  have tE := wlist_spec cap O [false] (apd σ' O [true, b]) (apd_end' σ' O _)
  rw [apd_apd] at tE
  set τ := apd σ' O ([true, b] ++ [false]) with hτ
  have u1 := WExec.bwd (cap := cap) R1 τ
  have u2 := WExec.bwd (cap := cap) R2 (τ.seth R1 (τ.sh R1 - 1))
  have u3 := WExec.bwd (cap := cap) R3 ((τ.seth R1 (τ.sh R1 - 1)).seth R2 ((τ.seth R1 (τ.sh R1 - 1)).sh R2 - 1))
  have eF : ((τ.seth R1 (τ.sh R1 - 1)).seth R2 ((τ.seth R1 (τ.sh R1 - 1)).sh R2 - 1)).seth R3
      (((τ.seth R1 (τ.sh R1 - 1)).seth R2 ((τ.seth R1 (τ.sh R1 - 1)).sh R2 - 1)).sh R3 - 1) = apd σ O (frame [b]) := by
    rw [hτ, hσ']
    apply WState.eq
    · funext j
      by_cases j1 : j = R1
      · subst j1; simp [apd, WState.seth, h12, h13, h1O, Function.update_of_ne h1O, h10]
      · by_cases j2 : j = R2
        · subst j2; simp [apd, WState.seth, j1, h23, h2O, Function.update_of_ne h2O, h20]
        · by_cases j3 : j = R3
          · subst j3; simp [apd, WState.seth, j1, j2, h3O, Function.update_of_ne h3O, h30]
          · by_cases jO : j = O
            · subst jO; simp [apd, WState.seth, j1, j2, j3, Ne.symm h1O, Ne.symm h2O, Ne.symm h3O]
            · simp [apd, WState.seth, j1, j2, j3, jO]
    · funext j
      by_cases jO : j = O
      · subst jO; simp [apd, WState.seth, Ne.symm h1O, Ne.symm h2O, Ne.symm h3O]; rfl
      · simp [apd, WState.seth, jO]
    · rfl
    · rfl
  rw [eF] at u3
  exact WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq tI (WExec.seq tE
    (WExec.seq u1 (WExec.seq u2 u3))))))) rfl (by simp)

/-! ## The word `frame (binary ℓ 1)` -/

/-- The elimination's constant `frame (binary ℓ 1)` as the emitter builds it. -/
def bin1W (a : ℕ) : List Bool := (if a = 0 then [] else [true, true] ++ repW (a - 1) [true, false]) ++ [false]

theorem binary_zero_rep : ∀ ℓ : ℕ, SignedSortKey.binary ℓ 0 = List.replicate ℓ false
  | 0 => rfl
  | ℓ + 1 => by
    show (0 % 2 == 1) :: SignedSortKey.binary ℓ (0 / 2) = _
    rw [Nat.zero_div, binary_zero_rep ℓ]; rfl

theorem prs_rep_false (k : ℕ) : prs (List.replicate k false) = repW k [true, false] := by
  rw [← repW_single, prs_repW]; rfl

theorem prs_rep_true (k : ℕ) : prs (List.replicate k true) = repW k [true, true] := by
  rw [← repW_single, prs_repW]; rfl

theorem frame_rep_false (k : ℕ) : frame (List.replicate k false) = repW k [true, false] ++ [false] := by
  rw [frame_prs, prs_rep_false]

theorem bin1W_eq (a : ℕ) : bin1W a = frame (SignedSortKey.binary a 1) := by
  cases a with
  | zero => rfl
  | succ a =>
    show _ = frame ((1 % 2 == 1) :: SignedSortKey.binary a (1 / 2))
    rw [show (1 : ℕ) / 2 = 0 by rfl, binary_zero_rep]
    unfold bin1W
    rw [if_neg (by omega), Nat.add_sub_cancel]
    show _ = true :: true :: frame (List.replicate a false)
    rw [frame_rep_false]; rfl

/-- `frame (bin1W a)` from the ruler `mk a`. -/
def bin1M (R O : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd R) (.seq (.ifs R (.seq (wlist O (prs [true, true])) (.seq (.fwd R)
    (.whs R (.seq (wlist O (prs [true, false])) (.fwd R))))) .skip) (.seq (wlist O (prs [false] ++ [false])) (rewM R)))

theorem bin1M_spec (R O : Fin (ns + 1)) (hRO : R ≠ O) (a : ℕ) (σ : WState ns nr) (hR : σ.st R = mk a)
    (hR0 : σ.sh R = 0) (hO : σ.sh O = (σ.st O).length) :
    WExec cap (bin1M R O) σ (apd σ O (frame (bin1W a))) (25 * a + 40) := by
  have t0 := WExec.fwd (cap := cap) R σ
  rw [hR0] at t0
  have hR1 : (σ.seth R (0 + 1)).st R = mk a := by simp [hR]
  have hO1 : (σ.seth R (0 + 1)).sh O = ((σ.seth R (0 + 1)).st O).length := seth_end σ R O hRO _ hO
  set X : List Bool := if a = 0 then [] else prs [true, true] ++ repW (a - 1) (prs [true, false]) with hX
  obtain ⟨p, tB, hp1, hp2⟩ : ∃ p : ℕ, WExec cap (.ifs R (.seq (wlist O (prs [true, true])) (.seq (.fwd R)
      (.whs R (.seq (wlist O (prs [true, false])) (.fwd R))))) .skip : WM ns nr) (σ.seth R (0 + 1))
      ((apd σ O X).seth R p) (20 * a + 3) ∧ 1 ≤ p ∧ p ≤ a + 1 := by
    by_cases ha : a = 0
    · refine ⟨1, ?_, le_rfl, by omega⟩
      rw [hX, if_pos ha, apd_nil σ O hO]
      exact WExec.cast cap (WExec.ifsF (by rw [wbit_mk1 _ R a hR1 (by simp)]; simp [ha]) (WExec.skip _)) rfl
        (by omega)
    · refine ⟨a + 1, ?_, by omega, le_rfl⟩
      rw [hX, if_neg ha]
      have w1 := wlist_spec cap O (prs [true, true]) (σ.seth R (0 + 1)) hO1
      have f1 := WExec.fwd (cap := cap) R (apd (σ.seth R (0 + 1)) O (prs [true, true]))
      have e1 : (apd (σ.seth R (0 + 1)) O (prs [true, true])).seth R
          ((apd (σ.seth R (0 + 1)) O (prs [true, true])).sh R + 1) = (apd σ O (prs [true, true])).seth R 2 := by
        rw [apd_sh_ne _ O R hRO, apd_seth _ R O hRO, seth_seth']; simp
      rw [e1] at f1
      have lp := apd_loop cap R O hRO (wlist O (prs [true, false])) (prs [true, false]) 16 (fun _ => True)
        (fun τ _ h => wlist_spec cap O (prs [true, false]) τ h) (fun _ _ => trivial) (fun _ _ _ => trivial) (mk a) 1
        (a + 1) (fun q h1 h2 => by rw [rd_mk]; simp only [decide_eq_true_eq]; omega)
        (by rw [rd_mk]; simp only [decide_eq_false_iff_not]; omega) (a - 1) ((apd σ O (prs [true, true])).seth R 2)
        (by simp [apd_st_ne σ O R hRO, hR]) (by simp only [WState.seth_sh, Function.update_self]; omega)
        (by simp only [WState.seth_sh, Function.update_self]; omega) trivial (seth_end _ R O hRO _ (apd_end' σ O _))
      rw [apd_seth _ R O hRO, seth_seth', apd_apd] at lp
      refine WExec.cast cap (WExec.ifsT (by rw [wbit_mk1 _ R a hR1 (by simp)]; simp [ha])
        (WExec.seq w1 (WExec.seq f1 lp))) rfl ?_
      have h20 : (a - 1) * (16 + 4) + 20 = 20 * a := by
        obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring
      simp only [prs, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_cons,
        List.length_nil] at h20 ⊢
      omega
  have tW := wlist_spec cap O (prs [false] ++ [false]) ((apd σ O X).seth R p) (seth_end _ R O hRO _ (apd_end' σ O X))
  rw [apd_seth _ R O hRO, apd_apd] at tW
  have tR := rew_spec cap R a p ((apd σ O (X ++ (prs [false] ++ [false]))).seth R p)
    (by simp [apd_st_ne σ O R hRO, hR]) (by simp) hp1 (Or.inl hp2)
  rw [seth_seth', seth_same _ R 0 (by rw [apd_sh_ne σ O R hRO, hR0])] at tR
  have hw : X ++ (prs [false] ++ [false]) = frame (bin1W a) := by
    rw [frame_prs, hX]; unfold bin1W
    by_cases ha : a = 0
    · rw [if_pos ha, if_pos ha]; rfl
    · rw [if_neg ha, if_neg ha, prs_append, prs_append, prs_repW]; simp only [List.append_assoc]
  rw [hw] at tW tR
  refine WExec.cast cap (WExec.seq t0 (WExec.seq tB (WExec.seq tW tR))) rfl ?_
  have : (prs [false] ++ [false]).length = 3 := rfl
  rw [this]; omega

/-! ## The padded ruler -/

/-- The word `1^x ++ 0^{c − x}` (base's `pad c 1^x`). -/
def padW (x c : ℕ) : List Bool := List.replicate x true ++ List.replicate (c - x) false

theorem padW_eq (x c : ℕ) : padW x c = ZeroPadding.pad c (List.replicate x true) := by
  simp [padW, ZeroPadding.pad]

/-- `frame (padW x c)` from the distinct rulers `mk x`, `mk c`. -/
def padM (X C O : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd X) (.seq (.fwd C) (.seq (.whs X (.seq (wlist O (prs [true])) (.seq (.fwd X) (.ifs C (.fwd C) .skip))))
    (.seq (.whs C (.seq (wlist O (prs [false])) (.fwd C))) (.seq (wlist O [false]) (.seq (rewM X) (rewM C))))))

theorem pad_loop1 (X C O : Fin (ns + 1)) (hXC : X ≠ C) (hXO : X ≠ O) (hCO : C ≠ O) (x c : ℕ) :
    ∀ (k i : ℕ) (σ : WState ns nr), σ.st X = mk x → σ.st C = mk c → σ.sh X = 1 + i → σ.sh C = 1 + min i c →
      i + k = x → σ.sh O = (σ.st O).length →
      WExec cap (.whs X (.seq (wlist O (prs [true])) (.seq (.fwd X) (.ifs C (.fwd C) .skip)))) σ
        (((apd σ O (repW k (prs [true]))).seth X (1 + x)).seth C (1 + min x c)) (15 * k + 1)
  | 0, i, σ, hX, _, hXi, hCi, hk, hO => by
    rw [repW_zero, apd_nil σ O hO, seth_same σ X _ (by omega), seth_same σ C _ (by rw [hCi]; congr 2)]
    exact WExec.whsF (by rw [wbit_mk σ X x _ hX hXi]; simp only [decide_eq_false_iff_not]; omega)
  | k + 1, i, σ, hX, hC, hXi, hCi, hk, hO => by
    have hb : wbit σ X = true := by rw [wbit_mk σ X x _ hX hXi]; simp only [decide_eq_true_eq]; omega
    have w1 := wlist_spec cap O (prs [true]) σ hO
    set τ1 := apd σ O (prs [true]) with hτ1
    have f1 := WExec.fwd (cap := cap) X τ1
    have eX : τ1.sh X = 1 + i := by rw [hτ1, apd_sh_ne σ O X hXO, hXi]
    rw [eX] at f1
    set τ2 := τ1.seth X (1 + i + 1) with hτ2
    have c2 : τ2.st C = mk c := by rw [hτ2]; simp only [WState.seth_st]; rw [hτ1, apd_st_ne σ O C hCO, hC]
    have hc2 : τ2.sh C = 1 + min i c := by
      rw [hτ2]; simp only [WState.seth_sh]; rw [Function.update_of_ne (Ne.symm hXC), hτ1, apd_sh_ne σ O C hCO, hCi]
    obtain ⟨tI, e3⟩ : WExec cap (.ifs C (.fwd C) .skip : WM ns nr) τ2 (τ2.seth C (1 + min (i + 1) c)) 2 ∧ True := by
      refine ⟨?_, trivial⟩
      by_cases hic : i < c
      · have t := WExec.fwd (cap := cap) C τ2
        rw [hc2, show 1 + min i c + 1 = 1 + min (i + 1) c by omega] at t
        exact WExec.cast cap (WExec.ifsT (by rw [wbit_mk τ2 C c _ c2 hc2]; simp only [decide_eq_true_eq]; omega) t)
          rfl (by omega)
      · rw [seth_same τ2 C _ (by rw [hc2]; omega)]
        exact WExec.cast cap (WExec.ifsF (by rw [wbit_mk τ2 C c _ c2 hc2]; simp only [decide_eq_false_iff_not]; omega)
          (WExec.skip _)) rfl (by omega)
    set τ3 := τ2.seth C (1 + min (i + 1) c) with hτ3
    have ih := pad_loop1 X C O hXC hXO hCO x c k (i + 1) τ3
      (by rw [hτ3, hτ2]; simp only [WState.seth_st]; rw [hτ1, apd_st_ne σ O X hXO, hX])
      (by rw [hτ3]; simp only [WState.seth_st]; exact c2)
      (by rw [hτ3, hτ2]; simp only [WState.seth_sh]; rw [Function.update_of_ne hXC]; simp only [Function.update_self]
          omega)
      (by rw [hτ3]; simp)
      (by omega)
      (by rw [hτ3, hτ2]; exact seth_end _ C O hCO _ (seth_end _ X O hXO _ (apd_end' σ O _)))
    have eF : ((apd τ3 O (repW k (prs [true]))).seth X (1 + x)).seth C (1 + min x c) =
        ((apd σ O (repW (k + 1) (prs [true]))).seth X (1 + x)).seth C (1 + min x c) := by
      rw [hτ3, hτ2, hτ1, apd_seth _ C O hCO, apd_seth _ X O hXO, apd_apd, ← repW_succ]
      rw [seth_comm _ C X (Ne.symm hXC), seth_seth', seth_seth']
    rw [eF] at ih
    exact WExec.cast cap (WExec.whsT hb (WExec.seq w1 (WExec.seq f1 tI)) ih) rfl (by
      simp only [prs, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_cons, List.length_nil]
      omega)

theorem padM_spec (X C O : Fin (ns + 1)) (hXC : X ≠ C) (hXO : X ≠ O) (hCO : C ≠ O) (x c : ℕ) (σ : WState ns nr)
    (hX : σ.st X = mk x) (hC : σ.st C = mk c) (hX0 : σ.sh X = 0) (hC0 : σ.sh C = 0) (hO : σ.sh O = (σ.st O).length) :
    WExec cap (padM X C O) σ (apd σ O (frame (padW x c))) (20 * x + 16 * c + 40) := by
  have t0 := WExec.fwd (cap := cap) X σ
  rw [hX0] at t0
  have t1 := WExec.fwd (cap := cap) C (σ.seth X (0 + 1))
  have e1 : (σ.seth X (0 + 1)).sh C = 0 := by simp only [WState.seth_sh]; rw [Function.update_of_ne (Ne.symm hXC), hC0]
  rw [e1] at t1
  set σ1 := (σ.seth X (0 + 1)).seth C (0 + 1) with hσ1
  have l1 := pad_loop1 cap X C O hXC hXO hCO x c x 0 σ1 (by rw [hσ1]; simp [hX]) (by rw [hσ1]; simp [hC])
    (by rw [hσ1]; simp only [WState.seth_sh]; rw [Function.update_of_ne hXC]; simp only [Function.update_self])
    (by rw [hσ1]; simp) (by omega)
    (by rw [hσ1]; exact seth_end _ C O hCO _ (seth_end _ X O hXO _ hO))
  have eL : ((apd σ1 O (repW x (prs [true]))).seth X (1 + x)).seth C (1 + min x c) =
      ((apd σ O (repW x (prs [true]))).seth X (1 + x)).seth C (1 + min x c) := by
    rw [hσ1, apd_seth _ C O hCO, apd_seth _ X O hXO, seth_comm _ X C hXC, seth_seth', seth_comm _ C X (Ne.symm hXC),
      seth_seth']
  rw [eL] at l1
  set σ2 := ((apd σ O (repW x (prs [true]))).seth X (1 + x)).seth C (1 + min x c) with hσ2
  have hC2 : σ2.st C = mk c := by rw [hσ2]; simp only [WState.seth_st]; rw [apd_st_ne σ O C hCO, hC]
  have l2 := apd_loop cap C O hCO (wlist O (prs [false])) (prs [false]) 8 (fun _ => True)
    (fun τ _ h => wlist_spec cap O (prs [false]) τ h) (fun _ _ => trivial) (fun _ _ _ => trivial) (mk c) 1 (c + 1)
    (fun q h1 h2 => by rw [rd_mk]; simp only [decide_eq_true_eq]; omega)
    (by rw [rd_mk]; simp only [decide_eq_false_iff_not]; omega) (c - x) σ2 hC2 (by rw [hσ2]; simp; omega)
    (by rw [hσ2]; simp) trivial (by rw [hσ2]; exact seth_end _ C O hCO _ (seth_end _ X O hXO _ (apd_end' σ O _)))
  have eL2 : (apd σ2 O (repW (c - x) (prs [false]))).seth C (c + 1) =
      ((apd σ O (repW x (prs [true]) ++ repW (c - x) (prs [false]))).seth X (1 + x)).seth C (c + 1) := by
    rw [hσ2, apd_seth _ C O hCO, apd_seth _ X O hXO, apd_apd, seth_seth']
  rw [eL2] at l2
  set σ3 := ((apd σ O (repW x (prs [true]) ++ repW (c - x) (prs [false]))).seth X (1 + x)).seth C (c + 1) with hσ3
  have tW := wlist_spec cap O [false] σ3 (by rw [hσ3]; exact seth_end _ C O hCO _ (seth_end _ X O hXO _ (apd_end' σ O _)))
  have eW : apd σ3 O [false] = ((apd σ O (repW x (prs [true]) ++ repW (c - x) (prs [false]) ++ [false])).seth X
      (1 + x)).seth C (c + 1) := by
    rw [hσ3, apd_seth _ C O hCO, apd_seth _ X O hXO, apd_apd]
  rw [eW] at tW
  set Y := repW x (prs [true]) ++ repW (c - x) (prs [false]) ++ [false] with hY
  have rX := rew_spec cap X x (1 + x) (((apd σ O Y).seth X (1 + x)).seth C (c + 1))
    (by simp [apd_st_ne σ O X hXO, hX]) (by simp only [WState.seth_sh]; rw [Function.update_of_ne hXC]; simp)
    (by omega) (Or.inl (by omega))
  have eX : (((apd σ O Y).seth X (1 + x)).seth C (c + 1)).seth X 0 = (apd σ O Y).seth C (c + 1) := by
    rw [seth_comm _ C X (Ne.symm hXC), seth_seth', seth_same _ X 0 (by rw [apd_sh_ne σ O X hXO, hX0])]
  rw [eX] at rX
  have rC := rew_spec cap C c (c + 1) ((apd σ O Y).seth C (c + 1)) (by simp [apd_st_ne σ O C hCO, hC]) (by simp)
    (by omega) (Or.inl le_rfl)
  rw [seth_seth', seth_same _ C 0 (by rw [apd_sh_ne σ O C hCO, hC0])] at rC
  have hw : Y = frame (padW x c) := by
    rw [hY, frame_prs, padW, prs_append, prs_rep_true, prs_rep_false]; rfl
  rw [hw] at tW rX rC
  refine WExec.cast cap (WExec.seq t0 (WExec.seq t1 (WExec.seq l1 (WExec.seq l2 (WExec.seq tW (WExec.seq rX rC))))))
    rfl ?_
  have hmul : (c - x) * (8 + 4) ≤ 12 * c := by
    have := Nat.mul_le_mul_right (8 + 4) (show c - x ≤ c by omega); omega
  simp only [List.length_singleton]
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4KW

