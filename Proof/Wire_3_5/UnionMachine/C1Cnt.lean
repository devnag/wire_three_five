import Proof.Wire_3_5.UnionMachine.C1Rat
import Proof.Wire_3_5.Primitive.Writers.ParseNat

/-! # C6 front, the C1 dock: a variable's incidence count `c_X` (P3:3395-3399)

The union's weight `p_X = c_X/(2·2^{cb})` counts the clause positions naming `X` (`UnionGuess.weight`, P3:3395-3399).
The PCPP output word (`pcppOutput`: `natListWord [sys, aux, cb]`, the systematic bitmaps, `natListWord` of the literal
indices `2i`, `2i+1`) is read once per variable:
* **`litBody_spec`**: one literal index `ℓ` read (PA's `readNatM`), `c += [ℓ/2 = X]` (PA's `halveM`, `gtFlagW`);
* **`cntW_spec`**: the header, the bitmaps skipped (`sys·q` cells), the literal list: `CNT = #{ℓ ∈ lits : ℓ/2 = X}`
  and `CB = cb`.

Paper quantity of the main type: the incidence count `c_X` of a PCPP variable. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Cnt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.RepairRepresentation (natWord)

/-- The literal indices naming `x`. -/
def cntOf (x : ℕ) (lits : List ℕ) : ℕ := (lits.filter fun l => l / 2 = x).length

theorem cntOf_snoc (x : ℕ) (lits : List ℕ) (l : ℕ) :
    cntOf x (lits ++ [l]) = cntOf x lits + (if l / 2 = x then 1 else 0) := by
  unfold cntOf; rw [List.filter_append]; by_cases h : l / 2 = x <;> simp [h]

theorem pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
    rw [pow_succ]; omega

/-- A uniform bound of PA's reader's cost at values `≤ V`. -/
def rdC (V : ℕ) : ℕ := (V + 3) * (80 * V + 120)

theorem rd_le (x V : ℕ) (h : x ≤ V) : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ rdC V := by
  unfold rdC
  have h1 : natBitLength x ≤ x + 1 := by
    unfold natBitLength; have := Nat.log_lt_self 2 (show x + 1 ≠ 0 by omega)
    have := Nat.log_mono_right (show x ≤ x + 1 by omega) (b := 2); omega
  have h2 := pow_nbl_le x
  apply Nat.mul_le_mul <;> omega

section Prog
variable {ns nr : ℕ} (cap : ℕ) (po : Fin (ns + 1)) (W : Fin 20 ↪ Fin nr)

def g1 : Fin 6 ↪ Fin 20 := ⟨![6, 0, 14, 16, 17, 18], by decide⟩
def g2 : Fin 6 ↪ Fin 20 := ⟨![0, 6, 15, 16, 17, 18], by decide⟩

/-- One literal: `L := ℓ/2`, `CNT += [L = X]`. Registers: `X = W 0`, `CNT = W 2`, `L = W 6`, reader scratch
`W 8 … W 11`, halving `W 12, W 13`, flags `W 14, W 15`, compare scratch `W 16 … W 18`. -/
def litBody : WM ns nr :=
  .seq (readNatM false po (W 8) (W 9) (W 6) (W 10) (W 11)) (.seq (halveM (W 6) (W 12) (W 13))
    (.seq (WM.clear (W 13)) (.seq (gtFlagW (g1.trans W)) (.seq (gtFlagW (g2.trans W))
      (.seq (.ifr (W 14) (WM.clear (W 14)) (.ifr (W 15) (WM.clear (W 15)) (.inc (W 2)))) (WM.clear (W 6)))))))

/-- One literal's cost at values `≤ V`. -/
def litC (V : ℕ) : ℕ := rdC V + 200 * V + 100

theorem litBody_spec (σ : WState ns nr) (x n l V : ℕ) (pre rest : List Bool)
    (hst : σ.st po = pre ++ natWord l ++ rest) (hsh : σ.sh po = pre.length) (hx : σ.val (W 0) = x)
    (hn : σ.val (W 2) = n) (h6 : σ.val (W 6) = 0) (h8 : σ.val (W 8) = 0) (h9 : σ.val (W 9) = 0)
    (h10 : σ.val (W 10) = 0) (h11 : σ.val (W 11) = 0) (h12 : σ.val (W 12) = 0) (h13 : σ.val (W 13) = 0)
    (h14 : σ.val (W 14) = 0) (h15 : σ.val (W 15) = 0) (h16 : σ.val (W 16) = 0) (h17 : σ.val (W 17) = 0)
    (h18 : σ.val (W 18) = 0) (hlV : l ≤ V) (hxV : x ≤ V) (hcap : n + 4 * V + 8 ≤ cap) :
    WExec cap (litBody po W) σ ((σ.seth po (pre.length + (natWord l).length)).setv (W 2)
      (n + if l / 2 = x then 1 else 0)) (litC V) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → W i ≠ W j := fun h => W.injective.ne h
  have hpl := pow_nbl_le l
  -- 1. L := l
  have e1 := readNatM_spec cap false po (W 8) (W 9) (W 6) (W 10) (W 11) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) l pre rest σ (by simp [PrimAsm.ParseNat.enc, hst]) hsh h8 h9 h10 h11
    (by rw [h6, pow_succ]; omega)
  rw [h6, Nat.zero_add] at e1
  simp only [stp, Bool.false_eq_true, if_false, one_mul] at e1
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = (σ.seth po (pre.length + (natWord l).length)).setv (W 6) l := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have f1 : ∀ j, j ≠ W 6 → σ1.val j = σ.val j := fun j hj => by rw [hσ1]; simp [hj]
  -- 2. L := l/2, RB := l%2
  have e2 := halveM_spec cap (W 6) (W 12) (W 13) (hne (by decide)) (hne (by decide)) (hne (by decide)) σ1
    (by rw [f1 _ (hne (by decide)), h12]) (by rw [f1 _ (hne (by decide)), h13])
    (by rw [hσ1]; simp; omega) (by omega)
  have v16 : σ1.val (W 6) = l := by rw [hσ1]; simp
  rw [v16] at e2
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = (σ1.setv (W 6) (l / 2)).setv (W 13) (l % 2) := ⟨_, rfl⟩
  rw [← hσ2] at e2
  -- 3. RB := 0
  have v213 : σ2.val (W 13) = l % 2 := by rw [hσ2]; simp
  have e3 := wclear_spec cap (W 13) (l % 2) σ2 v213 (by rw [v213]; omega)
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setv (W 13) 0 := ⟨_, rfl⟩
  rw [← hσ3] at e3
  have f3 : ∀ j, j ≠ W 6 → σ3.val j = σ.val j := fun j hj => by
    rw [hσ3, hσ2]
    by_cases h13' : j = W 13
    · subst h13'; simp [h13]
    · simp [h13', hj, f1 j hj]
  have v36 : σ3.val (W 6) = l / 2 := by rw [hσ3, hσ2]; simp [hne (show (6 : Fin 20) ≠ 13 by decide)]
  -- 4. G1 := [x < l/2]
  have e4 := gtFlagW_spec cap (g1.trans W) σ3 (by show σ3.val (W 14) = 0; rw [f3 _ (hne (by decide)), h14])
    (by show σ3.val (W 16) = 0; rw [f3 _ (hne (by decide)), h16])
    (by show σ3.val (W 17) = 0; rw [f3 _ (hne (by decide)), h17])
    (by show σ3.val (W 18) = 0; rw [f3 _ (hne (by decide)), h18])
    (by show σ3.val (W 6) ≤ cap; rw [v36]; omega) (by show σ3.val (W 0) ≤ cap; rw [f3 _ (hne (by decide)), hx]; omega)
    (by omega)
  have t0 : (g1.trans W) 0 = W 6 := rfl
  have t1 : (g1.trans W) 1 = W 0 := rfl
  have t2 : (g1.trans W) 2 = W 14 := rfl
  rw [t0, t1, t2, v36, f3 _ (hne (by decide)), hx] at e4
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setv (W 14) (if x < l / 2 then 1 else 0) := ⟨_, rfl⟩
  rw [← hσ4] at e4
  have f4 : ∀ j, j ≠ W 14 → σ4.val j = σ3.val j := fun j hj => by rw [hσ4]; simp [hj]
  -- 5. G2 := [l/2 < x]
  have e5 := gtFlagW_spec cap (g2.trans W) σ4
    (by show σ4.val (W 15) = 0; rw [f4 _ (hne (by decide)), f3 _ (hne (by decide)), h15])
    (by show σ4.val (W 16) = 0; rw [f4 _ (hne (by decide)), f3 _ (hne (by decide)), h16])
    (by show σ4.val (W 17) = 0; rw [f4 _ (hne (by decide)), f3 _ (hne (by decide)), h17])
    (by show σ4.val (W 18) = 0; rw [f4 _ (hne (by decide)), f3 _ (hne (by decide)), h18])
    (by show σ4.val (W 0) ≤ cap; rw [f4 _ (hne (by decide)), f3 _ (hne (by decide)), hx]; omega)
    (by show σ4.val (W 6) ≤ cap; rw [f4 _ (hne (by decide)), v36]; omega) (by omega)
  have u0 : (g2.trans W) 0 = W 0 := rfl
  have u1 : (g2.trans W) 1 = W 6 := rfl
  have u2 : (g2.trans W) 2 = W 15 := rfl
  rw [u0, u1, u2, f4 (W 0) (hne (by decide)), f3 (W 0) (hne (by decide)), hx, f4 (W 6) (hne (by decide)), v36] at e5
  obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = σ4.setv (W 15) (if l / 2 < x then 1 else 0) := ⟨_, rfl⟩
  rw [← hσ5] at e5
  have v514 : σ5.val (W 14) = if x < l / 2 then 1 else 0 := by
    rw [hσ5, hσ4]; simp [hne (show (14 : Fin 20) ≠ 15 by decide)]
  have v515 : σ5.val (W 15) = if l / 2 < x then 1 else 0 := by rw [hσ5]; simp
  have v52 : σ5.val (W 2) = n := by
    rw [hσ5, hσ4]; simp [hne (show (2 : Fin 20) ≠ 15 by decide), hne (show (2 : Fin 20) ≠ 14 by decide)]
    rw [f3 _ (hne (by decide)), hn]
  have v56 : σ5.val (W 6) = l / 2 := by
    rw [hσ5, hσ4]; simp [hne (show (6 : Fin 20) ≠ 15 by decide), hne (show (6 : Fin 20) ≠ 14 by decide), v36]
  -- 6. the count, 7. L := 0
  have key : ∃ σ6 : WState ns nr, WExec cap (.ifr (W 14) (WM.clear (W 14)) (.ifr (W 15) (WM.clear (W 15))
      (.inc (W 2)))) σ5 σ6 6 ∧
      σ6 = ((σ5.setv (W 14) 0).setv (W 15) 0).setv (W 2) (n + if l / 2 = x then 1 else 0) := by
    by_cases hA : x < l / 2
    · have hB : ¬ l / 2 < x := by omega
      have hE : ¬ l / 2 = x := by omega
      have c1 := wclear_spec cap (W 14) 1 σ5 (by rw [v514, if_pos hA]) (by rw [v514, if_pos hA]; omega)
      refine ⟨_, WExec.mono (WExec.ifrT (by rw [v514, if_pos hA]; exact one_ne_zero) c1) (by omega), ?_⟩
      rw [if_neg hE, Nat.add_zero, ← hn]
      refine WState.eq rfl rfl ?_ rfl
      funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases a2 : j = W 2
      · subst a2; simp [hne (show (2 : Fin 20) ≠ 14 by decide), hne (show (2 : Fin 20) ≠ 15 by decide), v52, hn]
      by_cases a15 : j = W 15
      · subst a15; simp [hne (show (15 : Fin 20) ≠ 14 by decide), v515, hB]
      simp [a2, a15]
    · by_cases hB : l / 2 < x
      · have hE : ¬ l / 2 = x := by omega
        have c1 := wclear_spec cap (W 15) 1 σ5 (by rw [v515, if_pos hB]) (by rw [v515, if_pos hB]; omega)
        have hB1 : σ5.val (W 15) ≠ 0 := by rw [v515, if_pos hB]; exact one_ne_zero
        refine ⟨_, WExec.mono (WExec.ifrF (by rw [v514, if_neg hA]) (WExec.ifrT hB1 c1)) (by omega), ?_⟩
        rw [if_neg hE, Nat.add_zero, ← hn]
        refine WState.eq rfl rfl ?_ rfl
        funext j
        simp only [WState.setv_val, Function.update_apply]
        by_cases a2 : j = W 2
        · subst a2; simp [hne (show (2 : Fin 20) ≠ 14 by decide), hne (show (2 : Fin 20) ≠ 15 by decide), v52, hn]
        by_cases a14 : j = W 14
        · subst a14; simp [hne (show (14 : Fin 20) ≠ 15 by decide), v514, hA]
        simp [a2, a14]
      · have hE : l / 2 = x := by omega
        have c1 := WExec.inc (cap := cap) (W 2) σ5 (by rw [v52]; omega)
        refine ⟨_, WExec.mono (WExec.ifrF (by rw [v514, if_neg hA]) (WExec.ifrF (by rw [v515, if_neg hB]) c1))
          (by omega), ?_⟩
        rw [if_pos hE, v52]
        refine WState.eq rfl rfl ?_ rfl
        funext j
        simp only [WState.setv_val, Function.update_apply]
        by_cases a2 : j = W 2
        · subst a2; simp [hne (show (2 : Fin 20) ≠ 14 by decide), hne (show (2 : Fin 20) ≠ 15 by decide)]
        by_cases a14 : j = W 14
        · subst a14; simp [hne (show (14 : Fin 20) ≠ 15 by decide), v514, hA]
        by_cases a15 : j = W 15
        · subst a15; simp [v515, hB]
        simp [a2, a14, a15]
  obtain ⟨σ6, e6, hσ6⟩ := key
  have v66 : σ6.val (W 6) = l / 2 := by
    rw [hσ6]; simp [hne (show (6 : Fin 20) ≠ 2 by decide), hne (show (6 : Fin 20) ≠ 15 by decide),
      hne (show (6 : Fin 20) ≠ 14 by decide), v56]
  have e7 := wclear_spec cap (W 6) (l / 2) σ6 v66 (by rw [v66]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7)))))) ?_ le_rfl) ?_
  · rw [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
    refine WState.eq rfl rfl ?_ rfl
    funext j
    simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases a6 : j = W 6
    · subst a6; simp [hne (show (6 : Fin 20) ≠ 2 by decide), h6]
    by_cases a2 : j = W 2
    · subst a2; simp [a6, hne (show (2 : Fin 20) ≠ 14 by decide), hne (show (2 : Fin 20) ≠ 15 by decide)]
    by_cases a14 : j = W 14
    · subst a14; simp [a6, a2, hne (show (14 : Fin 20) ≠ 15 by decide), h14]
    by_cases a15 : j = W 15
    · subst a15; simp [a6, a2, a14, h15]
    by_cases a13 : j = W 13
    · subst a13; simp [a6, a2, a14, a15, h13]
    simp [a6, a2, a14, a15, a13]
  · unfold litC
    have r1 := rd_le l V hlV
    have hl2 : l / 2 ≤ V := by omega
    omega

theorem take_succ_getD (lits : List ℕ) (k : ℕ) (hk : k < lits.length) :
    lits.take (k + 1) = lits.take k ++ [lits.getD k 0] := by
  rw [List.take_succ_eq_append_getElem hk, List.getD_eq_getElem _ _ hk]

theorem flat_split (lits : List ℕ) (k : ℕ) (hk : k < lits.length) :
    lits.flatMap natWord = (lits.take k).flatMap natWord ++ natWord (lits.getD k 0) ++
      (lits.drop (k + 1)).flatMap natWord := by
  conv_lhs => rw [← List.take_append_drop (k + 1) lits]
  rw [take_succ_getD lits k hk]
  simp [List.flatMap_append]

theorem getD_mem (lits : List ℕ) (k : ℕ) (hk : k < lits.length) : lits.getD k 0 ∈ lits := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

/-- **The literal loop**: `LEN = |lits|` rounds of `litBody`. -/
theorem litLoop_spec (σ : WState ns nr) (x V : ℕ) (lits : List ℕ) (pre rest : List Bool)
    (hst : σ.st po = pre ++ lits.flatMap natWord ++ rest) (hsh : σ.sh po = pre.length) (hx : σ.val (W 0) = x)
    (hn : σ.val (W 2) = 0) (hlen : σ.val (W 5) = lits.length) (h6 : σ.val (W 6) = 0) (h8 : σ.val (W 8) = 0)
    (h9 : σ.val (W 9) = 0) (h10 : σ.val (W 10) = 0) (h11 : σ.val (W 11) = 0) (h12 : σ.val (W 12) = 0)
    (h13 : σ.val (W 13) = 0) (h14 : σ.val (W 14) = 0) (h15 : σ.val (W 15) = 0) (h16 : σ.val (W 16) = 0)
    (h17 : σ.val (W 17) = 0) (h18 : σ.val (W 18) = 0) (hV : ∀ l ∈ lits, l ≤ V) (hxV : x ≤ V)
    (hcap : lits.length + 4 * V + 8 ≤ cap) :
    WExec cap (.whr (W 5) (.seq (.dec (W 5)) (litBody po W))) σ
      (((σ.seth po (pre.length + (lits.flatMap natWord).length)).setv (W 2) (cntOf x lits)).setv (W 5) 0)
      (lits.length * (litC V + 4) + 1) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → W i ≠ W j := fun h => W.injective.ne h
  set n := lits.length with hnl
  set S : ℕ → WState ns nr := fun k => ((σ.seth po (pre.length + ((lits.take k).flatMap natWord).length)).setv (W 2)
    (cntOf x (lits.take k))).setv (W 5) (n - k) with hS
  have hS0 : S 0 = σ := by
    simp only [hS, List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero, Nat.sub_zero]
    rw [← hsh, wseth_same, show cntOf x [] = 0 from rfl, ← hn, ← hlen, wsetv_same, wsetv_same]
  have hSn : S n = ((σ.seth po (pre.length + (lits.flatMap natWord).length)).setv (W 2) (cntOf x lits)).setv (W 5) 0 := by
    simp only [hS, Nat.sub_self]; rw [hnl, List.take_length]
  have hloop := UnionMachine.Round.wloop cap (W 5) (litBody po W) (litC V) n S
    (fun k _ => by simp [hS])
    (by omega)
    (fun k hk => by
      have hk' : k < lits.length := hk
      set σk := (S k).setv (W 5) (n - k - 1) with hσk
      have g : ∀ j, j ≠ W 2 → j ≠ W 5 → σk.val j = σ.val j := fun j a b => by simp [hσk, hS, a, b]
      have hb := litBody_spec cap po W σk x (cntOf x (lits.take k)) (lits.getD k 0) V
        (pre ++ (lits.take k).flatMap natWord) ((lits.drop (k + 1)).flatMap natWord ++ rest)
        (by simp only [hσk, hS, WState.setv_st, WState.seth_st]; rw [hst, flat_split lits k hk']; simp)
        (by simp [hσk, hS])
        (by rw [g _ (hne (by decide)) (hne (by decide)), hx])
        (by simp [hσk, hS, hne (show (2 : Fin 20) ≠ 5 by decide)])
        (by rw [g _ (hne (by decide)) (hne (by decide)), h6]) (by rw [g _ (hne (by decide)) (hne (by decide)), h8])
        (by rw [g _ (hne (by decide)) (hne (by decide)), h9]) (by rw [g _ (hne (by decide)) (hne (by decide)), h10])
        (by rw [g _ (hne (by decide)) (hne (by decide)), h11]) (by rw [g _ (hne (by decide)) (hne (by decide)), h12])
        (by rw [g _ (hne (by decide)) (hne (by decide)), h13]) (by rw [g _ (hne (by decide)) (hne (by decide)), h14])
        (by rw [g _ (hne (by decide)) (hne (by decide)), h15]) (by rw [g _ (hne (by decide)) (hne (by decide)), h16])
        (by rw [g _ (hne (by decide)) (hne (by decide)), h17]) (by rw [g _ (hne (by decide)) (hne (by decide)), h18])
        (hV _ (getD_mem lits k hk')) hxV
        (by
          have : cntOf x (lits.take k) ≤ k := by
            unfold cntOf; exact (List.length_filter_le _ _).trans (by simp)
          omega)
      refine WExec.cast cap hb ?_ le_rfl
      simp only [hσk, hS]
      rw [take_succ_getD lits k hk', cntOf_snoc]
      refine WState.eq ?_ rfl ?_ rfl
      · funext j; by_cases hj : j = po
        · subst hj; simp [List.flatMap_append]; omega
        · simp [hj]
      · funext j
        simp only [WState.setv_val, WState.seth_val, Function.update_apply]
        by_cases a5 : j = W 5
        · subst a5; simp [hne (show (5 : Fin 20) ≠ 2 by decide)]; omega
        · by_cases a2 : j = W 2
          · subst a2; simp [hne (show (2 : Fin 20) ≠ 5 by decide)]
          · simp [a5, a2])
  rw [hS0, hSn] at hloop
  exact hloop

def m5 : Fin 5 ↪ Fin 20 := ⟨![4, 1, 7, 16, 17], by decide⟩

/-- **The count**: the header (`K = W 19`, `SYS = W 4`, `CB = W 3`), the bitmaps skipped (`SK = W 7`, `Q = W 1`),
the list length (`LEN = W 5`), the literal loop. -/
def cntW : WM ns nr :=
  .seq (readNatM false po (W 8) (W 9) (W 19) (W 10) (W 11)) (.seq (WM.clear (W 19))
    (.seq (readNatM false po (W 8) (W 9) (W 4) (W 10) (W 11)) (.seq (readNatM false po (W 8) (W 9) (W 19) (W 10) (W 11))
      (.seq (WM.clear (W 19)) (.seq (readNatM false po (W 8) (W 9) (W 3) (W 10) (W 11))
        (.seq (mulAddW (m5.trans W)) (.seq (.whr (W 7) (.seq (.dec (W 7)) (.fwd po)))
          (.seq (readNatM false po (W 8) (W 9) (W 5) (W 10) (W 11))
            (.seq (.whr (W 5) (.seq (.dec (W 5)) (litBody po W))) (WM.clear (W 4)))))))))))

/-- The PCPP output word's shape (`pcppOutput`). -/
def poWord (sys aux cb : ℕ) (bits : List Bool) (lits : List ℕ) : List Bool :=
  natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ bits ++ natWord lits.length ++ lits.flatMap natWord

/-- The count's cost. -/
def cntC (V q n : ℕ) : ℕ := 6 * rdC V + 40 * V + q * (18 * V + 8) + 18 * q + 5 * (V * q) + n * (litC V + 4) + 100

theorem cntW_spec (σ : WState ns nr) (x q sys aux cb V : ℕ) (bits : List Bool) (lits : List ℕ) (rest : List Bool)
    (hst : σ.st po = poWord sys aux cb bits lits ++ rest) (hsh : σ.sh po = 0) (hbits : bits.length = sys * q)
    (hx : σ.val (W 0) = x) (hq : σ.val (W 1) = q) (hz : ∀ i : Fin 20, 2 ≤ i.val → σ.val (W i) = 0)
    (hsV : sys ≤ V) (haV : aux ≤ V) (hcV : cb ≤ V) (hlV : lits.length ≤ V) (hV : ∀ l ∈ lits, l ≤ V) (hxV : x ≤ V)
    (h3 : 3 ≤ V) (hcap : sys * q + q + lits.length + 6 * V + 8 ≤ cap) :
    WExec cap (cntW po W) σ (((σ.seth po (poWord sys aux cb bits lits).length).setv (W 2) (cntOf x lits)).setv (W 3) cb)
      (cntC V q lits.length) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → W i ≠ W j := fun h => W.injective.ne h
  have z : ∀ i : Fin 20, 2 ≤ i.val → σ.val (W i) = 0 := hz
  have pw : ∀ y, y ≤ V → y + 2 ^ (natBitLength y + 1) ≤ cap := fun y hy => by
    have := pow_nbl_le y; rw [pow_succ]; omega
  -- 1. K := 3
  have e1 := readNatM_spec cap false po (W 8) (W 9) (W 19) (W 10) (W 11) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) 3 [] (natWord sys ++ natWord aux ++ natWord cb ++ bits ++
      natWord lits.length ++ lits.flatMap natWord ++ rest) σ
    (by rw [hst]; simp [PrimAsm.ParseNat.enc, poWord]) (by rw [hsh]; rfl) (z 8 (by decide)) (z 9 (by decide))
    (z 10 (by decide)) (z 11 (by decide)) (by rw [z 19 (by decide)]; have := pw 3 h3; omega)
  simp only [stp, Bool.false_eq_true, if_false, one_mul, List.length_nil, Nat.zero_add, z 19 (by decide)] at e1
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = (σ.seth po (natWord 3).length).setv (W 19) 3 := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have e2 := wclear_spec cap (W 19) 3 σ1 (by rw [hσ1]; simp) (by rw [hσ1]; simp; omega)
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setv (W 19) 0 := ⟨_, rfl⟩
  rw [← hσ2] at e2
  have f2 : ∀ j, σ2.val j = σ.val j := fun j => by
    rw [hσ2, hσ1]; by_cases hj : j = W 19
    · subst hj; simp [z 19 (by decide)]
    · simp [hj]
  have s2 : σ2.st = σ.st := by rw [hσ2, hσ1]; rfl
  have sh2 : σ2.sh po = (natWord 3).length := by rw [hσ2, hσ1]; simp
  -- 3. SYS := sys
  have e3 := readNatM_spec cap false po (W 8) (W 9) (W 4) (W 10) (W 11) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) sys (natWord 3) (natWord aux ++ natWord cb ++ bits ++
      natWord lits.length ++ lits.flatMap natWord ++ rest) σ2
    (by rw [s2, hst]; simp [PrimAsm.ParseNat.enc, poWord]) sh2 (by rw [f2, z 8 (by decide)])
    (by rw [f2, z 9 (by decide)]) (by rw [f2, z 10 (by decide)]) (by rw [f2, z 11 (by decide)])
    (by rw [f2, z 4 (by decide)]; have := pw sys hsV; omega)
  simp only [stp, Bool.false_eq_true, if_false, one_mul, f2, z 4 (by decide), Nat.zero_add] at e3
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = (σ2.seth po ((natWord 3).length + (natWord sys).length)).setv (W 4) sys := ⟨_, rfl⟩
  rw [← hσ3] at e3
  have f3 : ∀ j, j ≠ W 4 → σ3.val j = σ.val j := fun j hj => by rw [hσ3]; simp [hj, f2]
  -- 4. K := aux
  have e4 := readNatM_spec cap false po (W 8) (W 9) (W 19) (W 10) (W 11) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) aux (natWord 3 ++ natWord sys) (natWord cb ++ bits ++
      natWord lits.length ++ lits.flatMap natWord ++ rest) σ3
    (by rw [hσ3]; simp only [WState.setv_st, WState.seth_st]; rw [s2, hst]; simp [PrimAsm.ParseNat.enc, poWord])
    (by rw [hσ3]; simp) (by rw [f3 _ (hne (by decide)), z 8 (by decide)])
    (by rw [f3 _ (hne (by decide)), z 9 (by decide)]) (by rw [f3 _ (hne (by decide)), z 10 (by decide)])
    (by rw [f3 _ (hne (by decide)), z 11 (by decide)])
    (by rw [f3 _ (hne (by decide)), z 19 (by decide)]; have := pw aux haV; omega)
  simp only [stp, Bool.false_eq_true, if_false, one_mul, f3 _ (hne (show (19 : Fin 20) ≠ 4 by decide)),
    z 19 (by decide), Nat.zero_add, List.length_append] at e4
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = (σ3.seth po ((natWord 3).length + (natWord sys).length + (natWord aux).length)).setv
    (W 19) aux := ⟨_, rfl⟩
  rw [← hσ4] at e4
  have e5 := wclear_spec cap (W 19) aux σ4 (by rw [hσ4]; simp) (by rw [hσ4]; simp; omega)
  obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = σ4.setv (W 19) 0 := ⟨_, rfl⟩
  rw [← hσ5] at e5
  have f5 : ∀ j, j ≠ W 4 → σ5.val j = σ.val j := fun j hj => by
    rw [hσ5, hσ4]; by_cases h19 : j = W 19
    · subst h19; simp [z 19 (by decide)]
    · simp [h19, f3 j hj]
  have v54 : σ5.val (W 4) = sys := by
    rw [hσ5, hσ4, hσ3]; simp [hne (show (4 : Fin 20) ≠ 19 by decide)]
  -- 6. CB := cb
  have e6 := readNatM_spec cap false po (W 8) (W 9) (W 3) (W 10) (W 11) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) cb (natWord 3 ++ natWord sys ++ natWord aux) (bits ++
      natWord lits.length ++ lits.flatMap natWord ++ rest) σ5
    (by rw [hσ5, hσ4, hσ3]; simp only [WState.setv_st, WState.seth_st]; rw [s2, hst]; simp [PrimAsm.ParseNat.enc, poWord])
    (by rw [hσ5, hσ4]; simp; try omega) (by rw [f5 _ (hne (by decide)), z 8 (by decide)])
    (by rw [f5 _ (hne (by decide)), z 9 (by decide)]) (by rw [f5 _ (hne (by decide)), z 10 (by decide)])
    (by rw [f5 _ (hne (by decide)), z 11 (by decide)])
    (by rw [f5 _ (hne (by decide)), z 3 (by decide)]; have := pw cb hcV; omega)
  simp only [stp, Bool.false_eq_true, if_false, one_mul, f5 _ (hne (show (3 : Fin 20) ≠ 4 by decide)),
    z 3 (by decide), Nat.zero_add, List.length_append] at e6
  obtain ⟨σ6, hσ6⟩ : ∃ τ, τ = (σ5.seth po ((natWord 3).length + (natWord sys).length + (natWord aux).length +
    (natWord cb).length)).setv (W 3) cb := ⟨_, rfl⟩
  rw [← hσ6] at e6
  have f6 : ∀ j, j ≠ W 4 → j ≠ W 3 → σ6.val j = σ.val j := fun j a b => by rw [hσ6]; simp [b, f5 j a]
  have v64 : σ6.val (W 4) = sys := by rw [hσ6]; simp [hne (show (4 : Fin 20) ≠ 3 by decide), v54]
  -- 7. SK := sys·q
  have e7 := mulAddW_spec cap (m5.trans W) σ6
    (by show σ6.val (W 16) = 0; rw [f6 _ (hne (by decide)) (hne (by decide)), z 16 (by decide)])
    (by show σ6.val (W 17) = 0; rw [f6 _ (hne (by decide)) (hne (by decide)), z 17 (by decide)])
    (by show σ6.val (W 1) ≤ cap; rw [f6 _ (hne (by decide)) (hne (by decide)), hq]; omega)
    (by show σ6.val (W 7) + σ6.val (W 4) * σ6.val (W 1) ≤ cap
        rw [f6 _ (hne (by decide)) (hne (by decide)), z 7 (by decide), v64, f6 _ (hne (by decide)) (hne (by decide)),
          hq]; omega)
    (by show σ6.val (W 4) ≤ cap; rw [v64]; omega)
  have t0 : (m5.trans W) 0 = W 4 := rfl
  have t1 : (m5.trans W) 1 = W 1 := rfl
  have t2 : (m5.trans W) 2 = W 7 := rfl
  rw [t0, t1, t2, v64, f6 (W 1) (hne (by decide)) (hne (by decide)), hq,
    f6 (W 7) (hne (by decide)) (hne (by decide)), z 7 (by decide), Nat.zero_add] at e7
  obtain ⟨σ7, hσ7⟩ : ∃ τ, τ = σ6.setv (W 7) (sys * q) := ⟨_, rfl⟩
  rw [← hσ7] at e7
  -- 8. skip the bitmaps
  set P4 := (natWord 3).length + (natWord sys).length + (natWord aux).length + (natWord cb).length with hP4
  set m := sys * q with hm
  set T : ℕ → WState ns nr := fun k => (σ7.seth po (P4 + k)).setv (W 7) (m - k) with hT
  have hT0 : T 0 = σ7 := by
    simp only [hT, Nat.add_zero, Nat.sub_zero]
    rw [hσ7, hσ6]; refine WState.eq ?_ rfl ?_ rfl
    · funext j; by_cases hj : j = po
      · subst hj; simp [hσ5, hσ4]
      · simp [hj]
    · funext j; by_cases hj : j = W 7
      · subst hj; simp
      · simp [hj]
  have e8 := UnionMachine.Round.wloop cap (W 7) (.fwd po) 1 m T (fun k _ => by simp [hT]) (by omega)
    (fun k hk => by
      refine WExec.cast cap (WExec.fwd po _) ?_ le_rfl
      simp only [hT]
      refine WState.eq ?_ rfl ?_ rfl
      · funext j; by_cases hj : j = po
        · subst hj; simp; omega
        · simp [hj]
      · funext j; by_cases hj : j = W 7
        · subst hj; simp; omega
        · simp [hj])
  rw [hT0] at e8
  obtain ⟨σ8, hσ8⟩ : ∃ τ, τ = T m := ⟨_, rfl⟩
  rw [← hσ8] at e8
  have f8 : ∀ j, j ≠ W 4 → j ≠ W 3 → j ≠ W 7 → σ8.val j = σ.val j := fun j a b c => by
    rw [hσ8, hT, hσ7]; simp [c, f6 j a b]
  have s8 : σ8.st po = σ.st po := by rw [hσ8, hT, hσ7, hσ6, hσ5, hσ4, hσ3]; simp [s2]
  have sh8 : σ8.sh po = P4 + m := by rw [hσ8, hT]; simp
  -- 9. LEN := |lits|
  have e9 := readNatM_spec cap false po (W 8) (W 9) (W 5) (W 10) (W 11) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) lits.length (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ bits)
      (lits.flatMap natWord ++ rest) σ8
    (by rw [s8, hst]; simp [PrimAsm.ParseNat.enc, poWord])
    (by rw [sh8]; simp [hP4, hbits, hm]; try omega)
    (by rw [f8 _ (hne (by decide)) (hne (by decide)) (hne (by decide)), z 8 (by decide)])
    (by rw [f8 _ (hne (by decide)) (hne (by decide)) (hne (by decide)), z 9 (by decide)])
    (by rw [f8 _ (hne (by decide)) (hne (by decide)) (hne (by decide)), z 10 (by decide)])
    (by rw [f8 _ (hne (by decide)) (hne (by decide)) (hne (by decide)), z 11 (by decide)])
    (by rw [f8 _ (hne (by decide)) (hne (by decide)) (hne (by decide)), z 5 (by decide)]; have := pw _ hlV; omega)
  simp only [stp, Bool.false_eq_true, if_false, one_mul, f8 _ (hne (show (5 : Fin 20) ≠ 4 by decide))
    (hne (show (5 : Fin 20) ≠ 3 by decide)) (hne (show (5 : Fin 20) ≠ 7 by decide)), z 5 (by decide),
    Nat.zero_add, List.length_append] at e9
  obtain ⟨σ9, hσ9⟩ : ∃ τ, τ = (σ8.seth po ((natWord 3).length + (natWord sys).length + (natWord aux).length +
    (natWord cb).length + bits.length + (natWord lits.length).length)).setv (W 5) lits.length := ⟨_, rfl⟩
  rw [← hσ9] at e9
  have f9 : ∀ j, j ≠ W 4 → j ≠ W 3 → j ≠ W 7 → j ≠ W 5 → σ9.val j = σ.val j := fun j a b c d => by
    rw [hσ9]; simp [d, f8 j a b c]
  -- 10. the literal loop
  have e10 := litLoop_spec cap po W σ9 x V lits (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ bits ++
      natWord lits.length) rest
    (by rw [hσ9]; simp only [WState.setv_st, WState.seth_st]; rw [s8, hst]; simp [poWord])
    (by rw [hσ9]; simp; try omega)
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), hx])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 2 (by decide)])
    (by rw [hσ9]; simp)
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 6 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 8 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 9 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 10 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 11 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 12 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 13 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 14 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 15 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 16 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 17 (by decide)])
    (by rw [f9 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), z 18 (by decide)])
    hV hxV (by omega)
  obtain ⟨σ10, hσ10⟩ : ∃ τ, τ = ((σ9.seth po ((natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ bits ++
      natWord lits.length).length + (lits.flatMap natWord).length)).setv (W 2) (cntOf x lits)).setv (W 5) 0 :=
    ⟨_, rfl⟩
  rw [← hσ10] at e10
  -- 11. SYS := 0
  have v104 : σ10.val (W 4) = sys := by
    rw [hσ10, hσ9, hσ8, hT, hσ7]
    simp [hne (show (4 : Fin 20) ≠ 5 by decide), hne (show (4 : Fin 20) ≠ 2 by decide),
      hne (show (4 : Fin 20) ≠ 7 by decide), v64]
  have e11 := wclear_spec cap (W 4) sys σ10 v104 (by rw [v104]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 e11)))))))))) ?_ le_rfl) ?_
  · rw [hσ10, hσ9, hσ8, hT, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
    refine WState.eq ?_ rfl ?_ rfl
    · funext j; by_cases hj : j = po
      · subst hj; simp [poWord]; try omega
      · simp [hj]
    · funext j
      simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases a4 : j = W 4
      · subst a4; simp [hne (show (4 : Fin 20) ≠ 3 by decide), hne (show (4 : Fin 20) ≠ 2 by decide), z 4 (by decide)]
      by_cases a3 : j = W 3
      · subst a3; simp [hne (show (3 : Fin 20) ≠ 2 by decide), hne (show (3 : Fin 20) ≠ 5 by decide),
          hne (show (3 : Fin 20) ≠ 7 by decide), hne (show (3 : Fin 20) ≠ 19 by decide)]
      by_cases a2 : j = W 2
      · subst a2; simp [hne (show (2 : Fin 20) ≠ 5 by decide)]
      by_cases a5 : j = W 5
      · subst a5; simp [a2, z 5 (by decide)]
      by_cases a7 : j = W 7
      · subst a7; simp [a2, a5, a3, a4, z 7 (by decide)]
      by_cases a19 : j = W 19
      · subst a19; simp [a2, a5, a3, a4, a7, z 19 (by decide)]
      simp [a2, a5, a3, a4, a7, a19]
  · unfold cntC
    have r1 := rd_le 3 V h3
    have r2 := rd_le sys V hsV
    have r3 := rd_le aux V haV
    have r4 := rd_le cb V hcV
    have r5 := rd_le lits.length V hlV
    have hmq : sys * q ≤ V * q := Nat.mul_le_mul_right _ hsV
    have hmq2 : q * (18 * sys + 8) ≤ q * (18 * V + 8) := Nat.mul_le_mul_left _ (by omega)
    omega

end Prog

end NearCubicWires.WireExponent3_5.UnionMachine.C1Cnt
