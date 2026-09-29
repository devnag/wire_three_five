import Proof.Wire_3_5.Selection.CosPop

/-! # C1.5: one population's weighted step (P3:1356-1362)

Paper: "Sum its exact count with the rational population weights, over gates and rows" (P3:1356-1357); "Repeated
labelled occurrences are charged with their weights; they need not be deduplicated" (P3:1361-1362). One population
`X = (l, p)` of the population table (its record `popRec W X`: `1^|l| 0`, the index words, the weight's numerator and
denominator words): `TX := 0`; read the index count into `MC`; the index loop (`idxL`: `TX += Σ_{i ∈ l} rowsAt i`, the
population's exact row count at the coset); read the numerator and the denominator; then C6's `ratStepB`:
`(AN, AD) := ratAccStep (AN, AD) (num, den, TX)`. Main declarations: `zStep`, `qStep`, `popM`, `popCost`,
**`popM_spec`**. Paper quantity: the weighted sum `Σ_X p_X T_X` of the objective, one population at a time. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

/-- The step's streams: `AN = S 35`, `AD = S 36`, `NUM = S 33`, `DEN = S 34`, `TX = S 3`, scratch `S 37 … S 40`. -/
def zStep (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) : Fin 9 ↪ Fin (ns + 1) :=
  ⟨fun i => S (![35, 36, 33, 34, 3, 37, 38, 39, 40] i), hS.comp (by decide)⟩

/-- The step's registers `Q 61, Q 62, Q 63`. -/
def qStep (Q : Fin 64 → Fin nr) (hQ : Function.Injective Q) : Fin 3 ↪ Fin nr :=
  ⟨fun i => Q (![61, 62, 63] i), hQ.comp (by decide)⟩

theorem zStep_apply (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (i : Fin 9) :
    zStep S hS i = S (![35, 36, 33, 34, 3, 37, 38, 39, 40] i) := rfl

theorem qStep_apply (Q : Fin 64 → Fin nr) (hQ : Function.Injective Q) (i : Fin 3) :
    qStep Q hQ i = Q (![61, 62, 63] i) := rfl

/-- **One population**: `TX := 0`, `MC := |l|`, the index loop, the weight's words, the weighted step. -/
def popM (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) : WM ns nr :=
  .seq (zeroB (S 3) (S 2) (Q 61) (Q 62)) (.seq (readUn (S 31) (Q 53)) (.seq (idxL S Q)
    (.seq (copyAtB (S 33) (S 31) (Q 61) (Q 62)) (.seq (copyAtB (S 34) (S 31) (Q 61) (Q 62))
      (ratStepB (zStep S hS) (qStep Q hQ))))))

/-- One population's cost at index count `m`. -/
def popCost (P : StarParams) (n W V g m : ℕ) : ℕ :=
  41 * W + 3 + 1 + (m * 7 + 1 + 1 + 1 + 1 + (m * (1 + 1 + idxCost P n W V g + 2) + 1 + 1 +
    (46 * W + 7 + 1 + (46 * W + 7 + 1 + ratStepCost W))))

/-- A population's row count at the coset `N`, as the machine sums it. -/
def popT (R : SelectionReq) (h : ParamsOk R) (N : ℕ) (X : List ℕ × ℚ) : ℕ := (X.1.map (rowsAt R h N)).sum

theorem popRec_eq (W : ℕ) (X : List ℕ × ℚ) : popRec W X = List.replicate X.1.length true ++ (false ::
    (idxWords W X.1 ++ (frame (binary W X.2.num.toNat) ++ frame (binary W X.2.den)))) := by
  simp [popRec, idxWords, List.append_assoc]

theorem popRec_length (W : ℕ) (X : List ℕ × ℚ) :
    (popRec W X).length = X.1.length + 1 + X.1.length * (2 * W + 1) + (2 * W + 1) + (2 * W + 1) := by
  rw [popRec_eq]
  simp only [List.length_append, List.length_replicate, List.length_cons, idxWords_length,
    RepairOrdinary.frame_length, binary_length]
  ring

theorem rd_rep (pre tail : List Bool) (m j : ℕ) (hj : j < m) :
    readTapeBit (pre ++ (List.replicate m true ++ tail)) (pre.length + j) = true := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem rd_rep_end (pre tail : List Bool) (m : ℕ) :
    readTapeBit (pre ++ (List.replicate m true ++ false :: tail)) (pre.length + m) = false := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The population table's words the loop keeps (each some width-`W` number). -/
def Words (S : Fin 50 → Fin (ns + 1)) (σ : WState ns nr) (W : ℕ) : Prop :=
  ∀ k : Fin 50, (k = 3 ∨ k = 33 ∨ k = 34 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 44 ∨ k = 46) →
    ∃ v, NumOn σ (S k) W v

/-- **One population's weighted step**: `(AN, AD) := ratAccStep (AN, AD) (num, den, T_X)`; the table's head moves
past the record; `Base` holds; the registers and the cell come back. -/
theorem popM_spec (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (W V N : ℕ)
    (hng : R.gates.length < 2 ^ W) (hN : N < 2 ^ (R.r * R.s))
    (hKB : ∀ g ∈ R.gates, KeyBound (gateOf g) V) (hW : 2 * V + 3 ≤ W) (hnk : R.n + (starParamsOf R h).k + 4 ≤ W)
    (hcap : gateNeed (starParamsOf R h) W V ≤ cap) (hcap2 : 2 * W + 1 ≤ cap)
    (hcapG : R.gates.length * (R.n + 1) * (2 * W + 2) + 2 < cap)
    (σ : WState ns nr) (X : List ℕ × ℚ) (pre rest : List Bool) (an ad : ℕ) (b : Base S Q R h W V N σ)
    (hPT : σ.st (S 31) = pre ++ popRec W X ++ rest) (hPTh : σ.sh (S 31) = pre.length) (hWd : Words S σ W)
    (hAN : NumOn σ (S 35) W an) (hAD : NumOn σ (S 36) W ad) (q53 : σ.val (Q 53) = 0)
    (hm : X.1.length ≤ cap) (hil : ∀ i ∈ X.1, i < 2 ^ W) (hT : popT R h N X < 2 ^ W) (hd1 : 1 ≤ ad)
    (hsum : an * X.2.den + X.2.num.toNat * popT R h N X * ad < 2 ^ W) (hdb : ad * X.2.den < 2 ^ W)
    (hb : X.2.den < 2 ^ W) (hd : ad < 2 ^ W) :
    ∃ τ : WState ns nr, WExec cap (popM S hS Q hQ) σ τ
        (popCost (starParamsOf R h) R.n W V R.gates.length X.1.length) ∧
      Base S Q R h W V N τ ∧ τ.st (S 31) = σ.st (S 31) ∧ τ.sh (S 31) = pre.length + (popRec W X).length ∧
      NumOn τ (S 35) W (ratAccStep (an, ad) (X.2.num.toNat, X.2.den, popT R h N X)).1 ∧
      NumOn τ (S 36) W (ratAccStep (an, ad) (X.2.num.toNat, X.2.den, popT R h N X)).2 ∧ Words S τ W ∧
      (∀ k : Fin 50, 28 ≤ k.val → k.val ≠ 44 → k.val ≠ 46 → (k.val < 33 ∨ 40 < k.val) → τ.st (S k) = σ.st (S k)) ∧
      (∀ k : Fin 50, k ≠ 31 → τ.sh (S k) = σ.sh (S k)) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have sne : ∀ a c : Fin 50, a ≠ c → S a ≠ S c := fun a c h => hS.ne h
  have qne : ∀ a c : Fin 64, a ≠ c → Q a ≠ Q c := fun a c h => hQ.ne h
  have q61 : σ.val (Q 61) = 0 := b.tmp 61 (by decide)
  have q62 : σ.val (Q 62) = 0 := b.tmp 62 (by decide)
  have q63 : σ.val (Q 63) = 0 := b.tmp 63 (by decide)
  obtain ⟨t0, hTX⟩ := hWd 3 (by decide)
  -- TX := 0
  have x1 := zeroB_spec cap W (A := S 3) (B := S 2) (F := Q 61) (R := Q 62) (sne 3 2 (by decide))
    (qne 61 62 (by decide)) σ t0 (2 ^ V) hTX b.of q61 q62 hcap2
  set σ1 := σ.sets (S 3) (frame (binary W 0)) with hσ1
  have b1 : Base S Q R h W V N σ1 := b.sets hS hQ 3 (Or.inl rfl) _
  -- MC := |l|
  have hPT1 : σ1.st (S 31) = pre ++ (List.replicate X.1.length true ++ (false ::
      (idxWords W X.1 ++ (frame (binary W X.2.num.toNat) ++ frame (binary W X.2.den)) ++ rest))) := by
    simp [hσ1, sne 31 3 (by decide), hPT, popRec_eq, List.append_assoc]
  have hPTh1 : σ1.sh (S 31) = pre.length := by simp [hσ1, hPTh]
  have x2 := readUn_spec cap (S 31) (Q 53) σ1 X.1.length (fun j hj => by rw [hPT1, hPTh1]; exact rd_rep _ _ _ _ hj)
    (by rw [hPT1, hPTh1]; exact rd_rep_end _ _ _) (by simp [hσ1, q53]) hm
  set σ2 := (σ1.seth (S 31) (σ1.sh (S 31) + X.1.length + 1)).setv (Q 53) X.1.length with hσ2
  have b2 : Base S Q R h W V N σ2 := (b1.seth31 hS hQ _).setv hS hQ 53 (by decide) _
  -- the index loop
  set pre2 := pre ++ (List.replicate X.1.length true ++ [false]) with hpre2
  set rest2 := frame (binary W X.2.num.toNat) ++ (frame (binary W X.2.den) ++ rest) with hrest2
  have hPT2 : σ2.st (S 31) = pre2 ++ idxWords W X.1 ++ rest2 := by
    simp [hσ2, hPT1, hpre2, hrest2, List.append_assoc]
  have hPTh2 : σ2.sh (S 31) = pre2.length := by simp [hσ2, hPTh1, hpre2]; omega
  have tx2 : NumOn σ2 (S 3) W 0 := ⟨by simp [hσ2, hσ1], by simp [hσ2, hσ1, sne 3 31 (by decide), hTX.2]⟩
  have hIX2 : ∃ x, NumOn σ2 (S 44) W x := by
    obtain ⟨x, hx⟩ := hWd 44 (by decide)
    exact ⟨x, by simp [hσ2, hσ1, sne 44 3 (by decide), hx.1], by simp [hσ2, hσ1, sne 44 31 (by decide), hx.2]⟩
  have hJ2 : ∃ j, NumOn σ2 (S 46) W j := by
    obtain ⟨x, hx⟩ := hWd 46 (by decide)
    exact ⟨x, by simp [hσ2, hσ1, sne 46 3 (by decide), hx.1], by simp [hσ2, hσ1, sne 46 31 (by decide), hx.2]⟩
  obtain ⟨τ3, x3, b3, hTX3, hPTh3, hIX3, hJ3, hst3, hsh3, hval3, h53τ3, hoth3, hcell3⟩ :=
    idxL_spec S hS Q hQ cap R h W V N hng hN hKB hW hnk hcap hcap2 hcapG X.1 σ2 0 pre2 rest2 b2 hPT2 hPTh2 tx2
      hIX2 hJ2 (by simp [hσ2]) hm hil (by rw [Nat.zero_add]; exact hT)
  rw [Nat.zero_add] at hTX3
  -- the weight's words
  have hPT3 : τ3.st (S 31) = (pre2 ++ idxWords W X.1) ++ frame (binary W X.2.num.toNat) ++
      (frame (binary W X.2.den) ++ rest) := by
    rw [hst3 31 (by decide) (by decide) (by decide), hPT2]; simp [hrest2, List.append_assoc]
  have hPTh3' : τ3.sh (S 31) = (pre2 ++ idxWords W X.1).length := by
    rw [hPTh3]; simp [hpre2, idxWords_length]; ring
  obtain ⟨a33, h33⟩ := hWd 33 (by decide)
  have n33 : NumOn τ3 (S 33) W a33 := by
    refine ⟨?_, ?_⟩
    · rw [hst3 33 (by decide) (by decide) (by decide)]; simp [hσ2, hσ1, sne 33 3 (by decide), h33.1]
    · rw [hsh3 33 (by decide)]; simp [hσ2, hσ1, sne 33 31 (by decide), h33.2]
  have v3 : ∀ j : Fin 64, j ≠ 53 → τ3.val (Q j) = σ.val (Q j) := by
    intro j hj; rw [hval3 j hj]; simp [hσ2, hσ1, qne j 53 hj]
  have x4 := copyAtB_spec cap W (A := S 33) (I := S 31) (F := Q 61) (R := Q 62) (sne 33 31 (by decide))
    (qne 61 62 (by decide)) τ3 a33 X.2.num.toNat (pre2 ++ idxWords W X.1) (frame (binary W X.2.den) ++ rest)
    n33 hPT3 hPTh3' (by rw [v3 61 (by decide), q61]) (by rw [v3 62 (by decide), q62]) hcap2
  set σ4 := (τ3.sets (S 33) (frame (binary W X.2.num.toNat))).seth (S 31)
    ((pre2 ++ idxWords W X.1).length + 2 * W + 1) with hσ4
  obtain ⟨a34, h34⟩ := hWd 34 (by decide)
  have n34 : NumOn σ4 (S 34) W a34 := by
    refine ⟨?_, ?_⟩
    · simp only [hσ4, WState.seth_st, WState.sets_st, Function.update_apply, sne 34 33 (by decide), if_false]
      rw [hst3 34 (by decide) (by decide) (by decide)]; simp [hσ2, hσ1, sne 34 3 (by decide), h34.1]
    · simp only [hσ4, WState.seth_sh, WState.sets_sh, Function.update_apply, sne 34 31 (by decide), if_false]
      rw [hsh3 34 (by decide)]; simp [hσ2, hσ1, sne 34 31 (by decide), h34.2]
  have hPT4 : σ4.st (S 31) = ((pre2 ++ idxWords W X.1) ++ frame (binary W X.2.num.toNat)) ++
      frame (binary W X.2.den) ++ rest := by
    simp only [hσ4, WState.seth_st, WState.sets_st, Function.update_apply, sne 31 33 (by decide), if_false]
    rw [hPT3]; simp [List.append_assoc]
  have hPTh4 : σ4.sh (S 31) = ((pre2 ++ idxWords W X.1) ++ frame (binary W X.2.num.toNat)).length := by
    simp [hσ4, RepairOrdinary.frame_length]; omega
  have x5 := copyAtB_spec cap W (A := S 34) (I := S 31) (F := Q 61) (R := Q 62) (sne 34 31 (by decide))
    (qne 61 62 (by decide)) σ4 a34 X.2.den ((pre2 ++ idxWords W X.1) ++ frame (binary W X.2.num.toNat)) rest
    n34 hPT4 hPTh4 (by simp [hσ4, v3 61 (by decide), q61]) (by simp [hσ4, v3 62 (by decide), q62]) hcap2
  set σ5 := (σ4.sets (S 34) (frame (binary W X.2.den))).seth (S 31)
    (((pre2 ++ idxWords W X.1) ++ frame (binary W X.2.num.toNat)).length + 2 * W + 1) with hσ5
  -- the weighted step
  have e5 : ∀ k : Fin 50, k ≠ 33 → k ≠ 34 → σ5.st (S k) = τ3.st (S k) := by
    intro k h33' h34'
    simp [hσ5, hσ4, sne k 33 h33', sne k 34 h34']
  have e5h : ∀ k : Fin 50, k ≠ 31 → σ5.sh (S k) = τ3.sh (S k) := by
    intro k hk
    simp [hσ5, hσ4, sne k 31 hk]
  have w5 : ∀ k : Fin 50, 36 < k.val → k.val ≤ 40 → ∃ v, NumOn σ5 (S k) W v := by
    intro k hk1 hk2
    obtain ⟨v, hv⟩ := hWd k (by
      rcases (show k.val = 37 ∨ k.val = 38 ∨ k.val = 39 ∨ k.val = 40 by omega) with e | e | e | e <;>
        [exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e)))); exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (Fin.ext e))))); exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e)))))); exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e)))))))])
    have k33 : k ≠ 33 := fun e => by subst e; simp at hk1
    have k34 : k ≠ 34 := fun e => by subst e; simp at hk1
    have k31 : k ≠ 31 := fun e => by subst e; simp at hk1
    have k3 : S k ≠ S 3 := sne k 3 (fun e => by subst e; simp at hk1)
    refine ⟨v, ?_, ?_⟩
    · rw [e5 k k33 k34, hst3 k (by omega) (by omega) (by omega)]; simp [hσ2, hσ1, k3, hv.1]
    · rw [e5h k k31, hsh3 k k31]; simp [hσ2, hσ1, sne k 31 k31, hv.2]
  have an5 : NumOn σ5 (S 35) W an := by
    refine ⟨?_, ?_⟩
    · rw [e5 35 (by decide) (by decide), hst3 35 (by decide) (by decide) (by decide)]
      simp [hσ2, hσ1, sne 35 3 (by decide), hAN.1]
    · rw [e5h 35 (by decide), hsh3 35 (by decide)]; simp [hσ2, hσ1, sne 35 31 (by decide), hAN.2]
  have ad5 : NumOn σ5 (S 36) W ad := by
    refine ⟨?_, ?_⟩
    · rw [e5 36 (by decide) (by decide), hst3 36 (by decide) (by decide) (by decide)]
      simp [hσ2, hσ1, sne 36 3 (by decide), hAD.1]
    · rw [e5h 36 (by decide), hsh3 36 (by decide)]; simp [hσ2, hσ1, sne 36 31 (by decide), hAD.2]
  have num5 : NumOn σ5 (S 33) W X.2.num.toNat := by
    refine ⟨?_, ?_⟩
    · simp [hσ5, hσ4, sne 33 34 (by decide)]
    · rw [e5h 33 (by decide), hsh3 33 (by decide)]; simp [hσ2, hσ1, sne 33 31 (by decide), h33.2]
  have den5 : NumOn σ5 (S 34) W X.2.den := by
    refine ⟨by simp [hσ5], ?_⟩
    rw [e5h 34 (by decide), hsh3 34 (by decide)]; simp [hσ2, hσ1, sne 34 31 (by decide), h34.2]
  have tx5 : NumOn σ5 (S 3) W (popT R h N X) := by
    refine ⟨?_, ?_⟩
    · rw [e5 3 (by decide) (by decide)]; exact hTX3.1
    · rw [e5h 3 (by decide)]; exact hTX3.2
  obtain ⟨s37, h37⟩ := w5 37 (by decide) (by decide)
  obtain ⟨s38, h38⟩ := w5 38 (by decide) (by decide)
  obtain ⟨s39, h39⟩ := w5 39 (by decide) (by decide)
  obtain ⟨s40, h40⟩ := w5 40 (by decide) (by decide)
  have v5 : σ5.val = τ3.val := rfl
  have x6 := ratStepB_spec cap W (zStep S hS) (qStep Q hQ) σ5 an ad X.2.num.toNat X.2.den (popT R h N X)
    s37 s38 s39 s40 an5 ad5 num5 den5 tx5 h37 h38 h39 h40
    (by rw [qStep_apply]; simp [v5, v3 61 (by decide), q61]) (by rw [qStep_apply]; simp [v5, v3 62 (by decide), q62])
    (by rw [qStep_apply]; simp [v5, v3 63 (by decide), q63]) hd1 hsum hdb hb hT hd hcap2
  simp only [zStep_apply] at x6
  set N' := (ratAccStep (an, ad) (X.2.num.toNat, X.2.den, popT R h N X)).1 with hN'
  set D' := (ratAccStep (an, ad) (X.2.num.toNat, X.2.den, popT R h N X)).2 with hD'
  set τ := (((((σ5.sets (S 35) (frame (binary W N'))).sets (S 36) (frame (binary W D'))).sets (S 37)
    (frame (binary W 0))).sets (S 38) (frame (binary W 0))).sets (S 39) (frame (binary W 0))).sets (S 40)
    (frame (binary W 0)) with hτ
  have x6' : WExec cap (ratStepB (zStep S hS) (qStep Q hQ)) σ5 τ (ratStepCost W) := x6
  have b5 : Base S Q R h W V N σ5 :=
    ((((b3.sets hS hQ 33 (Or.inr (by decide)) _).seth31 hS hQ _).sets hS hQ 34 (Or.inr (by decide)) _).seth31 hS hQ _)
  have bτ : Base S Q R h W V N τ :=
    (((((b5.sets hS hQ 35 (Or.inr (by decide)) _).sets hS hQ 36 (Or.inr (by decide)) _).sets hS hQ 37
      (Or.inr (by decide)) _).sets hS hQ 38 (Or.inr (by decide)) _).sets hS hQ 39 (Or.inr (by decide)) _).sets hS hQ
      40 (Or.inr (by decide)) _
  have eτ : ∀ k : Fin 50, (k.val < 35 ∨ 40 < k.val) → τ.st (S k) = σ5.st (S k) := by
    intro k hk
    have n35 : S k ≠ S 35 := sne k 35 (fun e => by subst e; simp at hk)
    have n36 : S k ≠ S 36 := sne k 36 (fun e => by subst e; simp at hk)
    have n37 : S k ≠ S 37 := sne k 37 (fun e => by subst e; simp at hk)
    have n38 : S k ≠ S 38 := sne k 38 (fun e => by subst e; simp at hk)
    have n39 : S k ≠ S 39 := sne k 39 (fun e => by subst e; simp at hk)
    have n40 : S k ≠ S 40 := sne k 40 (fun e => by subst e; simp at hk)
    simp [hτ, n35, n36, n37, n38, n39, n40]
  have hτsh : τ.sh = σ5.sh := rfl
  have hτval : τ.val = σ5.val := rfl
  refine ⟨τ, ?_, bτ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold popM popCost
    exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 x6'))))
  · rw [eτ 31 (Or.inl (by decide)), e5 31 (by decide) (by decide), hst3 31 (by decide) (by decide) (by decide)]
    simp [hσ2, hσ1, sne 31 3 (by decide)]
  · rw [hτsh]; simp [hσ5, popRec_length, hpre2, idxWords_length, RepairOrdinary.frame_length]; ring
  · exact ⟨by simp [hτ, sne 35 36 (by decide), sne 35 37 (by decide), sne 35 38 (by decide),
      sne 35 39 (by decide), sne 35 40 (by decide)], by rw [hτsh]; exact an5.2⟩
  · exact ⟨by simp [hτ, sne 36 37 (by decide), sne 36 38 (by decide), sne 36 39 (by decide), sne 36 40 (by decide)],
      by rw [hτsh]; exact ad5.2⟩
  · intro k hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [eτ 3 (Or.inl (by decide))]; exact tx5.1, by rw [hτsh]; exact tx5.2⟩
    · exact ⟨_, by rw [eτ 33 (Or.inl (by decide))]; exact num5.1, by rw [hτsh]; exact num5.2⟩
    · exact ⟨_, by rw [eτ 34 (Or.inl (by decide))]; exact den5.1, by rw [hτsh]; exact den5.2⟩
    · exact ⟨0, by simp [hτ, sne 37 38 (by decide), sne 37 39 (by decide), sne 37 40 (by decide)],
        by rw [hτsh]; exact h37.2⟩
    · exact ⟨0, by simp [hτ, sne 38 39 (by decide), sne 38 40 (by decide)], by rw [hτsh]; exact h38.2⟩
    · exact ⟨0, by simp [hτ, sne 39 40 (by decide)], by rw [hτsh]; exact h39.2⟩
    · exact ⟨0, by simp [hτ], by rw [hτsh]; exact h40.2⟩
    · obtain ⟨x, hx⟩ := hIX3
      exact ⟨x, by rw [eτ 44 (Or.inr (by decide)), e5 44 (by decide) (by decide)]; exact hx.1,
        by rw [hτsh, e5h 44 (by decide)]; exact hx.2⟩
    · obtain ⟨x, hx⟩ := hJ3
      exact ⟨x, by rw [eτ 46 (Or.inr (by decide)), e5 46 (by decide) (by decide)]; exact hx.1,
        by rw [hτsh, e5h 46 (by decide)]; exact hx.2⟩
  · intro k hk h44 h46 hk2
    have k33 : k ≠ 33 := fun e => by subst e; simp at hk2
    have k34 : k ≠ 34 := fun e => by subst e; simp at hk2
    have k3 : S k ≠ S 3 := sne k 3 (fun e => by subst e; simp at hk)
    rw [eτ k (by omega), e5 k k33 k34, hst3 k hk h44 h46]
    simp [hσ2, hσ1, k3]
  · intro k hk
    rw [hτsh, e5h k hk, hsh3 k hk]
    simp [hσ2, hσ1, sne k 31 hk]
  · rw [hτval, v5]
    funext r
    by_cases hr : ∃ j, Q j = r
    · obtain ⟨j, rfl⟩ := hr
      by_cases hj : j = 53
      · subst hj; rw [h53τ3, q53]
      · exact v3 j hj
    · simp only [not_exists] at hr
      rw [hoth3 r hr]
      simp [hσ2, hσ1, Function.update_apply, Ne.symm (hr 53)]
  · rw [show τ.cell = σ5.cell from rfl]
    simp [hσ5, hσ4, hcell3, hσ2, hσ1]

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
