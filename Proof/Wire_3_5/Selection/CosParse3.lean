import Proof.Wire_3_5.Selection.CosParse2

/-! # C1.5 parse, part 3: the coset loop's words (P3:1356-1360)

Paper: "Sum its exact count with the rational population weights [...] Select a minimum objective" (P3:1356-1360): the
loop keeps width-`W` words (the row count `TX`, the weight's words, the exact accumulator `AN/AD`, the best key `BN/BD`,
the step and compare scratch, the index words `IX/J`, the gate count `NG`, the key offset `OF = 2^V`) and width-`k`
counter words (`NS`, `BEST`). `wordsP` writes them all as C1.4's zero words (`zw`), sets `BN := 1` (the
sentinel best key `(1, 0)`) and `OF := 2^V` (C6's `oneB`, `V` shifts by `shlB`). Main declarations: `zwP_spec`, `zwSeq`,
`zwSeq_spec`, `shlL_spec`, `wordsSt`, **`wordsP_spec`**. Paper quantity: the loop's exact arithmetic words. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.SelectionMachine.Gate (zw zw_spec zwCost)

/-! ## Zero words -/

theorem zwP_spec (cap : ℕ) (Z : Fin 50) (hZ : Z ≠ Sm 47) (N : Fin 112) (hN : N ≠ 89 ∧ N ≠ 98 ∧ N ≠ 99)
    (σ : WState 49 112) (n : ℕ) (hNv : σ.val N = n) (h89 : σ.val 89 = 0) (h98 : σ.val 98 = 0) (h99 : σ.val 99 = 0)
    (h47 : σ.sh (Sm 47) = 0) (hZh : σ.sh Z = 0) (hlen : (σ.st Z).length ≤ 2 * n + 1) (hcap : 2 * n + 2 ≤ cap) :
    WExec cap (zwP Z N) σ (σ.sets Z (frame (binary n 0))) (zwCost n) :=
  zw_spec cap σ (A := Sm 47) (Z := Z) (CA := 99) (CZ := 98) (N := N) (T := 89) (Ne.symm hZ) (by decide) hN.1
    hN.2.2 hN.2.1 (by decide) (by decide) n h47 h99 hZh h98 hNv h89 hlen hcap

/-- A run of zero words of width `N`, then `k`. -/
def zwSeq (Zs : List (Fin 50)) (N : Fin 112) (k : WM 49 112) : WM 49 112 :=
  Zs.foldr (fun Z acc => .seq (zwP Z N) acc) k

/-- The streams set to a word. -/
def setsAll (σ : WState 49 112) (Zs : List (Fin 50)) (w : List Bool) : WState 49 112 :=
  Zs.foldl (fun σ Z => σ.sets Z w) σ

theorem setsAll_sh (Zs : List (Fin 50)) (w : List Bool) : ∀ σ : WState 49 112, (setsAll σ Zs w).sh = σ.sh := by
  induction Zs with
  | nil => intro σ; rfl
  | cons Z Zs ih => intro σ; simp only [setsAll, List.foldl_cons] at ih ⊢; rw [ih]; rfl

theorem setsAll_val (Zs : List (Fin 50)) (w : List Bool) : ∀ σ : WState 49 112, (setsAll σ Zs w).val = σ.val := by
  induction Zs with
  | nil => intro σ; rfl
  | cons Z Zs ih => intro σ; simp only [setsAll, List.foldl_cons] at ih ⊢; rw [ih]; rfl

theorem setsAll_st (Zs : List (Fin 50)) (w : List Bool) : ∀ (σ : WState 49 112) (i : Fin 50),
    (setsAll σ Zs w).st i = if i ∈ Zs then w else σ.st i := by
  induction Zs with
  | nil => intro σ i; simp [setsAll]
  | cons Z Zs ih =>
    intro σ i
    simp only [setsAll, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases h1 : i ∈ Zs
    · simp [h1]
    · by_cases h2 : i = Z
      · subst h2; simp [h1]
      · simp [h1, h2, Function.update_apply]

/-- **A run of zero words** (continuation-passing). -/
theorem zwSeq_spec (cap : ℕ) (N : Fin 112) (hN : N ≠ 89 ∧ N ≠ 98 ∧ N ≠ 99) (n : ℕ) (hcap : 2 * n + 2 ≤ cap)
    (k : WM 49 112) (τ : WState 49 112) (c : ℕ) :
    ∀ (Zs : List (Fin 50)) (σ : WState 49 112), Zs.Nodup → (∀ Z ∈ Zs, Z ≠ Sm 47 ∧ σ.sh Z = 0 ∧ σ.st Z = []) →
      σ.val N = n → σ.val 89 = 0 → σ.val 98 = 0 → σ.val 99 = 0 → σ.sh (Sm 47) = 0 →
      WExec cap k (setsAll σ Zs (frame (binary n 0))) τ c →
      WExec cap (zwSeq Zs N k) σ τ (Zs.length * (zwCost n + 1) + c)
  | [], σ, _, _, _, _, _, _, _, hk => by simpa [zwSeq, setsAll] using hk
  | Z :: Zs, σ, hnd, hZs, hNv, h89, h98, h99, h47, hk => by
    obtain ⟨hZ47, hZh, hZst⟩ := hZs Z List.mem_cons_self
    have x1 := zwP_spec cap Z hZ47 N hN σ n hNv h89 h98 h99 h47 hZh (by rw [hZst]; simp) hcap
    have hnd' := List.nodup_cons.mp hnd
    have ih := zwSeq_spec cap N hN n hcap k τ c Zs (σ.sets Z (frame (binary n 0))) hnd'.2
      (fun Z' hZ' => by
        have hne : Z' ≠ Z := fun e => hnd'.1 (e ▸ hZ')
        obtain ⟨a, b, d⟩ := hZs Z' (List.mem_cons_of_mem _ hZ')
        exact ⟨a, by simp [b], by simp [hne, d]⟩)
      (by simp [hNv]) (by simp [h89]) (by simp [h98]) (by simp [h99]) (by simp [h47]) hk
    refine WExec.cast cap (WExec.seq x1 ih) rfl ?_
    simp only [List.length_cons]; ring_nf; omega

/-! ## `OF = 2^V` -/

theorem wsets_sets' (σ : WState 49 112) (i : Fin 50) (a b : List Bool) : (σ.sets i a).sets i b = σ.sets i b :=
  WState.eq rfl (by simp) rfl rfl

/-- The shift loop: `V` doublings of `OF`. -/
def shlL : WM 49 112 := .whr 92 (.seq (.dec 92) (shlB (Sm 2) (Sm 3) 90 91))

theorem shlL_spec (cap W b : ℕ) (hcap : 2 * W + 1 ≤ cap) :
    ∀ (j : ℕ) (σ : WState 49 112) (a : ℕ), σ.val 92 = j → NumOn σ (Sm 2) W a → NumOn σ (Sm 3) W b →
      σ.val 90 = 0 → σ.val 91 = 0 → j ≤ cap →
      WExec cap shlL σ ((σ.sets (Sm 2) (frame (binary W (a * 2 ^ j)))).setv 92 0) (j * (41 * W + 12) + 1)
  | 0, σ, a, h92, hA, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h92) ?_ (by omega)
    rw [pow_zero, Nat.mul_one, ← hA.1, wsets_same, Gate.wsetv_zero _ _ h92]
  | j + 1, σ, a, h92, hA, hB, h90, h91, hj => by
    have d := WExec.dec (cap := cap) 92 σ (by omega)
    set σ1 := σ.setv 92 (σ.val 92 - 1) with hσ1
    have x := shlB_spec cap W (A := Sm 2) (B := Sm 3) (F := 90) (R := 91) (by decide) (by decide) σ1 a b
      (numOn_setv _ _ _ _ _ _ hA) (numOn_setv _ _ _ _ _ _ hB) (by simp [hσ1, h90]) (by simp [hσ1, h91]) hcap
    have ih := shlL_spec cap W b hcap j (σ1.sets (Sm 2) (frame (binary W (2 * a)))) (2 * a)
      (by simp [hσ1, h92]) (numOn_sets_self _ _ _ _ (by simp [hσ1, hA.2]))
      (numOn_sets_other _ _ _ _ _ _ (by decide) (numOn_setv _ _ _ _ _ _ hB)) (by simp [hσ1, h90])
      (by simp [hσ1, h91]) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d x) ih) ?_ (by ring_nf; omega)
    rw [hσ1, wsets_sets', show 2 * a * 2 ^ j = a * 2 ^ (j + 1) by ring]
    apply WState.eq
    · rfl
    · rfl
    · simp [Function.update_idem]
    · rfl

/-! ## All the words -/

/-- The zero words of width `W`. -/
def zs13 : List (Fin 50) := [Sm 3, Sm 33, Sm 34, Sm 35, Sm 36, Sm 37, Sm 38, Sm 39, Sm 40, Sm 42, Sm 44, Sm 46, Sm 41]

/-- **The words' state.** -/
def wordsSt (σ : WState 49 112) (W L k : ℕ) : WState 49 112 :=
  (((((setsAll σ zs13 (frame (binary W 0))).sets (Sm 41) (frame (binary W 1))).sets (Sm 2)
    (frame (binary W (2 ^ L)))).sets (Sm 32) (frame (binary W 0))).sets (Sm 0) (frame (binary k 0))).sets (Sm 43)
    (frame (binary k 0))

/-- The words' cost. -/
def wordsCost (W L k : ℕ) : ℕ :=
  13 * (zwCost W + 1) + (41 * W + 7 + 1 + (zwCost W + 1 + (41 * W + 7 + 1 + (18 * L + 3 + 1 + (L * (41 * W + 12) + 1 +
    1 + (zwCost W + 1 + (zwCost k + 1 + zwCost k)))))))

/-- The words after the zero-word run. -/
def wordsRest : WM 49 112 :=
  .seq (oneB (Sm 41) (Sm 3) 90 91) (.seq (zwP (Sm 2) 86) (.seq (oneB (Sm 2) (Sm 3) 90 91)
    (.seq (FinalPass.Hash4.wcopyR 85 92 89) (.seq shlL (.seq (zwP (Sm 32) 86) (.seq (zwP (Sm 0) 73) (zwP (Sm 43) 73)))))))

/-- The rest's cost. -/
def restCost (W L k : ℕ) : ℕ :=
  41 * W + 7 + 1 + (zwCost W + 1 + (41 * W + 7 + 1 + (18 * L + 3 + 1 + (L * (41 * W + 12) + 1 + 1 + (zwCost W + 1 +
    (zwCost k + 1 + zwCost k))))))

theorem wordsRest_spec (cap : ℕ) (σ : WState 49 112) (W L k : ℕ) (h86 : σ.val 86 = W) (h85 : σ.val 85 = L)
    (h73 : σ.val 73 = k) (hz : ∀ r : Fin 112, (r = 89 ∨ r = 90 ∨ r = 91 ∨ r = 92 ∨ r = 98 ∨ r = 99) → σ.val r = 0)
    (n3 : NumOn σ (Sm 3) W 0) (n41 : NumOn σ (Sm 41) W 0)
    (hst : ∀ Z : Fin 50, (Z = Sm 2 ∨ Z = Sm 32 ∨ Z = Sm 0 ∨ Z = Sm 43) → σ.st Z = [] ∧ σ.sh Z = 0)
    (h47 : σ.sh (Sm 47) = 0) (hW1 : 1 ≤ W) (hcap : 2 * W + 2 * k + L + 2 ≤ cap) :
    WExec cap wordsRest σ ((((σ.sets (Sm 41) (frame (binary W 1))).sets (Sm 2) (frame (binary W (2 ^ L)))).sets (Sm 32)
      (frame (binary W 0))).sets (Sm 0) (frame (binary k 0)) |>.sets (Sm 43) (frame (binary k 0))) (restCost W L k) := by
  have z := hz
  have d1 : Sm 2 ≠ Sm 41 := by decide
  have d2 : Sm 32 ≠ Sm 41 := by decide
  have d3 : Sm 32 ≠ Sm 2 := by decide
  have d4 : Sm 0 ≠ Sm 41 := by decide
  have d5 : Sm 0 ≠ Sm 2 := by decide
  have d6 : Sm 0 ≠ Sm 32 := by decide
  have d7 : Sm 43 ≠ Sm 41 := by decide
  have d8 : Sm 43 ≠ Sm 2 := by decide
  have d9 : Sm 43 ≠ Sm 32 := by decide
  have d10 : Sm 43 ≠ Sm 0 := by decide
  have y1 := oneB_spec cap W (A := Sm 41) (B := Sm 3) (F := 90) (R := 91) (by decide) (by decide) σ 0 0 n41 n3
    (z 90 (by decide)) (z 91 (by decide)) hW1 (by omega)
  set σ2 := σ.sets (Sm 41) (frame (binary W 1)) with hσ2
  obtain ⟨s2, h2⟩ := hst (Sm 2) (Or.inl rfl)
  have y2 := zwP_spec cap (Sm 2) (by decide) 86 (by decide) σ2 W (by simp [hσ2, h86]) (by simp [hσ2, z 89 (by decide)])
    (by simp [hσ2, z 98 (by decide)]) (by simp [hσ2, z 99 (by decide)]) (by simp [hσ2, h47]) (by simp [hσ2, h2])
    (by simp [hσ2, d1, s2]) (by omega)
  set σ3 := σ2.sets (Sm 2) (frame (binary W 0)) with hσ3
  have y3 := oneB_spec cap W (A := Sm 2) (B := Sm 3) (F := 90) (R := 91) (by decide) (by decide) σ3 0 0
    (numOn_sets_self _ _ _ _ (by simp [hσ2, h2]))
    (numOn_sets_other _ _ _ _ _ _ (by decide) (numOn_sets_other _ _ _ _ _ _ (by decide) n3))
    (by simp [hσ3, hσ2, z 90 (by decide)]) (by simp [hσ3, hσ2, z 91 (by decide)]) hW1 (by omega)
  set σ4 := σ3.sets (Sm 2) (frame (binary W 1)) with hσ4
  have y4 := cp_spec cap 85 92 89 (by decide) (by decide) (by decide) σ4 L (by simp [hσ4, hσ3, hσ2, h85])
    (by simp [hσ4, hσ3, hσ2, z 92 (by decide)]) (by simp [hσ4, hσ3, hσ2, z 89 (by decide)]) (by omega)
  set σ5 := σ4.setv 92 L with hσ5
  have y5 := shlL_spec cap W 0 (by omega) L σ5 1 (by simp [hσ5])
    (numOn_setv _ _ _ _ _ _ (numOn_sets_self _ _ _ _ (by simp [hσ3, hσ2, h2])))
    (numOn_setv _ _ _ _ _ _ (numOn_sets_other _ _ _ _ _ _ (by decide) (numOn_sets_other _ _ _ _ _ _ (by decide)
      (numOn_sets_other _ _ _ _ _ _ (by decide) n3))))
    (by simp [hσ5, hσ4, hσ3, hσ2, z 90 (by decide)]) (by simp [hσ5, hσ4, hσ3, hσ2, z 91 (by decide)]) (by omega)
  rw [Nat.one_mul] at y5
  have e6 : (σ5.sets (Sm 2) (frame (binary W (2 ^ L)))).setv 92 0 = σ2.sets (Sm 2) (frame (binary W (2 ^ L))) := by
    rw [hσ5, hσ4, hσ3]
    apply WState.eq
    · rfl
    · simp [wsets_sets']
    · simp [hσ2, Function.update_idem, Gate.wsetv_zero, z 92 (by decide)]
    · rfl
  rw [e6] at y5
  set σ6 := σ2.sets (Sm 2) (frame (binary W (2 ^ L))) with hσ6
  obtain ⟨s32, h32⟩ := hst (Sm 32) (Or.inr (Or.inl rfl))
  have y6 := zwP_spec cap (Sm 32) (by decide) 86 (by decide) σ6 W (by simp [hσ6, hσ2, h86])
    (by simp [hσ6, hσ2, z 89 (by decide)]) (by simp [hσ6, hσ2, z 98 (by decide)]) (by simp [hσ6, hσ2, z 99 (by decide)])
    (by simp [hσ6, hσ2, h47]) (by simp [hσ6, hσ2, h32]) (by simp [hσ6, hσ2, d2, d3, s32]) (by omega)
  set σ7 := σ6.sets (Sm 32) (frame (binary W 0)) with hσ7
  obtain ⟨s0, h0⟩ := hst (Sm 0) (Or.inr (Or.inr (Or.inl rfl)))
  have y7 := zwP_spec cap (Sm 0) (by decide) 73 (by decide) σ7 k (by simp [hσ7, hσ6, hσ2, h73])
    (by simp [hσ7, hσ6, hσ2, z 89 (by decide)]) (by simp [hσ7, hσ6, hσ2, z 98 (by decide)])
    (by simp [hσ7, hσ6, hσ2, z 99 (by decide)]) (by simp [hσ7, hσ6, hσ2, h47]) (by simp [hσ7, hσ6, hσ2, h0])
    (by simp [hσ7, hσ6, hσ2, d4, d5, d6, s0]) (by omega)
  set σ8 := σ7.sets (Sm 0) (frame (binary k 0)) with hσ8
  obtain ⟨s43, h43⟩ := hst (Sm 43) (Or.inr (Or.inr (Or.inr rfl)))
  have y8 := zwP_spec cap (Sm 43) (by decide) 73 (by decide) σ8 k (by simp [hσ8, hσ7, hσ6, hσ2, h73])
    (by simp [hσ8, hσ7, hσ6, hσ2, z 89 (by decide)]) (by simp [hσ8, hσ7, hσ6, hσ2, z 98 (by decide)])
    (by simp [hσ8, hσ7, hσ6, hσ2, z 99 (by decide)]) (by simp [hσ8, hσ7, hσ6, hσ2, h47])
    (by simp [hσ8, hσ7, hσ6, hσ2, h43]) (by simp [hσ8, hσ7, hσ6, hσ2, d7, d8, d9, d10, s43]) (by omega)
  exact WExec.seq y1 (WExec.seq y2 (WExec.seq y3 (WExec.seq y4 (WExec.seq y5 (WExec.seq y6 (WExec.seq y7 y8))))))

theorem wordsP_eq : wordsP = zwSeq zs13 86 wordsRest := rfl

/-- **The loop's words.** -/
theorem wordsP_spec (cap : ℕ) (σ : WState 49 112) (W L k : ℕ) (h86 : σ.val 86 = W) (h85 : σ.val 85 = L)
    (h73 : σ.val 73 = k) (hz : ∀ r : Fin 112, (r = 89 ∨ r = 90 ∨ r = 91 ∨ r = 92 ∨ r = 98 ∨ r = 99) → σ.val r = 0)
    (hst : ∀ Z : Fin 50, (Z ∈ zs13 ∨ Z = Sm 2 ∨ Z = Sm 32 ∨ Z = Sm 0 ∨ Z = Sm 43) → σ.st Z = [] ∧ σ.sh Z = 0)
    (h47 : σ.sh (Sm 47) = 0) (hW1 : 1 ≤ W) (hcap : 2 * W + 2 * k + L + 2 ≤ cap) :
    WExec cap wordsP σ (wordsSt σ W L k) (wordsCost W L k) := by
  have v1 : (setsAll σ zs13 (frame (binary W 0))).val = σ.val := setsAll_val _ _ σ
  have sh1 : (setsAll σ zs13 (frame (binary W 0))).sh = σ.sh := setsAll_sh _ _ σ
  have st1 := setsAll_st zs13 (frame (binary W 0)) σ
  have rest := wordsRest_spec cap (setsAll σ zs13 (frame (binary W 0))) W L k (by rw [v1, h86]) (by rw [v1, h85])
    (by rw [v1, h73]) (fun r hr => by rw [v1]; exact hz r hr)
    ⟨by rw [st1]; simp [zs13], by rw [sh1]; exact (hst (Sm 3) (Or.inl (by simp [zs13]))).2⟩
    ⟨by rw [st1]; simp [zs13], by rw [sh1]; exact (hst (Sm 41) (Or.inl (by simp [zs13]))).2⟩
    (fun Z hZ => by
      have hn : Z ∉ zs13 := by rcases hZ with rfl | rfl | rfl | rfl <;> decide
      refine ⟨by rw [st1, if_neg hn]; exact (hst Z (Or.inr hZ)).1, by rw [sh1]; exact (hst Z (Or.inr hZ)).2⟩)
    (by rw [sh1]; exact h47) hW1 hcap
  have x := zwSeq_spec cap 86 (by decide) W (by omega) _ _ _ zs13 σ (by decide)
    (fun Z hZ => ⟨fun e => by subst e; revert hZ; decide, (hst Z (Or.inl hZ)).2, (hst Z (Or.inl hZ)).1⟩)
    h86 (hz 89 (by decide)) (hz 98 (by decide)) (hz 99 (by decide)) h47 rest
  rw [wordsP_eq]
  exact WExec.cast cap x rfl (by unfold wordsCost restCost; simp only [zs13, List.length_cons, List.length_nil]; omega)

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
