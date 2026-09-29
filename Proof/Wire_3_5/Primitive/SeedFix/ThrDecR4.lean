import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR3

/-! # THR decode front, RADIX part 4: the prime row's `(p, s)` from W6's primes word

The RADIX setup's values carry the unit's prime `p` and residue `s` (`RadSetup.radVals`: the THR state's prime row
`(Enum.primeRowEquiv c).symm (t mod Σp)`, primes increasing, then the residue). After the docks, W6's primes word
`unaryList (primesList cut)` is on stream `130`; **`scanW`** reads it item by item, subtracting each prime from the
prime-row index `H 15` until the index falls below the current prime: then `H 25 = p_m` and `H 24 = idx − Σ_{i<m} p_i`
(`Σ_{i<m} p_i ≤ idx < Σ_{i≤m} p_i`), and the stream is rewound.

* `gtS`, `sbS`, `scanBody`, **`scan_loop`** (the loop invariant, by induction on the items left), `scanW`,
  **`scan_run`**.

Paper quantity of the main type: the prime row `(p, s mod p)` of the THR state (row:prime, P3:2573-2580). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.CapNum

def gtS : Fin 6 ↪ Fin LNR := ⟨![H 25, H 24, H 28, H 33, H 34, H 35], by decide⟩
def sbS : Fin 4 ↪ Fin LNR := ⟨![H 24, H 25, H 36, H 37], by decide⟩
@[simp] theorem gtS_apply (i : Fin 6) : gtS i = ![H 25, H 24, H 28, H 33, H 34, H 35] i := rfl
@[simp] theorem sbS_apply (i : Fin 4) : sbS i = ![H 24, H 25, H 36, H 37] i := rfl

theorem uL_take_succ (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (Data.unaryList (L.take (k + 1))).length = (Data.unaryList (L.take k)).length + L.getD k 0 + 1 := by
  rw [unaryList_length_le, unaryList_length_le, List.sum_take_succ _ _ hk, List.length_take, List.length_take,
    List.getD_eq_getElem _ _ hk]
  omega

theorem sum_take_succ' (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (L.take (k + 1)).sum = (L.take k).sum + L.getD k 0 := by
  rw [List.sum_take_succ _ _ hk, List.getD_eq_getElem _ _ hk]

theorem getD_le_sum (L : List ℕ) (k : ℕ) : L.getD k 0 ≤ L.sum := by
  rcases Nat.lt_or_ge k L.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk]; exact List.le_sum_of_mem (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ hk]; omega

theorem uL_take_le (L : List ℕ) (k : ℕ) : (Data.unaryList (L.take k)).length ≤ (Data.unaryList L).length := by
  rw [unaryList_length_le, unaryList_length_le]
  have h1 : (L.take k).length ≤ L.length := by rw [List.length_take]; omega
  have h2 : (L.take k).sum ≤ L.sum := by
    conv_rhs => rw [← List.take_append_drop k L]
    rw [List.sum_append]; omega
  omega

/-- The value-named truncated subtraction `a := a − b` (UnaryArith's `subW`). -/
theorem sub1'' {ns nr : ℕ} (cap : ℕ) (R : Fin 4 ↪ Fin nr) (a b : ℕ) (σ : WState ns nr) (ha : σ.val (R 0) = a)
    (hb : σ.val (R 1) = b) (ht : σ.val (R 2) = 0) (hw : σ.val (R 3) = 0) (hac : a ≤ cap) (hbc : b ≤ cap) :
    WExec cap (subW R) σ (σ.setv (R 0) (a - b)) (UnaryPow.sq cap) := by
  have h := subW_spec cap R σ ht hw (by rw [ha]; exact hac) (by rw [hb]; exact hbc)
  rw [ha, hb] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

section R4
variable (cap : ℕ) (x : ℕ)

/-- The scan's decision: below the current prime, stop; else subtract it and clear it. -/
def scanIfr : WM (LNS x) LNR :=
  .ifr (H 28) (.seq (.dec (H 27)) (.dec (H 28))) (.seq (subW sbS) (WM.clear (H 25)))

/-- One item of the scan: read the next prime, count its cells, compare, subtract or stop. -/
def scanBody (s : Fin (LNS x + 1)) : WM (LNS x) LNR :=
  .seq (readItemW s (H 25)) (.seq (addTo (H 25) (H 26) TM) (.seq (.inc (H 26)) (.seq (gtFlagW gtS) (scanIfr x))))

theorem hne (a b : Fin 40) (h : a.val ≠ b.val) : H a ≠ H b := fun e => h (congrArg Fin.val (H.injective e))

theorem TM_ne_H (k : Fin 40) : TM ≠ H k := H_ne k TM (by decide)

/-- **The scan's invariant** at item `k`. -/
structure ScanInv (s : Fin (LNS x + 1)) (L : List ℕ) (tail : List Bool) (idx k : ℕ) (σ : WState (LNS x) LNR) :
    Prop where
  st : σ.st s = Data.unaryList L ++ tail
  sh : σ.sh s = (Data.unaryList (L.take k)).length
  le : (L.take k).sum ≤ idx
  r24 : σ.val (H 24) = idx - (L.take k).sum
  r25 : σ.val (H 25) = 0
  r26 : σ.val (H 26) = (Data.unaryList (L.take k)).length
  r27 : σ.val (H 27) = 1
  r28 : σ.val (H 28) = 0
  r33 : σ.val (H 33) = 0
  r34 : σ.val (H 34) = 0
  r35 : σ.val (H 35) = 0
  r36 : σ.val (H 36) = 0
  r37 : σ.val (H 37) = 0
  rT : σ.val TM = 0

/-- The item's first four steps: read, count, compare. -/
theorem scan_pre (s : Fin (LNS x + 1)) (L : List ℕ) (tail : List Bool) (idx k : ℕ) (σ : WState (LNS x) LNR)
    (hI : ScanInv x s L tail idx k σ) (hk : k < L.length) (hLc : (Data.unaryList L).length + idx + 2 ≤ cap) :
    ∃ σ4 : WState (LNS x) LNR, (∀ τ c, WExec cap (scanIfr x) σ4 τ c →
        WExec cap (scanBody x s) σ τ (4 * UnaryPow.sq cap + 4 + c)) ∧
      σ4.val (H 25) = L.getD k 0 ∧ σ4.val (H 24) = idx - (L.take k).sum ∧
      σ4.val (H 26) = (Data.unaryList (L.take (k + 1))).length ∧
      σ4.sh s = (Data.unaryList (L.take (k + 1))).length ∧
      σ4.val (H 28) = (if idx - (L.take k).sum < L.getD k 0 then 1 else 0) ∧
      (∀ r, r ≠ H 25 → r ≠ H 26 → r ≠ H 28 → σ4.val r = σ.val r) ∧ σ4.st = σ.st ∧
      (∀ s', s' ≠ s → σ4.sh s' = σ.sh s') ∧ σ4.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hsumL : L.sum ≤ (Data.unaryList L).length := by rw [unaryList_length_le]; omega
  set q := L.getD k 0 with hq
  have hqL : q ≤ L.sum := getD_le_sum L k
  have hkl := uL_take_succ L k hk
  have hkle := uL_take_le L (k + 1)
  have hkle0 := uL_take_le L k
  have e1 := readItem_at cap s (H 25) L tail k hk 0 σ hI.st hI.sh hI.r25 (by omega)
  have hr1 : readItemW s (H 25) = readItemW s (H 25) := rfl
  set σ1 := (σ.seth s (Data.unaryList (L.take (k + 1))).length).setv (H 25) (0 + q) with hσ1
  have e2 := add1 cap (H 25) (H 26) TM (by decide) (by decide) (by decide) (0 + q)
    (Data.unaryList (L.take k)).length σ1 (by rw [hσ1]; simp)
    (by rw [hσ1]; simp only [WState.setv_val, WState.seth_val]; rw [Function.update_of_ne (hne 26 25 (by decide))]
        exact hI.r26)
    (by rw [hσ1]; simp only [WState.setv_val, WState.seth_val]; rw [Function.update_of_ne (TM_ne_H 25)]; exact hI.rT)
    (by omega) (by omega)
  set σ2 := σ1.setv (H 26) ((Data.unaryList (L.take k)).length + (0 + q)) with hσ2
  have e3 := inc1 cap (H 26) ((Data.unaryList (L.take k)).length + (0 + q)) σ2 (by rw [hσ2]; simp) (by omega)
  set σ3 := σ2.setv (H 26) ((Data.unaryList (L.take k)).length + (0 + q) + 1) with hσ3
  have k3 : ∀ r, r ≠ H 25 → r ≠ H 26 → σ3.val r = σ.val r := fun r a b => by
    rw [hσ3, hσ2, hσ1]; simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne b, Function.update_of_ne b, Function.update_of_ne a]
  have e4 := gt1 cap gtS (0 + q) (idx - (L.take k).sum) σ3
    (show σ3.val (H 25) = 0 + q by rw [hσ3, hσ2, hσ1]; simp only [WState.setv_val, WState.seth_val]
                                   rw [Function.update_of_ne (hne 25 26 (by decide)),
                                     Function.update_of_ne (hne 25 26 (by decide)), Function.update_self])
    (show σ3.val (H 24) = _ by rw [k3 _ (hne 24 25 (by decide)) (hne 24 26 (by decide)), hI.r24])
    (show σ3.val (H 28) = 0 by rw [k3 _ (hne 28 25 (by decide)) (hne 28 26 (by decide)), hI.r28])
    (show σ3.val (H 33) = 0 by rw [k3 _ (hne 33 25 (by decide)) (hne 33 26 (by decide)), hI.r33])
    (show σ3.val (H 34) = 0 by rw [k3 _ (hne 34 25 (by decide)) (hne 34 26 (by decide)), hI.r34])
    (show σ3.val (H 35) = 0 by rw [k3 _ (hne 35 25 (by decide)) (hne 35 26 (by decide)), hI.r35])
    (by omega) (by omega) (by omega)
  have g2 : gtS 2 = H 28 := rfl
  rw [g2] at e4
  refine ⟨σ3.setv (H 28) (if idx - (L.take k).sum < 0 + q then 1 else 0), fun τ c e =>
    WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e)))) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (hne 25 28 (by decide)), hσ3, hσ2, hσ1]
    simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne (hne 25 26 (by decide)), Function.update_of_ne (hne 25 26 (by decide)),
      Function.update_self]; omega
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (hne 24 28 (by decide)), k3 _ (hne 24 25 (by decide)) (hne 24 26 (by decide)), hI.r24]
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (hne 26 28 (by decide)), hσ3]
    simp only [WState.setv_val, Function.update_self]; omega
  · rw [WState.setv_sh, hσ3, WState.setv_sh, hσ2, WState.setv_sh, hσ1, WState.setv_sh, WState.seth_sh,
      Function.update_self]
  · simp only [WState.setv_val, Function.update_self, Nat.zero_add]
  · intro r a b c
    simp only [WState.setv_val]
    rw [Function.update_of_ne c, k3 r a b]
  · rw [WState.setv_st, hσ3, WState.setv_st, hσ2, WState.setv_st, hσ1, WState.setv_st, WState.seth_st]
  · intro s' hs'
    rw [WState.setv_sh, hσ3, WState.setv_sh, hσ2, WState.setv_sh, hσ1, WState.setv_sh, WState.seth_sh,
      Function.update_of_ne hs']
  · rw [WState.setv_cell, hσ3, WState.setv_cell, hσ2, WState.setv_cell, hσ1, WState.setv_cell, WState.seth_cell]

/-- **The scan loop.** -/
theorem scan_loop (s : Fin (LNS x + 1)) (L : List ℕ) (tail : List Bool) (idx : ℕ) (hidx : idx < L.sum)
    (hLc : (Data.unaryList L).length + idx + 2 ≤ cap) :
    ∀ (m k : ℕ) (σ : WState (LNS x) LNR), m + k = L.length → ScanInv x s L tail idx k σ →
      ∃ τ c t, WExec cap (.whr (H 27) (scanBody x s)) σ τ c ∧ c ≤ (m + 1) * (10 * UnaryPow.sq cap) ∧
        k ≤ t ∧ t < L.length ∧ (L.take t).sum ≤ idx ∧ idx < (L.take (t + 1)).sum ∧
        τ.val (H 25) = L.getD t 0 ∧ τ.val (H 24) = idx - (L.take t).sum ∧
        τ.val (H 26) = (Data.unaryList (L.take (t + 1))).length ∧
        τ.sh s = (Data.unaryList (L.take (t + 1))).length ∧ τ.val (H 27) = 0 ∧ τ.val (H 28) = 0 ∧
        (∀ r, r ≠ H 24 → r ≠ H 25 → r ≠ H 26 → r ≠ H 27 → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
        (∀ s', s' ≠ s → τ.sh s' = σ.sh s') ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hsumL : L.sum ≤ (Data.unaryList L).length := by rw [unaryList_length_le]; omega
  intro m
  induction m with
  | zero =>
    intro k σ hmk hI
    exfalso
    have hle := hI.le
    have : L.take k = L := List.take_of_length_le (by omega)
    rw [this] at hle; omega
  | succ m ih =>
    intro k σ hmk hI
    have hk : k < L.length := by omega
    have hks := sum_take_succ' L k hk
    have hqL : L.getD k 0 ≤ L.sum := getD_le_sum L k
    obtain ⟨σ4, comp, v25, v24, v26, sh4, v28, k4, st4, sho4, cl4⟩ := scan_pre cap x s L tail idx k σ hI hk hLc
    by_cases hlt : idx - (L.take k).sum < L.getD k 0
    · have f4 : σ4.val (H 28) = 1 := by rw [v28, if_pos hlt]
      have d27 : σ4.val (H 27) = 1 := by
        rw [k4 _ (hne 27 25 (by decide)) (hne 27 26 (by decide)) (hne 27 28 (by decide))]; exact hI.r27
      have e5 := dec1 cap (H 27) 1 σ4 d27 (by omega)
      have e6 := dec1 cap (H 28) 1 (σ4.setv (H 27) (1 - 1))
        (by simp only [WState.setv_val]; rw [Function.update_of_ne (hne 28 27 (by decide)), f4]) (by omega)
      set σ6 := (σ4.setv (H 27) (1 - 1)).setv (H 28) (1 - 1) with hσ6
      have e7 : WExec cap (.whr (H 27) (scanBody x s)) σ6 σ6 1 := WExec.whrF (by
        rw [hσ6]; simp only [WState.setv_val]; rw [Function.update_of_ne (hne 27 28 (by decide)), Function.update_self])
      have eb := comp σ6 _ (WExec.ifrT (by rw [f4]; omega) (WExec.seq e5 e6))
      refine ⟨σ6, _, k, WExec.whrT (by rw [hI.r27]; omega) eb e7, ?_, le_rfl, hk, hI.le, by rw [hks]; omega, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := Nat.le_mul_of_pos_left (10 * UnaryPow.sq cap) (show 0 < m + 1 + 1 by omega)
        omega
      · rw [hσ6]; simp only [WState.setv_val]
        rw [Function.update_of_ne (hne 25 28 (by decide)), Function.update_of_ne (hne 25 27 (by decide)), v25]
      · rw [hσ6]; simp only [WState.setv_val]
        rw [Function.update_of_ne (hne 24 28 (by decide)), Function.update_of_ne (hne 24 27 (by decide)), v24]
      · rw [hσ6]; simp only [WState.setv_val]
        rw [Function.update_of_ne (hne 26 28 (by decide)), Function.update_of_ne (hne 26 27 (by decide)), v26]
      · rw [hσ6, WState.setv_sh, WState.setv_sh, sh4]
      · rw [hσ6]; simp only [WState.setv_val]
        rw [Function.update_of_ne (hne 27 28 (by decide)), Function.update_self]
      · rw [hσ6]; simp only [WState.setv_val, Function.update_self]
      · intro r a b c d
        rw [hσ6]; simp only [WState.setv_val]
        by_cases h28r : r = H 28
        · subst h28r; rw [Function.update_self, hI.r28]
        · rw [Function.update_of_ne h28r, Function.update_of_ne d, k4 r b c h28r]
      · rw [hσ6, WState.setv_st, WState.setv_st, st4]
      · intro s' hs'; rw [hσ6, WState.setv_sh, WState.setv_sh, sho4 s' hs']
      · rw [hσ6, WState.setv_cell, WState.setv_cell, cl4]
    · have f4 : σ4.val (H 28) = 0 := by rw [v28, if_neg hlt]
      have e5 := sub1'' cap sbS (idx - (L.take k).sum) (L.getD k 0) σ4 (show σ4.val (H 24) = _ from v24)
        (show σ4.val (H 25) = _ from v25)
        (show σ4.val (H 36) = 0 by
          rw [k4 _ (hne 36 25 (by decide)) (hne 36 26 (by decide)) (hne 36 28 (by decide))]; exact hI.r36)
        (show σ4.val (H 37) = 0 by
          rw [k4 _ (hne 37 25 (by decide)) (hne 37 26 (by decide)) (hne 37 28 (by decide))]; exact hI.r37)
        (by omega) (by omega)
      have s0 : sbS 0 = H 24 := rfl
      rw [s0] at e5
      have e6 := clear1 cap (H 25) (L.getD k 0) (σ4.setv (H 24) (idx - (L.take k).sum - L.getD k 0))
        (by simp only [WState.setv_val]; rw [Function.update_of_ne (hne 25 24 (by decide)), v25]) (by omega)
      set σ6 := (σ4.setv (H 24) (idx - (L.take k).sum - L.getD k 0)).setv (H 25) 0 with hσ6
      have eb := comp σ6 _ (WExec.ifrF f4 (WExec.seq e5 e6))
      have kk : ∀ r, r ≠ H 24 → r ≠ H 25 → r ≠ H 26 → r ≠ H 28 → σ6.val r = σ.val r := fun r a b c d => by
        rw [hσ6]; simp only [WState.setv_val]; rw [Function.update_of_ne b, Function.update_of_ne a, k4 r b c d]
      have hI' : ScanInv x s L tail idx (k + 1) σ6 :=
        { st := by rw [hσ6, WState.setv_st, WState.setv_st, st4]; exact hI.st
          sh := by rw [hσ6, WState.setv_sh, WState.setv_sh, sh4]
          le := by have := hI.le; rw [hks]; omega
          r24 := by
            rw [hσ6]; simp only [WState.setv_val]
            rw [Function.update_of_ne (hne 24 25 (by decide)), Function.update_self, hks]; omega
          r25 := by rw [hσ6]; simp only [WState.setv_val, Function.update_self]
          r26 := by
            rw [hσ6]; simp only [WState.setv_val]
            rw [Function.update_of_ne (hne 26 25 (by decide)), Function.update_of_ne (hne 26 24 (by decide)), v26]
          r27 := by
            rw [kk _ (hne 27 24 (by decide)) (hne 27 25 (by decide)) (hne 27 26 (by decide)) (hne 27 28 (by decide))]
            exact hI.r27
          r28 := by
            rw [hσ6]; simp only [WState.setv_val]
            rw [Function.update_of_ne (hne 28 25 (by decide)), Function.update_of_ne (hne 28 24 (by decide)), f4]
          r33 := by
            rw [kk _ (hne 33 24 (by decide)) (hne 33 25 (by decide)) (hne 33 26 (by decide)) (hne 33 28 (by decide))]
            exact hI.r33
          r34 := by
            rw [kk _ (hne 34 24 (by decide)) (hne 34 25 (by decide)) (hne 34 26 (by decide)) (hne 34 28 (by decide))]
            exact hI.r34
          r35 := by
            rw [kk _ (hne 35 24 (by decide)) (hne 35 25 (by decide)) (hne 35 26 (by decide)) (hne 35 28 (by decide))]
            exact hI.r35
          r36 := by
            rw [kk _ (hne 36 24 (by decide)) (hne 36 25 (by decide)) (hne 36 26 (by decide)) (hne 36 28 (by decide))]
            exact hI.r36
          r37 := by
            rw [kk _ (hne 37 24 (by decide)) (hne 37 25 (by decide)) (hne 37 26 (by decide)) (hne 37 28 (by decide))]
            exact hI.r37
          rT := by
            rw [kk _ (TM_ne_H 24) (TM_ne_H 25) (TM_ne_H 26) (TM_ne_H 28)]; exact hI.rT }
      obtain ⟨τ, c, t, e, cle, kt, tlt, tle, tlt2, t25, t24, t26, tsh, t27, t28, tk, tst, tsho, tcl⟩ :=
        ih (k + 1) σ6 (by omega) hI'
      refine ⟨τ, _, t, WExec.whrT (by rw [hI.r27]; omega) eb e, ?_, by omega, tlt, tle, tlt2, t25, t24, t26, tsh, t27,
        t28, ?_, ?_, ?_, ?_⟩
      · have : c ≤ (m + 1) * (10 * UnaryPow.sq cap) := cle
        nlinarith
      · intro r a b c' d
        rw [tk r a b c' d]
        by_cases h28r : r = H 28
        · subst h28r; rw [hσ6]; simp only [WState.setv_val]
          rw [Function.update_of_ne (hne 28 25 (by decide)), Function.update_of_ne (hne 28 24 (by decide)), f4, hI.r28]
        · exact kk r a b c' h28r
      · rw [tst, hσ6, WState.setv_st, WState.setv_st, st4]
      · intro s' hs'; rw [tsho s' hs', hσ6, WState.setv_sh, WState.setv_sh, sho4 s' hs']
      · rw [tcl, hσ6, WState.setv_cell, WState.setv_cell, cl4]

/-- **The prime scan**: `H 24 := idx` (from `H 15`), the loop, the primes word rewound. -/
def scanW (s : Fin (LNS x + 1)) : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (H 15) (H 24) TM) (.seq (.inc (H 27)) (.seq (.whr (H 27) (scanBody x s))
    (WM.rewind s (H 26))))

/-- **The prime scan, run**: the item `t` with `Σ_{i<t} ≤ idx < Σ_{i≤t}`, `H 25 = L_t`, `H 24 = idx − Σ_{i<t}`, the
scan's counters back at `0`, the stream's head back at `0`. -/
theorem scan_run (s : Fin (LNS x + 1)) (L : List ℕ) (tail : List Bool) (idx : ℕ) (σ : WState (LNS x) LNR)
    (hst : σ.st s = Data.unaryList L ++ tail) (hsh : σ.sh s = 0) (h15 : σ.val (H 15) = idx)
    (z : ∀ k : Fin 40, 24 ≤ k.val → k.val ≤ 37 → k.val ≠ 29 → k.val ≠ 30 → k.val ≠ 31 → k.val ≠ 32 →
      σ.val (H k) = 0) (zT : σ.val TM = 0) (hidx : idx < L.sum)
    (hLc : (Data.unaryList L).length + idx + 2 ≤ cap) :
    ∃ τ c t, WExec cap (scanW x s) σ τ c ∧
      c ≤ UnaryPow.sq cap + 1 + (3 + 1 + ((L.length + 1) * (10 * UnaryPow.sq cap) + 1 +
        (5 * (Data.unaryList L).length + 1))) ∧
      t < L.length ∧ (L.take t).sum ≤ idx ∧ idx < (L.take (t + 1)).sum ∧
      τ.val (H 25) = L.getD t 0 ∧ τ.val (H 24) = idx - (L.take t).sum ∧ τ.val (H 26) = 0 ∧ τ.val (H 27) = 0 ∧
      τ.val (H 28) = 0 ∧ τ.sh s = 0 ∧
      (∀ r, r ≠ H 24 → r ≠ H 25 → r ≠ H 26 → r ≠ H 27 → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
      (∀ s', s' ≠ s → τ.sh s' = σ.sh s') ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have e1 := copy1 cap (H 15) (H 24) TM (by decide) (by decide) (by decide) idx σ h15
    (z 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) zT (by omega)
  set σ1 := σ.setv (H 24) idx with hσ1
  have e2 := WExec.inc (cap := cap) (H 27) σ1 (by
    rw [hσ1]; simp only [WState.setv_val]; rw [Function.update_of_ne (hne 27 24 (by decide))]
    rw [z 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
  set σ2 := σ1.setv (H 27) (σ1.val (H 27) + 1) with hσ2
  have k2 : ∀ r, r ≠ H 24 → r ≠ H 27 → σ2.val r = σ.val r := fun r a b => by
    rw [hσ2, hσ1]; simp only [WState.setv_val]; rw [Function.update_of_ne b, Function.update_of_ne a]
  have zz : ∀ k : Fin 40, 24 < k.val → k.val ≤ 37 → k.val ≠ 27 → k.val ≠ 29 → k.val ≠ 30 → k.val ≠ 31 →
      k.val ≠ 32 → σ2.val (H k) = 0 := fun k a b c d e f g => by
    rw [k2 _ (hne k 24 (by omega)) (hne k 27 c)]; exact z k (by omega) b d e f g
  have hI : ScanInv x s L tail idx 0 σ2 :=
    { st := by rw [hσ2, hσ1]; exact hst
      sh := by rw [hσ2, hσ1]; simp [hsh, Data.unaryList]
      le := by simp
      r24 := by rw [hσ2]; simp only [WState.setv_val]; rw [Function.update_of_ne (hne 24 27 (by decide)), hσ1]; simp
      r25 := zz 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r26 := by rw [zz 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [Data.unaryList]
      r27 := by
        rw [hσ2]; simp only [WState.setv_val, Function.update_self]
        rw [hσ1]; simp only [WState.setv_val]; rw [Function.update_of_ne (hne 27 24 (by decide))]
        rw [z 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      r28 := zz 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r33 := zz 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r34 := zz 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r35 := zz 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r36 := zz 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r37 := zz 37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rT := by rw [k2 _ (TM_ne_H 24) (TM_ne_H 27)]; exact zT }
  obtain ⟨τ, c, t, e3, cle, -, tlt, tle, tlt2, t25, t24, t26, tsh, t27, t28, tk, tst, tsho, tcl⟩ :=
    scan_loop cap x s L tail idx hidx hLc L.length 0 σ2 (by omega) hI
  have hle := uL_take_le L (t + 1)
  have e4 := wrewind_spec cap s (H 26) _ τ t26 (by rw [t26]; omega)
  refine ⟨_, _, t, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), ?_, tlt, tle, tlt2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have : c ≤ (L.length + 1) * (10 * UnaryPow.sq cap) := cle
    have : 3 * (idx) ≤ 3 * idx := le_rfl
    omega
  · simp only [WState.seth_val, WState.setv_val]; rw [Function.update_of_ne (hne 25 26 (by decide)), t25]
  · simp only [WState.seth_val, WState.setv_val]; rw [Function.update_of_ne (hne 24 26 (by decide)), t24]
  · simp
  · simp only [WState.seth_val, WState.setv_val]; rw [Function.update_of_ne (hne 27 26 (by decide)), t27]
  · simp only [WState.seth_val, WState.setv_val]; rw [Function.update_of_ne (hne 28 26 (by decide)), t28]
  · simp [tsh]
  · intro r a b c' d
    simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne c', tk r a b c' d, k2 r a d]
  · simp [tst, hσ2, hσ1]
  · intro s' hs'
    simp only [WState.seth_sh, WState.setv_sh]; rw [Function.update_of_ne hs', tsho s' hs']; rfl
  · simp [tcl, hσ2, hσ1]

end R4

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
