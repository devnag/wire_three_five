import Proof.Wire_3_5.Selection.CosPops

/-! # C1.5: one candidate coset (P3:1356-1360)

Paper: "Sum its exact count with the rational population weights, over gates and rows. There are 2^k candidate
cosets [...] Select a minimum objective" (P3:1356-1360). At the coset counter `N` the machine computes the exact key
`(AN, AD) = objKey` of the coset `codesOfIdx s r N` (from `(0, 1)`, the population loop), rewinds the population table,
compares the key with the best key `(BN, BD)` by C6's cross-multiplied `ratLtB` (`ratLt`), and on a strict
improvement copies the key into `(BN, BD)` and the counter word into `BEST` (C6's `copyB`): the running first
minimizer (`argminIdx`). Main declarations: `keyAt`, `zLt`, `qLt`, `cosetB`, `cosetBCost`, **`cosetB_spec`**.
Paper quantity: a candidate coset's exact objective and the running minimum over the cosets. -/

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

/-- The exact key of the coset with counter value `N`. -/
def keyAt (R : SelectionReq) (h : ParamsOk R) (N : ℕ) : RegRat := objKey R h (codesOfIdx R.s R.r N)

/-- The compare's streams: `(AN, AD, BN, BD)`, scratch `S 37, S 38, S 40`. -/
def zLt (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) : Fin 7 ↪ Fin (ns + 1) :=
  ⟨fun i => S (![35, 36, 41, 42, 37, 38, 40] i), hS.comp (by decide)⟩

/-- The compare's registers: the flag `Q 52`, scratch `Q 61, Q 62, Q 63`. -/
def qLt (Q : Fin 64 → Fin nr) (hQ : Function.Injective Q) : Fin 4 ↪ Fin nr :=
  ⟨fun i => Q (![52, 61, 62, 63] i), hQ.comp (by decide)⟩

theorem zLt_apply (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (i : Fin 7) :
    zLt S hS i = S (![35, 36, 41, 42, 37, 38, 40] i) := rfl

theorem qLt_apply (Q : Fin 64 → Fin nr) (hQ : Function.Injective Q) (i : Fin 4) :
    qLt Q hQ i = Q (![52, 61, 62, 63] i) := rfl

/-- On a strict improvement: `BN := AN`, `BD := AD`, `BEST := NS`. -/
def upd (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) : WM ns nr :=
  .seq (copyB (S 41) (S 35) (Q 61) (Q 62)) (.seq (copyB (S 42) (S 36) (Q 61) (Q 62)) (copyB (S 43) (S 0) (Q 61) (Q 62)))

/-- **One candidate coset**: its exact key, the compare, the update. -/
def cosetB (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) : WM ns nr :=
  .seq (zeroB (S 35) (S 2) (Q 61) (Q 62)) (.seq (oneB (S 36) (S 2) (Q 61) (Q 62)) (.seq (copyR (Q 59) (Q 52) (Q 57))
    (.seq (popsL S hS Q hQ) (.seq (rewS (S 31) (Q 58) (Q 52)) (.seq (ratLtB (zLt S hS) (qLt Q hQ))
      (.seq (.ifr (Q 52) (upd S Q) .skip) (WM.clear (Q 52))))))))

/-- The coset's cost (the update's branch counted). -/
def cosetBCost (P : StarParams) (n W V g k np tl : ℕ) (ps : List (List ℕ × ℚ)) : ℕ :=
  41 * W + 3 + 1 + (41 * W + 7 + 1 + (np * (3 + 8) + 1 + 1 + (7 * np + 1) + 1 + (popsCost P n W V g ps + 1 +
    (tl * (1 + 8) + 1 + 1 + (7 * tl + 1) + 1 + (ratLtCost W + 1 +
      (41 * W + 3 + 1 + (41 * W + 3 + 1 + (41 * k + 3)) + 1 + 1 + (3 * 1 + 1)))))))

theorem popTable_eq (W : ℕ) (R : SelectionReq) : popTable W R = [] ++ (R.pops.map (popRec W)).flatten ++ [] := by
  simp [popTable]

/-- **One candidate coset**: with the flag `f = ratLt (keyAt N) (bn, bd)`, the best key becomes the coset's key and
`BEST` the counter `N` exactly when `f`; `Base` holds; every head, register and the cell come back. -/
theorem cosetB_spec (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (W V N : ℕ)
    (hng : R.gates.length < 2 ^ W) (hN : N < 2 ^ (R.r * R.s))
    (hKB : ∀ g ∈ R.gates, KeyBound (gateOf g) V) (hW : 2 * V + 3 ≤ W) (hnk : R.n + (starParamsOf R h).k + 4 ≤ W)
    (hcap : gateNeed (starParamsOf R h) W V ≤ cap) (hcap2 : 2 * W + 1 ≤ cap)
    (hcapG : R.gates.length * (R.n + 1) * (2 * W + 2) + 2 < cap) (hcapk : 2 * (R.r * R.s) + 1 ≤ cap)
    (hcapP : R.pops.length ≤ cap) (hcapT : (popTable W R).length ≤ cap) (hW1 : 1 ≤ W)
    (σ : WState ns nr) (bn bd be : ℕ) (b : Base S Q R h W V N σ) (hPTh : σ.sh (S 31) = 0) (hWd : Words S σ W)
    (hAN : ∃ v, NumOn σ (S 35) W v) (hAD : ∃ v, NumOn σ (S 36) W v) (hBN : NumOn σ (S 41) W bn)
    (hBD : NumOn σ (S 42) W bd) (hBE : NumOn σ (S 43) (R.r * R.s) be) (q52 : σ.val (Q 52) = 0)
    (q53 : σ.val (Q 53) = 0) (q57 : σ.val (Q 57) = 0) (hfit : PopsFit R h N W cap (0, 1) R.pops)
    (hl1 : (keyAt R h N).1 * bd < 2 ^ W) (hl2 : bn * (keyAt R h N).2 < 2 ^ W) (hl3 : (keyAt R h N).2 < 2 ^ W)
    (hl4 : bd < 2 ^ W) :
    ∃ τ : WState ns nr, WExec cap (cosetB S hS Q hQ) σ τ
        (cosetBCost (starParamsOf R h) R.n W V R.gates.length (R.r * R.s) R.pops.length (popTable W R).length
          R.pops) ∧
      Base S Q R h W V N τ ∧ τ.sh (S 31) = 0 ∧ Words S τ W ∧ (∃ v, NumOn τ (S 35) W v) ∧
      (∃ v, NumOn τ (S 36) W v) ∧
      NumOn τ (S 41) W (if ratLt (keyAt R h N) (bn, bd) then (keyAt R h N).1 else bn) ∧
      NumOn τ (S 42) W (if ratLt (keyAt R h N) (bn, bd) then (keyAt R h N).2 else bd) ∧
      NumOn τ (S 43) (R.r * R.s) (if ratLt (keyAt R h N) (bn, bd) then N else be) ∧
      (∀ k : Fin 50, 28 ≤ k.val → k.val ≠ 46 → (k.val < 33 ∨ 44 < k.val) → τ.st (S k) = σ.st (S k)) ∧
      (∀ k : Fin 50, τ.sh (S k) = σ.sh (S k)) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have sne : ∀ a c : Fin 50, a ≠ c → S a ≠ S c := fun a c h => hS.ne h
  have qne : ∀ a c : Fin 64, a ≠ c → Q a ≠ Q c := fun a c h => hQ.ne h
  have q61 : σ.val (Q 61) = 0 := b.tmp 61 (by decide)
  have q62 : σ.val (Q 62) = 0 := b.tmp 62 (by decide)
  have q63 : σ.val (Q 63) = 0 := b.tmp 63 (by decide)
  obtain ⟨an0, hAN⟩ := hAN
  obtain ⟨ad0, hAD⟩ := hAD
  -- AN := 0, AD := 1
  have x1 := zeroB_spec cap W (A := S 35) (B := S 2) (F := Q 61) (R := Q 62) (sne 35 2 (by decide))
    (qne 61 62 (by decide)) σ an0 (2 ^ V) hAN b.of q61 q62 hcap2
  set σ1 := σ.sets (S 35) (frame (binary W 0)) with hσ1
  have x2 := oneB_spec cap W (A := S 36) (B := S 2) (F := Q 61) (R := Q 62) (sne 36 2 (by decide))
    (qne 61 62 (by decide)) σ1 ad0 (2 ^ V) (numOn_sets_other _ _ _ _ _ _ (sne 36 35 (by decide)) hAD)
    (numOn_sets_other _ _ _ _ _ _ (sne 2 35 (by decide)) b.of) (by simp [hσ1, q61]) (by simp [hσ1, q62]) hW1 hcap2
  set σ2 := σ1.sets (S 36) (frame (binary W 1)) with hσ2
  -- MP := #pops
  have x3 := copyR_spec cap (Q 59) (Q 52) (Q 57) (qne 59 52 (by decide)) (qne 59 57 (by decide))
    (qne 52 57 (by decide)) σ2 R.pops.length (by simp [hσ2, hσ1, b.np]) (by simp [hσ2, hσ1, q52])
    (by simp [hσ2, hσ1, q57]) hcapP
  set σ3 := σ2.setv (Q 57) R.pops.length with hσ3
  have b3 : Base S Q R h W V N σ3 :=
    ((b.sets hS hQ 35 (Or.inr (by decide)) _).sets hS hQ 36 (Or.inr (by decide)) _).setv hS hQ 57 (by decide) _
  have wd3 : Words S σ3 W := by
    intro k hk
    obtain ⟨v, hv⟩ := hWd k hk
    have k35 : S k ≠ S 35 := sne k 35 (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have k36 : S k ≠ S 36 := sne k 36 (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    exact ⟨v, by simp [hσ3, hσ2, hσ1, k35, k36, hv.1], by simp [hσ3, hσ2, hσ1, hv.2]⟩
  -- the population loop
  obtain ⟨σ4, x4, b4, hPT4, hPTh4, hAN4, hAD4, hWd4, hst4, hsh4, hval4, h57τ4, hcell4⟩ :=
    popsL_spec S hS Q hQ cap R h W V N hng hN hKB hW hnk hcap hcap2 hcapG R.pops σ3 [] [] (0, 1) b3
      (by simp [hσ3, hσ2, hσ1, sne 31 35 (by decide), sne 31 36 (by decide), b.pt, popTable_eq])
      (by simp [hσ3, hσ2, hσ1, hPTh]) wd3
      (numOn_setv _ _ _ _ _ _ (numOn_sets_other _ _ _ _ _ _ (sne 35 36 (by decide))
        (numOn_sets_self _ _ _ _ hAN.2)))
      (numOn_setv _ _ _ _ _ _ (numOn_sets_self _ _ _ _ (by simp [hσ1, sne 36 35 (by decide), hAD.2])))
      (by simp [hσ3, hσ2, hσ1, qne 53 57 (by decide), q53]) (by simp [hσ3]) hcapP hfit
  rw [popsFold_eq_objKey] at hAN4 hAD4
  have v4 : ∀ r : Fin nr, r ≠ Q 57 → σ4.val r = σ.val r := by
    intro r hr; rw [hval4 r hr]; simp [hσ3, hσ2, hσ1, Function.update_apply, hr]
  -- the table's head back
  have x5 := rewS_spec cap (S 31) (Q 58) (Q 52) (qne 58 52 (by decide)) σ4 (popTable W R).length
    (by rw [v4 _ (qne 58 57 (by decide)), b.ptl]) (by rw [v4 _ (qne 52 57 (by decide)), q52]) hcapT
    (by rw [hPTh4]; simp [popTable])
  set σ5 := σ4.seth (S 31) 0 with hσ5
  have b5 : Base S Q R h W V N σ5 := b4.seth31 hS hQ 0
  have e5 : ∀ k : Fin 50, 28 ≤ k.val → k.val ≠ 44 → k.val ≠ 46 → (k.val < 33 ∨ 40 < k.val) → k ≠ 35 → k ≠ 36 →
      σ5.st (S k) = σ.st (S k) := by
    intro k hk h44 h46 hk2 h35 h36
    rw [show σ5.st = σ4.st from rfl, hst4 k hk h44 h46 hk2]
    simp [hσ3, hσ2, hσ1, sne k 35 h35, sne k 36 h36]
  have eh5 : ∀ k : Fin 50, k ≠ 31 → σ5.sh (S k) = σ.sh (S k) := by
    intro k hk
    simp only [hσ5, WState.seth_sh, Function.update_apply, sne k 31 hk, if_false]
    rw [hsh4 k hk]; simp [hσ3, hσ2, hσ1]
  -- the compare
  have bn5 : NumOn σ5 (S 41) W bn :=
    ⟨by rw [e5 41 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBN.1,
      by rw [eh5 41 (by decide)]; exact hBN.2⟩
  have bd5 : NumOn σ5 (S 42) W bd :=
    ⟨by rw [e5 42 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBD.1,
      by rw [eh5 42 (by decide)]; exact hBD.2⟩
  have an5 : NumOn σ5 (S 35) W (keyAt R h N).1 := ⟨hAN4.1, by simp [hσ5, sne 35 31 (by decide), hAN4.2]⟩
  have ad5 : NumOn σ5 (S 36) W (keyAt R h N).2 := ⟨hAD4.1, by simp [hσ5, sne 36 31 (by decide), hAD4.2]⟩
  have w5 : ∀ k : Fin 50, (k = 37 ∨ k = 38 ∨ k = 40) → ∃ v, NumOn σ5 (S k) W v := by
    intro k hk
    obtain ⟨v, hv⟩ := hWd4 k (by rcases hk with rfl | rfl | rfl <;> simp)
    refine ⟨v, hv.1, ?_⟩
    simp only [hσ5, WState.seth_sh, Function.update_apply, sne k 31 (by rcases hk with rfl | rfl | rfl <;> decide),
      if_false]
    exact hv.2
  obtain ⟨s37, h37⟩ := w5 37 (by decide)
  obtain ⟨s38, h38⟩ := w5 38 (by decide)
  obtain ⟨s40, h40⟩ := w5 40 (by decide)
  have v5 : ∀ r : Fin nr, r ≠ Q 57 → σ5.val r = σ.val r := v4
  have x6 := ratLtB_spec cap W (zLt S hS) (qLt Q hQ) σ5 (keyAt R h N).1 (keyAt R h N).2 bn bd s37 s38 s40
    an5 ad5 bn5 bd5 h37 h38 h40 (by rw [qLt_apply]; simp [v5 _ (qne 52 57 (by decide)), q52])
    (by rw [qLt_apply]; simp [v5 _ (qne 61 57 (by decide)), q61])
    (by rw [qLt_apply]; simp [v5 _ (qne 62 57 (by decide)), q62])
    (by rw [qLt_apply]; simp [v5 _ (qne 63 57 (by decide)), q63]) hl1 hl2 hl3 hl4 hcap2
  simp only [zLt_apply, qLt_apply] at x6
  set f := ratLt (keyAt R h N) (bn, bd) with hf
  set σ6 := (((σ5.sets (S 37) (frame (binary W 0))).sets (S 38) (frame (binary W 0))).sets (S 40)
    (frame (binary W 0))).setv (Q 52) f.toNat with hσ6
  have x6' : WExec cap (ratLtB (zLt S hS) (qLt Q hQ)) σ5 σ6 (ratLtCost W) := x6
  have b6 : Base S Q R h W V N σ6 :=
    ((((b5.sets hS hQ 37 (Or.inr (by decide)) _).sets hS hQ 38 (Or.inr (by decide)) _).sets hS hQ 40
      (Or.inr (by decide)) _).setv hS hQ 52 (by decide) _)
  have e6 : ∀ k : Fin 50, k ≠ 37 → k ≠ 38 → k ≠ 40 → σ6.st (S k) = σ5.st (S k) := by
    intro k h37' h38' h40'
    simp [hσ6, sne k 37 h37', sne k 38 h38', sne k 40 h40']
  have v6 : ∀ r : Fin nr, r ≠ Q 57 → r ≠ Q 52 → σ6.val r = σ.val r := by
    intro r hr hr'; simp [hσ6, Function.update_apply, hr', v5 r hr]
  have q57_6 : σ6.val (Q 57) = 0 := by simp [hσ6, hσ5, qne 57 52 (by decide), h57τ4]
  have q52_6 : σ6.val (Q 52) = f.toNat := by simp [hσ6]
  have q61_6 : σ6.val (Q 61) = 0 := by rw [v6 _ (qne 61 57 (by decide)) (qne 61 52 (by decide)), q61]
  have q62_6 : σ6.val (Q 62) = 0 := by rw [v6 _ (qne 62 57 (by decide)) (qne 62 52 (by decide)), q62]
  have ns6 : NumOn σ6 (S 0) (R.r * R.s) N := b6.nsw
  have be6 : NumOn σ6 (S 43) (R.r * R.s) be :=
    ⟨by rw [e6 43 (by decide) (by decide) (by decide), e5 43 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]; exact hBE.1,
      by simp only [hσ6, WState.setv_sh, WState.sets_sh]; rw [eh5 43 (by decide)]; exact hBE.2⟩
  have an6 : NumOn σ6 (S 35) W (keyAt R h N).1 :=
    ⟨by rw [e6 35 (by decide) (by decide) (by decide)]; exact an5.1, an5.2⟩
  have ad6 : NumOn σ6 (S 36) W (keyAt R h N).2 :=
    ⟨by rw [e6 36 (by decide) (by decide) (by decide)]; exact ad5.1, ad5.2⟩
  have bn6 : NumOn σ6 (S 41) W bn := ⟨by rw [e6 41 (by decide) (by decide) (by decide)]; exact bn5.1, bn5.2⟩
  have bd6 : NumOn σ6 (S 42) W bd := ⟨by rw [e6 42 (by decide) (by decide) (by decide)]; exact bd5.1, bd5.2⟩
  -- the update, the flag cleared
  have main : ∃ σ7 : WState ns nr, WExec cap (.ifr (Q 52) (upd S Q) .skip) σ6 σ7
      (41 * W + 3 + 1 + (41 * W + 3 + 1 + (41 * (R.r * R.s) + 3)) + 1) ∧
      σ7 = (if f then ((σ6.sets (S 41) (frame (binary W (keyAt R h N).1))).sets (S 42)
        (frame (binary W (keyAt R h N).2))).sets (S 43) (frame (binary (R.r * R.s) N)) else σ6) := by
    by_cases hfv : f = true
    · have u1 := copyB_spec cap W (A := S 41) (B := S 35) (F := Q 61) (R := Q 62) (sne 41 35 (by decide))
        (qne 61 62 (by decide)) σ6 bn (keyAt R h N).1 bn6 an6 q61_6 q62_6 hcap2
      have u2 := copyB_spec cap W (A := S 42) (B := S 36) (F := Q 61) (R := Q 62) (sne 42 36 (by decide))
        (qne 61 62 (by decide)) (σ6.sets (S 41) (frame (binary W (keyAt R h N).1))) bd (keyAt R h N).2
        (numOn_sets_other _ _ _ _ _ _ (sne 42 41 (by decide)) bd6)
        (numOn_sets_other _ _ _ _ _ _ (sne 36 41 (by decide)) ad6) (by simp [q61_6]) (by simp [q62_6]) hcap2
      have u3 := copyB_spec cap (R.r * R.s) (A := S 43) (B := S 0) (F := Q 61) (R := Q 62) (sne 43 0 (by decide))
        (qne 61 62 (by decide)) ((σ6.sets (S 41) (frame (binary W (keyAt R h N).1))).sets (S 42)
          (frame (binary W (keyAt R h N).2))) be N
        (numOn_sets_other _ _ _ _ _ _ (sne 43 42 (by decide)) (numOn_sets_other _ _ _ _ _ _ (sne 43 41 (by decide))
          be6))
        (numOn_sets_other _ _ _ _ _ _ (sne 0 42 (by decide)) (numOn_sets_other _ _ _ _ _ _ (sne 0 41 (by decide))
          ns6)) (by simp [q61_6]) (by simp [q62_6]) hcapk
      refine ⟨_, WExec.ifrT (by rw [q52_6, hfv]; decide) (WExec.seq u1 (WExec.seq u2 u3)), by rw [if_pos hfv]⟩
    · have hfv' : f = false := by simpa using hfv
      refine ⟨σ6, WExec.mono (WExec.ifrF (by rw [q52_6, hfv']; rfl) (WExec.skip σ6)) (by omega), by rw [if_neg hfv]⟩
  obtain ⟨σ7, x7, hσ7⟩ := main
  have q52_7 : σ7.val (Q 52) = f.toNat := by rw [hσ7]; split_ifs <;> simp [q52_6]
  have x8 := wclear_spec (cap := cap) (Q 52) f.toNat σ7 q52_7 (by rw [q52_7]; cases f <;> simp <;> omega)
  set τ := σ7.setv (Q 52) 0 with hτ
  have x8' : WExec cap (WM.clear (Q 52)) σ7 τ (3 * 1 + 1) := WExec.mono x8 (by cases f <;> simp)
  have st7 : ∀ k : Fin 50, k ≠ 41 → k ≠ 42 → k ≠ 43 → τ.st (S k) = σ6.st (S k) := by
    intro k h41 h42 h43
    rw [hτ, hσ7]; split_ifs <;> simp [sne k 41 h41, sne k 42 h42, sne k 43 h43]
  have sh7 : τ.sh = σ6.sh := by rw [hτ, hσ7]; split_ifs <;> rfl
  have val7 : τ.val = σ.val := by
    have e : σ7.val = σ6.val := by rw [hσ7]; split_ifs <;> rfl
    funext r
    by_cases h52 : r = Q 52
    · subst h52; simp [hτ, q52]
    · by_cases h57 : r = Q 57
      · subst h57; simp [hτ, h52, e, q57_6, q57]
      · simp [hτ, h52, e, v6 r h57 h52]
  have b7 : Base S Q R h W V N τ := by
    refine Base.of_agree b6 (fun k hk => ?_) ?_ (fun k _ => by rw [sh7]) (fun j hj => ?_)
    · have h41 : k ≠ 41 := fun e => by subst e; simp at hk
      have h42 : k ≠ 42 := fun e => by subst e; simp at hk
      have h43 : k ≠ 43 := fun e => by subst e; simp at hk
      exact st7 k h41 h42 h43
    · rw [st7 1 (by decide) (by decide) (by decide)]; exact b6.ga
    · have a : Q j ≠ Q 57 := qne j 57 (fun e => by subst e; simp at hj)
      have c : Q j ≠ Q 52 := qne j 52 (fun e => by subst e; simp at hj)
      rw [val7, v6 _ a c]
  refine ⟨τ, ?_, b7, ?_, ?_, ⟨(keyAt R h N).1, ?_, ?_⟩, ⟨(keyAt R h N).2, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, val7, ?_⟩
  · unfold cosetB cosetBCost
    exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6' (WExec.seq x7 x8'))))))
  · rw [sh7]; simp [hσ6, hσ5]
  · intro k hk
    have hk' : k ≠ 41 ∧ k ≠ 42 ∧ k ≠ 43 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨v, hv⟩ := hWd4 3 (by decide)
      exact ⟨v, by rw [st7 3 hk'.1 hk'.2.1 hk'.2.2, e6 3 (by decide) (by decide) (by decide)]; exact hv.1,
        by rw [sh7]; simp [hσ6, hσ5, sne 3 31 (by decide), hv.2]⟩
    · obtain ⟨v, hv⟩ := hWd4 33 (by decide)
      exact ⟨v, by rw [st7 33 hk'.1 hk'.2.1 hk'.2.2, e6 33 (by decide) (by decide) (by decide)]; exact hv.1,
        by rw [sh7]; simp [hσ6, hσ5, sne 33 31 (by decide), hv.2]⟩
    · obtain ⟨v, hv⟩ := hWd4 34 (by decide)
      exact ⟨v, by rw [st7 34 hk'.1 hk'.2.1 hk'.2.2, e6 34 (by decide) (by decide) (by decide)]; exact hv.1,
        by rw [sh7]; simp [hσ6, hσ5, sne 34 31 (by decide), hv.2]⟩
    · exact ⟨0, by rw [st7 37 hk'.1 hk'.2.1 hk'.2.2]; simp [hσ6, sne 37 38 (by decide), sne 37 40 (by decide)],
        by rw [sh7]; simp [hσ6]; exact h37.2⟩
    · exact ⟨0, by rw [st7 38 hk'.1 hk'.2.1 hk'.2.2]; simp [hσ6, sne 38 40 (by decide)],
        by rw [sh7]; simp [hσ6]; exact h38.2⟩
    · obtain ⟨v, hv⟩ := hWd4 39 (by decide)
      exact ⟨v, by rw [st7 39 hk'.1 hk'.2.1 hk'.2.2, e6 39 (by decide) (by decide) (by decide)]; exact hv.1,
        by rw [sh7]; simp [hσ6, hσ5, sne 39 31 (by decide), hv.2]⟩
    · exact ⟨0, by rw [st7 40 hk'.1 hk'.2.1 hk'.2.2]; simp [hσ6], by rw [sh7]; simp [hσ6]; exact h40.2⟩
    · obtain ⟨v, hv⟩ := hWd4 44 (by decide)
      exact ⟨v, by rw [st7 44 hk'.1 hk'.2.1 hk'.2.2, e6 44 (by decide) (by decide) (by decide)]; exact hv.1,
        by rw [sh7]; simp [hσ6, hσ5, sne 44 31 (by decide), hv.2]⟩
    · obtain ⟨v, hv⟩ := hWd4 46 (by decide)
      exact ⟨v, by rw [st7 46 hk'.1 hk'.2.1 hk'.2.2, e6 46 (by decide) (by decide) (by decide)]; exact hv.1,
        by rw [sh7]; simp [hσ6, hσ5, sne 46 31 (by decide), hv.2]⟩
  · rw [st7 35 (by decide) (by decide) (by decide)]; exact an6.1
  · rw [sh7]; exact an6.2
  · rw [st7 36 (by decide) (by decide) (by decide)]; exact ad6.1
  · rw [sh7]; exact ad6.2
  · refine ⟨?_, by rw [sh7]; exact bn6.2⟩
    rw [hτ, hσ7]
    by_cases hfv : f = true
    · simp [hfv, sne 41 42 (by decide), sne 41 43 (by decide)]
    · simp [hfv, bn6.1]
  · refine ⟨?_, by rw [sh7]; exact bd6.2⟩
    rw [hτ, hσ7]
    by_cases hfv : f = true
    · simp [hfv, sne 42 43 (by decide)]
    · simp [hfv, bd6.1]
  · refine ⟨?_, by rw [sh7]; exact be6.2⟩
    rw [hτ, hσ7]
    by_cases hfv : f = true
    · simp [hfv]
    · simp [hfv, be6.1]
  · intro k hk h46 hk2
    have h44 : k.val ≠ 44 := by omega
    have n : k ≠ 41 ∧ k ≠ 42 ∧ k ≠ 43 ∧ k ≠ 37 ∧ k ≠ 38 ∧ k ≠ 40 ∧ k ≠ 35 ∧ k ≠ 36 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; subst e; simp at hk2)
    rw [st7 k n.1 n.2.1 n.2.2.1, e6 k n.2.2.2.1 n.2.2.2.2.1 n.2.2.2.2.2.1,
      e5 k hk h44 h46 (by omega) n.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2]
  · intro k
    rw [sh7]
    by_cases hk : k = 31
    · subst hk; simp [hσ6, hσ5, hPTh]
    · have : σ6.sh (S k) = σ4.sh (S k) := by simp [hσ6, hσ5, sne k 31 hk]
      rw [this, hsh4 k hk]; simp [hσ3, hσ2, hσ1]
  · rw [hτ, hσ7]; split_ifs <;> simp [hσ6, hσ5, hcell4, hσ3, hσ2, hσ1]

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
