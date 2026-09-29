import Proof.Wire_3_5.Selection.CosPopM

/-! # C1.5: the population loop at one coset (P3:1356-1362)

Paper: "Sum its exact count with the rational population weights, over gates and rows" (P3:1356-1357). At the coset
`N`, the machine walks the population table once: for each population `X` in the request's order, `popM` adds
`p_X · T_X(N)` to the exact accumulator `(AN, AD)` (C6's `ratStepB`, `ratAccStep`). After the table,
`(AN, AD)` is the fold of `popStep` over the populations from the start value: at `(0, 1)` this is the objective key
`objKey` at the coset (`popsFold_eq_objKey`). Main declarations: `popStep`, `PopsFit`, `popsL`, `popsCost`,
**`popsL_spec`**, **`popsFold_eq_objKey`**. Paper quantity: the coset's exact objective `Σ_X p_X T_X`. -/

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

/-- One population's exact weighted step at the coset `N`. -/
def popStep (R : SelectionReq) (h : ParamsOk R) (N : ℕ) (acc : RegRat) (X : List ℕ × ℚ) : RegRat :=
  ratAccStep acc (X.2.num.toNat, X.2.den, popT R h N X)

/-- **The fold is the objective's key**: from `(0, 1)`, over the request's populations. -/
theorem popsFold_eq_objKey (R : SelectionReq) (h : ParamsOk R) (N : ℕ) :
    R.pops.foldl (popStep R h N) (0, 1) = objKey R h (codesOfIdx R.s R.r N) := by
  unfold objKey ratAcc
  rw [List.foldl_map]
  rfl

/-- The width conditions of the weighted steps along a population list. -/
def PopsFit (R : SelectionReq) (h : ParamsOk R) (N W cap : ℕ) : RegRat → List (List ℕ × ℚ) → Prop
  | _, [] => True
  | acc, X :: ps => (X.1.length ≤ cap ∧ (∀ i ∈ X.1, i < 2 ^ W) ∧ popT R h N X < 2 ^ W ∧ 1 ≤ acc.2 ∧
      acc.1 * X.2.den + X.2.num.toNat * popT R h N X * acc.2 < 2 ^ W ∧ acc.2 * X.2.den < 2 ^ W ∧
      X.2.den < 2 ^ W ∧ acc.2 < 2 ^ W) ∧ PopsFit R h N W cap (popStep R h N acc X) ps

/-- **The population loop**: `MP = Q 57` rounds of `popM`. -/
def popsL (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) : WM ns nr :=
  .whr (Q 57) (.seq (.dec (Q 57)) (popM S hS Q hQ))

/-- The loop's cost over a population list. -/
def popsCost (P : StarParams) (n W V g : ℕ) : List (List ℕ × ℚ) → ℕ
  | [] => 1
  | X :: ps => 1 + 1 + popCost P n W V g X.1.length + 2 + popsCost P n W V g ps

theorem words_setv (S : Fin 50 → Fin (ns + 1)) (σ : WState ns nr) (W : ℕ) (r : Fin nr) (x : ℕ)
    (h : Words S σ W) : Words S (σ.setv r x) W := fun k hk => by
  obtain ⟨v, hv⟩ := h k hk
  exact ⟨v, numOn_setv _ _ _ _ _ _ hv⟩

/-- **The population loop**: `(AN, AD)` becomes the fold of `popStep` over the list; the table's head moves past
the records; `Base` holds; only `MP` changes among the registers (to `0`). -/
theorem popsL_spec (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (W V N : ℕ)
    (hng : R.gates.length < 2 ^ W) (hN : N < 2 ^ (R.r * R.s))
    (hKB : ∀ g ∈ R.gates, KeyBound (gateOf g) V) (hW : 2 * V + 3 ≤ W) (hnk : R.n + (starParamsOf R h).k + 4 ≤ W)
    (hcap : gateNeed (starParamsOf R h) W V ≤ cap) (hcap2 : 2 * W + 1 ≤ cap)
    (hcapG : R.gates.length * (R.n + 1) * (2 * W + 2) + 2 < cap) :
    ∀ (ps : List (List ℕ × ℚ)) (σ : WState ns nr) (pre rest : List Bool) (acc : RegRat),
      Base S Q R h W V N σ → σ.st (S 31) = pre ++ (ps.map (popRec W)).flatten ++ rest →
      σ.sh (S 31) = pre.length → Words S σ W → NumOn σ (S 35) W acc.1 → NumOn σ (S 36) W acc.2 →
      σ.val (Q 53) = 0 → σ.val (Q 57) = ps.length → ps.length ≤ cap → PopsFit R h N W cap acc ps →
      ∃ τ : WState ns nr, WExec cap (popsL S hS Q hQ) σ τ
          (popsCost (starParamsOf R h) R.n W V R.gates.length ps) ∧
        Base S Q R h W V N τ ∧ τ.st (S 31) = σ.st (S 31) ∧
        τ.sh (S 31) = pre.length + ((ps.map (popRec W)).flatten).length ∧
        NumOn τ (S 35) W (ps.foldl (popStep R h N) acc).1 ∧ NumOn τ (S 36) W (ps.foldl (popStep R h N) acc).2 ∧
        Words S τ W ∧
        (∀ k : Fin 50, 28 ≤ k.val → k.val ≠ 44 → k.val ≠ 46 → (k.val < 33 ∨ 40 < k.val) →
          τ.st (S k) = σ.st (S k)) ∧
        (∀ k : Fin 50, k ≠ 31 → τ.sh (S k) = σ.sh (S k)) ∧ (∀ r : Fin nr, r ≠ Q 57 → τ.val r = σ.val r) ∧
        τ.val (Q 57) = 0 ∧ τ.cell = σ.cell
  | [], σ, pre, rest, acc, b, hPT, hPTh, hWd, hAN, hAD, _, h57, _, _ => by
    refine ⟨σ, WExec.whrF (by rw [h57]; rfl), b, rfl, by simp [hPTh], hAN, hAD, hWd, fun _ _ _ _ _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl, by rw [h57]; rfl, rfl⟩
  | X :: ps, σ, pre, rest, acc, b, hPT, hPTh, hWd, hAN, hAD, h53, h57, hlc, hfit => by
    obtain ⟨⟨hm, hil, hT, hd1, hsum, hdb, hb, hd⟩, hfit'⟩ := hfit
    have q5753 : Q 53 ≠ Q 57 := hQ.ne (by decide)
    have hne : σ.val (Q 57) ≠ 0 := by rw [h57]; simp
    have d := WExec.dec (cap := cap) (Q 57) σ (by rw [h57]; exact hlc)
    set σ1 := σ.setv (Q 57) (σ.val (Q 57) - 1) with hσ1
    have b1 : Base S Q R h W V N σ1 := b.setv hS hQ 57 (by decide) _
    obtain ⟨τ1, x1, bτ1, hPT1, hPTh1, hAN1, hAD1, hWd1, hst1, hsh1, hval1, hcell1⟩ :=
      popM_spec S hS Q hQ cap R h W V N hng hN hKB hW hnk hcap hcap2 hcapG σ1 X pre
        ((ps.map (popRec W)).flatten ++ rest) acc.1 acc.2 b1 (by simp [hσ1, hPT, List.append_assoc])
        (by simp [hσ1, hPTh]) (words_setv S σ W _ _ hWd) (numOn_setv _ _ _ _ _ _ hAN) (numOn_setv _ _ _ _ _ _ hAD)
        (by simp [hσ1, q5753, h53]) hm hil hT hd1 hsum hdb hb hd
    obtain ⟨τ, x2, bτ, hPT2, hPTh2, hAN2, hAD2, hWd2, hst2, hsh2, hval2, h57τ, hcell2⟩ :=
      popsL_spec S hS Q hQ cap R h W V N hng hN hKB hW hnk hcap hcap2 hcapG ps τ1 (pre ++ popRec W X) rest
        (popStep R h N acc X) bτ1 (by rw [hPT1]; simp [hσ1, hPT, List.append_assoc])
        (by rw [hPTh1]; simp) hWd1 hAN1 hAD1 (by rw [hval1]; simp [hσ1, q5753, h53])
        (by rw [hval1]; simp [hσ1, h57]) (by simp at hlc; omega) hfit'
    refine ⟨τ, ?_, bτ, ?_, ?_, hAN2, hAD2, hWd2, ?_, ?_, ?_, h57τ, ?_⟩
    · refine WExec.cast cap (WExec.whrT hne (WExec.seq d x1) x2) rfl ?_
      simp only [popsCost]; omega
    · rw [hPT2, hPT1]; simp [hσ1]
    · rw [hPTh2]; simp [List.length_append, Nat.add_assoc]
    · intro k hk h44 h46 hk2
      rw [hst2 k hk h44 h46 hk2, hst1 k hk h44 h46 hk2]; rfl
    · intro k hk
      rw [hsh2 k hk, hsh1 k hk]; rfl
    · intro r hr
      rw [hval2 r hr, hval1]
      simp [hσ1, Function.update_apply, hr]
    · rw [hcell2, hcell1]; rfl

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
