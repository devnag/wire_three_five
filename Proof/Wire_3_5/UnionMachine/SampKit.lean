import Proof.Wire_3_5.UnionMachine.TailAsm
import Proof.Wire_3_5.FinalPass.WordLib

/-! # C6 tail, item 2 (part 2): ruler loops over word programs

Kit for the sample expansion's word programs: a loop along a unary ruler `1^n`, the body once per cell and a counter
that rewinds the ruler (**`ruler_spec`**; the loop's invariant is read at the state with the ruler's head and the counter
reset, `nrm`), and its instances on framed words: `n` pairs skipped or backed over (`skipP_spec`, `backP_spec`, exact
states), `n` pairs copied to the end of an output (`copyP_spec`) and `n` zero pairs written (`zeroP_spec`), both in the
read/append relation `TailAsm.Cp`.

Paper quantity: none (the loops' bookkeeping). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SampKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emitW rd_marker rd_bit)
open NearCubicWires.WireExponent3_5.UnionMachine.TailAsm (Cp Cp.refl Cp.tr cp_emit cp_rb rbW fp_cons fp_app fpl)

section Kit
variable {ns nr : ℕ} (cap : ℕ)

theorem rd_rep (n k : ℕ) (hk : k < n) : readTapeBit (List.replicate n true) k = true := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk]

theorem rd_rep_end (n : ℕ) : readTapeBit (List.replicate n true) n = false := by
  simp [readTapeBit, List.getD_eq_getElem?_getD]

/-! ## The state with the ruler's head and the counter reset -/

def nrm (R : Fin (ns + 1)) (c : Fin nr) (σ : WState ns nr) : WState ns nr := (σ.seth R 0).setv c 0

theorem nrm_seth_setv (R : Fin (ns + 1)) (c : Fin nr) (σ : WState ns nr) (x y : ℕ) :
    nrm R c ((σ.seth R x).setv c y) = nrm R c σ :=
  WState.eq (by simp [nrm]) rfl (by simp [nrm]) rfl

theorem nrm_self (R : Fin (ns + 1)) (c : Fin nr) (σ : WState ns nr) (hh : σ.sh R = 0) (hc : σ.val c = 0) :
    nrm R c σ = σ := by
  have e1 : σ.seth R 0 = σ := by rw [show (0 : ℕ) = σ.sh R from hh.symm]; exact wseth_same σ R
  have e2 : σ.setv c 0 = σ := by rw [show (0 : ℕ) = σ.val c from hc.symm]; exact wsetv_same σ c
  unfold nrm; rw [e1, e2]

theorem nrm_seth (R X : Fin (ns + 1)) (c : Fin nr) (h : X ≠ R) (σ : WState ns nr) (x : ℕ) :
    nrm R c (σ.seth X x) = (nrm R c σ).seth X x :=
  WState.eq (by simp only [nrm, WState.setv_sh, WState.seth_sh]; exact Function.update_comm h _ _ _) rfl rfl rfl

theorem cp_nrm (R X D : Fin (ns + 1)) (c : Fin nr) (hXR : X ≠ R) (hDR : D ≠ R) {σ τ : WState ns nr}
    {u v : List Bool} (h : Cp X D σ τ u v) : Cp X D (nrm R c σ) (nrm R c τ) u v := by
  refine ⟨h.st, ?_, h.out, ?_, fun j hjX hjD => ⟨(h.same j hjX hjD).1, ?_⟩, ?_, h.cell⟩
  · simp only [nrm, WState.setv_sh, WState.seth_sh, Function.update_of_ne hXR]; exact h.sh
  · simp only [nrm, WState.setv_sh, WState.seth_sh, WState.setv_st, WState.seth_st, Function.update_of_ne hDR]
    exact h.endO
  · simp only [nrm, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs
    · rfl
    · exact (h.same j hjX hjD).2
  · simp only [nrm, WState.setv_val, WState.seth_val, h.val]

/-! ## The ruler loop -/

/-- A loop along the ruler `R` (`1^n`), the body once per cell, the counter `c` counting; then `R` rewound by `c`. -/
def rulerW (R : Fin (ns + 1)) (c : Fin nr) (B : WM ns nr) : WM ns nr :=
  .seq (.whs R (.seq B (.seq (.fwd R) (.inc c)))) (WM.rewind R c)

theorem rulerLoop (R : Fin (ns + 1)) (c : Fin nr) (B : WM ns nr) (n m : ℕ) (P : ℕ → WState ns nr → Prop)
    (hn : n ≤ cap)
    (hB : ∀ k, k < n → ∀ σ : WState ns nr, P k (nrm R c σ) → σ.st R = List.replicate n true → σ.sh R = k →
      σ.val c = k → ∃ τ, WExec cap B σ τ m ∧ P (k + 1) (nrm R c τ) ∧ τ.st R = σ.st R ∧ τ.sh R = σ.sh R ∧
        τ.val c = σ.val c) :
    ∀ (j k : ℕ) (σ : WState ns nr), k + j = n → P k (nrm R c σ) → σ.st R = List.replicate n true →
      σ.sh R = k → σ.val c = k → ∃ τ, WExec cap (.whs R (.seq B (.seq (.fwd R) (.inc c)))) σ τ (j * (m + 8) + 1) ∧
        P n (nrm R c τ) ∧ τ.st R = List.replicate n true ∧ τ.sh R = n ∧ τ.val c = n
  | 0, k, σ, hk, hP, hR, hh, hc => by
    have hz : wbit σ R = false := by
      unfold wbit; rw [hR, hh, show k = n by omega]; exact rd_rep_end n
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by omega), ?_, hR, by omega, by omega⟩
    rw [show n = k by omega]; exact hP
  | j + 1, k, σ, hk, hP, hR, hh, hc => by
    have hw : wbit σ R = true := by
      unfold wbit; rw [hR, hh]; exact rd_rep n k (by omega)
    obtain ⟨τ1, s1, hP1, e1, eh1, ec1⟩ := hB k (by omega) σ hP hR hh hc
    have s2 := WExec.fwd (cap := cap) R τ1
    have s3 := WExec.inc (cap := cap) c (τ1.seth R (τ1.sh R + 1)) (by simp only [WState.seth_val]; omega)
    obtain ⟨τ, s4, hP4, e4, eh4, ec4⟩ := rulerLoop R c B n m P hn hB j (k + 1)
      ((τ1.seth R (τ1.sh R + 1)).setv c ((τ1.seth R (τ1.sh R + 1)).val c + 1)) (by omega)
      (by rw [nrm_seth_setv]; exact hP1) (by simp [e1, hR]) (by simp [eh1, hh]) (by simp [ec1, hc])
    exact ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) s4)
      (by rw [Nat.add_mul, Nat.one_mul]; omega), hP4, e4, eh4, ec4⟩

/-- **The ruler loop**: from `P 0` at a state with the ruler at `0` and the counter `0`, `P n`, the ruler and the
counter back. -/
theorem ruler_spec (R : Fin (ns + 1)) (c : Fin nr) (B : WM ns nr) (n m : ℕ) (P : ℕ → WState ns nr → Prop)
    (hn : n ≤ cap)
    (hB : ∀ k, k < n → ∀ σ : WState ns nr, P k (nrm R c σ) → σ.st R = List.replicate n true → σ.sh R = k →
      σ.val c = k → ∃ τ, WExec cap B σ τ m ∧ P (k + 1) (nrm R c τ) ∧ τ.st R = σ.st R ∧ τ.sh R = σ.sh R ∧
        τ.val c = σ.val c)
    (σ : WState ns nr) (hP : P 0 σ) (hR : σ.st R = List.replicate n true) (hh : σ.sh R = 0) (hc : σ.val c = 0) :
    ∃ τ, WExec cap (rulerW R c B) σ τ (n * (m + 13) + 3) ∧ P n τ ∧ τ.st R = List.replicate n true ∧
      τ.sh R = 0 ∧ τ.val c = 0 := by
  obtain ⟨τ, s1, hP1, e1, eh1, ec1⟩ := rulerLoop cap R c B n m P hn hB n 0 σ (by omega)
    (by rw [nrm_self R c σ hh hc]; exact hP) hR hh hc
  have s2 := wrewind_spec cap R c n τ ec1 (by omega)
  have ecost : n * (m + 13) = n * (m + 8) + 5 * n := by ring
  refine ⟨_, WExec.mono (WExec.seq s1 s2) (by rw [ecost]; omega), ?_, by simp [e1], by simp [eh1], by simp⟩
  have e : (τ.setv c 0).seth R (τ.sh R - n) = nrm R c τ := by
    rw [eh1, Nat.sub_self]; rfl
  rw [e]; exact hP1

/-! ## Skipping and backing over pairs -/

/-- **`n` pairs skipped** on `X` along the ruler. -/
theorem skipP_spec (R X : Fin (ns + 1)) (c : Fin nr) (hXR : X ≠ R) (n : ℕ) (hn : n ≤ cap) (σ : WState ns nr)
    (hR : σ.st R = List.replicate n true) (hh : σ.sh R = 0) (hc : σ.val c = 0) :
    WExec cap (rulerW R c (.seq (.fwd X) (.fwd X))) σ (σ.seth X (σ.sh X + 2 * n)) (n * 16 + 3) := by
  have hB : ∀ k, k < n → ∀ σ' : WState ns nr, nrm R c σ' = nrm R c (σ.seth X (σ.sh X + 2 * k)) →
      σ'.st R = List.replicate n true → σ'.sh R = k → σ'.val c = k →
      ∃ τ, WExec cap (.seq (.fwd X) (.fwd X)) σ' τ 3 ∧ nrm R c τ = nrm R c (σ.seth X (σ.sh X + 2 * (k + 1))) ∧
        τ.st R = σ'.st R ∧ τ.sh R = σ'.sh R ∧ τ.val c = σ'.val c := by
    intro k _ σ' hP' _ _ _
    have hsx : σ'.sh X = σ.sh X + 2 * k := by
      have := congrArg (fun τ : WState ns nr => τ.sh X) hP'
      simpa [nrm, Function.update_of_ne hXR] using this
    refine ⟨_, WExec.seq (WExec.fwd X σ') (WExec.fwd X _), ?_, rfl, ?_, rfl⟩
    · rw [wseth_seth, nrm_seth R X c hXR σ', hP', ← nrm_seth R X c hXR (σ.seth X (σ.sh X + 2 * k)), wseth_seth]
      congr 2
      simp only [WState.seth_sh, Function.update_self, hsx]
      omega
    · simp [Function.update_of_ne (Ne.symm hXR)]
  have hP0 : σ = nrm R c (σ.seth X (σ.sh X + 2 * 0)) := by
    rw [Nat.mul_zero, Nat.add_zero, wseth_same, nrm_self R c σ hh hc]
  obtain ⟨τ, s, hP, -, -, -⟩ := ruler_spec cap R c (.seq (.fwd X) (.fwd X)) n 3
    (fun k τ => τ = nrm R c (σ.seth X (σ.sh X + 2 * k))) hn hB σ hP0 hR hh hc
  have e : τ = σ.seth X (σ.sh X + 2 * n) := by
    rw [hP, nrm_seth R X c hXR σ, nrm_self R c σ hh hc]
  rw [e] at s; exact s

/-- **`n` pairs backed over** on `X` along the ruler. -/
theorem backP_spec (R X : Fin (ns + 1)) (c : Fin nr) (hXR : X ≠ R) (n : ℕ) (hn : n ≤ cap) (σ : WState ns nr)
    (hR : σ.st R = List.replicate n true) (hh : σ.sh R = 0) (hc : σ.val c = 0) :
    WExec cap (rulerW R c (.seq (.bwd X) (.bwd X))) σ (σ.seth X (σ.sh X - 2 * n)) (n * 16 + 3) := by
  have hB : ∀ k, k < n → ∀ σ' : WState ns nr, nrm R c σ' = nrm R c (σ.seth X (σ.sh X - 2 * k)) →
      σ'.st R = List.replicate n true → σ'.sh R = k → σ'.val c = k →
      ∃ τ, WExec cap (.seq (.bwd X) (.bwd X)) σ' τ 3 ∧ nrm R c τ = nrm R c (σ.seth X (σ.sh X - 2 * (k + 1))) ∧
        τ.st R = σ'.st R ∧ τ.sh R = σ'.sh R ∧ τ.val c = σ'.val c := by
    intro k _ σ' hP' _ _ _
    have hsx : σ'.sh X = σ.sh X - 2 * k := by
      have := congrArg (fun τ : WState ns nr => τ.sh X) hP'
      simpa [nrm, Function.update_of_ne hXR] using this
    refine ⟨_, WExec.seq (WExec.bwd X σ') (WExec.bwd X _), ?_, rfl, ?_, rfl⟩
    · rw [wseth_seth, nrm_seth R X c hXR σ', hP', ← nrm_seth R X c hXR (σ.seth X (σ.sh X - 2 * k)), wseth_seth]
      congr 2
      simp only [WState.seth_sh, Function.update_self, hsx]
      omega
    · simp [Function.update_of_ne (Ne.symm hXR)]
  have hP0 : σ = nrm R c (σ.seth X (σ.sh X - 2 * 0)) := by
    rw [Nat.mul_zero, Nat.sub_zero, wseth_same, nrm_self R c σ hh hc]
  obtain ⟨τ, s, hP, -, -, -⟩ := ruler_spec cap R c (.seq (.bwd X) (.bwd X)) n 3
    (fun k τ => τ = nrm R c (σ.seth X (σ.sh X - 2 * k))) hn hB σ hP0 hR hh hc
  have e : τ = σ.seth X (σ.sh X - 2 * n) := by
    rw [hP, nrm_seth R X c hXR σ, nrm_self R c σ hh hc]
  rw [e] at s; exact s

/-! ## Copying pairs and writing zero pairs -/

/-- **`n` pairs copied**: the next pairs of `X` (the framed bits `w`) to the end of `D`, along the ruler. -/
theorem copyP_spec (R X D : Fin (ns + 1)) (c : Fin nr) (hXR : X ≠ R) (hDR : D ≠ R) (hXD : X ≠ D)
    (w pre rest : List Bool) (hn : w.length ≤ cap) (σ : WState ns nr)
    (hX : σ.st X = pre ++ (frameP w ++ rest)) (hhX : σ.sh X = pre.length) (hD : σ.sh D = (σ.st D).length)
    (hR : σ.st R = List.replicate w.length true) (hh : σ.sh R = 0) (hc : σ.val c = 0) :
    ∃ τ, WExec cap (rulerW R c (.seq (rbW X D) (rbW X D))) σ τ (w.length * 26 + 3) ∧
      Cp X D σ τ (frameP w) (frameP w) := by
  have hB : ∀ k, k < w.length → ∀ σ' : WState ns nr,
      Cp X D σ (nrm R c σ') (frameP (w.take k)) (frameP (w.take k)) →
      σ'.st R = List.replicate w.length true → σ'.sh R = k → σ'.val c = k →
      ∃ τ, WExec cap (.seq (rbW X D) (rbW X D)) σ' τ 13 ∧
        Cp X D σ (nrm R c τ) (frameP (w.take (k + 1))) (frameP (w.take (k + 1))) ∧
        τ.st R = σ'.st R ∧ τ.sh R = σ'.sh R ∧ τ.val c = σ'.val c := by
    intro k hk σ' hP' _ _ _
    have hsplit : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
    have hfk : frameP (w.take (k + 1)) = frameP (w.take k) ++ [true, w[k]] := by
      rw [hsplit, fp_app, fp_cons, frameP_nil]
    have hdrop : w.drop k = w[k] :: w.drop (k + 1) := List.drop_eq_getElem_cons hk
    have hwsplit : frameP w = frameP (w.take k) ++ (true :: w[k] :: frameP (w.drop (k + 1))) := by
      conv_lhs => rw [← List.take_append_drop k w]
      rw [fp_app, hdrop, fp_cons]
    have hX' : σ'.st X = (pre ++ frameP (w.take k)) ++ (true :: (w[k] :: (frameP (w.drop (k + 1)) ++ rest))) := by
      rw [show σ'.st X = σ.st X from hP'.st, hX, hwsplit]; simp
    have hhX' : σ'.sh X = (pre ++ frameP (w.take k)).length := by
      have := hP'.sh
      simp only [nrm, WState.setv_sh, WState.seth_sh, Function.update_of_ne hXR] at this
      rw [this, hhX, List.length_append]
    have hD' : σ'.sh D = (σ'.st D).length := by
      have := hP'.endO
      simp only [nrm, WState.setv_sh, WState.seth_sh, WState.setv_st, WState.seth_st,
        Function.update_of_ne hDR] at this
      exact this
    obtain ⟨τ1, s1, c1⟩ := cp_rb cap X D hXD true (pre ++ frameP (w.take k)) _ σ' hX' hhX' hD'
    obtain ⟨τ, s2, c2⟩ := cp_rb cap X D hXD w[k] (pre ++ frameP (w.take k) ++ [true])
      (frameP (w.drop (k + 1)) ++ rest) τ1 (by rw [c1.st, hX']; simp) (by rw [c1.sh, hhX']; simp <;> omega) c1.endO
    have c12 := c1.tr c2 rfl rfl
    refine ⟨τ, WExec.seq s1 s2, hP'.tr (cp_nrm R X D c hXR hDR c12) (by rw [hfk, List.singleton_append])
      (by rw [hfk, List.singleton_append]), ?_, ?_, ?_⟩
    · exact (c12.same R (Ne.symm hXR) (Ne.symm hDR)).1
    · exact (c12.same R (Ne.symm hXR) (Ne.symm hDR)).2
    · rw [c12.val]
  obtain ⟨τ, s, hP, -, -, -⟩ := ruler_spec cap R c (.seq (rbW X D) (rbW X D)) w.length 13
    (fun k τ => Cp X D σ τ (frameP (w.take k)) (frameP (w.take k))) hn hB σ (Cp.refl X D σ hD) hR hh hc
  rw [List.take_length] at hP
  exact ⟨τ, s, hP⟩

/-- **`n` zero pairs** `T F` written to the end of `D` along the ruler (`Y` is not read). -/
theorem zeroP_spec (R Y D : Fin (ns + 1)) (c : Fin nr) (hYR : Y ≠ R) (hDR : D ≠ R) (hYD : Y ≠ D) (n : ℕ)
    (hn : n ≤ cap) (σ : WState ns nr) (hD : σ.sh D = (σ.st D).length) (hR : σ.st R = List.replicate n true)
    (hh : σ.sh R = 0) (hc : σ.val c = 0) :
    ∃ τ, WExec cap (rulerW R c (.seq (emitW D true) (emitW D false))) σ τ (n * 20 + 3) ∧
      Cp Y D σ τ [] (frameP (List.replicate n false)) := by
  have hB : ∀ k, k < n → ∀ σ' : WState ns nr, Cp Y D σ (nrm R c σ') [] (frameP (List.replicate k false)) →
      σ'.st R = List.replicate n true → σ'.sh R = k → σ'.val c = k →
      ∃ τ, WExec cap (.seq (emitW D true) (emitW D false)) σ' τ 7 ∧
        Cp Y D σ (nrm R c τ) [] (frameP (List.replicate (k + 1) false)) ∧
        τ.st R = σ'.st R ∧ τ.sh R = σ'.sh R ∧ τ.val c = σ'.val c := by
    intro k _ σ' hP' _ _ _
    have hD' : σ'.sh D = (σ'.st D).length := by
      have := hP'.endO
      simp only [nrm, WState.setv_sh, WState.seth_sh, WState.setv_st, WState.seth_st,
        Function.update_of_ne hDR] at this
      exact this
    obtain ⟨τ1, s1, c1⟩ := cp_emit cap Y D hYD true σ' hD'
    obtain ⟨τ, s2, c2⟩ := cp_emit cap Y D hYD false τ1 c1.endO
    have c12 := c1.tr c2 rfl rfl
    refine ⟨τ, WExec.seq s1 s2, hP'.tr (cp_nrm R Y D c hYR hDR c12) rfl
      (by rw [List.replicate_succ', fp_app, fp_cons, frameP_nil, List.singleton_append]), ?_, ?_, ?_⟩
    · exact (c12.same R (Ne.symm hYR) (Ne.symm hDR)).1
    · exact (c12.same R (Ne.symm hYR) (Ne.symm hDR)).2
    · rw [c12.val]
  obtain ⟨τ, s, hP, -, -, -⟩ := ruler_spec cap R c (.seq (emitW D true) (emitW D false)) n 7
    (fun k τ => Cp Y D σ τ [] (frameP (List.replicate k false))) hn hB σ (Cp.refl Y D σ hD) hR hh hc
  exact ⟨τ, s, hP⟩

end Kit

end NearCubicWires.WireExponent3_5.UnionMachine.SampKit
