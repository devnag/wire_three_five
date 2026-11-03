import Proof.Wire_3_5.Primitive.SeedFix.C4SC
import Proof.Wire_3_5.Compiler.MachinePoolConv

/-! # C4 per-call setup (item 3), part 4: emitting the stage's words, generically

P3:3011-3016 and P3:2929-2941 (the enumeration's and the generator's per-call words: the rulers `1^ℓ`, `1^{kh}`, …,
the framed `ℓ`-bit words, the loop counters `0 1^v`): each word is a list of parts (constants, `A` copies of a
constant, the `ℓ`-bit payload of a register) written on its own stream, every part from the current registers.

* `Part`, `partW`, `partVal`, `partsW`, `PartOK`, **`partsW_spec`** (one stream);
* `Emit1`, `emitsW`, **`emitsW_spec`** (distinct streams, each from blank).

Paper quantities of the main types: the words written (`partVal`), from the registers' numbers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.FiltRec

/-- `repRegW`'s scratch registers. -/
def rK : Fin LNR := ⟨240, by decide⟩
def rTT : Fin LNR := ⟨241, by decide⟩

/-- **A part of an emitted word**: a constant, or `A` copies of a constant. -/
inductive Part where
  | c (u : List Bool)
  | r (A : Fin LNR) (u : List Bool)

/-- A part's program. -/
def partW (O : Fin (LNS 0 + 1)) (OP : Fin LNR) : Part → WM (LNS 0) LNR
  | .c u => Emit.emitW O OP u
  | .r A u => Emit.repRegW O OP A rK rTT u

/-- A part's word at a state. -/
def partVal (σ : WState (LNS 0) LNR) : Part → List Bool
  | .c u => u
  | .r A u => reps (σ.val A) u

/-- A part's step bound at a state. -/
def partCost (σ : WState (LNS 0) LNR) : Part → ℕ
  | .c u => 8 * u.length
  | .r A u => 18 * σ.val A + 3 + 1 + (σ.val A * (8 * u.length + 4) + 1)

/-- A word's program: its parts in order. -/
def partsW (O : Fin (LNS 0 + 1)) (OP : Fin LNR) : List Part → WM (LNS 0) LNR
  | [] => .skip
  | p :: ps => .seq (partW O OP p) (partsW O OP ps)

/-- A part's register avoids the output counter and the scratch, within the capacity. -/
def PartOK (cap : ℕ) (OP : Fin LNR) (σ : WState (LNS 0) LNR) : Part → Prop
  | .c _ => True
  | .r A _ => A ≠ OP ∧ A ≠ rK ∧ A ≠ rTT ∧ σ.val A ≤ cap

theorem appendO_val_ne (σ : WState (LNS 0) LNR) (O : Fin (LNS 0 + 1)) (OP q : Fin LNR) (u : List Bool) (h : q ≠ OP) :
    (appendO σ O OP u).val q = σ.val q := by
  simp [Function.update_apply, h]

theorem partVal_app (σ : WState (LNS 0) LNR) (O : Fin (LNS 0 + 1)) (OP : Fin LNR) (u : List Bool) (cap : ℕ) (p : Part)
    (h : PartOK cap OP σ p) : partVal (appendO σ O OP u) p = partVal σ p := by
  cases p with
  | c u' => rfl
  | r A u' => simp only [partVal]; rw [appendO_val_ne _ _ _ _ _ h.1]

theorem partCost_app (σ : WState (LNS 0) LNR) (O : Fin (LNS 0 + 1)) (OP : Fin LNR) (u : List Bool) (cap : ℕ) (p : Part)
    (h : PartOK cap OP σ p) : partCost (appendO σ O OP u) p = partCost σ p := by
  cases p with
  | c u' => rfl
  | r A u' => simp only [partCost]; rw [appendO_val_ne _ _ _ _ _ h.1]

theorem partOK_app (σ : WState (LNS 0) LNR) (O : Fin (LNS 0 + 1)) (OP : Fin LNR) (u : List Bool) (cap : ℕ) (p : Part)
    (h : PartOK cap OP σ p) : PartOK cap OP (appendO σ O OP u) p := by
  cases p with
  | c u' => trivial
  | r A u' => exact ⟨h.1, h.2.1, h.2.2.1, by rw [appendO_val_ne _ _ _ _ _ h.1]; exact h.2.2.2⟩

/-- **A word written**: its parts appended to stream `O`, from the current registers. -/
theorem partsW_spec (cap : ℕ) (O : Fin (LNS 0 + 1)) (OP : Fin LNR) (hOK : OP ≠ rK) (hOT : OP ≠ rTT) :
    ∀ (ps : List Part) (σ : WState (LNS 0) LNR), (∀ p ∈ ps, PartOK cap OP σ p) → σ.val rK = 0 → σ.val rTT = 0 →
      σ.sh O = (σ.st O).length → σ.val OP + (ps.flatMap (partVal σ)).length ≤ cap →
      WExec cap (partsW O OP ps) σ (appendO σ O OP (ps.flatMap (partVal σ))) ((ps.map (partCost σ)).sum + ps.length)
  | [], σ, _, _, _, _, _ => by
    simp only [partsW, List.flatMap_nil, List.map_nil, List.sum_nil, List.length_nil, Nat.add_zero]
    rw [appendO_nil]; exact WExec.skip σ
  | p :: ps, σ, hok, hk, ht, ho, hc => by
    have hp := hok p (List.mem_cons_self)
    have h1 : WExec cap (partW O OP p) σ (appendO σ O OP (partVal σ p)) (partCost σ p) := by
      cases p with
      | c u =>
        simp only [partW, partVal, partCost]
        exact Emit.emitW_spec cap O OP u σ ho (by simp [List.flatMap_cons, partVal] at hc; omega)
      | r A u =>
        simp only [partW, partVal, partCost]
        obtain ⟨hAO, hAK, hAT, hAc⟩ := hp
        have hlen : (reps (σ.val A) u).length = σ.val A * u.length := by unfold reps; simp
        exact Emit.repRegW_spec cap O OP A rK rTT hAK hAT (by decide) (Ne.symm hOK) u σ hk ht ho hAc
          (by simp [List.flatMap_cons, partVal] at hc; rw [hlen] at hc; omega)
    set σ1 := appendO σ O OP (partVal σ p) with hσ1
    have hok1 : ∀ q ∈ ps, PartOK cap OP σ1 q := fun q hq => partOK_app σ O OP _ cap q (hok q (List.mem_cons_of_mem _ hq))
    have ev : ps.flatMap (partVal σ1) = ps.flatMap (partVal σ) := by
      apply List.flatMap_congr
      intro q hq; exact partVal_app σ O OP _ cap q (hok q (List.mem_cons_of_mem _ hq))
    have ec : ps.map (partCost σ1) = ps.map (partCost σ) := by
      apply List.map_congr_left
      intro q hq; exact partCost_app σ O OP _ cap q (hok q (List.mem_cons_of_mem _ hq))
    have h2 := partsW_spec cap O OP hOK hOT ps σ1 hok1
      (by rw [hσ1, appendO_val_ne _ _ _ _ _ (Ne.symm hOK)]; exact hk)
      (by rw [hσ1, appendO_val_ne _ _ _ _ _ (Ne.symm hOT)]; exact ht)
      (by simp [σ1, ho])
      (by rw [ev]; simp [σ1, List.flatMap_cons] at hc ⊢; omega)
    rw [ev, ec] at h2
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp [List.map_cons, List.sum_cons]; omega)
    rw [hσ1, appendO_append]
    simp [List.flatMap_cons]

/-- An output counter: registers `200 … 239`. -/
def IsOP (q : Fin LNR) : Prop := 200 ≤ q.val ∧ q.val < 240

/-- A read register: outside the counters and the scratch `rK`, `rTT`. -/
def IsRd (q : Fin LNR) : Prop := q.val < 200 ∨ 242 ≤ q.val

/-- **One emitted word**: its stream, its output counter, an optional `R 4`-bit payload head (the block `R`, `R 7` the
counter), its parts. -/
structure Emit1 where
  O : Fin (LNS 0 + 1)
  OP : Fin LNR
  hb : Option (Fin 8 ↪ Fin LNR)
  ps : List Part

/-- The word's program. -/
def wordW (e : Emit1) : WM (LNS 0) LNR :=
  match e.hb with
  | none => partsW e.O e.OP e.ps
  | some R => .seq (WriteNat.payM e.O R) (partsW e.O e.OP e.ps)

/-- The word's head at a state. -/
def headVal (σ : WState (LNS 0) LNR) : Option (Fin 8 ↪ Fin LNR) → List Bool
  | none => []
  | some R => Streaming.marks (WilliamsPublishedForm.fixedWidthNatBits (σ.val (R 4)) (σ.val (R 0)))

/-- The word at a state. -/
def wordVal (σ : WState (LNS 0) LNR) (e : Emit1) : List Bool := headVal σ e.hb ++ e.ps.flatMap (partVal σ)

/-- The word's step bound at a state. -/
def wordCost (σ : WState (LNS 0) LNR) (e : Emit1) : ℕ :=
  (match e.hb with
    | none => 0
    | some R => σ.val (R 4) * (10 * σ.val (R 0) + 40) + 40 * σ.val (R 0) + 40 * σ.val (R 4) + 20 + 1) +
  ((e.ps.map (partCost σ)).sum + e.ps.length)

/-- A head's admissibility: its block's registers read and blank scratch, its counter the word's. -/
def HeadOK (cap : ℕ) (OP : Fin LNR) (σ : WState (LNS 0) LNR) : Option (Fin 8 ↪ Fin LNR) → Prop
  | none => True
  | some R => R 7 = OP ∧ (∀ i : Fin 8, i ≠ 7 → IsRd (R i)) ∧ σ.val (R 1) = 0 ∧ σ.val (R 2) = 0 ∧
      σ.val (R 3) = 0 ∧ σ.val (R 5) = 0 ∧ σ.val (R 6) = 0 ∧ σ.val (R 0) < 2 ^ σ.val (R 4) ∧
      σ.val (R 0) + σ.val (R 4) + 2 * σ.val (R 4) + 2 ≤ cap

/-- A word's admissibility at a state (its stream blank, its counter `0`, its registers read). -/
structure WordOK (cap : ℕ) (σ : WState (LNS 0) LNR) (e : Emit1) : Prop where
  hO : σ.st e.O = []
  hsh : σ.sh e.O = 0
  hOP : IsOP e.OP
  hv : σ.val e.OP = 0
  hps : ∀ p ∈ e.ps, ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap
  hhd : HeadOK cap e.OP σ e.hb
  hlen : (wordVal σ e).length ≤ cap

theorem isOP_ne_rK {q : Fin LNR} (h : IsOP q) : q ≠ rK := fun e => by subst e; simp [IsOP, rK] at h
theorem isOP_ne_rTT {q : Fin LNR} (h : IsOP q) : q ≠ rTT := fun e => by subst e; simp [IsOP, rTT] at h
theorem isRd_ne_OP {q r : Fin LNR} (hq : IsRd q) (hr : IsOP r) : q ≠ r := fun e => by
  subst e; simp [IsRd, IsOP] at hq hr; omega
theorem isRd_ne_rK {q : Fin LNR} (hq : IsRd q) : q ≠ rK := fun e => by subst e; simp [IsRd, rK] at hq
theorem isRd_ne_rTT {q : Fin LNR} (hq : IsRd q) : q ≠ rTT := fun e => by subst e; simp [IsRd, rTT] at hq

/-- **One word written** on its blank stream. -/
theorem wordW_spec (cap : ℕ) (e : Emit1) (σ : WState (LNS 0) LNR) (h : WordOK cap σ e) (hk : σ.val rK = 0)
    (ht : σ.val rTT = 0) :
    WExec cap (wordW e) σ (appendO σ e.O e.OP (wordVal σ e)) (wordCost σ e) := by
  have hOK := isOP_ne_rK h.hOP
  have hOT := isOP_ne_rTT h.hOP
  have pok : ∀ (τ : WState (LNS 0) LNR), (∀ A, IsRd A → τ.val A = σ.val A) → ∀ p ∈ e.ps, PartOK cap e.OP τ p := by
    intro τ hτ p hp
    cases p with
    | c u => trivial
    | r A u =>
      obtain ⟨hr, hc⟩ := h.hps _ hp A u rfl
      exact ⟨isRd_ne_OP hr h.hOP, isRd_ne_rK hr, isRd_ne_rTT hr, by rw [hτ A hr]; exact hc⟩
  have pv : ∀ (τ : WState (LNS 0) LNR), (∀ A, IsRd A → τ.val A = σ.val A) →
      e.ps.flatMap (partVal τ) = e.ps.flatMap (partVal σ) := by
    intro τ hτ
    apply List.flatMap_congr
    intro p hp
    cases p with
    | c u => rfl
    | r A u => simp only [partVal]; rw [hτ A (h.hps _ hp A u rfl).1]
  have pc : ∀ (τ : WState (LNS 0) LNR), (∀ A, IsRd A → τ.val A = σ.val A) →
      e.ps.map (partCost τ) = e.ps.map (partCost σ) := by
    intro τ hτ
    apply List.map_congr_left
    intro p hp
    cases p with
    | c u => rfl
    | r A u => simp only [partCost]; rw [hτ A (h.hps _ hp A u rfl).1]
  have hhd := h.hhd
  have hlen := h.hlen
  unfold wordW wordVal wordCost
  cases hb : e.hb with
  | none =>
    simp only [headVal, List.nil_append, Nat.zero_add]
    simp only [wordVal, hb, headVal, List.nil_append] at hlen
    exact partsW_spec cap e.O e.OP hOK hOT e.ps σ (pok σ (fun _ _ => rfl)) hk ht (by rw [h.hsh, h.hO]; rfl)
      (by rw [h.hv]; omega)
  | some R =>
    rw [hb] at hhd
    obtain ⟨h7, hrd, h1, h2, h3, h5, h6, hlt, hcp⟩ := hhd
    simp only [wordVal, hb, headVal, List.length_append] at hlen
    have e1 := WriteNat.payM_spec cap e.O R σ h1 h2 h3 h5 h6 (by rw [h.hsh, h.hO]; rfl) hlt
      (by rw [h7, h.hv]; omega)
    rw [h7] at e1
    set mw := Streaming.marks (WilliamsPublishedForm.fixedWidthNatBits (σ.val (R 4)) (σ.val (R 0))) with hmw
    set σ1 := appendO σ e.O e.OP mw with hσ1
    have k1 : ∀ A, IsRd A → σ1.val A = σ.val A := fun A hA => appendO_val_ne _ _ _ _ _ (isRd_ne_OP hA h.hOP)
    have hv1 : σ1.val e.OP = mw.length := by simp [σ1, h.hv]
    have e2 := partsW_spec cap e.O e.OP hOK hOT e.ps σ1 (pok σ1 k1)
      (by rw [hσ1, appendO_val_ne _ _ _ _ _ (Ne.symm hOK)]; exact hk)
      (by rw [hσ1, appendO_val_ne _ _ _ _ _ (Ne.symm hOT)]; exact ht)
      (by simp [σ1, h.hsh, h.hO])
      (by rw [pv σ1 k1, hv1]; omega)
    rw [pv σ1 k1, pc σ1 k1, hσ1, appendO_append] at e2
    refine WExec.cast cap (WExec.seq e1 e2) rfl ?_
    dsimp only
    omega

/-- The words' registers are read registers (so later words see them unchanged). -/
def RdOK (e : Emit1) : Prop :=
  (∀ p ∈ e.ps, ∀ A u, p = .r A u → IsRd A) ∧ (∀ R, e.hb = some R → IsRd (R 0) ∧ IsRd (R 4))

theorem rdOK_of (cap : ℕ) (σ : WState (LNS 0) LNR) (e : Emit1) (h : WordOK cap σ e) : RdOK e := by
  refine ⟨fun p hp A u hpA => (h.hps p hp A u hpA).1, fun R hR => ?_⟩
  have hhd := h.hhd
  rw [hR] at hhd
  exact ⟨hhd.2.1 0 (by decide), hhd.2.1 4 (by decide)⟩

theorem wordVal_eq (σ τ : WState (LNS 0) LNR) (e : Emit1) (hr : RdOK e) (hτ : ∀ A, IsRd A → τ.val A = σ.val A) :
    wordVal τ e = wordVal σ e := by
  unfold wordVal
  congr 1
  · cases hb : e.hb with
    | none => rfl
    | some R =>
      obtain ⟨h0, h4⟩ := hr.2 R hb
      simp only [headVal]; rw [hτ _ h0, hτ _ h4]
  · apply List.flatMap_congr
    intro p hp
    cases p with
    | c u => rfl
    | r A u => simp only [partVal]; rw [hτ A (hr.1 _ hp A u rfl)]

theorem wordCost_eq (σ τ : WState (LNS 0) LNR) (e : Emit1) (hr : RdOK e) (hτ : ∀ A, IsRd A → τ.val A = σ.val A) :
    wordCost τ e = wordCost σ e := by
  unfold wordCost
  congr 1
  · cases hb : e.hb with
    | none => rfl
    | some R =>
      obtain ⟨h0, h4⟩ := hr.2 R hb
      simp only []; rw [hτ _ h0, hτ _ h4]
  · congr 1
    congr 1
    apply List.map_congr_left
    intro p hp
    cases p with
    | c u => rfl
    | r A u => simp only [partCost]; rw [hτ A (hr.1 _ hp A u rfl)]

/-- **The words**, one after another. -/
def emitsW : List Emit1 → WM (LNS 0) LNR
  | [] => .skip
  | e :: es => .seq (wordW e) (emitsW es)

/-- **The words written**, each on its blank stream (distinct streams, distinct counters): every word from the
registers at entry, every other stream and every read register unchanged. -/
theorem emitsW_spec (cap : ℕ) : ∀ (es : List Emit1) (σ : WState (LNS 0) LNR), (∀ e ∈ es, WordOK cap σ e) →
    (es.map (·.O)).Nodup → (es.map (·.OP)).Nodup → σ.val rK = 0 → σ.val rTT = 0 →
    ∃ τ, WExec cap (emitsW es) σ τ ((es.map (wordCost σ)).sum + es.length) ∧
      (∀ e ∈ es, τ.st e.O = wordVal σ e) ∧ (∀ o, (∀ e ∈ es, o ≠ e.O) → τ.st o = σ.st o) ∧
      (∀ q, IsRd q → τ.val q = σ.val q) ∧ τ.val rK = 0 ∧ τ.val rTT = 0 ∧ τ.cell = σ.cell
  | [], σ, _, _, _, hk, ht => ⟨σ, WExec.skip σ, fun e he => by simp at he, fun _ _ => rfl, fun _ _ => rfl, hk, ht, rfl⟩
  | e :: es, σ, hok, hO, hP, hk, ht => by
    have he := hok e List.mem_cons_self
    have h1 := wordW_spec cap e σ he hk ht
    set σ1 := appendO σ e.O e.OP (wordVal σ e) with hσ1
    have hOP := he.hOP
    have k1 : ∀ A, IsRd A → σ1.val A = σ.val A := fun A hA => appendO_val_ne _ _ _ _ _ (isRd_ne_OP hA hOP)
    have hO' : (es.map (·.O)).Nodup := (List.nodup_cons.mp hO).2
    have hP' : (es.map (·.OP)).Nodup := (List.nodup_cons.mp hP).2
    have nO : ∀ e' ∈ es, e'.O ≠ e.O := fun e' he' h => (List.nodup_cons.mp hO).1 (List.mem_map.mpr ⟨e', he', h⟩)
    have nP : ∀ e' ∈ es, e'.OP ≠ e.OP := fun e' he' h => (List.nodup_cons.mp hP).1 (List.mem_map.mpr ⟨e', he', h⟩)
    have hok1 : ∀ e' ∈ es, WordOK cap σ1 e' := by
      intro e' he'
      have h' := hok e' (List.mem_cons_of_mem _ he')
      have hr := rdOK_of cap σ e' h'
      refine ⟨?_, ?_, h'.hOP, ?_, fun p hp A u hpA => ?_, ?_, ?_⟩
      · simp [σ1, Function.update_apply, nO e' he', h'.hO]
      · simp [σ1, Function.update_apply, nO e' he', h'.hsh]
      · rw [hσ1, appendO_val_ne _ _ _ _ _ (nP e' he')]; exact h'.hv
      · obtain ⟨hA, hc⟩ := h'.hps p hp A u hpA
        exact ⟨hA, by rw [k1 A hA]; exact hc⟩
      · have hhd := h'.hhd
        cases hb : e'.hb with
        | none => trivial
        | some R =>
          rw [hb] at hhd
          obtain ⟨h7, hrd, g1, g2, g3, g5, g6, hlt, hcp⟩ := hhd
          refine ⟨h7, hrd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first
            | (rw [k1 _ (hrd _ (by decide))]; assumption)
            | (rw [k1 _ (hrd 0 (by decide)), k1 _ (hrd 4 (by decide))]; assumption)
      · rw [wordVal_eq σ σ1 e' hr k1]; exact h'.hlen
    obtain ⟨τ, h2, s2, o2, v2, kk, tt, c2⟩ := emitsW_spec cap es σ1 hok1 hO' hP'
      (by rw [hσ1, appendO_val_ne _ _ _ _ _ (Ne.symm (isOP_ne_rK hOP))]; exact hk)
      (by rw [hσ1, appendO_val_ne _ _ _ _ _ (Ne.symm (isOP_ne_rTT hOP))]; exact ht)
    have ec : es.map (wordCost σ1) = es.map (wordCost σ) := by
      apply List.map_congr_left
      intro e' he'
      exact wordCost_eq σ σ1 e' (rdOK_of cap σ e' (hok e' (List.mem_cons_of_mem _ he'))) k1
    rw [ec] at h2
    refine ⟨τ, WExec.cast cap (WExec.seq h1 h2) rfl (by simp [List.map_cons, List.sum_cons]; omega), ?_, ?_, ?_, kk, tt, ?_⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he''
      · rw [o2 _ (fun e'' h'' => nO e'' h'' |>.symm)]
        simp [σ1, he.hO]
      · rw [s2 e' he'', wordVal_eq σ σ1 e' (rdOK_of cap σ e' (hok e' he')) k1]
    · intro o ho
      rw [o2 o (fun e' he' => ho e' (List.mem_cons_of_mem _ he'))]
      simp [σ1, Function.update_apply, ho e List.mem_cons_self]
    · intro q hq; rw [v2 q hq, k1 q hq]
    · rw [c2]; simp [σ1]

end NearCubicWires.WireExponent3_5.PrimT.C4Set
