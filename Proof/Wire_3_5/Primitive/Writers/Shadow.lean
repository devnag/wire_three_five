import Proof.MachineModel.Runs

/-! # The output-length shadow of a machine (leaf-P kit for PA.compose's glue)

A `RewoundWordFunction` leaves its output word RAW on its output tape, and a reader of a tape cannot see where the word
ends: `readTapeBit` reads `false` beyond the materialized cells. Composing two word functions, where the second reads
`frame (w ++ s)` (`prim:runtime`, P3:3105-3115: the per-call program is seed fixing followed by the final pass), therefore
needs the LENGTH of the first one's output `s`.

`Shadow.machine o p` runs `p` unchanged on its own tapes, with two extra tapes whose heads follow the head of the output
tape `o`: `V` receives `true` at every cell at which a transition starts, `W` receives `true` at every cell at which `p`
writes the output tape. Since heads move by unit steps from `0`, `V = replicate m true` with `m ≤` the number of
transitions, and `|W| = |s|` with the last cell of `W` marked (`step_shadow`). The ruler kernel (`PrimAsmRuler`) turns
`(V, W)` into `replicate |s| true`.

Paper quantity of the main type: the output length `|s|` of the first machine (`step_shadow`: `W.length = (tout o).length`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Shadow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch

/-! ## Tape lemmas -/

theorem write_nil (h : ℕ) (v : Bool) : writeTapeBit [] h v = List.replicate h false ++ [v] := by
  induction h with
  | zero => rfl
  | succ h ih => simp [writeTapeBit, ih, List.replicate_succ]

theorem length_write (l : List Bool) (h : ℕ) (v : Bool) :
    (writeTapeBit l h v).length = max l.length (h + 1) := by
  induction l generalizing h with
  | nil =>
    rw [write_nil]
    simp only [List.length_append, List.length_replicate, List.length_singleton, List.length_nil]
    omega
  | cons b l ih =>
    cases h with
    | zero => simp only [writeTapeBit, List.length_cons]; omega
    | succ h => simp only [writeTapeBit, List.length_cons, ih]; omega

theorem read_nil (j : ℕ) : readTapeBit [] j = false := by simp [readTapeBit]

theorem read_cons_zero (b : Bool) (l : List Bool) : readTapeBit (b :: l) 0 = b := by simp [readTapeBit]

theorem read_cons_succ (b : Bool) (l : List Bool) (j : ℕ) : readTapeBit (b :: l) (j + 1) = readTapeBit l j := by
  simp [readTapeBit]

theorem read_write_same (l : List Bool) (h : ℕ) (v : Bool) : readTapeBit (writeTapeBit l h v) h = v := by
  induction l generalizing h with
  | nil =>
    induction h with
    | zero => simp [writeTapeBit, read_cons_zero]
    | succ h ih => simp only [writeTapeBit, read_cons_succ]; exact ih
  | cons b l ih =>
    cases h with
    | zero => simp only [writeTapeBit, read_cons_zero]
    | succ h => simp only [writeTapeBit, read_cons_succ]; exact ih h

theorem read_write_other_nil (h j : ℕ) (v : Bool) (hj : j ≠ h) : readTapeBit (writeTapeBit [] h v) j = false := by
  induction h generalizing j with
  | zero =>
    cases j with
    | zero => exact absurd rfl hj
    | succ j => simp [writeTapeBit, read_cons_succ, read_nil]
  | succ h ih =>
    cases j with
    | zero => simp [writeTapeBit, read_cons_zero]
    | succ j => simp only [writeTapeBit, read_cons_succ]; exact ih j (by omega)

theorem read_write_other (l : List Bool) (h j : ℕ) (v : Bool) (hj : j ≠ h) :
    readTapeBit (writeTapeBit l h v) j = readTapeBit l j := by
  induction l generalizing h j with
  | nil => rw [read_write_other_nil h j v hj, read_nil]
  | cons b l ih =>
    cases h with
    | zero =>
      cases j with
      | zero => exact absurd rfl hj
      | succ j => simp only [writeTapeBit, read_cons_succ]
    | succ h =>
      cases j with
      | zero => simp only [writeTapeBit, read_cons_zero]
      | succ j => simp only [writeTapeBit, read_cons_succ]; exact ih h j (by omega)

theorem write_rep_true (n h : ℕ) (hh : h ≤ n) :
    writeTapeBit (List.replicate n true) h true = List.replicate (max n (h + 1)) true := by
  induction h generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [show max (n + 1) (0 + 1) = n + 1 by omega]
      rfl
  | succ h ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [List.replicate_succ]
      simp only [writeTapeBit]
      rw [ih n (by omega), show max (n + 1) (h + 1 + 1) = max n (h + 1) + 1 by omega, List.replicate_succ]

theorem read_beyond (l : List Bool) (j : ℕ) (hj : l.length ≤ j) : readTapeBit l j = false := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

/-- The last cell of a word is marked (or the word is empty). -/
def LastTrue (W : List Bool) : Prop := W.length = 0 ∨ readTapeBit W (W.length - 1) = true

theorem lastTrue_write (W : List Bool) (h : ℕ) (hW : LastTrue W) : LastTrue (writeTapeBit W h true) := by
  right
  rw [length_write]
  by_cases hc : W.length ≤ h + 1
  · rw [show max W.length (h + 1) - 1 = h by omega]
    exact read_write_same W h true
  · rw [show max W.length (h + 1) - 1 = W.length - 1 by omega, read_write_other W h _ true (by omega)]
    rcases hW with h0 | h1
    · omega
    · exact h1

/-! ## The shadowed machine -/

/-- The two shadow writes: `V` always, `W` when the output tape is written. -/
def shadowWrite {t s : ℕ} (o : Fin t) (a : Action t s) : Fin 2 → Option Bool :=
  fun k => if k.val = 0 then some true else (a.write o).map (fun _ => true)

def action {t s : ℕ} (o : Fin t) (a : Action t s) : Action (t + 2) s where
  nextControl := a.nextControl
  write := Fin.addCases a.write (shadowWrite o a)
  move := Fin.addCases a.move (fun _ => a.move o)

/-- **The shadowed machine**: `p` on its own tapes, and the two shadow tapes following the head of tape `o`. -/
def machine {t s : ℕ} (o : Fin t) (p : Machine t s) : Machine (t + 2) s where
  descriptionBits := 0
  start := p.start
  halted := p.halted
  rule := fun state scanned => (p.rule state (fun i => scanned (i.castAdd 2))).map (action o)

def shadowTapes (V W : List Bool) : Fin 2 → List Bool := fun k => if k.val = 0 then V else W

def config {t s : ℕ} (o : Fin t) (c : Configuration t s) (V W : List Bool) : Configuration (t + 2) s where
  control := c.control
  heads := Fin.addCases c.heads (fun _ => c.heads o)
  tapes := Fin.addCases c.tapes (shadowTapes V W)

/-- The `W` tape after one transition with action `a` at output head `h`. -/
def nextW {t s : ℕ} (o : Fin t) (a : Action t s) (h : ℕ) (W : List Bool) : List Bool :=
  match a.write o with
  | none => W
  | some _ => writeTapeBit W h true

theorem config_scanned {t s : ℕ} (o : Fin t) (c : Configuration t s) (V W : List Bool) :
    (fun i : Fin t => (config o c V W).scanned (i.castAdd 2)) = c.scanned := by
  funext i
  simp [Configuration.scanned, config]

theorem apply_action {t s : ℕ} (o : Fin t) (c : Configuration t s) (a : Action t s) (V W : List Bool) :
    applyAction (config o c V W) (action o a) =
      config o (applyAction c a) (writeTapeBit V (c.heads o) true) (nextW o a (c.heads o) W) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [applyAction, action, config]
    · simp [applyAction, action, config]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [applyAction, action, config]
    · fin_cases j
      · simp [applyAction, action, config, shadowWrite, shadowTapes]
      · rcases hw : a.write o with _ | v
        · simp [applyAction, action, config, shadowWrite, shadowTapes, nextW, hw]
        · simp [applyAction, action, config, shadowWrite, shadowTapes, nextW, hw]

theorem step_eq {t s : ℕ} (o : Fin t) (p : Machine t s) (c : Configuration t s) (V W : List Bool)
    (a : Action t s) (ha : p.rule c.control c.scanned = some a) :
    step (machine o p) (config o c V W) =
      some (config o (applyAction c a) (writeTapeBit V (c.heads o) true) (nextW o a (c.heads o) W)) := by
  change ((p.rule c.control (fun i => (config o c V W).scanned (i.castAdd 2))).map (action o)).map
    (applyAction (config o c V W)) = _
  rw [config_scanned, ha]
  show some (applyAction (config o c V W) (action o a)) = _
  rw [apply_action]

/-! ## The invariant -/

/-- The shadow invariant at a configuration of `p`. -/
structure Inv {t s : ℕ} (o : Fin t) (c : Configuration t s) (V W : List Bool) : Prop where
  vtrue : ∃ n, V = List.replicate n true
  head : c.heads o ≤ V.length
  wlen : W.length = (c.tapes o).length
  wle : W.length ≤ V.length
  wlast : LastTrue W

theorem inv_step {t s : ℕ} (o : Fin t) (c : Configuration t s) (a : Action t s) (V W : List Bool)
    (hI : Inv o c V W) :
    Inv o (applyAction c a) (writeTapeBit V (c.heads o) true) (nextW o a (c.heads o) W) ∧
      (writeTapeBit V (c.heads o) true).length ≤ V.length + 1 := by
  obtain ⟨⟨n, rfl⟩, hh, hwl, hwle, hlast⟩ := hI
  simp only [List.length_replicate] at hh hwle
  rw [write_rep_true n (c.heads o) hh]
  refine ⟨⟨⟨_, rfl⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.length_replicate]
    show (a.move o).apply (c.heads o) ≤ _
    cases a.move o <;> simp only [HeadMove.apply] <;> omega
  · show (nextW o a (c.heads o) W).length = ((applyAction c a).tapes o).length
    rcases hw : a.write o with _ | v
    · simp [nextW, applyAction, hw, hwl]
    · simp [nextW, applyAction, hw, length_write, hwl]
  · rcases hw : a.write o with _ | v
    · simp only [nextW, hw, List.length_replicate]; omega
    · simp only [nextW, hw, length_write, List.length_replicate]; omega
  · rcases hw : a.write o with _ | v
    · simpa [nextW, hw] using hlast
    · simpa [nextW, hw] using lastTrue_write W (c.heads o) hlast
  · simp only [List.length_replicate]; omega

/-! ## The run -/

theorem run_shadow {t s : ℕ} (o : Fin t) (p : Machine t s) (fuel : ℕ) :
    ∀ (c : Configuration t s) (r : ExecutionReceipt t s), runFrom p fuel c = some r →
      ∀ V W, Inv o c V W → ∃ (r' : ExecutionReceipt (t + 2) s) (V' W' : List Bool),
        runFrom (machine o p) fuel (config o c V W) = some r' ∧ r'.final = config o r.final V' W' ∧
          r'.steps = r.steps ∧ Inv o r.final V' W' ∧ V'.length ≤ V.length + r.steps := by
  induction fuel with
  | zero =>
    intro c r hrun V W hI
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        refine ⟨⟨config o c V W, 0, (config o c V W).tapeCells⟩, V, W, ?_, rfl, rfl, hI, by simp⟩
        exact runFrom_zero_of_halted (machine o p) (config o c V W) h
    · contradiction
  | succ fuel ih =>
    intro c r hrun V W hI
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        refine ⟨⟨config o c V W, 0, (config o c V W).tapeCells⟩, V, W, ?_, rfl, rfl, hI, by simp⟩
        simp [runFrom, machine, config, h]
    · next h =>
        split at hrun
        · contradiction
        · next next hs =>
            split at hrun
            · contradiction
            · next suffix htail =>
                cases hrun
                cases ha : p.rule c.control c.scanned with
                | none => simp [step, ha] at hs
                | some a =>
                  have hn : applyAction c a = next := by simpa [step, ha] using hs
                  subst hn
                  obtain ⟨hI', hlen⟩ := inv_step o c a V W hI
                  obtain ⟨r', V', W', hr', hf, hst, hI'', hl⟩ := ih _ suffix htail _ _ hI'
                  have hfirst := runFrom_step (machine o p) (config o c V W) _ r'
                    (by simpa [machine, config] using h) (step_eq o p c V W a ha) hr'
                  refine ⟨_, V', W', hfirst, hf, ?_, hI'', ?_⟩
                  · simp [hst]
                  · simp only; omega

/-- **The shadowed run at a rewound step.** A `Step` of `p` from and to heads `0`, with the output tape `o` blank at the
start, is a `Step` of the shadowed machine, whose shadow tapes end as `replicate m true` and `W`, where
`|W| = |tout o|` (the output's length), `|W| ≤ m ≤ n`, and the last cell of `W` is marked. -/
theorem step_shadow {t s : ℕ} (o : Fin t) (p : Machine t s) {n : ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (ho : tin o = []) :
    ∃ (m : ℕ) (W : List Bool), Step (machine o p) n (fun _ => 0) (Fin.addCases tin (fun _ => [])) (fun _ => 0)
        (Fin.addCases tout (shadowTapes (List.replicate m true) W)) ∧
      W.length = (tout o).length ∧ W.length ≤ m ∧ m ≤ n ∧ LastTrue W := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hI : Inv o (⟨p.start, fun _ => 0, tin⟩ : Configuration t s) [] [] :=
    ⟨⟨0, rfl⟩, by simp, by simp [ho], by simp, Or.inl rfl⟩
  obtain ⟨r', V', W', hr', hf, hst, hI', hl⟩ := run_shadow o p n _ r hr [] [] hI
  obtain ⟨⟨m, rfl⟩, -, hwl, hwle, hlast⟩ := hI'
  simp only [List.length_replicate, List.length_nil, Nat.zero_add] at hl hwle
  refine ⟨m, W', ⟨r', ?_, ?_, ?_, ?_⟩, ?_, hwle, by omega, hlast⟩
  · have he : (⟨(machine o p).start, fun _ => 0, Fin.addCases tin (fun _ => [])⟩ : Configuration (t + 2) s) =
        config o ⟨p.start, fun _ => 0, tin⟩ [] [] := by
      apply configuration_ext
      · rfl
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [config]
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [config]
        · simp [config, shadowTapes]
    rw [he]
    exact hr'
  · rw [hf]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [config, hh]
  · rw [hf]
    simp only [config, ht]
  · omega
  · rw [hwl, ht]

end NearCubicWires.WireExponent3_5.PrimAsm.Shadow
