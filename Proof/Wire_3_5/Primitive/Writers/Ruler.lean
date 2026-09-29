import Proof.Wire_3_5.Primitive.Writers.Shadow

/-! # The ruler kernel (leaf-P kit for PA.compose's glue)

From the two shadow tapes of `PrimAsmShadow` (`V = replicate m true`, and `W` with `|W| ≤ m` and its last cell marked)
the ruler kernel writes the unary length `replicate |W| true` of the shadowed output, on a fresh tape `R`, and returns
every head to `0`. Tapes: `0` V, `1` W, `2` E (a left-end marker it writes itself), `3` R. States: `0` mark `E`, `1`
forward to the end of `V`, `2` backward before the last mark of `W`, `3` backward after it, `4` halt.

Paper quantity of the main type: the unary length `replicate |s| true` of the first machine's output (`ruler_step`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Ruler
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.PrimAsm.Shadow

def machine : Machine 4 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q bits =>
    if q.val = 0 then some ⟨1, ![none, none, some true, none], fun _ => .stay⟩
    else if q.val = 1 then
      some (if bits 0 then ⟨1, fun _ => none, fun _ => .right⟩ else ⟨2, fun _ => none, fun _ => .left⟩)
    else if q.val = 2 then
      some (if bits 1 then
          (if bits 2 then ⟨4, ![none, none, none, some true], fun _ => .stay⟩
            else ⟨3, ![none, none, none, some true], fun _ => .left⟩)
        else (if bits 2 then ⟨4, fun _ => none, fun _ => .stay⟩ else ⟨2, fun _ => none, fun _ => .left⟩))
    else if q.val = 3 then
      some (if bits 2 then ⟨4, ![none, none, none, some true], fun _ => .stay⟩
        else ⟨3, ![none, none, none, some true], fun _ => .left⟩)
    else none

def cfg (q : Fin 5) (j : ℕ) (V W E R : List Bool) : Configuration 4 5 := ⟨q, fun _ => j, ![V, W, E, R]⟩

/-! ## One transition each -/

theorem mark_step (V W R : List Bool) : step machine (cfg 0 0 V W [] R) = some (cfg 1 0 V W [true] R) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, writeTapeBit]

theorem fwd_step (j : ℕ) (V W E R : List Bool) (hV : readTapeBit V j = true) :
    step machine (cfg 1 j V W E R) = some (cfg 1 (j + 1) V W E R) := by
  simp [step, machine, cfg, Configuration.scanned, hV]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem turn_step (j : ℕ) (V W E R : List Bool) (hV : readTapeBit V j = false) :
    step machine (cfg 1 j V W E R) = some (cfg 2 (j - 1) V W E R) := by
  simp [step, machine, cfg, Configuration.scanned, hV]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem skip_step (j : ℕ) (V W E R : List Bool) (hW : readTapeBit W j = false) (hE : readTapeBit E j = false) :
    step machine (cfg 2 j V W E R) = some (cfg 2 (j - 1) V W E R) := by
  simp [step, machine, cfg, Configuration.scanned, hW, hE]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem skipStop_step (j : ℕ) (V W E R : List Bool) (hW : readTapeBit W j = false) (hE : readTapeBit E j = true) :
    step machine (cfg 2 j V W E R) = some (cfg 4 j V W E R) := by
  simp [step, machine, cfg, Configuration.scanned, hW, hE]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem hit_step (j : ℕ) (V W E R : List Bool) (hW : readTapeBit W j = true) (hE : readTapeBit E j = false) :
    step machine (cfg 2 j V W E R) = some (cfg 3 (j - 1) V W E (writeTapeBit R j true)) := by
  simp [step, machine, cfg, Configuration.scanned, hW, hE]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem hitStop_step (j : ℕ) (V W E R : List Bool) (hW : readTapeBit W j = true) (hE : readTapeBit E j = true) :
    step machine (cfg 2 j V W E R) = some (cfg 4 j V W E (writeTapeBit R j true)) := by
  simp [step, machine, cfg, Configuration.scanned, hW, hE]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem fill_step (j : ℕ) (V W E R : List Bool) (hE : readTapeBit E j = false) :
    step machine (cfg 3 j V W E R) = some (cfg 3 (j - 1) V W E (writeTapeBit R j true)) := by
  simp [step, machine, cfg, Configuration.scanned, hE]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem fillStop_step (j : ℕ) (V W E R : List Bool) (hE : readTapeBit E j = true) :
    step machine (cfg 3 j V W E R) = some (cfg 4 j V W E (writeTapeBit R j true)) := by
  simp [step, machine, cfg, Configuration.scanned, hE]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

/-! ## The loops -/

theorem fwd_loop (m : ℕ) (W E R : List Bool) (k : ℕ) :
    ∀ j, j + k ≤ m → Timed machine k (cfg 1 j (List.replicate m true) W E R)
      (cfg 1 (j + k) (List.replicate m true) W E R) := by
  induction k with
  | zero => intro j _; simpa using Timed.refl machine (cfg 1 j (List.replicate m true) W E R)
  | succ k ih =>
    intro j hj
    have h1 := Timed.single (p := machine) (by rfl)
      (fwd_step j (List.replicate m true) W E R (read_replicate_true m j (by omega)))
    have h2 := ih (j + 1) (by omega)
    have h := h1.trans h2
    rw [show j + 1 + k = j + (k + 1) by omega, show 1 + k = k + 1 by omega] at h
    exact h

theorem skip_loop (V W E R : List Bool) (i d : ℕ) (hW : ∀ x, i < x → x ≤ i + d → readTapeBit W x = false)
    (hE : ∀ x, i < x → x ≤ i + d → readTapeBit E x = false) :
    Timed machine d (cfg 2 (i + d) V W E R) (cfg 2 i V W E R) := by
  induction d with
  | zero => simpa using Timed.refl machine (cfg 2 i V W E R)
  | succ d ih =>
    have h1 := Timed.single (p := machine) (by rfl)
      (skip_step (i + (d + 1)) V W E R (hW _ (by omega) le_rfl) (hE _ (by omega) le_rfl))
    rw [show i + (d + 1) - 1 = i + d by omega] at h1
    have h2 := ih (fun x h1 h2 => hW x h1 (by omega)) (fun x h1 h2 => hE x h1 (by omega))
    have h := h1.trans h2
    rw [show 1 + d = d + 1 by omega] at h
    exact h

theorem write_ruler (x y : ℕ) :
    writeTapeBit (List.replicate (x + 1) false ++ List.replicate y true) x true =
      List.replicate x false ++ List.replicate (y + 1) true := by
  induction x with
  | zero => simp [List.replicate_succ, writeTapeBit]
  | succ x ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [writeTapeBit]
    rw [ih]
    rfl

theorem fill_loop (V W E : List Bool) (i : ℕ) (hE : ∀ x, i < x → readTapeBit E x = false) (d : ℕ) :
    ∀ y, Timed machine d (cfg 3 (i + d) V W E (List.replicate (i + d + 1) false ++ List.replicate y true))
      (cfg 3 i V W E (List.replicate (i + 1) false ++ List.replicate (y + d) true)) := by
  induction d with
  | zero => intro y; simpa using Timed.refl machine (cfg 3 i V W E (List.replicate (i + 1) false ++ List.replicate y true))
  | succ d ih =>
    intro y
    have h1 := Timed.single (p := machine) (by rfl)
      (fill_step (i + (d + 1)) V W E (List.replicate (i + (d + 1) + 1) false ++ List.replicate y true)
        (hE _ (by omega)))
    rw [show i + (d + 1) - 1 = i + d by omega, show i + (d + 1) + 1 = (i + (d + 1)) + 1 by omega, write_ruler,
      show i + (d + 1) = i + d + 1 by omega] at h1
    have h2 := ih (y + 1)
    have h := h1.trans h2
    rw [show 1 + d = d + 1 by omega, show y + 1 + d = y + (d + 1) by omega] at h
    exact h

/-! ## The whole run -/

theorem read_marker (x : ℕ) (hx : 0 < x) : readTapeBit [true] x = false := read_beyond [true] x (by simp; omega)

theorem ruler_timed (m : ℕ) (W : List Bool) (hle : W.length ≤ m) (hlast : LastTrue W) :
    ∃ T, T ≤ 2 * m + 3 ∧ Timed machine T (cfg 0 0 (List.replicate m true) W [] [])
      (cfg 4 0 (List.replicate m true) W [true] (List.replicate W.length true)) := by
  set V := List.replicate m true with hVd
  have h0 := Timed.single (p := machine) (by rfl) (mark_step V W [])
  have h1 := fwd_loop m W [true] [] m 0 (by omega)
  rw [Nat.zero_add] at h1
  have h2 := Timed.single (p := machine) (by rfl) (turn_step m V W [true] [] (read_replicate_end m true))
  have hWb : ∀ x, W.length ≤ x → readTapeBit W x = false := fun x hx => read_beyond W x hx
  have hEb : ∀ x, 0 < x → readTapeBit [true] x = false := read_marker
  rcases Nat.eq_zero_or_pos W.length with hL | hL
  · -- no mark: skip down to `0`, stop at the marker
    have h3 := skip_loop V W [true] [] 0 (m - 1) (fun x _ _ => hWb x (by omega)) (fun x hx _ => hEb x hx)
    rw [Nat.zero_add] at h3
    have h4 := Timed.single (p := machine) (by rfl) (skipStop_step 0 V W [true] [] (hWb 0 (by omega)) rfl)
    refine ⟨1 + m + 1 + (m - 1) + 1, by omega, ?_⟩
    have h := (((h0.trans h1).trans h2).trans h3).trans h4
    rw [hL]
    exact h
  · have hlastv : readTapeBit W (W.length - 1) = true := by
      rcases hlast with h | h
      · omega
      · exact h
    have h3 := skip_loop V W [true] [] (W.length - 1) (m - W.length) (fun x hx _ => hWb x (by omega))
      (fun x hx _ => hEb x (by omega))
    rw [show W.length - 1 + (m - W.length) = m - 1 by omega] at h3
    rcases Nat.lt_or_ge 1 W.length with hL2 | hL2
    · -- the last mark is past the marker: fill backwards to `0`
      have h4 := Timed.single (p := machine) (by rfl)
        (hit_step (W.length - 1) V W [true] [] hlastv (hEb _ (by omega)))
      rw [write_nil] at h4
      have h5 := fill_loop V W [true] 0 hEb (W.length - 2) 1
      rw [Nat.zero_add, show W.length - 2 + 1 = W.length - 1 by omega] at h5
      rw [show W.length - 1 - 1 = W.length - 2 by omega] at h4
      have h4' : Timed machine 1 (cfg 2 (W.length - 1) V W [true] [])
          (cfg 3 (W.length - 2) V W [true] (List.replicate (W.length - 1) false ++ List.replicate 1 true)) := h4
      have h6 := Timed.single (p := machine) (by rfl)
        (fillStop_step 0 V W [true] (List.replicate (0 + 1) false ++ List.replicate (1 + (W.length - 2)) true) rfl)
      rw [write_ruler, show 1 + (W.length - 2) + 1 = W.length by omega] at h6
      refine ⟨1 + m + 1 + (m - W.length) + 1 + (W.length - 2) + 1, by omega, ?_⟩
      have h := (((((h0.trans h1).trans h2).trans h3).trans h4').trans h5).trans h6
      simpa using h
    · -- the last mark is at the marker
      have hL1 : W.length = 1 := by omega
      have h4 := Timed.single (p := machine) (by rfl)
        (hitStop_step (W.length - 1) V W [true] [] hlastv (by rw [show W.length - 1 = 0 by omega]; rfl))
      rw [show W.length - 1 = 0 by omega] at h3 h4
      refine ⟨1 + m + 1 + (m - W.length) + 1, by omega, ?_⟩
      have h := (((h0.trans h1).trans h2).trans h3).trans h4
      have e : writeTapeBit [] 0 true = List.replicate W.length true := by rw [hL1]; rfl
      rw [e] at h
      exact h

/-- **The ruler kernel.** From `V = replicate m true` and `W` (`|W| ≤ m`, last cell marked), all heads at `0`, within
`2m + 3` transitions: `R = replicate |W| true`, `V, W` unchanged, all heads back at `0`. -/
theorem ruler_step (m : ℕ) (W : List Bool) (hle : W.length ≤ m) (hlast : LastTrue W) :
    Step machine (2 * m + 3) (fun _ => 0) ![List.replicate m true, W, [], []] (fun _ => 0)
      ![List.replicate m true, W, [true], List.replicate W.length true] := by
  obtain ⟨T, hT, h⟩ := ruler_timed m W hle hlast
  obtain ⟨r, hr, hf, hs⟩ := h.run rfl
  have hstep : Step machine T (fun _ => 0) ![List.replicate m true, W, [], []] (fun _ => 0)
      ![List.replicate m true, W, [true], List.replicate W.length true] :=
    ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, le_of_eq hs⟩
  exact hstep.enlarge hT

end NearCubicWires.WireExponent3_5.PrimAsm.Ruler
