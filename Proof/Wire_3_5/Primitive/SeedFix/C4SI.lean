import Proof.Wire_3_5.Primitive.SeedFix.C4SH
import Proof.Wire_3_5.Primitive.Writers.Modulus
import Proof.Wire_3_5.Primitive.Writers.DataBlank
import Proof.Wire_3_5.Primitive.Writers.NumsX
import Proof.Wire_3_5.Primitive.SeedFix.C4Pipe

/-! # C4 per-call setup (item 3), part 9: the stage's slots and its front runs in one form

P3:3119-3120 ("The algorithm receives polynomial-bit integer circuit descriptions"), P3:2939-2941 (the field's
modulus "can be found and implemented in `2^{O(ℓ)}` elementary preprocessing time") and P3:2987-2988 (the seed's
numbers): every machine of the SYM setup runs on its own region of the stage's bank, reading its inputs from the tapes
earlier machines wrote; the region above the running one is still blank.

* `slx` (a stage's slots: its inputs onto the given tapes, every other tape onto its own region), `slx_inj`, `slx_ne`;
* **`stageP`**: any run with every head at `0`, docked by `slx` onto a bank blank from the region up: the outputs on the
  region, the inputs as the run leaves them, the bank below the region otherwise unchanged, the bank above it blank;
* the front runs as such runs: `unS` (the raw request), `crS` (`1^v` from `natWord v`), `srcS` (`1^{2^m}` from
  `srcWord m`), `ucS` (`1^{C(n+1)^D}`), `modS` (the modulus word `frame (binary ℓ (firstPrimitive ℓ))`), `cpS` (the
  call's counts from the data word), `c3S` (the C3 request writer's fields).

Paper quantities of the main types: the request word, its numbers in unary, the modulus word, the counts, the
compiler request's fields. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.GeoFront
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## Slots -/

/-- **A stage's slots**: tape `j` onto the bank's tape `ext j` when given (the stage's inputs), else onto `off + j`
(the stage's own region). -/
def slx {t u : ℕ} (off : ℕ) (hoff : off + t ≤ u) (ext : Fin t → Option (Fin u)) (j : Fin t) : Fin u :=
  match ext j with
  | some g => g
  | none => ⟨off + j.val, by have := j.isLt; omega⟩

theorem slx_some {t u : ℕ} {off : ℕ} {hoff : off + t ≤ u} {ext : Fin t → Option (Fin u)} {j : Fin t} {g : Fin u}
    (h : ext j = some g) : slx off hoff ext j = g := by
  unfold slx; rw [h]

theorem slx_none {t u : ℕ} {off : ℕ} {hoff : off + t ≤ u} {ext : Fin t → Option (Fin u)} {j : Fin t}
    (h : ext j = none) : (slx off hoff ext j).val = off + j.val := by
  unfold slx; rw [h]

theorem slx_inj {t u : ℕ} (off : ℕ) (hoff : off + t ≤ u) (ext : Fin t → Option (Fin u))
    (hinj : ∀ i j g, ext i = some g → ext j = some g → i = j) (hlt : ∀ i g, ext i = some g → g.val < off) :
    Function.Injective (slx off hoff ext) := by
  intro i j h
  have hv := congrArg Fin.val h
  cases hi : ext i with
  | some gi =>
    cases hj : ext j with
    | some gj =>
      rw [slx_some hi, slx_some hj] at h
      subst h
      exact hinj i j gi hi hj
    | none =>
      rw [slx_some hi, slx_none hj] at hv
      have := hlt i gi hi
      omega
  | none =>
    cases hj : ext j with
    | some gj =>
      rw [slx_none hi, slx_some hj] at hv
      have := hlt j gj hj
      omega
    | none =>
      rw [slx_none hi, slx_none hj] at hv
      exact Fin.ext (by omega)

theorem slx_ne {t u : ℕ} (off : ℕ) (hoff : off + t ≤ u) (ext : Fin t → Option (Fin u)) (g : Fin u)
    (hg : g.val < off ∨ off + t ≤ g.val) (he : ∀ j, ext j ≠ some g) : ∀ j, slx off hoff ext j ≠ g := by
  intro j e
  cases hj : ext j with
  | some g' => rw [slx_some hj] at e; subst e; exact he j hj
  | none =>
    have hv := congrArg Fin.val e
    rw [slx_none hj] at hv
    have := j.isLt
    omega

/-- **A docked stage**: a run with every head at `0` from `tin`, its inputs read from the tapes `ext` names (all below
its region), the bank blank from its region up. -/
theorem stageP {t u s n : ℕ} {M : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) (off : ℕ) (hoff : off + t ≤ u) (ext : Fin t → Option (Fin u))
    (hinj : ∀ i j g, ext i = some g → ext j = some g → i = j) (hlt : ∀ i g, ext i = some g → g.val < off)
    (B : Fin u → List Bool) (hex : ∀ j g, ext j = some g → B g = tin j)
    (hblank : ∀ i : Fin u, off ≤ i.val → B i = []) (htin : ∀ j, ext j = none → tin j = []) :
    Step (RecoveryFocus.machine (slx off hoff ext) M) n (fun _ => 0) B (fun _ => 0) (install (slx off hoff ext) B tout) ∧
      (∀ i : Fin u, off + t ≤ i.val → install (slx off hoff ext) B tout i = []) ∧
      (∀ i : Fin u, i.val < off → (∀ j, ext j ≠ some i) → install (slx off hoff ext) B tout i = B i) ∧
      (∀ (j : Fin t) (i : Fin u), ext j = none → i.val = off + j.val → install (slx off hoff ext) B tout i = tout j) ∧
      (∀ j g, ext j = some g → install (slx off hoff ext) B tout g = tout j) := by
  have hinj' := slx_inj off hoff ext hinj hlt
  refine ⟨GeoFront.dockZ h _ hinj' (fun _ => 0) B (fun _ => rfl) (fun j => ?_), ?_, ?_, ?_, ?_⟩
  · cases hj : ext j with
    | some g => rw [slx_some hj]; exact hex j g hj
    | none =>
      rw [htin j hj]
      apply hblank
      rw [slx_none hj]
      omega
  · intro i hi
    rw [install_other _ _ _ _ (slx_ne off hoff ext i (Or.inr hi) (fun j e => by have := hlt j i e; omega))]
    exact hblank i (by omega)
  · intro i hi he
    exact install_other _ _ _ _ (slx_ne off hoff ext i (Or.inl hi) he)
  · intro j i hj hi
    have e : slx off hoff ext j = i := Fin.ext (by rw [slx_none hj]; exact hi.symm)
    rw [← e]
    exact install_slot _ hinj' _ _ j
  · intro j g hj
    rw [← slx_some (hoff := hoff) hj]
    exact install_slot _ hinj' _ _ j

/-! ## The front runs, every head at `0` -/

/-- The raw request: from `frame w` on tape `0`, `w` on tape `1`. -/
theorem unS (w : List Bool) : ∃ tout : Fin 3 → List Bool,
    Step unM (2 * (2 * w.length + 1) + 2) (fun _ => 0) (fun j => if j.val = 0 then frame w else []) (fun _ => 0) tout ∧
      tout 0 = frame w ∧ tout 1 = w := by
  obtain ⟨m1, h⟩ := maskBlank (Unframe.run [] w [] [] []) (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have eh0 : (Fin.addCases (fun _ : Fin 2 => 0) (fun _ : Fin 1 => 0) : Fin (2 + 1) → ℕ) = fun _ => 0 := by
    funext i; fin_cases i <;> rfl
  refine ⟨_, (h.congr_in ?_ ?_).congr ?_ rfl, ?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · show [] ++ frame w ++ [] = frame w; simp
    · show overlay [] [] = []; simp [overlay_nil]
    · rfl
  · funext i; fin_cases i <;> rfl
  · show [] ++ frame w ++ [] = frame w; simp
  · show overlay w [] = w; simp [overlay_nil]

/-- `1^v`, twice, from the self-delimiting binary `natWord v ++ sfx` (the source kept). -/
theorem crS (v : ℕ) (sfx : List Bool) : ∃ tout : Fin 12 → List Bool,
    Step crM (crCost v) (fun _ => 0) (fun j => if j.val = 0 then RepairRepresentation.natWord v ++ sfx else [])
      (fun _ => 0) tout ∧ tout 0 = RepairRepresentation.natWord v ++ sfx ∧ tout 8 = List.replicate v true ∧
      tout 9 = List.replicate v true := by
  obtain ⟨H, A, h, hout⟩ := PCJ45bee56da9f34d5a_CapReader.natural_run [] sfx v
  obtain ⟨h0', _, h8, _, h9, _, _, _⟩ := hout
  obtain ⟨m2, hm⟩ := maskBlank h (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have eh0 : (Fin.addCases (PCJ45bee56da9f34d5a_CapReader.initialHeads ([] : List Bool).length) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · fin_cases a <;> rfl
    · simp
  have eh1 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else H i) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have hm' := (hm.congr_in eh0 rfl).congr eh1 rfl
  refine ⟨_, hm'.congr_in rfl ?_, h0', h8, h9⟩
  funext j
  fin_cases j <;> rfl

/-- The CapReader cost of `srcWord m`. -/
def srcCost (m : ℕ) : ℕ := 2 * (8 * 2 ^ m + 20 * (m + 1) + 17) + 2

/-- `1^{2^m}`, twice, from `srcWord m` (the source kept). -/
theorem srcS (m : ℕ) : ∃ tout : Fin 12 → List Bool,
    Step crM (srcCost m) (fun _ => 0) (fun j => if j.val = 0 then NumsX.srcWord m else []) (fun _ => 0) tout ∧
      tout 0 = NumsX.srcWord m ∧ tout 8 = List.replicate (2 ^ m) true ∧ tout 9 = List.replicate (2 ^ m) true := by
  have hne : (List.replicate m false ++ [true]) ≠ [] := by simp
  obtain ⟨H3, A3, h3, f3⟩ := PCJ45bee56da9f34d5a_CapReader.run [] (List.replicate m false ++ [true]) [] hne
  obtain ⟨a0, -, a8, -, a9, -, -, -⟩ := f3
  obtain ⟨m3, hm⟩ := maskBlank h3 (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have eh0 : (Fin.addCases (PCJ45bee56da9f34d5a_CapReader.initialHeads ([] : List Bool).length) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · fin_cases a <;> rfl
    · simp
  have eh1 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else H3 i) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have hm' := (hm.congr_in eh0 rfl).congr eh1 rfl
  have hsrc := NumsX.srcWord_eq m
  have hv := NumsX.src_value m
  refine ⟨_, (hm'.congr_in rfl ?_).enlarge ?_, ?_, ?_, ?_⟩
  · funext j
    fin_cases j
    · show _ = NumsX.srcWord m
      rw [hsrc]
      rfl
    all_goals rfl
  · unfold srcCost
    simp only [List.length_append, List.length_replicate, List.length_singleton, hv]
    omega
  · show A3 0 = _
    rw [a0, hsrc]
    rfl
  · show A3 8 = _
    rw [a8, hv]
  · show A3 9 = _
    rw [a9, hv]

/-- The copy-in machine (C2's `cpW`, every head back at `0`). -/
noncomputable def cpZ := MaskedReset.machine CellLoopD.cpW.toProg.compile (fun _ => true)

/-- The copy-in's step bound. -/
def cpZCost (u : List Bool) : ℕ := 2 * CellLoopD.cpCost u.length + 2

/-- **The call's counts** from the data word `false :: frame u`: `u` on tape `2`. -/
theorem cpS (u : List Bool) : ∃ tout : Fin (1 + 2 + 0 + 1) → List Bool,
    Step cpZ (cpZCost u) (fun _ => 0) (fun j => if j.val = 0 then false :: (Streaming.marks u ++ [false]) else [])
      (fun _ => 0) tout ∧ tout ⟨2, by omega⟩ = u := by
  set σ : WState 1 0 := ⟨fun _ => 0, ![false :: (Streaming.marks u ++ [false]), []], fun r => r.elim0, false⟩ with hσ
  have hw := CellLoopD.cpW_spec 0 u σ rfl rfl rfl rfl
  obtain ⟨A', hs, hA⟩ := C4Pipe.wm_blank 0 (CellLoopD.cpCost u.length) CellLoopD.cpW σ (σ.sets 1 u) _ hw
    (fun _ => rfl) (fun r => r.elim0) rfl le_rfl
  refine ⟨A', hs.congr_in rfl ?_, ?_⟩
  · funext j
    fin_cases j <;> rfl
  · have h1 := hA 1
    have e : (Fin.castAdd 1 (sTape (ns := 1) (nr := 0) 1) : Fin (1 + 2 + 0 + 1)) = ⟨2, by omega⟩ := rfl
    rw [e] at h1
    rw [h1]
    simp [WState.sets]

end NearCubicWires.WireExponent3_5.PrimT.C4Set
