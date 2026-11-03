import Proof.Wire_3_5.Compiler.MachineC3aOut
import Proof.Wire_3_5.Compiler.MachinePoolRunCost

/-! # C3a machine, the pool and its output word (P3:1636-1664)

Paper: alg:pullback, "Every child becomes an equation `E_{j,y}(z) = a_{j,y}(z_L) + b_{j,y}(z_R) = 0` [...] The children
remain disjoint and represent the pulled-back threshold exactly" (P3:1636-1650), for a common pool over all rows
(P3:1661-1664). The pool builder (`pool_run_cost`, MC6's machine) writes the pool stream (word (1), closed by `false`)
on its output tape and the children table (word (2)) on its table tape; with every cursor but the output's returned to
cell `0` (a masked reset), the table is appended to the output (`tab_run`), and a final masked reset returns every
head. **`po_run`**: from the pool builder's entry bank and the unary count of the pool's atoms, the output tape holds
exactly C3a's encoding `poolRecs … .flatMap frame ++ false :: table.flatMap atomStream`. The paper quantity is the
contract's output word. Main declarations: `poolR`, `poM`, `poCost`, **`po_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.PO
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Top NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Dec NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Count
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Out
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The pool builder with every cursor but the output's returned to cell `0`. -/
noncomputable def poolR := MaskedReset.machine poolM (fun i : Fin 38 => decide (i ≠ 21))

def sTab : Fin 3 → Fin 40 := ![34, 21, 39]
theorem sTab_inj : Function.Injective sTab := by decide

/-- The pool builder, then the table appended (tapes: the pool's 38, its mask log, the atom count). -/
noncomputable def poInnerM := Composition.machine (TapeEmbedding.machine 1 poolR) (RecoveryFocus.machine sTab tabLoopM)
/-- **The pool and its output word**, every head back at cell `0`. -/
noncomputable def poM := MaskedReset.machine poInnerM (fun _ => true)

def poInnerCost (pc a m L : ℕ) : ℕ := (2 * pc + 2) + 1 + tabLoopCost a m L
def poCost (pc a m L : ℕ) : ℕ := 2 * poInnerCost pc a m L + 2

variable (a : DecompositionAlgorithm)

theorem shape_flat {α : Type} (D : List (List α)) : (shapeOf D).flatten.length = D.flatten.length := by
  simp [shapeOf, List.length_flatten, Function.comp_def]

/-- The pool's children: `P_ex = |flips|·B`. -/
theorem densePool_flatten_length {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) :
    (densePool a gates side width flips).flatten.length = flips.length * (counts a gates).sum := by
  induction flips with
  | nil => simp [densePool]
  | cons f fs ih =>
    have e : densePool a gates side width (f :: fs) =
        gates.map (fun g => (children a g).map (pullDense side f width)) ++ densePool a gates side width fs := by
      simp [densePool]
    rw [e, List.flatten_append, List.length_append, ih, List.length_cons]
    have hg : (gates.map (fun g => (children a g).map (pullDense side f width))).flatten.length = (counts a gates).sum := by
      rw [List.length_flatten, List.map_map]
      simp [counts, Function.comp_def]
    rw [hg]
    ring

/-- The pool's atom count: one atom per flip pattern and carrier gate. -/
theorem childTable_length (Q : ℕ) {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) :
    (childTable Q (shapeOf (densePool a gates side width flips))).length = flips.length * gates.length := by
  simp [childTable, shapeOf, densePool_length]

/-- Every entry of the children table has the entry width `Q + P_ex + 1`. -/
theorem childTable_entry (Q : ℕ) (pool : List (List SynEq)) :
    ∀ E ∈ childTable Q pool, ∀ r ∈ E, r.length = Q + pool.flatten.length + 1 := by
  intro E hE r hr
  simp only [childTable, List.mem_map, List.mem_range] at hE
  obtain ⟨i, _, rfl⟩ := hE
  simp only [List.mem_map] at hr
  obtain ⟨c, _, rfl⟩ := hr
  simp [Unions.ew, Unions.entryWord_length]

/-- Every atom has at most `P_ex` children labels. -/
theorem childTable_count (Q : ℕ) (pool : List (List SynEq)) :
    ∀ E ∈ childTable Q pool, E.length ≤ pool.flatten.length := by
  intro E hE
  simp only [childTable, List.mem_map, List.mem_range] at hE
  obtain ⟨i, _, rfl⟩ := hE
  simp only [List.length_map, labelsOf, List.length_range']
  exact length_getD_le_flatten pool i

theorem entry_ne (Q : ℕ) (pool : List (List SynEq)) : ∀ E ∈ childTable Q pool, ∀ r ∈ E, r ≠ [] := by
  intro E hE r hr h
  have := childTable_entry Q pool E hE r hr
  rw [h] at this
  simp at this

/-- **The pool and its output word** (P3:1636-1664): from the pool builder's entry bank (MC6's `pool_run` with an
empty output and table) and the unary count of the atoms, the output tape holds C3a's encoding. -/
theorem po_run (h Q Wc V : ℕ) (h1 : 1 ≤ h) (hW1 : 1 ≤ Wc) {n : ℕ} (hn : 1 ≤ n) (gates : List (SupportedNormalizedGate n))
    (side : List Bool) (width : ℕ) (flips : List (List Bool)) (hs : side.length = n)
    (hfl : ∀ f ∈ flips, f.length = n) (hL : nLeft side n ≤ width) (hR : nRight side n ≤ width)
    (postG postC tS sZL sZR staleF MR FR RP RN OL OR PA NA TM NM : List Bool)
    (x0 capK cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP cap0 : ℕ)
    (hok : ∀ e ∈ GS a gates, ∀ z ∈ List.ofFn e.weight ++ [e.target], CoefOk h capK cap z)
    (hcs : ∀ v ∈ counts a gates, v < 2 ^ Wc ∧ v ≤ V ∧ natBitLength v ≤ capK)
    (hc1 : 2 * h + 1 ≤ cap) (hcF : 2 * n + 1 ≤ cap)
    (hcT1 : 2 * (Q + flips.length * (counts a gates).sum + 1) + 1 ≤ cap) (hcT2 : 2 * Wc + 2 ≤ cap)
    (hcT3 : 3 * Wc + 2 ≤ cap)
    (hcN2 : innerCost h n ≤ capN2) (hcN7 : normCost h n (GS a gates).length ≤ capN7) (hcC2 : cloopCost h n ≤ capC2)
    (hcC3 : appCost h (2 * nLeft side n) (2 * (width - nLeft side n)) (2 * nRight side n)
      (2 * (width - nRight side n)) ≤ capC3)
    (hcC4 : kidsCost h n width (nLeft side n) (nRight side n) (GS a gates).length ≤ capC4)
    (hcF8 : flips.length * (flipCost h n width (nLeft side n) (nRight side n) (GS a gates).length + 2) + 1 ≤ capF8)
    (hc5 : gatesCost Q (flips.length * (counts a gates).sum) Wc V (counts a gates).length ≤ cap5)
    (hcP : poolCost h Q Wc V n width (nLeft side n) (nRight side n) (GS a gates).length flips.length
      (flips.length * (counts a gates).sum) (counts a gates).length ≤ capP)
    (hc0 : poInnerCost (poolCost h Q Wc V n width (nLeft side n) (nRight side n) (GS a gates).length flips.length
      (flips.length * (counts a gates).sum) (counts a gates).length) (flips.length * gates.length)
      (flips.length * (counts a gates).sum) (Q + flips.length * (counts a gates).sum + 1) ≤ cap0) :
    ∃ Af : Fin 40 → List Bool, Step poM
      (poCost (poolCost h Q Wc V n width (nLeft side n) (nRight side n) (GS a gates).length flips.length
        (flips.length * (counts a gates).sum) (counts a gates).length) (flips.length * gates.length)
        (flips.length * (counts a gates).sum) (Q + flips.length * (counts a gates).sum + 1)) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) (Fin.addCases (motive := fun _ => List Bool)
        (Fin.addCases (motive := fun _ => List Bool)
          (rA (rtPool ((GS a gates).flatMap exactWord ++ postG) (false :: List.replicate capK true) MR (frame (binary h 0))
            NM (List.replicate cap false) (List.replicate n true) (List.replicate capN2 false)
            (List.replicate (GS a gates).length true) (frame side ++ tS) FR RP RN OL OR PA NA TM
            (List.replicate capC2 false) (streamTape (zeroRecs h (width - nLeft side n)) sZL)
            (streamTape (zeroRecs h (width - nRight side n)) sZR) [] (List.replicate capC3 false)
            (List.replicate capC4 false) (streamTape flips staleF) ((counts a gates).flatMap natWord ++ false :: postC)
            (frame (binary Wc x0)) (frame (binary Wc 0)) (frame (binary Wc x0)) [false] [true]
            (frame (entC Q (flips.length * (counts a gates).sum) 0)) (frame (shiftMask Q (flips.length * (counts a gates).sum)))
            (frame (entC Q (flips.length * (counts a gates).sum) 0)) [] (List.replicate cap5 false)
            (List.replicate capN7 false) (List.replicate capF8 false)))
          (fun _ : Fin 1 => List.replicate capP false))
        (fun _ : Fin 1 => List.replicate (flips.length * gates.length) true))
        (fun _ : Fin 1 => List.replicate cap0 false))
      (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) Af (fun _ : Fin 1 => List.replicate cap0 false)) ∧
      Af 21 = (poolRecs a h gates side width flips).flatMap frame ++
        false :: (childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream := by
  set W := flips.length * (counts a gates).sum with hWdef
  set pc := poolCost h Q Wc V n width (nLeft side n) (nRight side n) (GS a gates).length flips.length W
    (counts a gates).length
  set Es := childTable Q (shapeOf (densePool a gates side width flips))
  set O0 := (poolRecs a h gates side width flips).flatMap frame ++ [false]
  obtain ⟨tout, hout, htb, hp⟩ := pool_run_cost a h Q Wc V h1 hW1 hn gates side width flips hs hfl hL hR postG postC tS
    sZL sZR staleF MR FR RP RN OL OR PA NA TM NM [] [] x0 capK cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 hok hcs hc1 hcF
    hcT1 hcT2 hcT3 hcN2 hcN7 hcC2 hcC3 hcC4 hcF8 hc5
  rw [overlay_nil_right] at hout htb
  -- the pool, every cursor but the output's returned
  have m1 := hp.mask (fun i : Fin 38 => decide (i ≠ 21)) (by intro i _; fin_cases i <;> rfl) hcP
  have e1 := m1.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate Es.length true)
  set A1 := Fin.addCases (motive := fun _ => List Bool) (Fin.addCases (motive := fun _ => List Bool) (rA tout)
    (fun _ : Fin 1 => List.replicate capP false)) (fun _ : Fin 1 => List.replicate Es.length true)
  set H1 := Fin.addCases (motive := fun _ => ℕ) (Fin.addCases (motive := fun _ => ℕ)
    (fun i : Fin 38 => if decide (i ≠ 21) = true then 0 else
      rH ((GS a gates).flatMap exactWord).length (GS a gates).length
        ((poolRecs a h gates side width flips).flatMap frame ++ [false]).length (flips.flatMap frame).length
        ((childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream).length i)
    (fun _ : Fin 1 => 0)) (fun _ : Fin 1 => 0)
  -- the table appended
  have hflat : (shapeOf (densePool a gates side width flips)).flatten.length = W := by
    rw [shape_flat, hWdef, densePool_flatten_length]
  have hne := entry_ne Q (shapeOf (densePool a gates side width flips))
  have hlen : ∀ E ∈ Es, ∀ r ∈ E, r.length = Q + W + 1 := by
    have := childTable_entry Q (shapeOf (densePool a gates side width flips)); rw [hflat] at this; exact this
  have hcnt : ∀ E ∈ Es, E.length ≤ W := by
    have := childTable_count Q (shapeOf (densePool a gates side width flips)); rw [hflat] at this; exact this
  have t1 := tab_run Es (Q + W + 1) W hne hlen hcnt O0
  have hH : ∀ j, H1 (sTab j) = ![0, O0.length, 0] j := by
    intro j; fin_cases j <;> rfl
  have hA : ∀ j, A1 (sTab j) = ![Es.flatMap atomStream, O0, List.replicate Es.length true] j := by
    intro j; fin_cases j
    · exact htb
    · exact hout
    · rfl
  have d := dockRun t1 sTab sTab_inj H1 A1 hH hA
  have all := e1.seq d
  have hz : Fin.addCases (motive := fun _ => ℕ) (Fin.addCases (motive := fun _ => ℕ) (rH 0 0 0 0 0)
      (fun _ : Fin 1 => 0)) (fun _ : Fin 1 => 0) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left]
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · rw [Fin.addCases_left]; fin_cases k <;> rfl
      · rw [Fin.addCases_right]
    · rw [Fin.addCases_right]
  rw [hz] at all
  have hEs : Es.length = flips.length * gates.length := childTable_length a Q gates side width flips
  have m2 := all.mask (fun _ => true) (by intro i _; rfl) (cap := cap0) (by rw [← hEs] at hc0; exact hc0)
  refine ⟨install sTab A1 ![Es.flatMap atomStream, O0 ++ Es.flatMap atomStream,
    List.replicate (flips.length * gates.length) true], ?_, ?_⟩
  · rw [hEs] at m2
    refine (m2.congr_in addCases_zero' ?_).congr (mask_zero _) rfl
    rfl
  · rw [install_eval _ sTab_inj]
    show O0 ++ Es.flatMap atomStream = _
    simp [O0]

end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.PO
