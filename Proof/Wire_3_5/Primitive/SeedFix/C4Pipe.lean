import Proof.Wire_3_5.Primitive.SeedFix.C4Frame
import Proof.MachineModel.PlanDirectCount
import Proof.Wire_3_5.Compiler.MachineTopWord

/-! # SEEDFIX C4.L, the printer dock part 2: one child's recovered sum (P3:1728-1737, 1886-1906, 1965-1982, 3035-3037)

"For each candidate child prefix [...] sum the recovered integers" (P3:3035-3037): the child's expression is compiled
(`alg:compiler`, C3's `c3_run`), its request word framed (`C4Frame.frameW`), and base's printer with its selected-cell
sum (`P1Plan.DirectCount.run`: `CompetitorCountTable.machine` then `CompetitorSelectedRequestCount`) prints the table
and sums its least residues, "Reduction must precede the column sum" (`alg:recovery`, P3:1965-1982).

This module has the pieces: word programs run from BLANK scratch (`wm_blank`: the register and cell tapes may be `[]`,
by base's `ZeroPadding.run_unpad`), the printer metadata writer `prepW` (`1^Q`, the parity `[false]`, the all-selected
mask), and the printer's entry bank (`dcIn_eq`).

Paper quantity of the main types: the recovered child sum `Σ_{row,col} (2^{m−1}·V(z) mod 2^{Q'})`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Pipe
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch

/-! ## Word programs from blank scratch -/

/-- A word state's streams on their tapes, every register and the cell tape blank. -/
def wblank {ns nr : ℕ} (σ : WState ns nr) (j : Fin (ns + 2 + nr)) : List Bool :=
  match role j with
  | .stream i => σ.st i
  | .cell => []
  | .reg _ => []

/-- The padding that turns `wblank σ` into `wenc σ` (at zero registers and a `false` cell), and the blank log into
the log of capacity `capL`. -/
def wcap {ns nr : ℕ} (cap capL : ℕ) : Fin (ns + 2 + nr + 1) → ℕ :=
  Fin.addCases (fun j => match role (ns := ns) (nr := nr) j with
    | .stream _ => 0
    | .cell => 1
    | .reg _ => cap + 1) (fun _ : Fin 1 => capL)

/-- **A word program from blank scratch**: from its streams, blank register and cell tapes and a blank log (every head
at `0`), the compiled program under the masked reset ends with every head at `0` and its streams as the program's. -/
theorem wm_blank {ns nr : ℕ} (cap capL : ℕ) (P : WM ns nr) (σ τ : WState ns nr) (n : ℕ) (hw : WExec cap P σ τ n)
    (hs : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) (hc : σ.cell = false) (hn : n ≤ capL) :
    ∃ A' : Fin (ns + 2 + nr + 1) → List Bool,
      Step (MaskedReset.machine P.toProg.compile (fun _ => true)) (2 * n + 2) (fun _ => 0)
        (Fin.addCases (wblank σ) (fun _ : Fin 1 => [])) (fun _ => 0) A' ∧
      ∀ i, A' (Fin.castAdd 1 (sTape i)) = τ.st i := by
  have hm := HbM.wm_mask cap capL P σ τ n hw (HbM.wenc_H_zero' cap σ hs hv) hn
  have hpad : Fin.addCases (wenc cap σ).A (fun _ : Fin 1 => List.replicate capL false) =
      fun i => ZeroPadding.pad (wcap (ns := ns) (nr := nr) cap capL i)
        (Fin.addCases (wblank σ) (fun _ : Fin 1 => ([] : List Bool)) i) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp only [Fin.addCases_left, wcap, wblank, wenc]
      cases hr : role j with
      | stream i => simp
      | cell => simp [hc, ZeroPadding.pad]
      | reg r => simp [hv, FinalPass.Tm.regTape_zero, ZeroPadding.pad]
    · simp [wcap, ZeroPadding.pad]
  obtain ⟨src, hsrc, hh, ht, hsteps⟩ := hm
  have hcfg : (⟨(MaskedReset.machine P.toProg.compile (fun _ => true)).start, fun _ => 0,
      Fin.addCases (wenc cap σ).A (fun _ : Fin 1 => List.replicate capL false)⟩ :
        Configuration (ns + 2 + nr + 1) _) =
      ZeroPadding.config (wcap (ns := ns) (nr := nr) cap capL)
        ⟨(MaskedReset.machine P.toProg.compile (fun _ => true)).start, fun _ => 0,
          Fin.addCases (wblank σ) (fun _ : Fin 1 => [])⟩ := by
    rw [hpad]; rfl
  rw [hcfg] at hsrc
  obtain ⟨r, hr, hcf, hst, _⟩ := ZeroPadding.run_unpad _ _ _ _ src hsrc
  have hheads : r.final.heads = fun _ => 0 := by
    have := congrArg Configuration.heads hcf
    simp only [ZeroPadding.config] at this
    rw [this, hh]
  refine ⟨r.final.tapes, ⟨r, hr, hheads, rfl, by omega⟩, ?_⟩
  intro i
  have h1 := congrFun (congrArg Configuration.tapes hcf) (Fin.castAdd 1 (sTape i))
  simp only [ZeroPadding.config] at h1
  rw [ht] at h1
  simp only [wcap, Fin.addCases_left, role_sTape, ZeroPadding.pad_zero] at h1
  rw [h1]
  exact wenc_A_s cap τ i

/-! ## The printer's metadata writer -/

theorem write_end : ∀ (l : List Bool) (b : Bool), writeTapeBit l l.length b = l ++ [b]
  | [], b => rfl
  | x :: l, b => by
    show writeTapeBit (x :: l) (l.length + 1) b = x :: (l ++ [b])
    simp only [writeTapeBit, write_end l b]

section Prep
variable (cap : ℕ)

/-- Copy a unary word from `s` onto the blank `d`. -/
def ucopy (s d : Fin 5) : WM 4 1 := .whs s (.seq (.wr d true) (.seq (.fwd s) (.fwd d)))

theorem ucopy_spec (s d : Fin 5) (hsd : s ≠ d) (q : ℕ) :
    ∀ (m k : ℕ) (σ : WState 4 1), k + m = q → σ.st s = List.replicate q true → σ.sh s = k →
      σ.st d = List.replicate k true → σ.sh d = k →
      WExec cap (ucopy s d) σ (((σ.sets d (List.replicate q true)).seth s q).seth d q) (m * 7 + 1) := by
  intro m
  induction m with
  | zero =>
    intro k σ hk hs hsk hd hdk
    have hb : wbit σ s = false := by
      simp only [wbit, hs, hsk, readTapeBit]; rw [List.getD_eq_default _ _ (by simp; omega)]
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    apply WState.eq
    · funext i; simp only [WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext i; simp only [WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · rfl
    · rfl
  | succ m ih =>
    intro k σ hk hs hsk hd hdk
    have hb : wbit σ s = true := by
      simp only [wbit, hs, hsk, readTapeBit]; rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
    have h1 := WExec.wr (cap := cap) d true σ
    have e1 : writeTapeBit (σ.st d) (σ.sh d) true = List.replicate (k + 1) true := by
      rw [hd, hdk]
      have := write_end (List.replicate k true) true
      simp only [List.length_replicate] at this
      rw [this, List.replicate_succ']
    rw [e1] at h1
    set σ1 := σ.sets d (List.replicate (k + 1) true) with hσ1
    have h2 := WExec.fwd (cap := cap) s σ1
    have h3 := WExec.fwd (cap := cap) d (σ1.seth s (σ1.sh s + 1))
    set σ3 := (σ1.seth s (σ1.sh s + 1)).seth d ((σ1.seth s (σ1.sh s + 1)).sh d + 1) with hσ3
    have hrec := ih (k + 1) σ3 (by omega)
      (by simp [σ3, σ1, Function.update_apply, Ne.symm hsd, hsd, hs] <;> intro h <;> exact absurd h hsd)
      (by simp [σ3, σ1, Function.update_apply, hsd, hsk] <;> intro h <;> exact absurd h hsd) (by simp [σ3, σ1])
      (by simp [σ3, σ1, Function.update_apply, Ne.symm hsd, hsd, hdk] <;> intro h <;> exact absurd h hsd)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 (WExec.seq h2 h3)) hrec) ?_ (by omega)
    apply WState.eq
    · funext i; simp only [σ3, σ1, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext i; simp only [σ3, σ1, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · rfl
    · rfl

/-- **The printer's metadata**: `1^Q` (from stream `0`), the parity `[false]`, the mask `1^M` (from stream `1`). -/
def prepW : WM 4 1 := .seq (ucopy 0 2) (.seq (.wr 3 false) (ucopy 1 4))

theorem prepW_spec (q u : ℕ) (σ : WState 4 1) (h0 : σ.st 0 = List.replicate q true)
    (h1 : σ.st 1 = List.replicate u true) (h2 : σ.st 2 = []) (h3 : σ.st 3 = []) (h4 : σ.st 4 = [])
    (hs : ∀ i, σ.sh i = 0) :
    ∃ τ : WState 4 1, WExec cap prepW σ τ (q * 7 + 1 + 1 + (1 + 1 + (u * 7 + 1))) ∧
      τ.st 0 = List.replicate q true ∧ τ.st 1 = List.replicate u true ∧ τ.st 2 = List.replicate q true ∧
      τ.st 3 = [false] ∧ τ.st 4 = List.replicate u true := by
  have s1 := ucopy_spec cap 0 2 (by decide) q q 0 σ (by omega) h0 (hs 0) (by simp [h2]) (hs 2)
  set σ1 := ((σ.sets 2 (List.replicate q true)).seth 0 q).seth 2 q with hσ1
  have s2 := WExec.wr (cap := cap) 3 false σ1
  have e2 : writeTapeBit (σ1.st 3) (σ1.sh 3) false = [false] := by
    simp [σ1, Function.update_apply, h3, hs 3]; rfl
  rw [e2] at s2
  set σ2 := σ1.sets 3 [false] with hσ2
  have s3 := ucopy_spec cap 1 4 (by decide) u u 0 σ2 (by omega) (by simp [σ2, σ1, Function.update_apply, h1])
    (by simp [σ2, σ1, Function.update_apply, hs 1]) (by simp [σ2, σ1, Function.update_apply, h4])
    (by simp [σ2, σ1, Function.update_apply, hs 4])
  refine ⟨_, WExec.seq s1 (WExec.seq s2 s3), ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [σ2, σ1, Function.update_apply, h0, h1]

end Prep

/-! ## The printer's entry bank -/

section Dock
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)

variable (p : Program)

/-- The printer's tapes (the selected-count layout). -/
abbrev DT : ℕ := CompetitorSelectedTable.tapes p

/-- The sum port (`CompetitorSelectedTable.slot 86`). -/
def dcS : Fin (DT p) := CompetitorSelectedTable.slot p 86

/-- The printer's entry bank, port by port. -/
def dcBank (w q m : List Bool) (odd : Bool) : Fin (DT p) → List Bool :=
  fun i => if i.val = 0 then w else if i.val = CompetitorCountBanks.tapes p + 1 then q
    else if i.val = CompetitorCountBanks.tapes p + 3 then [odd]
    else if i.val = CompetitorCountTable.tapes p then m else []

theorem dcIn_eq (r : MatrixScoreBatch.Request) (Q : ℕ) (odd : Bool) (xs : List (Bool × ℕ)) :
    P1Plan.DirectCount.input p r Q odd xs =
      dcBank p (MatrixScoreBatch.physicalInput r) (List.replicate Q true) (CompetitorCountMask.mask xs) odd := by
  have hCS : CompetitorCrossScheduler.tapes p = 181 + p.tapeCount := rfl
  have hCB : CompetitorCountBanks.tapes p = CompetitorCrossScheduler.tapes p + 511 := rfl
  have hCT : CompetitorCountTable.tapes p = CompetitorCountBanks.tapes p + 124 := rfl
  funext i
  unfold P1Plan.DirectCount.input CompetitorSelectedTable.extend CompetitorCountTable.input
    CompetitorCountTable.extend CompetitorCountBanks.input CompetitorCountBanks.extend dcBank
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · rw [Fin.addCases_left]
    refine Fin.addCases (fun j1 => ?_) (fun k1 => ?_) j
    · rw [Fin.addCases_left]
      refine Fin.addCases (fun j2 => ?_) (fun k2 => ?_) j1
      · rw [Fin.addCases_left]
        simp only [CompetitorCrossScheduler.input, Fin.val_castAdd]
        have := j2.isLt
        split_ifs
        all_goals first | rfl | omega
      · rw [Fin.addCases_right]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        have := k2.isLt
        split_ifs
        all_goals first | rfl | omega
    · rw [Fin.addCases_right]
      simp only [CompetitorCountTable.metadata, Fin.val_castAdd, Fin.val_natAdd]
      have := k1.isLt
      have e1 : (k1 = 1) ↔ k1.val = 1 := by rw [Fin.ext_iff]; rfl
      have e3 : (k1 = 3) ↔ k1.val = 3 := by rw [Fin.ext_iff]; rfl
      simp only [e1, e3]
      split_ifs
      all_goals first | rfl | omega
  · rw [Fin.addCases_right]
    simp only [CompetitorSelectedTable.extra, Fin.val_natAdd]
    have := k.isLt
    have e0 : (k = 0) ↔ k.val = 0 := by rw [Fin.ext_iff]; rfl
    simp only [e0]
    split_ifs
    all_goals first | rfl | omega

end Dock

/-! ## The printer and its sum, as a step -/

section Printer
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)

theorem flatten_rep : ∀ (u v : ℕ), (List.replicate u (List.replicate v true)).flatten = List.replicate (u * v) true
  | 0, v => by simp
  | u + 1, v => by
    rw [List.replicate_succ, List.flatten_cons, flatten_rep u v, Nat.succ_mul, Nat.add_comm, List.replicate_add]

theorem cells_all_mask (u : ℕ) (f : Fin u → Fin u → ℕ) :
    CompetitorCountMask.mask (CompetitorSelectedCells.cells false f (fun _ _ => true)) =
      List.replicate (u * u) true := by
  unfold CompetitorSelectedCells.cells CompetitorSelectedCells.rect CompetitorCountMask.mask
  simp only [Bool.false_eq_true, if_false]
  rw [List.map_flatten]
  have e : (List.map (List.map Prod.fst) (List.ofFn fun i => List.ofFn fun j => ((true, f i j) : Bool × ℕ))) =
      List.replicate u (List.replicate u true) := by
    simp [List.map_ofFn, Function.comp_def, List.ofFn_const]
  rw [e, flatten_rep]

theorem cells_all_sum (u : ℕ) (f : Fin u → Fin u → ℕ) :
    (CompetitorCountMask.selected (CompetitorSelectedCells.cells false f (fun _ _ => true))).sum =
      ∑ i, ∑ j, f i j := by
  unfold CompetitorSelectedCells.cells CompetitorSelectedCells.rect CompetitorCountMask.selected
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [List.map_flatten, List.sum_flatten]
  simp [List.map_ofFn, Function.comp_def, List.sum_ofFn]

/-- **The printer and its all-selected sum**, from its entry bank: the sum port holds the framed sum of the printed
table's values. -/
theorem dc_step (wa : WilliamsAlgorithm) (r : MatrixScoreBatch.Request) (Q : ℕ) (f : Fin r.U → Fin r.U → ℕ)
    (hQ : Q ≤ CompetitorSameBucketColdDense.width r) (hf : ∀ i j, f i j < 2 ^ Q)
    (hc : ∀ i : Fin (r.U * r.U), Int.ModEq ((2 : ℤ) ^ Q)
      (SupplierPrinter.weightedDominance (MatrixScoreBatch.leftScore r) (MatrixScoreBatch.rightScore r)
        (MatrixScoreBatch.weight r) i.divNat i.modNat) (f i.divNat i.modNat)) :
    ∃ (H' : Fin (DT (producer wa)) → ℕ) (A' : Fin (DT (producer wa)) → List Bool),
      Step (P1Plan.DirectCount.machine wa) (P1Plan.DirectCount.budget wa r Q) (fun _ => 0)
        (dcBank (producer wa) (MatrixScoreBatch.physicalInput r) (List.replicate Q true)
          (List.replicate (r.U * r.U) true) false) H' A' ∧
      A' (dcS (producer wa)) =
        frame (SignedSortKey.binary (CompetitorSelectedCount.scalarWidth r Q) (∑ i, ∑ j, f i j)) := by
  obtain ⟨actual, hrun, _, _, h86, _⟩ := P1Plan.DirectCount.run wa r Q false f (fun _ _ => true) hQ
    (fun h => absurd h (by decide)) hf hc
  refine ⟨actual.final.heads, actual.final.tapes, ?_, ?_⟩
  · have hs := Step.of_run (p := P1Plan.DirectCount.machine wa) hrun rfl rfl
    rw [dcIn_eq, cells_all_mask] at hs
    exact hs
  · rw [dcS, h86, cells_all_sum]

end Printer

/-! ## The child's bank -/

section Layout
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
variable (wa : WilliamsAlgorithm)

noncomputable section

/-- The printer's tape count. -/
abbrev PD : ℕ := DT (producer wa)

/-- The child's bank: the printer's tapes, the compiler's 75 (from `PD`), the framer's and the metadata writer's
private tapes, the kept `1^Q` (`PD + 98`) and mask (`PD + 99`). -/
abbrev CN : ℕ := PD wa + 100

theorem cb_lt : CompetitorCountBanks.tapes (producer wa) + 3 < CompetitorCountTable.tapes (producer wa) := by
  show _ < CompetitorCountBanks.tapes (producer wa) + 124; omega

theorem ct_lt : CompetitorCountTable.tapes (producer wa) < PD wa := by
  show _ < CompetitorCountTable.tapes (producer wa) + 92; omega

/-- The metadata writer's tapes: `1^Q` source, cell, mask source, the three printer ports, register, log. -/
def prSl : Fin 8 → Fin (CN wa) :=
  ![⟨PD wa + 98, by show _ < PD wa + 100; omega⟩, ⟨PD wa + 96, by show _ < PD wa + 100; omega⟩, ⟨PD wa + 99, by show _ < PD wa + 100; omega⟩,
    ⟨CompetitorCountBanks.tapes (producer wa) + 1, by show _ < PD wa + 100; have := cb_lt wa; have := ct_lt wa; omega⟩,
    ⟨CompetitorCountBanks.tapes (producer wa) + 3, by show _ < PD wa + 100; have := cb_lt wa; have := ct_lt wa; omega⟩,
    ⟨CompetitorCountTable.tapes (producer wa), by show _ < PD wa + 100; have := ct_lt wa; omega⟩,
    ⟨PD wa + 97, by show _ < PD wa + 100; omega⟩, ⟨PD wa + 76, by show _ < PD wa + 100; omega⟩]

theorem prSl_val (j : Fin 8) : (prSl wa j).val =
    if j.val = 0 then PD wa + 98 else if j.val = 1 then PD wa + 96 else if j.val = 2 then PD wa + 99
    else if j.val = 3 then CompetitorCountBanks.tapes (producer wa) + 1
    else if j.val = 4 then CompetitorCountBanks.tapes (producer wa) + 3
    else if j.val = 5 then CompetitorCountTable.tapes (producer wa) else if j.val = 6 then PD wa + 97 else PD wa + 76 := by
  fin_cases j <;> rfl

theorem prSl_inj : Function.Injective (prSl wa) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [prSl_val, prSl_val] at hv
  have h1 := cb_lt wa
  have h2 := ct_lt wa
  apply Fin.ext
  have := i.isLt; have := j.isLt
  split_ifs at hv <;> omega

/-- The compiler's tapes. -/
def c3Sl : Fin 75 → Fin (CN wa) := fun i => ⟨PD wa + i.val, by show _ < PD wa + 100; have := i.isLt; omega⟩

theorem c3Sl_inj : Function.Injective (c3Sl wa) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp [c3Sl] at this; omega

/-- The framer's tapes: its raw stream is the compiler's output, its framed stream the printer's request port. -/
def frSl : Fin 22 → Fin (CN wa) := fun j =>
  if j.val = 0 then ⟨PD wa + 1, by show _ < PD wa + 100; omega⟩ else if j.val = 2 then ⟨0, by show _ < PD wa + 100; omega⟩ else ⟨PD wa + 74 + j.val, by show _ < PD wa + 100; have := j.isLt; omega⟩

theorem frSl_val (j : Fin 22) : (frSl wa j).val =
    if j.val = 0 then PD wa + 1 else if j.val = 2 then 0 else PD wa + 74 + j.val := by
  unfold frSl; split_ifs <;> rfl

theorem frSl_inj : Function.Injective (frSl wa) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [frSl_val, frSl_val] at hv
  apply Fin.ext
  have := i.isLt; have := j.isLt
  split_ifs at hv <;> omega

/-- The printer's tapes. -/
def dcSl : Fin (PD wa) → Fin (CN wa) := Fin.castAdd 100

theorem dcSl_inj : Function.Injective (dcSl wa) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa [dcSl] using this

/-- The child's entry bank: the compiler's framed input at `PD`, the kept `1^Q` and mask, everything else blank. -/
def childIn (cin qq uu : List Bool) : Fin (CN wa) → List Bool :=
  fun i => if i.val = PD wa then cin else if i.val = PD wa + 98 then qq else if i.val = PD wa + 99 then uu else []

end

end Layout

/-! ## The child's stages -/

section Stages
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
variable (wa : WilliamsAlgorithm)

noncomputable section

/-- The metadata writer as a machine. -/
def prepM := MaskedReset.machine (prepW.toProg.compile) (fun _ => true)

/-- The framer as a machine. -/
def frM := MaskedReset.machine (C4Frame.frameW.toProg.compile) (fun _ => true)

/-- The metadata writer's entry state. -/
def prepSt (qq uu : List Bool) : WState 4 1 := ⟨fun _ => 0, ![qq, uu, [], [], []], fun _ => 0, false⟩

def prepCost (q u : ℕ) : ℕ := 2 * (q * 7 + 1 + 1 + (1 + 1 + (u * 7 + 1))) + 2

theorem dockH_zero' {t u : ℕ} (slots : Fin t → Fin u) : dockH slots (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing slots (fun _ => 0) (fun _ => 0) (fun _ => rfl)

/-- **Stage 1, the printer's metadata.** -/
theorem stageP (cin : List Bool) (q u : ℕ) :
    ∃ AP : Fin 8 → List Bool,
      Step (RecoveryFocus.machine (prSl wa) prepM) (prepCost q u) (fun _ => 0)
        (childIn wa cin (List.replicate q true) (List.replicate u true)) (fun _ => 0)
        (install (prSl wa) (childIn wa cin (List.replicate q true) (List.replicate u true)) AP) ∧
      AP 0 = List.replicate q true ∧ AP 2 = List.replicate u true ∧ AP 3 = List.replicate q true ∧
      AP 4 = [false] ∧ AP 5 = List.replicate u true := by
  obtain ⟨τ, hw, t0, t1, t2, t3, t4⟩ := prepW_spec 0 q u (prepSt (List.replicate q true) (List.replicate u true))
    rfl rfl rfl rfl rfl (fun _ => rfl)
  obtain ⟨A', hs, hA'⟩ := wm_blank 0 (q * 7 + 1 + 1 + (1 + 1 + (u * 7 + 1))) prepW _ τ _ hw (fun _ => rfl)
    (fun _ => rfl) rfl le_rfl
  have hd := hs.dock (prSl wa) (prSl_inj wa) (fun _ => 0)
    (childIn wa cin (List.replicate q true) (List.replicate u true)) (fun _ => rfl) (by
      intro j
      have h1 := cb_lt wa
      have h2 := ct_lt wa
      fin_cases j <;>
        simp [childIn, prSl, wblank, role, Fin.addCases, sTape, cTape, rTape, prepSt] <;> (first | omega | rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]))
  rw [dockH_zero'] at hd
  refine ⟨A', hd, ?_, ?_, ?_, ?_, ?_⟩
  · have := hA' 0; rw [t0] at this; exact this
  · have := hA' 1; rw [t1] at this; exact this
  · have := hA' 2; rw [t2] at this; exact this
  · have := hA' 3; rw [t3] at this; exact this
  · have := hA' 4; rw [t4] at this; exact this

/-- **Stage 2, the compiler** (C3's `c3_run`). -/
theorem stageC (a : DecompositionAlgorithm) (R : CompilerMachine.Req.C3Req) (hR : R.Pre a)
    (B : Fin (CN wa) → List Bool)
    (hB : ∀ i : Fin 75, B (c3Sl wa i) = if i.val = 0 then frame (CompilerMachine.Req.c3Input a R) else []) :
    ∃ AC : Fin 75 → List Bool,
      Step (RecoveryFocus.machine (c3Sl wa) CompilerMachine.Top.c3M) (CompilerMachine.Top.c3Cost a R) (fun _ => 0) B
        (fun _ => 0) (install (c3Sl wa) B AC) ∧
      AC 1 = CompilerMachine.Req.reqWord R.dRow (R.p + 1) R.P.width R.cols (CompilerMachine.Req.c3v2Ref a R) := by
  obtain ⟨AC, hs, h1⟩ := CompilerMachine.Top.c3_run a R hR
  have hd := hs.dock (c3Sl wa) (c3Sl_inj wa) (fun _ => 0) B (fun _ => rfl) hB
  rw [dockH_zero'] at hd
  exact ⟨AC, hd, h1⟩

/-- The framer's entry state. -/
def frSt (w : List Bool) : WState 1 18 := ⟨fun _ => 0, ![w, []], fun _ => 0, false⟩

/-- **Stage 3, the framer.** -/
theorem stageF (r : MatrixScoreBatch.Request) (B : Fin (CN wa) → List Bool)
    (h0 : B (frSl wa 0) = MatrixScoreBatch.word r) (hz : ∀ j : Fin 22, j ≠ 0 → B (frSl wa j) = []) :
    ∃ AF : Fin 22 → List Bool,
      Step (RecoveryFocus.machine (frSl wa) frM) (2 * C4Frame.frameCost r + 2) (fun _ => 0) B (fun _ => 0)
        (install (frSl wa) B AF) ∧ AF 2 = frame (MatrixScoreBatch.word r) := by
  obtain ⟨τ, hw, _, t1⟩ := C4Frame.frameW_spec (C4Frame.frameCap r) r [] (frSt (MatrixScoreBatch.word r))
    (by simp [frSt]) rfl rfl rfl (fun _ => rfl) le_rfl
  obtain ⟨A', hs, hA'⟩ := wm_blank (C4Frame.frameCap r) (C4Frame.frameCost r) C4Frame.frameW _ τ _ hw
    (fun _ => rfl) (fun _ => rfl) rfl le_rfl
  have hd := hs.dock (frSl wa) (frSl_inj wa) (fun _ => 0) B (fun _ => rfl) (by
    intro j
    by_cases hj : j = 0
    · subst hj; rw [h0]; rfl
    · rw [hz j hj]
      have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
      revert hj'
      fin_cases j <;> simp [wblank, role, Fin.addCases, frSt])
  rw [dockH_zero'] at hd
  refine ⟨A', hd, ?_⟩
  have := hA' 1
  rw [t1] at this
  exact this

/-- **Stage 4, the printer and its sum** (base's `P1Plan.DirectCount`). -/
theorem stageD (r : MatrixScoreBatch.Request) (Q : ℕ) (f : Fin r.U → Fin r.U → ℕ)
    (hQ : Q ≤ CompetitorSameBucketColdDense.width r) (hf : ∀ i j, f i j < 2 ^ Q)
    (hc : ∀ i : Fin (r.U * r.U), Int.ModEq ((2 : ℤ) ^ Q)
      (SupplierPrinter.weightedDominance (MatrixScoreBatch.leftScore r) (MatrixScoreBatch.rightScore r)
        (MatrixScoreBatch.weight r) i.divNat i.modNat) (f i.divNat i.modNat))
    (B : Fin (CN wa) → List Bool)
    (hB : ∀ i : Fin (PD wa), B (dcSl wa i) = dcBank (producer wa) (MatrixScoreBatch.physicalInput r)
      (List.replicate Q true) (List.replicate (r.U * r.U) true) false i) :
    ∃ (H' : Fin (PD wa) → ℕ) (AD : Fin (PD wa) → List Bool),
      Step (RecoveryFocus.machine (dcSl wa) (P1Plan.DirectCount.machine wa)) (P1Plan.DirectCount.budget wa r Q)
        (fun _ => 0) B (dockH (dcSl wa) (fun _ => 0) H') (install (dcSl wa) B AD) ∧
      AD (dcS (producer wa)) =
        frame (SignedSortKey.binary (CompetitorSelectedCount.scalarWidth r Q) (∑ i, ∑ j, f i j)) := by
  obtain ⟨H', AD, hs, h86⟩ := dc_step wa r Q f hQ hf hc
  exact ⟨H', AD, hs.dock (dcSl wa) (dcSl_inj wa) (fun _ => 0) B (fun _ => rfl) hB, h86⟩

end

end Stages

/-! ## One child -/

section Child
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
variable (wa : WilliamsAlgorithm)

noncomputable section

/-- The least residue modulo `2^Q` (`alg:recovery`'s representative, P3:1968-1971). -/
def lres (x : ℤ) (Q : ℕ) : ℕ := (x % 2 ^ Q).toNat

theorem lres_cast (x : ℤ) (Q : ℕ) : (lres x Q : ℤ) = x % 2 ^ Q :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (by positivity))

theorem lres_lt (x : ℤ) (Q : ℕ) : lres x Q < 2 ^ Q := by
  have h := Int.emod_lt_of_pos x (show (0 : ℤ) < 2 ^ Q by positivity)
  rw [← lres_cast] at h
  exact_mod_cast h

/-- **One child's machine**: the metadata, the compiler, the framer, the printer with its sum. -/
def childM :=
  Composition.machine (RecoveryFocus.machine (prSl wa) prepM)
    (Composition.machine (RecoveryFocus.machine (c3Sl wa) CompilerMachine.Top.c3M)
      (Composition.machine (RecoveryFocus.machine (frSl wa) frM)
        (RecoveryFocus.machine (dcSl wa) (P1Plan.DirectCount.machine wa))))

/-- The child's sum port. -/
def childSum : Fin (CN wa) := dcSl wa (dcS (producer wa))

def childCost (a : DecompositionAlgorithm) (R : CompilerMachine.Req.C3Req) (r : MatrixScoreBatch.Request) : ℕ :=
  prepCost R.P.Q (2 ^ R.dRow * 2 ^ R.dRow) + 1 + (CompilerMachine.Top.c3Cost a R + 1 +
    (2 * C4Frame.frameCost r + 2 + 1 + P1Plan.DirectCount.budget wa r R.P.Q))

/-- The kept `1^Q` tape. -/
def childQQ : Fin (CN wa) := ⟨PD wa + 98, by show _ < PD wa + 100; omega⟩
/-- The kept mask tape. -/
def childUU : Fin (CN wa) := ⟨PD wa + 99, by show _ < PD wa + 100; omega⟩

end

end Child

end NearCubicWires.WireExponent3_5.PrimT.C4Pipe
