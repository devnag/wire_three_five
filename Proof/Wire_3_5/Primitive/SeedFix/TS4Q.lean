import Proof.Wire_3_5.Primitive.SeedFix.TS4P

/-! # thrStage4U, part 3: the prep as one machine (fill, program, every head back at `0`)

P3:3083-3086, P3:3425-3430 (as part 2): the prep of part 2 as a stage in NumsX's pattern (`NumsX.nums_step`): the fill
(`UnionMachine.FrontFill.fillP` from the count `1^W`), the program `p0W`, then PA's masked reset (`maskBlank`):

* `regSelS`, `rawS` (the framed request on stream `0`, `1^W` on stream `1`, everything else blank), `fillS`,
  **`fillS_exec`**; `p0P`, **`p0M`**, `p0StageCost`, **`p0_step`**.

Paper quantities of the main type: `|carriers|`, the THR cap `B_T(n)`, W6's count `V = W + (n+1)^{26}`, in unary. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

/-- The register tapes (the fill's targets). -/
def regSelS (j : Fin (LNS 0 + 2 + LNR)) : Bool := decide (LNS 0 + 2 ≤ j.val)

/-- The prep's entry bank: the framed request and `1^W`, everything else blank. -/
def rawS (w : List Bool) (W : ℕ) : Fin (LNS 0 + 2 + LNR) → List Bool := fun j =>
  if j = sTape (sk 0 0) then RepairOrdinary.frame w else if j = sTape (sk 0 1) then List.replicate W true else []

/-- The fill and the cell. -/
def fillS : Prog (LNS 0 + 2 + LNR) :=
  .seq (UnionMachine.FrontFill.fillP (sTape (sk 0 1)) (sTape (sk 0 2)) regSelS) (.act (writeAt cTape false) (fun _ => .stay))

theorem sTape_valS (s : Fin (LNS 0 + 1)) : (sTape (nr := LNR) s).val = if s.val = 0 then 0 else s.val + 1 := rfl

theorem sTape_eq_iffS (a b : Fin (LNS 0 + 1)) : sTape (nr := LNR) a = sTape b ↔ a = b :=
  ⟨fun h => sTape_inj h, fun h => h ▸ rfl⟩

theorem regSelS_s (s : Fin (LNS 0 + 1)) : regSelS (sTape (nr := LNR) s) = false := by
  have := s.isLt
  simp only [regSelS, sTape_valS, decide_eq_false_iff_not, not_le]
  split <;> omega

theorem regSelS_c : regSelS (cTape (ns := LNS 0) (nr := LNR)) = false := by
  unfold regSelS
  rw [show (cTape (ns := LNS 0) (nr := LNR)).val = 1 from rfl]
  decide

theorem regSelS_r (r : Fin LNR) : regSelS (rTape (ns := LNS 0) r) = true := by simp [regSelS, rTape]

theorem rawS_c (w : List Bool) (W : ℕ) : rawS w W cTape = [] := by
  simp [rawS, fun s => (sTape_ne_c (nr := LNR) (ns := LNS 0) s).symm]

theorem rawS_r (w : List Bool) (W : ℕ) (r : Fin LNR) : rawS w W (rTape r) = [] := by
  simp [rawS, fun s => (sTape_ne_r (nr := LNR) (ns := LNS 0) s r).symm]

theorem rawS_s (w : List Bool) (W : ℕ) (s : Fin (LNS 0 + 1)) : rawS w W (sTape s) =
    if s = sk 0 0 then RepairOrdinary.frame w else if s = sk 0 1 then List.replicate W true else [] := by
  simp only [rawS, sTape_eq_iffS]

/-- **The fill and the cell**: from the entry bank to the register-language state `σS` at capacity `2W + 2`. -/
theorem fillS_exec (w : List Bool) (W : ℕ) :
    Exec fillS ⟨fun _ => 0, rawS w W⟩ (wenc (2 * W + 2) (σS w W)) (11 * W + 20 + 1 + 1) := by
  have hca : sTape (nr := LNR) (sk 0 1) ≠ sTape (sk 0 2) := fun h => absurd (sTape_inj h) (by decide)
  have hA : ∀ i, UnionMachine.FrontFill.side (sTape (nr := LNR) (sk 0 2)) regSelS i → rawS w W i = [] := by
    intro i hi
    rcases hi with hi | hi
    · rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [regSelS_s] at hi; exact absurd hi (by decide)
      · rw [regSelS_c] at hi; exact absurd hi (by decide)
      · exact rawS_r w W r
    · subst hi
      rw [rawS_s]
      simp [d02.symm, d12.symm]
  have e1 := UnionMachine.FrontFill.fillP_exec (sTape (sk 0 1)) (sTape (sk 0 2)) regSelS (fun _ => 0) (rawS w W) hca
    (regSelS_s _) (regSelS_s _) W (by rw [rawS_s]; simp [d01.symm]) (fun _ _ => rfl) hA
  have e2 := Exec.act (UnionMachine.FrontFill.stB (sTape (sk 0 1)) (sTape (sk 0 2)) regSelS (fun _ => 0) (rawS w W) W 0)
    (writeAt (cTape (ns := LNS 0) (nr := LNR)) false) (fun _ => .stay)
  have eB : (UnionMachine.FrontFill.stB (sTape (sk 0 1)) (sTape (sk 0 2)) regSelS (fun _ => 0) (rawS w W) W 0).act
      (writeAt (cTape (ns := LNS 0) (nr := LNR)) false) (fun _ => .stay) = wenc (2 * W + 2) (σS w W) := by
    apply Bank.ext'
    · intro j
      simp only [Bank.act, HeadMove.apply, UnionMachine.FrontFill.stB]
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_H_s]
        split_ifs <;> simp [σS] <;> omega
      · rw [wenc_H_c]
        split_ifs <;> omega
      · rw [wenc_H_r]
        split_ifs <;> simp [σS] <;> omega
    · intro j
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_A_s]
        simp only [Bank.act, writeAt, sTape_ne_c, if_false, UnionMachine.FrontFill.stB, regSelS_s, Bool.false_eq_true,
          sTape_eq_iffS, rawS_s, σS]
        by_cases hx : s = sk 0 2
        · subst hx; simp [d02.symm, d12.symm]
        · simp [hx]
      · rw [wenc_A_c]
        simp only [Bank.act, writeAt, if_true, UnionMachine.FrontFill.stB, regSelS_c, Bool.false_eq_true, if_false,
          fun s => (sTape_ne_c (nr := LNR) (ns := LNS 0) s).symm, rawS_c]
        simp [σS, UnionMachine.FrontFill.side, regSelS_c, fun s => (sTape_ne_c (nr := LNR) (ns := LNS 0) s).symm]
        rfl
      · rw [wenc_A_r]
        simp only [Bank.act, writeAt, cTape_ne_r, (cTape_ne_r _).symm, if_false, UnionMachine.FrontFill.stB,
          regSelS_r, if_true, σS]
        rw [regTape_zero]
  rw [← eB]
  exact Exec.seq e1 e2

/-- The prep before its teardown: the fill, then the program. -/
noncomputable def p0P (cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) :=
  Composition.machine fillS.compile (p0W cr ζ Cδ C).toProg.compile

/-- **The prep** (every head back at `0`). -/
noncomputable def p0M (cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) :=
  MaskedReset.machine (p0P cr ζ Cδ C) (fun _ => true)

/-- The prep's cost before the teardown. -/
def p0StageCost (n cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (a nc Kb W : ℕ) : ℕ :=
  11 * W + 20 + 1 + 1 + 1 + p0Cost n cr h0 h1 Cδ C a nc Kb W

/-- **The prep's run**: from `frame (reqW n mb codes cc tl)` and `1^W`, every head back at `0`: `1^{|cc|}`, `1^{cap_T}`,
`1^{W + (n+1)^{26}}` on streams `3`, `4`, `5`; the request and the fill count stay. -/
theorem p0_step (cr n : ℕ) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (Kb W : ℕ)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hN : P0Need W n h0 h1 Cδ C cr codes.length cc.length Kb) :
    ∃ (tout : Fin (LNS 0 + 2 + LNR) → List Bool) (m : ℕ),
      Step (p0M cr ζ Cδ C) (2 * p0StageCost n cr h0 h1 Cδ C codes.length cc.length Kb W + 2) (fun _ => 0)
        (Fin.addCases (rawS (Data.reqW n mb codes cc tl) W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => 0)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape (sk 0 0)) = RepairOrdinary.frame (Data.reqW n mb codes cc tl) ∧
      tout (sTape (sk 0 1)) = List.replicate W true ∧ tout (sTape (sk 0 3)) = List.replicate cc.length true ∧
      tout (sTape (sk 0 4)) = List.replicate (capTOf cr n h0 h1 Cδ C) true ∧
      tout (sTape (sk 0 5)) = List.replicate (W + (n + 1) ^ 26) true := by
  have s0 := Exec.step (fillS_exec (Data.reqW n mb codes cc tl) W)
  obtain ⟨σF, c, hx, o0, o1, o3, o4, o5, hc⟩ := p0_spec cr n h0 h1 Cδ C mb codes cc tl Kb W hKb hN
  have s1 := Exec.step (WExec.exec (2 * W + 2) hx)
  have core : Step (p0P cr ζ Cδ C) (p0StageCost n cr h0 h1 Cδ C codes.length cc.length Kb W) (fun _ => 0)
      (rawS (Data.reqW n mb codes cc tl) W) (wenc (2 * W + 2) σF).H (wenc (2 * W + 2) σF).A :=
    (s0.seq s1).enlarge (by unfold p0StageCost; omega)
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (LNS 0 + 2 + LNR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc (2 * W + 2) σF).H i)
      (fun _ : Fin 1 => 0) : Fin (LNS 0 + 2 + LNR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  refine ⟨(wenc (2 * W + 2) σF).A, m, (hm.congr_in eh rfl).congr eh' rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wenc_A_s, o0]
  · rw [wenc_A_s, o1]
  · rw [wenc_A_s, o3]
  · rw [wenc_A_s, o4]
  · rw [wenc_A_s, o5]

end NearCubicWires.WireExponent3_5.PrimT.TS4
