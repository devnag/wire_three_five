import Proof.Wire_3_5.Primitive.SeedFix.C4EnumDock
import Proof.Wire_3_5.Primitive.SeedFix.C4Iface

/-! # SEEDFIX C4.L, one child as a machine: print, assemble, compile, sum (P3:3034-3037)

"For each candidate child prefix, print its signed equation expression, reduce modulo the chosen power of two at each
column, and sum the recovered integers" (P3:3034-3036). The child of bit `b` of the prefix `p` is three docked stages
on `A.t + (95 + CN)` tapes, under base's masked reset (every head back at `0`, from a blank log):
1. the enumeration unit (`C4Dock.eu_step`): the printed objective `V = sampTerms … (p ++ [b])` as `exprWord V`, on the
   assembler's expression port;
2. the assembler (`C4Iface.AsmStage`, C6's): `frame (PRE ++ frame (exprWord V) ++ POST) = frame (c3Input R_V)`
   (`c3Input_split`) on the printer child's request tape;
3. the printer child (`C4Pipe.child_step`: the compiler, the framer, base's printer and its recovered sum).

* `pre`/`post`, **`c3Input_split`**: the compiler's input around its expression field;
* `mask_blank`: base's masked reset from a blank log;
* the layout (`asmSl`, `euSl`, `cmSl`), the entry bank `chInP`, the kept tapes `keepC`, the machines `coreM`/`chM`;
* **`core_step`**: the sum port holds `frame (binary W (chVal (p ++ [b])))`, the kept tapes unchanged;
* **`chFam`**: the child family (`C4Loop.ChildFam`) of the call, the enumeration's, the compiler's and the cost side
  conditions carried as hypotheses (C4.K).

Paper quantity of the main types: the recovered child sum `chVal` (the sum over the table of the least residues of
`2^{m−1}·V_{p ++ [b]}(z)`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Child
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.Sampler

noncomputable section

/-! ## The compiler's input around the expression -/

section Split
variable (a : DecompositionAlgorithm)

/-- The compiler's fields before the expression, framed. -/
def pre (R : CompilerMachine.Req.C3Req) : List Bool := ((CompilerMachine.Req.c3Fields a R).take 8).flatMap frame

/-- The compiler's fields after the expression, framed. -/
def post (R : CompilerMachine.Req.C3Req) : List Bool := ((CompilerMachine.Req.c3Fields a R).drop 9).flatMap frame

/-- The compiler's expression field is the list machine's `exprWord`. -/
theorem exprField_eq (V : Shared.IntExpression ℕ) :
    V.flatMap CompilerMachine.Poly.termRec ++ [false] = ListMachine.Rec.exprWord V := rfl

/-- **The compiler's input around its expression field.** -/
theorem c3Input_split (R : CompilerMachine.Req.C3Req) :
    CompilerMachine.Req.c3Input a R = pre a R ++ frame (ListMachine.Rec.exprWord R.V) ++ post a R := by
  rw [CompilerMachine.Req.c3Input_eq, ← exprField_eq]
  simp only [pre, post, CompilerMachine.Req.c3Fields, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

end Split

/-! ## The printer child with its request's word -/

section ChildW
open NearCubicWires.WireExponent3_5.PrimT.C4Pipe
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
variable (wa : WilliamsAlgorithm)

/-- `C4Pipe.child_step` with the printer request's word exposed (the argument of its step bound). -/
theorem child_step_w (a : DecompositionAlgorithm) (E : Cost.Envelope) (R : CompilerMachine.Req.C3Req)
    (hR : R.Pre a) (hQp : R.P.Q ≤ R.p) :
    ∃ r : MatrixScoreBatch.Request,
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R.dRow (R.p + 1) R.P.width R.cols
        (CompilerMachine.Req.c3v2Ref a R) ∧
      r.d = R.dRow ∧ r.p = R.p + 1 ∧ r.width = R.P.width ∧ r.cols = R.cols ∧
      ∃ (H' : Fin (CN wa) → ℕ) (A' : Fin (CN wa) → List Bool),
        Step (childM wa) (childCost wa a R r) (fun _ => 0)
          (childIn wa (frame (CompilerMachine.Req.c3Input a R)) (List.replicate R.P.Q true)
            (List.replicate (2 ^ R.dRow * 2 ^ R.dRow) true)) H' A' ∧
        A' (childSum wa) = frame (SignedSortKey.binary (CompetitorSelectedCount.scalarWidth r R.P.Q)
          (∑ i : Fin r.U, ∑ j : Fin r.U, lres (2 ^ (R.m - 1) *
            Shared.IntExpression.eval R.V (CompilerMachine.Req.atomVal R.P (r.phi i) (r.phi j))) R.P.Q)) ∧
        A' (childQQ wa) = List.replicate R.P.Q true ∧
        A' (childUU wa) = List.replicate (2 ^ R.dRow * 2 ^ R.dRow) true := by
  have he := CompilerMachine.Req.c3v2_err a E (fun _ => []) 0 R ⟨hR, by simp⟩
  simp only [CompilerMachine.Req.c3v2] at he
  obtain ⟨r, hw, _, hd, hp, _, hcols, _, hcong⟩ := he
  refine ⟨r, hw, hd, hp, by assumption, hcols, ?_⟩
  have h1 := cb_lt wa
  have h2 := ct_lt wa
  set q := R.P.Q with hq
  set u := 2 ^ R.dRow * 2 ^ R.dRow with hu
  have hU : r.U * r.U = u := by simp [MatrixScoreBatch.Request.U, hd, hu]
  set B0 := childIn wa (frame (CompilerMachine.Req.c3Input a R)) (List.replicate q true) (List.replicate u true)
    with hB0
  -- stage 1
  obtain ⟨AP, sP, p0, p2, p3, p4, p5⟩ := stageP wa (frame (CompilerMachine.Req.c3Input a R)) q u
  set B1 := install (prSl wa) B0 AP with hB1
  -- stage 2
  have hC : ∀ i : Fin 75, B1 (c3Sl wa i) = if i.val = 0 then frame (CompilerMachine.Req.c3Input a R) else [] := by
    intro i
    rw [hB1, install_other]
    · have := i.isLt
      simp only [hB0, childIn, c3Sl]
      split_ifs <;> first | rfl | omega
    · intro k hk
      have hv := congrArg Fin.val hk
      rw [prSl_val] at hv
      simp only [c3Sl] at hv
      have := i.isLt
      split_ifs at hv <;> omega
  obtain ⟨AC, sC, c1⟩ := stageC wa a R hR B1 hC
  set B2 := install (c3Sl wa) B1 AC with hB2
  -- stage 3
  have hF0 : B2 (frSl wa 0) = MatrixScoreBatch.word r := by
    have e : frSl wa 0 = c3Sl wa 1 := rfl
    rw [hB2, e, install_slot _ (c3Sl_inj wa), c1]
    exact hw.symm
  have hFz : ∀ j : Fin 22, j ≠ 0 → B2 (frSl wa j) = [] := by
    intro j hj
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hjv := frSl_val wa j
    have hjl := j.isLt
    have hn1 : (frSl wa j).val ≠ PD wa := by rw [hjv]; split_ifs <;> omega
    have hn2 : (frSl wa j).val ≠ PD wa + 98 := by rw [hjv]; split_ifs <;> omega
    have hn3 : (frSl wa j).val ≠ PD wa + 99 := by rw [hjv]; split_ifs <;> omega
    rw [hB2, install_other, hB1, install_other]
    · simp only [hB0, childIn]
      rw [if_neg hn1, if_neg hn2, if_neg hn3]
    · intro k hk
      have hv := congrArg Fin.val hk
      rw [prSl_val, hjv] at hv
      split_ifs at hv <;> omega
    · intro i hi
      have hv := congrArg Fin.val hi
      rw [hjv] at hv
      simp only [c3Sl] at hv
      have := i.isLt
      split_ifs at hv <;> omega
  obtain ⟨AF, sF, f2⟩ := stageF wa r B2 hF0 hFz
  set B3 := install (frSl wa) B2 AF with hB3
  -- stage 4
  have hQ : q ≤ CompetitorSameBucketColdDense.width r := by
    rw [CompetitorSameBucketColdDense.width_eq, hd, hp]; omega
  let f : Fin r.U → Fin r.U → ℕ := fun i j =>
    lres (2 ^ (R.m - 1) * Shared.IntExpression.eval R.V (CompilerMachine.Req.atomVal R.P (r.phi i) (r.phi j))) q
  have hf : ∀ i j, f i j < 2 ^ q := fun i j => lres_lt _ _
  have hc : ∀ i : Fin (r.U * r.U), Int.ModEq ((2 : ℤ) ^ q)
      (SupplierPrinter.weightedDominance (MatrixScoreBatch.leftScore r) (MatrixScoreBatch.rightScore r)
        (MatrixScoreBatch.weight r) i.divNat i.modNat) (f i.divNat i.modNat) := by
    intro i
    show _ ≡ ((lres _ q : ℕ) : ℤ) [ZMOD 2 ^ q]
    rw [lres_cast]
    exact (hcong i.divNat i.modNat).trans (Int.mod_modEq _ _).symm
  have hD : ∀ i : Fin (PD wa), B3 (dcSl wa i) = dcBank (producer wa) (MatrixScoreBatch.physicalInput r)
      (List.replicate q true) (List.replicate (r.U * r.U) true) false i := by
    intro i
    have hil := i.isLt
    by_cases hi0 : i.val = 0
    · have e : dcSl wa i = frSl wa 2 := by apply Fin.ext; simp [dcSl, frSl, hi0]
      rw [hB3, e, install_slot _ (frSl_inj wa), f2]
      simp [dcBank, hi0, MatrixScoreBatch.physicalInput]
    · rw [hB3, install_other, hB2, install_other]
      · by_cases hq3 : i.val = CompetitorCountBanks.tapes (producer wa) + 1
        · have e : dcSl wa i = prSl wa 3 := by apply Fin.ext; simp [dcSl, prSl, hq3]
          rw [hB1, e, install_slot _ (prSl_inj wa), p3]
          simp [dcBank, hq3]
        · by_cases hq4 : i.val = CompetitorCountBanks.tapes (producer wa) + 3
          · have e : dcSl wa i = prSl wa 4 := by apply Fin.ext; simp [dcSl, prSl, hq4]
            rw [hB1, e, install_slot _ (prSl_inj wa), p4]
            simp [dcBank, hq4]
          · by_cases hq5 : i.val = CompetitorCountTable.tapes (producer wa)
            · have e : dcSl wa i = prSl wa 5 := by apply Fin.ext; simp [dcSl, prSl, hq5]
              rw [hB1, e, install_slot _ (prSl_inj wa), p5, hU]
              simp only [dcBank]
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hq5]
            · rw [hB1, install_other]
              · have hb0 : B0 (dcSl wa i) = [] := by
                  simp only [hB0, childIn, dcSl, Fin.val_castAdd]
                  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                have hdb : dcBank (producer wa) (MatrixScoreBatch.physicalInput r) (List.replicate q true)
                    (List.replicate (r.U * r.U) true) false i = [] := by
                  simp only [dcBank]; rw [if_neg hi0, if_neg hq3, if_neg hq4, if_neg hq5]
                rw [hb0, hdb]
              · intro k hk
                have hv := congrArg Fin.val hk
                rw [prSl_val] at hv
                simp only [dcSl, Fin.val_castAdd] at hv
                split_ifs at hv <;> omega
      · intro j hj
        have hv := congrArg Fin.val hj
        simp only [c3Sl, dcSl, Fin.val_castAdd] at hv
        omega
      · intro j hj
        have hv := congrArg Fin.val hj
        rw [frSl_val] at hv
        simp only [dcSl, Fin.val_castAdd] at hv
        split_ifs at hv <;> omega
  obtain ⟨H', AD, sD, d86⟩ := stageD wa r q f hQ hf hc B3 hD
  refine ⟨_, _, Step.seq sP (Step.seq sC (Step.seq sF sD)), ?_, ?_, ?_⟩
  · rw [childSum, install_slot _ (dcSl_inj wa), d86]
  · rw [install_other, hB3, install_other, hB2, install_other, hB1]
    · have e : childQQ wa = prSl wa 0 := rfl
      rw [e, install_slot _ (prSl_inj wa), p0]
    · intro i hi; have hv := congrArg Fin.val hi; simp only [c3Sl, childQQ] at hv; omega
    · intro j hj; have hv := congrArg Fin.val hj; rw [frSl_val] at hv; simp only [childQQ] at hv
      have := j.isLt; split_ifs at hv <;> omega
    · intro i hi; have hv := congrArg Fin.val hi; simp only [dcSl, childQQ, Fin.val_castAdd] at hv
      have := i.isLt; omega
  · rw [install_other, hB3, install_other, hB2, install_other, hB1]
    · have e : childUU wa = prSl wa 2 := rfl
      rw [e, install_slot _ (prSl_inj wa), p2]
    · intro i hi; have hv := congrArg Fin.val hi; simp only [c3Sl, childUU] at hv; omega
    · intro j hj; have hv := congrArg Fin.val hj; rw [frSl_val] at hv; simp only [childUU] at hv
      have := j.isLt; split_ifs at hv <;> omega
    · intro i hi; have hv := congrArg Fin.val hi; simp only [dcSl, childUU, Fin.val_castAdd] at hv
      have := i.isLt; omega


end ChildW

/-! ## Heads back at `0` from a blank log -/

/-- **Base's masked reset from a blank log**: a run from heads at `0` becomes, under the masked reset with a blank
log, a run back to heads at `0` with the same tapes. -/
theorem mask_blank {t s : ℕ} {p : Machine t s} {n : ℕ} {tin : Fin t → List Bool} {hout : Fin t → ℕ}
    {tout : Fin t → List Bool} (h : Step p n (fun _ => 0) tin hout tout) :
    ∃ A' : Fin (t + 1) → List Bool,
      Step (MaskedReset.machine p (fun _ => true)) (2 * n + 2) (fun _ => 0) (Fin.addCases tin (fun _ : Fin 1 => []))
        (fun _ => 0) A' ∧ ∀ i, A' (Fin.castAdd 1 i) = tout i := by
  have hm := h.mask (cap := n) (fun _ => true) (fun _ _ => rfl) le_rfl
  have e1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (t + 1) → ℕ) = fun _ => 0 := by
    funext i; induction i using Fin.addCases <;> simp
  have e2 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else hout i) (fun _ : Fin 1 => 0) :
      Fin (t + 1) → ℕ) = fun _ => 0 := by
    funext i; induction i using Fin.addCases <;> simp
  rw [e1, e2] at hm
  let caps : Fin (t + 1) → ℕ := Fin.addCases (fun _ => 0) (fun _ => n)
  have hpad : Fin.addCases tin (fun _ : Fin 1 => List.replicate n false) =
      fun i => ZeroPadding.pad (caps i) (Fin.addCases tin (fun _ : Fin 1 => ([] : List Bool)) i) := by
    funext i
    induction i using Fin.addCases <;> simp [caps, ZeroPadding.pad]
  obtain ⟨src, hsrc, hh, ht, hsteps⟩ := hm
  have hcfg : (⟨(MaskedReset.machine p (fun _ => true)).start, fun _ => 0,
      Fin.addCases tin (fun _ : Fin 1 => List.replicate n false)⟩ : Configuration (t + 1) _) =
      ZeroPadding.config caps ⟨(MaskedReset.machine p (fun _ => true)).start, fun _ => 0,
        Fin.addCases tin (fun _ : Fin 1 => [])⟩ := by
    rw [hpad]; rfl
  rw [hcfg] at hsrc
  obtain ⟨r, hr, hcf, hst, _⟩ := ZeroPadding.run_unpad _ _ _ _ src hsrc
  have hheads : r.final.heads = fun _ => 0 := by
    have := congrArg Configuration.heads hcf
    simp only [ZeroPadding.config] at this
    rw [this, hh]
  refine ⟨r.final.tapes, ⟨r, hr, hheads, rfl, by omega⟩, ?_⟩
  intro i
  have h1 := congrFun (congrArg Configuration.tapes hcf) (Fin.castAdd 1 i)
  simp only [ZeroPadding.config] at h1
  rw [ht] at h1
  simp only [caps, Fin.addCases_left, ZeroPadding.pad_zero] at h1
  exact h1

/-! ## The layout -/

section Layout
variable (A : C4Iface.AsmStage) (wa : WilliamsAlgorithm)

/-- The child's tapes: the assembler's, the enumeration unit's, the printer child's. -/
abbrev CT : ℕ := A.t + (C4Dock.EU + C4Pipe.CN wa)

/-- The printer child's request tape. -/
def pdT : Fin (C4Pipe.CN wa) := ⟨C4Pipe.PD wa, by show C4Pipe.PD wa < C4Pipe.PD wa + 100; omega⟩

/-- The assembler's tapes. -/
def asmSl (i : Fin A.t) : Fin (CT A wa) := Fin.castAdd _ i

/-- The enumeration unit's tapes: its OUT tape is the assembler's expression port. -/
def euSl (j : Fin C4Dock.EU) : Fin (CT A wa) :=
  if j = C4Dock.aS 24 then Fin.castAdd _ A.pE else Fin.natAdd A.t (Fin.castAdd (C4Pipe.CN wa) j)

/-- The printer child's tapes: its request tape is the assembler's output port. -/
def cmSl (k : Fin (C4Pipe.CN wa)) : Fin (CT A wa) :=
  if k = pdT wa then Fin.castAdd _ A.pO else Fin.natAdd A.t (Fin.natAdd C4Dock.EU k)

theorem asmSl_val (i : Fin A.t) : (asmSl A wa i).val = i.val := rfl

theorem euSl_val (j : Fin C4Dock.EU) :
    (euSl A wa j).val = if j = C4Dock.aS 24 then A.pE.val else A.t + j.val := by
  unfold euSl; split_ifs <;> rfl

theorem cmSl_val (k : Fin (C4Pipe.CN wa)) :
    (cmSl A wa k).val = if k = pdT wa then A.pO.val else A.t + (C4Dock.EU + k.val) := by
  unfold cmSl; split_ifs <;> rfl

theorem asmSl_inj : Function.Injective (asmSl A wa) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [asmSl_val, asmSl_val] at hv
  exact Fin.ext hv

theorem euSl_inj : Function.Injective (euSl A wa) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [euSl_val, euSl_val] at hv
  have := A.pE.isLt
  split_ifs at hv with hi hj hj
  · rw [hi, hj]
  · exfalso; omega
  · exfalso; omega
  · exact Fin.ext (by omega)

theorem cmSl_inj : Function.Injective (cmSl A wa) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [cmSl_val, cmSl_val] at hv
  have := A.pO.isLt
  split_ifs at hv with hi hj hj
  · rw [hi, hj]
  · exfalso; omega
  · exfalso; omega
  · exact Fin.ext (by omega)

theorem eu_ne_asm (j : Fin C4Dock.EU) (i : Fin A.t) (hi : i ≠ A.pE) : euSl A wa j ≠ asmSl A wa i := by
  intro e
  have hv := congrArg Fin.val e
  rw [euSl_val, asmSl_val] at hv
  have := i.isLt
  split_ifs at hv
  · exact hi (Fin.ext hv.symm)
  · omega

theorem cm_ne_asm (k : Fin (C4Pipe.CN wa)) (i : Fin A.t) (hi : i ≠ A.pO) : cmSl A wa k ≠ asmSl A wa i := by
  intro e
  have hv := congrArg Fin.val e
  rw [cmSl_val, asmSl_val] at hv
  have := i.isLt
  split_ifs at hv
  · exact hi (Fin.ext hv.symm)
  · omega

theorem cm_ne_eu (k : Fin (C4Pipe.CN wa)) (j : Fin C4Dock.EU) : cmSl A wa k ≠ euSl A wa j := by
  intro e
  have hv := congrArg Fin.val e
  rw [cmSl_val, euSl_val] at hv
  have := A.pO.isLt
  have := A.pE.isLt
  have := j.isLt
  have hOE : A.pO.val ≠ A.pE.val := fun h => A.hEO (Fin.ext h.symm)
  split_ifs at hv <;> omega

/-- The child's kept tapes: the assembler's two field words; the arm's rulers and prefix and the unit's constants;
the printer child's `1^Q` and mask. -/
def keepC : Fin (CT A wa) → Bool :=
  Fin.addCases (fun i => decide (i = A.pA ∨ i = A.pB))
    (Fin.addCases (fun j => decide ((j.val ≤ 11 ∧ j.val ≠ 1) ∨ (67 ≤ j.val ∧ j.val < 84)))
      (fun k => decide (k = C4Pipe.childQQ wa ∨ k = C4Pipe.childUU wa)))

variable (PRE POST qq uu : List Bool)

/-- The assembler region's entry: the two field words on their ports. -/
def asmK (i : Fin A.t) : List Bool := if i = A.pA then frame PRE else if i = A.pB then frame POST else []

/-- **The child's entry bank**: the assembler's two field words, the enumeration unit's entry bank `eIn`, the
printer child's kept `1^Q` and mask. -/
def chIn (eIn : Fin C4Dock.EU → List Bool) : Fin (CT A wa) → List Bool :=
  Fin.addCases (asmK A PRE POST) (Fin.addCases eIn (C4Pipe.childIn wa [] qq uu))

end Layout

/-! ## The enumeration unit's entry bank, tape by tape -/

section EuIn
variable (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT : ℕ)

/-- Off the kept tapes, the unit's entry bank is blank. -/
theorem euIn_other (p : List Bool) (j : Fin C4Dock.EU)
    (hj : ¬ ((j.val ≤ 11 ∧ j.val ≠ 1) ∨ (67 ≤ j.val ∧ j.val < 84))) : C4Dock.euIn P ents TWd Cap nT p j = [] := by
  fin_cases j <;> first | rfl | (exfalso; revert hj; decide)

/-- Off the prefix tape, the unit's entry bank does not depend on the prefix. -/
theorem euIn_pfx (p : List Bool) (j : Fin C4Dock.EU) (hj : j ≠ C4Dock.aS 10) :
    C4Dock.euIn P ents TWd Cap nT p j = C4Dock.euIn P ents TWd Cap nT [] j := by
  fin_cases j <;> first | rfl | (exfalso; exact hj rfl)

theorem euIn_aS10 (p : List Bool) : C4Dock.euIn P ents TWd Cap nT p (C4Dock.aS 10) = frame p := rfl

end EuIn

/-! ## The child's run -/

section Run
variable (A : C4Iface.AsmStage) (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm)
  (R0 : CompilerMachine.Req.C3Req) (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT Rn K : ℕ)
  (batch : List SeedFix.SExpr)

/-- The printed objective of the child prefix `p'`. -/
def chV (p' : List Bool) : SeedFix.SExpr := SeedFix.sampTerms P nT Rn batch p'.length (SeedFix.listNum p')

/-- The compiler's request of the child prefix `p'`: the call's request with the child's expression. -/
def chR (p' : List Bool) : CompilerMachine.Req.C3Req := { R0 with V := chV P nT Rn batch p' }

/-- **The recovered child sum**: over the table positions, the least residues of `2^{m−1}·V_{p'}(z)`. -/
def chVal (p' : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (2 ^ R0.dRow), ∑ j ∈ Finset.range (2 ^ R0.dRow),
    C4Pipe.lres (2 ^ (R0.m - 1) * Shared.IntExpression.eval (chV P nT Rn batch p')
      (CompilerMachine.Req.atomVal R0.P (MatrixScorePhi.value R0.cols i) (MatrixScorePhi.value R0.cols j))) R0.P.Q

/-- The sum port's width (`scalarWidth`): `Q + 2·dRow + 2·(p+1) + 4`. -/
def chW : ℕ := R0.P.Q + (2 * R0.dRow + 2 * (R0.p + 1) + 4)

theorem chVal_lt (p' : List Bool) : chVal R0 P nT Rn batch p' < 2 ^ chW R0 := by
  have h1 : chVal R0 P nT Rn batch p' ≤ 2 ^ R0.dRow * (2 ^ R0.dRow * (2 ^ R0.P.Q - 1)) := by
    unfold chVal
    calc _ ≤ ∑ i ∈ Finset.range (2 ^ R0.dRow), ∑ j ∈ Finset.range (2 ^ R0.dRow), (2 ^ R0.P.Q - 1) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Nat.le_sub_one_of_lt (C4Pipe.lres_lt _ _)
      _ = _ := by simp
  have hq := Nat.two_pow_pos R0.P.Q
  have hd := Nat.two_pow_pos R0.dRow
  have h2 : 2 ^ R0.dRow * (2 ^ R0.dRow * (2 ^ R0.P.Q - 1)) < 2 ^ R0.dRow * (2 ^ R0.dRow * 2 ^ R0.P.Q) := by
    apply Nat.mul_lt_mul_of_pos_left _ hd
    apply Nat.mul_lt_mul_of_pos_left _ hd
    omega
  have h3 : 2 ^ R0.dRow * (2 ^ R0.dRow * 2 ^ R0.P.Q) ≤ 2 ^ chW R0 := by
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by unfold chW; omega)
  omega

/-- The child's entry bank of the prefix `p`. -/
def chInP (p : List Bool) : Fin (CT A wa) → List Bool :=
  chIn A wa (pre a R0) (post a R0) (List.replicate R0.P.Q true) (List.replicate (2 ^ R0.dRow * 2 ^ R0.dRow) true)
    (C4Dock.euIn P ents TWd Cap nT p)

/-- The child's three stages. -/
noncomputable def coreM (b : Bool) :=
  Composition.machine (RecoveryFocus.machine (euSl A wa) (C4Dock.euM b))
    (Composition.machine (RecoveryFocus.machine (asmSl A wa) A.M) (RecoveryFocus.machine (cmSl A wa) (C4Pipe.childM wa)))

/-- **The child of bit `b`**: the three stages under base's masked reset. -/
noncomputable def chM (b : Bool) := MaskedReset.machine (coreM A wa b) (fun _ => true)

/-- The stages' step bound at the child prefix `p'` and the printer's request `r`. -/
def coreCost (p' : List Bool) (r : MatrixScoreBatch.Request) : ℕ :=
  C4Dock.euCost P TWd Cap nT K + 1 + (C4Iface.asmCost (pre a R0) (post a R0) (chV P nT Rn batch p') + 1 +
    C4Pipe.childCost wa a (chR R0 P nT Rn batch p') r)

/-- The child's sum port. -/
def sumT : Fin (CT A wa) := cmSl A wa (C4Pipe.childSum wa)

theorem sum_fin_range (U : ℕ) (g : ℕ → ℕ → ℕ) :
    (∑ i : Fin U, ∑ j : Fin U, g i j) = ∑ i ∈ Finset.range U, ∑ j ∈ Finset.range U, g i j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin U, g i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fin.sum_univ_eq_sum_range (g i) U

theorem childSum_ne : C4Pipe.childSum wa ≠ pdT wa := by
  intro e
  have hv := congrArg Fin.val e
  simp only [C4Pipe.childSum, C4Pipe.dcSl, pdT, Fin.val_castAdd] at hv
  have := (C4Pipe.dcS (RepairOrdinary.CompetitorCrossScheduler.producer wa)).isLt
  simp only [C4Pipe.DT, C4Pipe.PD] at this hv
  omega

theorem childQQ_ne : C4Pipe.childQQ wa ≠ pdT wa := by
  intro e; have hv := congrArg Fin.val e; simp [C4Pipe.childQQ, pdT] at hv

theorem childUU_ne : C4Pipe.childUU wa ≠ pdT wa := by
  intro e; have hv := congrArg Fin.val e; simp [C4Pipe.childUU, pdT] at hv

/-- **The child's three stages**: the sum port holds `frame (binary W (chVal (p ++ [b])))`; the kept tapes are
unchanged. -/
theorem core_step (E : Cost.Envelope) (b : Bool) (p : List Bool) (hp : p.length + 1 ≤ 8 * P.ell)
    (ok : C4Dock.EnumOk P ents TWd Cap nT Rn K batch (p ++ [b]))
    (hR : (chR R0 P nT Rn batch (p ++ [b])).Pre a) (hQp : R0.P.Q ≤ R0.p) :
    ∃ r : MatrixScoreBatch.Request,
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
        (CompilerMachine.Req.c3v2Ref a (chR R0 P nT Rn batch (p ++ [b]))) ∧
      ∃ (H' : Fin (CT A wa) → ℕ) (A' : Fin (CT A wa) → List Bool),
        Step (coreM A wa b) (coreCost wa a R0 P TWd Cap nT Rn K batch (p ++ [b]) r) (fun _ => 0)
          (chInP A wa a R0 P ents TWd Cap nT p) H' A' ∧
        A' (sumT A wa) = frame (binary (chW R0) (chVal R0 P nT Rn batch (p ++ [b]))) ∧
        ∀ i, keepC A wa i = true → A' i = chInP A wa a R0 P ents TWd Cap nT p i := by
  -- 1: the enumeration unit
  obtain ⟨Ae, se, hOut, hLow, hKc⟩ := C4Dock.eu_step P ents TWd Cap nT Rn K batch b p hp ok
  set B0 := chInP A wa a R0 P ents TWd Cap nT p with hB0
  have h0 : ∀ j, B0 (euSl A wa j) = C4Dock.euIn P ents TWd Cap nT p j := by
    intro j
    by_cases hj : j = C4Dock.aS 24
    · have e : euSl A wa j = Fin.castAdd _ A.pE := by rw [euSl, if_pos hj]
      rw [e, hj, euIn_other P ents TWd Cap nT p _ (by decide)]
      simp [hB0, chInP, chIn, asmK, Ne.symm A.hAE, Ne.symm A.hBE]
    · have e : euSl A wa j = Fin.natAdd A.t (Fin.castAdd (C4Pipe.CN wa) j) := by rw [euSl, if_neg hj]
      rw [e]
      simp [hB0, chInP, chIn]
  have s1 := se.dock (euSl A wa) (euSl_inj A wa) (fun _ => 0) B0 (fun _ => rfl) h0
  rw [C4Pipe.dockH_zero'] at s1
  set B1 := install (euSl A wa) B0 Ae with hB1
  -- 2: the assembler
  obtain ⟨Aa, sa, haO, haA, haB⟩ := A.run (pre a R0) (post a R0) (chV P nT Rn batch (p ++ [b])) []
  have h1 : ∀ i, B1 (asmSl A wa i) =
      C4Iface.asmIn A.pA A.pB A.pE (pre a R0) (post a R0) (chV P nT Rn batch (p ++ [b])) [] i := by
    intro i
    by_cases hiE : i = A.pE
    · have e : asmSl A wa i = euSl A wa (C4Dock.aS 24) := by rw [euSl, if_pos rfl, hiE]; rfl
      rw [e, hB1, install_slot _ (euSl_inj A wa), hOut, hiE]
      simp [C4Iface.asmIn, Ne.symm A.hAE, Ne.symm A.hBE, chV]
    · rw [hB1, install_other _ _ _ _ (fun j => eu_ne_asm A wa j i hiE)]
      simp [hB0, chInP, chIn, asmSl, asmK, C4Iface.asmIn, hiE]
  have s2 := sa.dock (asmSl A wa) (asmSl_inj A wa) (fun _ => 0) B1 (fun _ => rfl) h1
  rw [C4Pipe.dockH_zero'] at s2
  set B2 := install (asmSl A wa) B1 Aa with hB2
  -- 3: the printer child
  obtain ⟨r, hw, hd, hpr, _, hcols, H', Ac, sc, hSum, hQQ, hUU⟩ :=
    child_step_w wa a E (chR R0 P nT Rn batch (p ++ [b])) hR hQp
  have h2 : ∀ k, B2 (cmSl A wa k) = C4Pipe.childIn wa
      (frame (CompilerMachine.Req.c3Input a (chR R0 P nT Rn batch (p ++ [b]))))
      (List.replicate (chR R0 P nT Rn batch (p ++ [b])).P.Q true)
      (List.replicate (2 ^ (chR R0 P nT Rn batch (p ++ [b])).dRow * 2 ^ (chR R0 P nT Rn batch (p ++ [b])).dRow) true)
      k := by
    intro k
    by_cases hk : k = pdT wa
    · have e : cmSl A wa k = asmSl A wa A.pO := by rw [cmSl, if_pos hk]; rfl
      have hpd : ∀ X y z, C4Pipe.childIn wa X y z (pdT wa) = X := fun X y z => by simp [C4Pipe.childIn, pdT]
      rw [e, hB2, install_slot _ (asmSl_inj A wa), haO, hk, hpd, c3Input_split]
      rfl
    · have e : cmSl A wa k = Fin.natAdd A.t (Fin.natAdd C4Dock.EU k) := by rw [cmSl, if_neg hk]
      have hne1 : ∀ i, asmSl A wa i ≠ cmSl A wa k := fun i e' => by
        have hv := congrArg Fin.val e'
        rw [asmSl_val, cmSl_val, if_neg hk] at hv
        have := i.isLt; omega
      have hne2 : ∀ j, euSl A wa j ≠ cmSl A wa k := fun j e' => cm_ne_eu A wa k j e'.symm
      rw [hB2, install_other _ _ _ _ hne1, hB1, install_other _ _ _ _ hne2, e]
      have hkv : k.val ≠ C4Pipe.PD wa := fun h => hk (Fin.ext h)
      simp [hB0, chInP, chIn, C4Pipe.childIn, hkv, chR]
  have s3 := sc.dock (cmSl A wa) (cmSl_inj A wa) (fun _ => 0) B2 (fun _ => rfl) h2
  refine ⟨r, hw, _, _, s1.seq (s2.seq s3), ?_, ?_⟩
  · -- the sum
    rw [sumT, install_slot _ (cmSl_inj A wa), hSum]
    have hW : CompetitorSelectedCount.scalarWidth r (chR R0 P nT Rn batch (p ++ [b])).P.Q = chW R0 := by
      unfold CompetitorSelectedCount.scalarWidth chW
      rw [CompetitorSelectedCount.extraWidth_eq, hd, hpr]
      rfl
    have hU : r.U = 2 ^ R0.dRow := by
      show 2 ^ r.d = 2 ^ R0.dRow
      rw [hd]
      rfl
    rw [hW, sum_fin_range r.U (fun i j => C4Pipe.lres (2 ^ ((chR R0 P nT Rn batch (p ++ [b])).m - 1) *
      Shared.IntExpression.eval (chR R0 P nT Rn batch (p ++ [b])).V
        (CompilerMachine.Req.atomVal (chR R0 P nT Rn batch (p ++ [b])).P (r.phi i) (r.phi j)))
      (chR R0 P nT Rn batch (p ++ [b])).P.Q), hU]
    simp only [MatrixScoreBatch.Request.phi, hcols]
    rfl
  · -- the kept tapes
    intro i hi
    refine Fin.addCases (motive := fun i => keepC A wa i = true → install (cmSl A wa) B2 Ac i = B0 i)
      (fun x hx => ?_) (fun y hy => ?_) i hi
    · -- the assembler's field words
      simp only [keepC, Fin.addCases_left, decide_eq_true_eq] at hx
      have hxO : x ≠ A.pO := by
        rcases hx with h | h <;> rw [h]
        · exact A.hAO
        · exact A.hBO
      have hc : ∀ k, cmSl A wa k ≠ Fin.castAdd _ x := fun k => cm_ne_asm A wa k x hxO
      rw [install_other _ _ _ _ hc]
      have e : (Fin.castAdd _ x : Fin (CT A wa)) = asmSl A wa x := rfl
      rw [e, hB2, install_slot _ (asmSl_inj A wa)]
      rcases hx with h | h
      · rw [h, haA]; simp [hB0, chInP, chIn, asmSl, asmK]
      · rw [h, haB]; simp [hB0, chInP, chIn, asmSl, asmK, A.hAB.symm]
    · refine Fin.addCases (motive := fun y => keepC A wa (Fin.natAdd A.t y) = true →
        install (cmSl A wa) B2 Ac (Fin.natAdd A.t y) = B0 (Fin.natAdd A.t y)) (fun j hj => ?_) (fun k hk => ?_) y hy
      · -- the unit's kept tapes
        simp only [keepC, Fin.addCases_right, Fin.addCases_left, decide_eq_true_eq] at hj
        have hj24 : j ≠ C4Dock.aS 24 := by
          intro e; rw [e] at hj; revert hj; decide
        have e : Fin.natAdd A.t (Fin.castAdd (C4Pipe.CN wa) j) = euSl A wa j := by rw [euSl, if_neg hj24]
        have hc : ∀ k, cmSl A wa k ≠ euSl A wa j := fun k => cm_ne_eu A wa k j
        have ha : ∀ i', asmSl A wa i' ≠ euSl A wa j := fun i' e' => by
          have hv := congrArg Fin.val e'
          rw [asmSl_val, euSl_val, if_neg hj24] at hv
          have := i'.isLt; omega
        rw [e, install_other _ _ _ _ hc, hB2, install_other _ _ _ _ ha, hB1, install_slot _ (euSl_inj A wa), h0]
        rcases hj with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · -- a ruler or the prefix: the arm's stream `d`
          have hd' : ∃ d : Fin (47 + 1), d.val ≤ 10 ∧ C4Dock.aS d = j := by
            by_cases hz : j.val = 0
            · exact ⟨0, by decide, Fin.ext (by rw [C4Dock.aS_val]; simp [hz])⟩
            · refine ⟨⟨j.val - 1, by omega⟩, by show j.val - 1 ≤ 10; omega, Fin.ext ?_⟩
              rw [C4Dock.aS_val]
              show (if j.val - 1 = 0 then 0 else j.val - 1 + 1) = j.val
              rw [if_neg (by omega)]
              omega
          obtain ⟨d, hd10, rfl⟩ := hd'
          exact hLow d hd10
        · -- a constant
          have hk' : ∃ k : Fin 17, C4Dock.kS k = j := ⟨⟨j.val - 67, by omega⟩, Fin.ext (by
            show 67 + (j.val - 67) = j.val; omega)⟩
          obtain ⟨k, rfl⟩ := hk'
          rw [hKc k]
          simp [C4Dock.euIn, C4Dock.kS]
      · -- the printer child's `1^Q` and mask
        simp only [keepC, Fin.addCases_right, decide_eq_true_eq] at hk
        have hkP : k ≠ pdT wa := by
          rcases hk with h | h <;> rw [h]
          · exact childQQ_ne wa
          · exact childUU_ne wa
        have e : Fin.natAdd A.t (Fin.natAdd C4Dock.EU k) = cmSl A wa k := by rw [cmSl, if_neg hkP]
        have hl : install (cmSl A wa) B2 Ac (Fin.natAdd A.t (Fin.natAdd C4Dock.EU k)) = Ac k := by
          rw [e, install_slot _ (cmSl_inj A wa)]
        rw [hl]
        rcases hk with h | h
        · rw [h, hQQ]
          simp only [hB0, chInP, chIn, Fin.addCases_right]
          simp [C4Pipe.childIn, C4Pipe.childQQ, chR]
        · rw [h, hUU]
          simp only [hB0, chInP, chIn, Fin.addCases_right]
          simp [C4Pipe.childIn, C4Pipe.childUU, chR]

end Run

/-! ## The child family -/

section Fam
variable (A : C4Iface.AsmStage) (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm)
  (R0 : CompilerMachine.Req.C3Req) (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT Rn K : ℕ)
  (batch : List SeedFix.SExpr)

/-- The child's prefix tape (the arm's stream `10`). -/
def pfxT : Fin (CT A wa + 1) := Fin.castAdd 1 (euSl A wa (C4Dock.aS 10))

/-- The child's sum port. -/
def sumP : Fin (CT A wa + 1) := Fin.castAdd 1 (sumT A wa)

/-- The child's kept tapes (the log is not kept). -/
def keepF : Fin (CT A wa + 1) → Bool := Fin.addCases (keepC A wa) (fun _ => false)

/-- The kept tapes' words. -/
def KF : Fin (CT A wa + 1) → List Bool := Fin.addCases (chInP A wa a R0 P ents TWd Cap nT []) (fun _ => [])

theorem euSl_aS10 : euSl A wa (C4Dock.aS 10) = Fin.natAdd A.t (Fin.castAdd (C4Pipe.CN wa) (C4Dock.aS 10)) := by
  rw [euSl, if_neg (by decide)]

theorem chInP_off (p : List Bool) (i : Fin (CT A wa)) (hk : keepC A wa i = false) :
    chInP A wa a R0 P ents TWd Cap nT p i = [] := by
  refine Fin.addCases (motive := fun i => keepC A wa i = false → chInP A wa a R0 P ents TWd Cap nT p i = [])
    (fun x hx => ?_) (fun y hy => ?_) i hk
  · simp only [keepC, Fin.addCases_left, decide_eq_false_iff_not, not_or] at hx
    simp [chInP, chIn, asmK, hx.1, hx.2]
  · refine Fin.addCases (motive := fun y => keepC A wa (Fin.natAdd A.t y) = false →
      chInP A wa a R0 P ents TWd Cap nT p (Fin.natAdd A.t y) = []) (fun j hj => ?_) (fun k hk => ?_) y hy
    · simp only [keepC, Fin.addCases_right, Fin.addCases_left, decide_eq_false_iff_not] at hj
      simp only [chInP, chIn, Fin.addCases_right, Fin.addCases_left]
      exact euIn_other P ents TWd Cap nT p j hj
    · simp only [keepC, Fin.addCases_right, decide_eq_false_iff_not, not_or] at hk
      simp only [chInP, chIn, Fin.addCases_right]
      have h1 : k.val ≠ C4Pipe.PD wa + 98 := fun h => hk.1 (Fin.ext h)
      have h2 : k.val ≠ C4Pipe.PD wa + 99 := fun h => hk.2 (Fin.ext h)
      simp [C4Pipe.childIn, h1, h2]

theorem chInP_pfx (p : List Bool) (i : Fin (CT A wa)) (hi : i ≠ euSl A wa (C4Dock.aS 10)) :
    chInP A wa a R0 P ents TWd Cap nT p i = chInP A wa a R0 P ents TWd Cap nT [] i := by
  refine Fin.addCases (motive := fun i => i ≠ euSl A wa (C4Dock.aS 10) →
    chInP A wa a R0 P ents TWd Cap nT p i = chInP A wa a R0 P ents TWd Cap nT [] i) (fun x _ => ?_) (fun y hy => ?_) i hi
  · simp [chInP, chIn]
  · refine Fin.addCases (motive := fun y => Fin.natAdd A.t y ≠ euSl A wa (C4Dock.aS 10) →
      chInP A wa a R0 P ents TWd Cap nT p (Fin.natAdd A.t y) = chInP A wa a R0 P ents TWd Cap nT [] (Fin.natAdd A.t y))
      (fun j hj => ?_) (fun k _ => ?_) y hy
    · simp only [chInP, chIn, Fin.addCases_right, Fin.addCases_left]
      apply euIn_pfx
      intro e
      apply hj
      rw [e, euSl_aS10]
    · simp [chInP, chIn]

/-- The child family's entry bank is the child's. -/
theorem cin_eq (p : List Bool) :
    C4Loop.cin (pfxT A wa) (keepF A wa) (KF A wa a R0 P ents TWd Cap nT) p =
      Fin.addCases (chInP A wa a R0 P ents TWd Cap nT p) (fun _ : Fin 1 => []) := by
  funext i
  unfold C4Loop.cin
  by_cases h1 : i = pfxT A wa
  · rw [if_pos h1, h1, pfxT, Fin.addCases_left, euSl_aS10]
    simp only [chInP, chIn, Fin.addCases_right, Fin.addCases_left]
    exact (euIn_aS10 P ents TWd Cap nT p).symm
  · rw [if_neg h1]
    refine Fin.addCases (motive := fun i => i ≠ pfxT A wa → (if keepF A wa i = true then
      KF A wa a R0 P ents TWd Cap nT i else []) = Fin.addCases (chInP A wa a R0 P ents TWd Cap nT p)
        (fun _ : Fin 1 => []) i) (fun x hx => ?_) (fun y _ => ?_) i h1
    · simp only [keepF, KF, Fin.addCases_left]
      have hx' : x ≠ euSl A wa (C4Dock.aS 10) := fun e => hx (by rw [e]; rfl)
      cases hk : keepC A wa x
      · simp [chInP_off A wa a R0 P ents TWd Cap nT p x hk]
      · simp [chInP_pfx A wa a R0 P ents TWd Cap nT p x hx']
    · simp [keepF, KF]

theorem keepF_pfx : keepF A wa (pfxT A wa) = true := by
  rw [pfxT, keepF, Fin.addCases_left, euSl_aS10, keepC, Fin.addCases_right, Fin.addCases_left]
  decide

theorem keepF_sum : keepF A wa (sumP A wa) = false := by
  have hne := childSum_ne wa
  have e : sumT A wa = Fin.natAdd A.t (Fin.natAdd C4Dock.EU (C4Pipe.childSum wa)) := by
    rw [sumT, cmSl, if_neg hne]
  rw [sumP, keepF, Fin.addCases_left, e, keepC, Fin.addCases_right, Fin.addCases_right]
  simp only [decide_eq_false_iff_not, not_or]
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [C4Pipe.childSum, C4Pipe.dcSl, C4Pipe.childQQ, Fin.val_castAdd] at hv
    have := (C4Pipe.dcS (RepairOrdinary.CompetitorCrossScheduler.producer wa)).isLt
    simp only [C4Pipe.DT, C4Pipe.PD] at this hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [C4Pipe.childSum, C4Pipe.dcSl, C4Pipe.childUU, Fin.val_castAdd] at hv
    have := (C4Pipe.dcS (RepairOrdinary.CompetitorCrossScheduler.producer wa)).isLt
    simp only [C4Pipe.DT, C4Pipe.PD] at this hv
    omega

/-- The two children at one state count (the arm's program has the same size for both bits). -/
noncomputable def chMs (b : Bool) : type_of% (chM A wa false) :=
  match b with
  | false => chM A wa false
  | true => chM A wa true

/-- **One child's run** from the child family's entry bank. -/
theorem ch_run (E : Cost.Envelope) (Kch : ℕ) (b : Bool) (p : List Bool) (hp : p.length < 8 * P.ell)
    (ok : C4Dock.EnumOk P ents TWd Cap nT Rn K batch (p ++ [b]))
    (hR : (chR R0 P nT Rn batch (p ++ [b])).Pre a) (hQp : R0.P.Q ≤ R0.p)
    (hcost : ∀ r : MatrixScoreBatch.Request,
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
        (CompilerMachine.Req.c3v2Ref a (chR R0 P nT Rn batch (p ++ [b]))) →
      coreCost wa a R0 P TWd Cap nT Rn K batch (p ++ [b]) r ≤ Kch) :
    ∃ A'' : Fin (CT A wa + 1) → List Bool,
      Step (chM A wa b) (2 * Kch + 2) (fun _ => 0)
        (C4Loop.cin (pfxT A wa) (keepF A wa) (KF A wa a R0 P ents TWd Cap nT) p) (fun _ => 0) A'' ∧
      A'' (sumP A wa) = frame (binary (chW R0) (chVal R0 P nT Rn batch (p ++ [b]))) ∧
      chVal R0 P nT Rn batch (p ++ [b]) < 2 ^ chW R0 ∧
      ∀ i, keepF A wa i = true → A'' i = C4Loop.cin (pfxT A wa) (keepF A wa) (KF A wa a R0 P ents TWd Cap nT) p i := by
  obtain ⟨r, hw, H', A', st, hS, hK'⟩ := core_step A wa a R0 P ents TWd Cap nT Rn K batch E b p (by omega) ok hR hQp
  obtain ⟨A'', st', hA''⟩ := mask_blank (st.enlarge (hcost r hw))
  refine ⟨A'', ?_, ?_, chVal_lt R0 P nT Rn batch (p ++ [b]), ?_⟩
  · rw [cin_eq]
    exact st'
  · rw [sumP, hA'', hS]
  · intro i hi
    rw [cin_eq]
    refine Fin.addCases (motive := fun i => keepF A wa i = true → A'' i =
      Fin.addCases (chInP A wa a R0 P ents TWd Cap nT p) (fun _ : Fin 1 => []) i) (fun x hx => ?_)
      (fun y hy => ?_) i hi
    · rw [hA'', Fin.addCases_left]
      exact hK' x (by simpa [keepF] using hx)
    · simp [keepF] at hy

/-- **The child family of the call** (`C4Loop.ChildFam`): one child machine per candidate bit, whose sum port holds
the recovered child sum `chVal (p ++ [b])` below `2^W`, the kept tapes unchanged, within `2·Kch + 2` steps. The
enumeration's side conditions (`hok`), the compiler's precondition (`hpre`), `Q ≤ p` and the stages' step bound
(`hcost`, at the printer request the compiler writes) are the hypotheses carried to C4.K. -/
def chFam (E : Cost.Envelope) (Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * P.ell → C4Dock.EnumOk P ents TWd Cap nT Rn K batch (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * P.ell → (chR R0 P nT Rn batch (p ++ [b])).Pre a)
    (hQp : R0.P.Q ≤ R0.p)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request), p.length < 8 * P.ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
        (CompilerMachine.Req.c3v2Ref a (chR R0 P nT Rn batch (p ++ [b]))) →
      coreCost wa a R0 P TWd Cap nT Rn K batch (p ++ [b]) r ≤ Kch) : C4Loop.ChildFam where
  t := CT A wa + 1
  s := _
  M := chMs A wa
  cost := 2 * Kch + 2
  PFX := pfxT A wa
  SUM := sumP A wa
  keep := keepF A wa
  hPFX := keepF_pfx A wa
  hSUM := keepF_sum A wa
  K := KF A wa a R0 P ents TWd Cap nT
  W := chW R0
  bound := 8 * P.ell
  val := chVal R0 P nT Rn batch
  run := by
    intro p b hp
    cases b
    · exact ch_run A wa a R0 P ents TWd Cap nT Rn K batch E Kch false p hp (hok p false hp) (hpre p false hp) hQp
        (fun r hw => hcost p false r hp hw)
    · exact ch_run A wa a R0 P ents TWd Cap nT Rn K batch E Kch true p hp (hok p true hp) (hpre p true hp) hQp
        (fun r hw => hcost p true r hp hw)

end Fam

end

end NearCubicWires.WireExponent3_5.PrimT.C4Child
