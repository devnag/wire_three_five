import Proof.Wire_3_5.Primitive.SeedFix.C4Val

/-! # SEEDFIX C4.L, the decision loop part 1: comparing the two children and appending the bit (P3:3035-3037)

"Choose a child with no larger sum" (P3:3035-3037; `SeedFix.greedyStep`: the bit is `true` iff the `true` child's sum is
smaller, ties to `false`). This module has the word programs of one decision after both children: `cmpW` copies the
second child's framed sum (on a reused tape: any tail) to a blank stream, compares it with the first child's sum
(C6's `RegRat.ltB`) and appends the resulting bit to the framed prefix; `copyS0W` keeps the first child's sum.

Paper quantity of the main type: the greedy decision `decide (v_true < v_false)` appended to the prefix
(**`cmpW_spec`**). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Loop
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

theorem frame_even : ∀ (p : List Bool) (k : ℕ), readTapeBit (frame p) (2 * k) = decide (k < p.length)
  | [], k => by cases k <;> simp [frame, readTapeBit]
  | b :: p, 0 => by simp [frame, readTapeBit]
  | b :: p, k + 1 => by
    have := frame_even p k
    simp only [readTapeBit] at this ⊢
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    show (true :: b :: frame p).getD (2 * k + 2) false = _
    simp only [List.getD_cons_succ, this, List.length_cons]
    simp

theorem write_last : ∀ (l : List Bool) (x b : Bool), writeTapeBit (l ++ [x]) l.length b = l ++ [b]
  | [], x, b => rfl
  | y :: l, x, b => by
    show writeTapeBit (y :: (l ++ [x])) (l.length + 1) b = y :: (l ++ [b])
    simp only [writeTapeBit, write_last l x b]

section Cmp
variable (cap : ℕ)

/-- Walk a framed word to its terminator. -/
def walkW (i : Fin 4) : WM 3 3 := .whs i (.seq (.fwd i) (.fwd i))

theorem walkW_spec (i : Fin 4) (p : List Bool) :
    ∀ (m k : ℕ) (σ : WState 3 3), k + m = p.length → σ.st i = frame p → σ.sh i = 2 * k →
      WExec cap (walkW i) σ (σ.seth i (2 * p.length)) (m * 5 + 1) := by
  intro m
  induction m with
  | zero =>
    intro k σ hk hs hh
    have hb : wbit σ i = false := by simp only [wbit, hs, hh, frame_even]; simp; omega
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [WState.seth_sh, Function.update_apply]; split_ifs <;> subst_vars <;> simp_all <;> omega
    · rfl
    · rfl
    · rfl
  | succ m ih =>
    intro k σ hk hs hh
    have hb : wbit σ i = true := by simp only [wbit, hs, hh, frame_even]; simp; omega
    have h1 := WExec.fwd (cap := cap) i σ
    have h2 := WExec.fwd (cap := cap) i (σ.seth i (σ.sh i + 1))
    have hrec := ih (k + 1) ((σ.seth i (σ.sh i + 1)).seth i ((σ.seth i (σ.sh i + 1)).sh i + 1)) (by omega)
      (by simp [hs]) (by simp [hh]; ring)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) hrec) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [WState.seth_sh, Function.update_apply]; split_ifs <;> simp_all
    · rfl
    · rfl
    · rfl

/-- Append the bit `F ≠ 0` to the framed prefix on stream `3`. -/
def appW : WM 3 3 :=
  .seq (walkW 3) (.seq (.wr 3 true) (.seq (.fwd 3) (.seq (.ifr 0 (.wr 3 true) (.wr 3 false)) (.seq (.fwd 3) (.wr 3 false)))))

theorem appW_spec (p : List Bool) (bit : Bool) (σ : WState 3 3) (hs : σ.st 3 = frame p) (hh : σ.sh 3 = 0)
    (hF : σ.val 0 = bit.toNat) :
    ∃ τ : WState 3 3, WExec cap appW σ τ (p.length * 5 + 1 + 1 + (1 + 1 + (1 + 1 + (2 + 1 + (1 + 1 + 1))))) ∧
      τ.st 3 = frame (p ++ [bit]) ∧ (∀ j, j ≠ 3 → τ.st j = σ.st j) ∧ τ.val = σ.val := by
  have s1 := walkW_spec cap 3 p p.length 0 σ (by omega) hs (by simp [hh])
  set σ1 := σ.seth 3 (2 * p.length) with hσ1
  have hfm : frame p = Streaming.marks p ++ [false] := C4Frame.frame_marks p
  have hml : (Streaming.marks p).length = 2 * p.length := C4Frame.marks_length p
  have s2 := WExec.wr (cap := cap) 3 true σ1
  have e2 : writeTapeBit (σ1.st 3) (σ1.sh 3) true = Streaming.marks p ++ [true] := by
    simp only [σ1, WState.seth_st, WState.seth_sh, Function.update_self, hs, hfm]
    rw [← hml, write_last]
  rw [e2] at s2
  set σ2 := σ1.sets 3 (Streaming.marks p ++ [true]) with hσ2
  have s3 := WExec.fwd (cap := cap) 3 σ2
  set σ3 := σ2.seth 3 (σ2.sh 3 + 1) with hσ3
  have hsh3 : σ3.sh 3 = (Streaming.marks p ++ [true]).length := by simp [σ3, σ2, σ1, hml]
  have s4 : WExec cap (.ifr 0 (.wr 3 true) (.wr 3 false)) σ3 (σ3.sets 3 (Streaming.marks p ++ [true, bit])) 2 := by
    have ew : ∀ b : Bool, writeTapeBit (σ3.st 3) (σ3.sh 3) b = Streaming.marks p ++ [true, b] := by
      intro b
      have : σ3.st 3 = Streaming.marks p ++ [true] := by simp [σ3, σ2]
      rw [this, hsh3, C4Pipe.write_end]; simp
    cases bit
    · have := WExec.ifrF (r := 0) (P := WM.wr 3 true) (by simp [σ3, σ2, σ1, hF]) (WExec.wr (cap := cap) 3 false σ3)
      rw [ew] at this; exact this
    · have := WExec.ifrT (r := 0) (Q := WM.wr 3 false) (by simp [σ3, σ2, σ1, hF]) (WExec.wr (cap := cap) 3 true σ3)
      rw [ew] at this; exact this
  set σ4 := σ3.sets 3 (Streaming.marks p ++ [true, bit]) with hσ4
  have s5 := WExec.fwd (cap := cap) 3 σ4
  set σ5 := σ4.seth 3 (σ4.sh 3 + 1) with hσ5
  have s6 := WExec.wr (cap := cap) 3 false σ5
  have e6 : writeTapeBit (σ5.st 3) (σ5.sh 3) false = frame (p ++ [bit]) := by
    have : σ5.st 3 = Streaming.marks p ++ [true, bit] := by simp [σ5, σ4]
    have hl : σ5.sh 3 = (Streaming.marks p ++ [true, bit]).length := by simp [σ5, σ4, hsh3]
    rw [this, hl, C4Pipe.write_end, C4Frame.frame_marks, PrimAsm.WriteNat.marks_append]
    simp [Streaming.marks]
  rw [e6] at s6
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6)))), ?_, ?_, ?_⟩
  · simp
  · intro j hj; simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hj]
  · simp [σ5, σ4, σ3, σ2, σ1]

end Cmp

section Cmp2
variable (cap : ℕ)

/-- **The comparison**: the second child's sum (stream `1`, any tail) is copied to stream `2`, compared with the first
child's sum (stream `0`) by `RegRat.ltB`, and the bit `sum₂ < sum₁` is appended to the framed prefix (stream `3`). -/
def cmpW : WM 3 3 :=
  .seq (HbM.copyFrameC 1 2 2) (.seq (WM.rewind 2 2) (.seq (UnionMachine.RegRat.ltB 2 0 0 1) appW))

def cmpCost (W : ℕ) (p : List Bool) : ℕ :=
  11 * (2 * W + 1) + 1 + (5 * (2 * W + 1) + 1 + 1 + (41 * W + 3 + 1 +
    (p.length * 5 + 1 + 1 + (1 + 1 + (1 + 1 + (2 + 1 + (1 + 1 + 1)))))))

theorem cmpW_spec (W v0 v1 : ℕ) (p tail : List Bool) (σ : WState 3 3) (h0 : σ.st 0 = frame (binary W v0))
    (h1 : σ.st 1 = frame (binary W v1) ++ tail) (h2 : σ.st 2 = []) (h3 : σ.st 3 = frame p)
    (hs : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) (hv0 : v0 < 2 ^ W) (hv1 : v1 < 2 ^ W)
    (hcap : 4 * W + 8 ≤ cap) :
    ∃ τ : WState 3 3, WExec cap cmpW σ τ (cmpCost W p) ∧ τ.st 3 = frame (p ++ [decide (v1 < v0)]) := by
  have hfl : (frame (binary W v1)).length = 2 * W + 1 := by rw [frame_length, binary_length]
  have s1 := HbM.copyFrameC_spec cap 1 2 (by decide) 2 [] (binary W v1) tail σ (by simp [h1]) (by simp [hs])
    (by simp [h2, hs]) (by rw [hv, hfl]; omega)
  rw [hfl] at s1
  set σ1 := PrimAsm.WriteNat.appendO (σ.seth 1 ([].length + (2 * W + 1))) 2 2 (frame (binary W v1)) with hσ1
  have v1r : σ1.val 2 = 2 * W + 1 := by simp [σ1, hv, hfl]
  have s2 := wrewind_spec cap 2 2 (2 * W + 1) σ1 v1r (by rw [v1r]; omega)
  set σ2 := (σ1.setv 2 0).seth 2 (σ1.sh 2 - (2 * W + 1)) with hσ2
  have s3 := UnionMachine.RegRat.ltB_spec cap W (A := 2) (B := 0) (by decide) (F := 0) (R := 1) (by decide) σ2 v1 v0
    ⟨by simp [σ2, σ1, h2], by simp [σ2, σ1, hs, hfl]⟩ ⟨by simp [σ2, σ1, h0], by simp [σ2, σ1, hs]⟩
    (by simp [σ2, σ1, hv]) (by simp [σ2, σ1, hv]) hv1 hv0 (by omega)
  set σ3 := σ2.setv 0 (decide (v1 < v0)).toNat with hσ3
  obtain ⟨τ, s4, t3, _, _⟩ := appW_spec cap p (decide (v1 < v0)) σ3 (by simp [σ3, σ2, σ1, h3])
    (by simp [σ3, σ2, σ1, hs]) (by simp [σ3])
  exact ⟨τ, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), t3⟩

end Cmp2

/-! ## A child family and one decision -/

/-- A child's entry bank: the framed prefix, the kept tapes, everything else blank. -/
def cin {t : ℕ} (PFX : Fin t) (keep : Fin t → Bool) (K : Fin t → List Bool) (p : List Bool) : Fin t → List Bool :=
  fun i => if i = PFX then frame p else if keep i then K i else []

/-- **A child family** (one decision's two children): one machine per candidate bit, from the framed prefix and the
kept tapes (every other tape blank, every head at `0`) to every head at `0`, the kept tapes unchanged, and the sum
port holding the child's value `val (p ++ [b])` below `2^W`. -/
structure ChildFam where
  t : ℕ
  s : ℕ
  M : Bool → Machine t s
  cost : ℕ
  PFX : Fin t
  SUM : Fin t
  keep : Fin t → Bool
  hPFX : keep PFX = true
  hSUM : keep SUM = false
  K : Fin t → List Bool
  W : ℕ
  bound : ℕ
  val : List Bool → ℕ
  run : ∀ (p : List Bool) (b : Bool), p.length < bound → ∃ A' : Fin t → List Bool,
    Step (M b) cost (fun _ => 0) (cin PFX keep K p) (fun _ => 0) A' ∧
      A' SUM = frame (binary W (val (p ++ [b]))) ∧ val (p ++ [b]) < 2 ^ W ∧
      ∀ i, keep i = true → A' i = cin PFX keep K p i

namespace ChildFam
variable (F : ChildFam)

noncomputable section

/-- The decision's bank: the child's tapes (the kept ones shared), the second child's scratch, the comparison's. -/
abbrev T : ℕ := 2 * F.t + 6

def sl0 : Fin F.t → Fin F.T := fun i => ⟨i.val, by show _ < 2 * F.t + 6; omega⟩

def sl1 : Fin F.t → Fin F.T := fun i =>
  if F.keep i then ⟨i.val, by show _ < 2 * F.t + 6; omega⟩ else ⟨F.t + i.val, by show _ < 2 * F.t + 6; omega⟩

theorem sl0_inj : Function.Injective F.sl0 := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa [sl0] using this

theorem sl1_val (i : Fin F.t) : (F.sl1 i).val = if F.keep i then i.val else F.t + i.val := by
  unfold sl1; split_ifs <;> rfl

theorem sl1_inj : Function.Injective F.sl1 := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [sl1_val, sl1_val] at hv
  have := i.isLt; have := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The comparison's tapes: the two sums, its work stream, the prefix, its cell, registers and log. -/
def cmpSl : Fin 9 → Fin F.T :=
  ![⟨F.SUM.val, by show _ < 2 * F.t + 6; have := F.SUM.isLt; omega⟩,
    ⟨2 * F.t + 1, by show _ < 2 * F.t + 6; omega⟩,
    ⟨F.t + F.SUM.val, by show _ < 2 * F.t + 6; have := F.SUM.isLt; omega⟩,
    ⟨2 * F.t, by show _ < 2 * F.t + 6; omega⟩,
    ⟨F.PFX.val, by show _ < 2 * F.t + 6; have := F.PFX.isLt; omega⟩,
    ⟨2 * F.t + 2, by show _ < 2 * F.t + 6; omega⟩, ⟨2 * F.t + 3, by show _ < 2 * F.t + 6; omega⟩,
    ⟨2 * F.t + 4, by show _ < 2 * F.t + 6; omega⟩, ⟨2 * F.t + 5, by show _ < 2 * F.t + 6; omega⟩]

theorem cmpSl_val (j : Fin 9) : (F.cmpSl j).val =
    if j.val = 0 then F.SUM.val else if j.val = 1 then 2 * F.t + 1 else if j.val = 2 then F.t + F.SUM.val
    else if j.val = 3 then 2 * F.t else if j.val = 4 then F.PFX.val else 2 * F.t + j.val - 3 := by
  fin_cases j <;> rfl

theorem sum_ne_pfx : F.SUM.val ≠ F.PFX.val := by
  intro h
  have e : F.SUM = F.PFX := Fin.ext h
  have h1 := F.hSUM
  rw [e, F.hPFX] at h1
  exact absurd h1 (by decide)

theorem cmpSl_inj : Function.Injective F.cmpSl := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [cmpSl_val, cmpSl_val] at hv
  have := i.isLt; have := j.isLt; have := F.SUM.isLt; have := F.PFX.isLt; have := F.sum_ne_pfx
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The comparison as a machine. -/
def cmpM := MaskedReset.machine (cmpW.toProg.compile) (fun _ => true)

/-- **One decision's machine**: child `false` on the shared bank, child `true` on its own scratch, the comparison. -/
def cellM :=
  Composition.machine (RecoveryFocus.machine F.sl0 (F.M false))
    (Composition.machine (RecoveryFocus.machine F.sl1 (F.M true)) (RecoveryFocus.machine F.cmpSl cmpM))

/-- The decision's entry bank (from blank scratch). -/
def cellIn (p : List Bool) : Fin F.T → List Bool :=
  fun i => if h : i.val < F.t then cin F.PFX F.keep F.K p ⟨i.val, h⟩ else []

/-- The comparison's entry state. -/
def cmpSt (w0 w1 p : List Bool) : WState 3 3 := ⟨fun _ => 0, ![w0, w1, [], p], fun _ => 0, false⟩

def cellCost : ℕ := F.cost + 1 + (F.cost + 1 + (2 * cmpCost F.W (List.replicate F.bound false) + 2))

theorem cmpCost_mono (W : ℕ) (p : List Bool) (h : p.length ≤ F.bound) :
    cmpCost W p ≤ cmpCost W (List.replicate F.bound false) := by
  unfold cmpCost; simp; omega

/-- **One decision** (from blank scratch): the prefix ends extended by the greedy bit
`decide (val (p ++ [true]) < val (p ++ [false]))`, the other kept tapes unchanged, every head at `0`. -/
theorem cell_step (p : List Bool) (hp : p.length < F.bound) :
    ∃ A' : Fin F.T → List Bool, Step F.cellM F.cellCost (fun _ => 0) (F.cellIn p) (fun _ => 0) A' ∧
      A' (F.sl0 F.PFX) = frame (p ++ [decide (F.val (p ++ [true]) < F.val (p ++ [false]))]) ∧
      ∀ i : Fin F.t, F.keep i = true → i ≠ F.PFX → A' (F.sl0 i) = F.K i := by
  obtain ⟨A0, st0, sum0, lt0, keep0⟩ := F.run p false hp
  obtain ⟨A1, st1, sum1, lt1, keep1⟩ := F.run p true hp
  have hPk := F.hPFX
  have hSk := F.hSUM
  have hsp := F.sum_ne_pfx
  have hSl := F.SUM.isLt
  have hPl := F.PFX.isLt
  -- the first child
  have d0 := st0.dock F.sl0 F.sl0_inj (fun _ => 0) (F.cellIn p) (fun _ => rfl) (by
    intro j; simp [cellIn, sl0, j.isLt])
  rw [C4Pipe.dockH_zero'] at d0
  set B1 := RecoveryRootRound.install F.sl0 (F.cellIn p) A0 with hB1
  -- the second child
  have hB1s : ∀ j : Fin F.t, B1 (F.sl1 j) = cin F.PFX F.keep F.K p j := by
    intro j
    by_cases hk : F.keep j = true
    · have e : F.sl1 j = F.sl0 j := by apply Fin.ext; rw [sl1_val, if_pos hk]; rfl
      rw [hB1, e, RecoveryRootRound.install_slot _ F.sl0_inj, keep0 j hk]
    · have hjP : j ≠ F.PFX := fun h => hk (h ▸ hPk)
      rw [hB1, RecoveryRootRound.install_other]
      · have hv : ¬ (F.sl1 j).val < F.t := by rw [sl1_val, if_neg hk]; omega
        simp only [cellIn, dif_neg hv, cin, if_neg hjP, if_neg hk]
      · intro i hi; have := congrArg Fin.val hi; rw [sl1_val, if_neg hk] at this; simp [sl0] at this; omega
  have d1 := st1.dock F.sl1 F.sl1_inj (fun _ => 0) B1 (fun _ => rfl) hB1s
  rw [C4Pipe.dockH_zero'] at d1
  set B2 := RecoveryRootRound.install F.sl1 B1 A1 with hB2
  -- the comparison
  set v0 := F.val (p ++ [false]) with hv0
  set v1 := F.val (p ++ [true]) with hv1
  obtain ⟨τ, hw, t3⟩ := cmpW_spec (4 * F.W + 8) F.W v0 v1 p [] (cmpSt (frame (binary F.W v0))
    (frame (binary F.W v1)) (frame p)) rfl (by simp [cmpSt]) rfl rfl (fun _ => rfl) (fun _ => rfl) lt0 lt1 le_rfl
  obtain ⟨AC, sC, hAC⟩ := C4Pipe.wm_blank (4 * F.W + 8) (cmpCost F.W p) cmpW _ τ _ hw (fun _ => rfl) (fun _ => rfl)
    rfl le_rfl
  have hk1 : ∀ i : Fin F.t, F.keep i = true → B2 (F.sl0 i) = cin F.PFX F.keep F.K p i := by
    intro i hk
    have e : F.sl0 i = F.sl1 i := by apply Fin.ext; rw [sl1_val, if_pos hk]; rfl
    rw [hB2, e, RecoveryRootRound.install_slot _ F.sl1_inj, keep1 i hk]
  have hfar : ∀ j : Fin 9, (F.cmpSl j).val ≥ 2 * F.t → B2 (F.cmpSl j) = [] := by
    intro j hj
    rw [hB2, RecoveryRootRound.install_other, hB1, RecoveryRootRound.install_other]
    · simp only [cellIn]; rw [dif_neg (by omega)]
    · intro i hi; have := congrArg Fin.val hi; simp only [sl0] at this; omega
    · intro i hi; have hv := congrArg Fin.val hi; rw [sl1_val] at hv; have hil := i.isLt; split_ifs at hv <;> omega
  have c0 : B2 (F.cmpSl 0) = frame (binary F.W v0) := by
    have e : F.cmpSl 0 = F.sl0 F.SUM := rfl
    rw [e, hB2, RecoveryRootRound.install_other, hB1, RecoveryRootRound.install_slot _ F.sl0_inj, sum0]
    intro i hi; have := congrArg Fin.val hi; rw [sl1_val] at this; simp only [sl0] at this
    split_ifs at this with hk
    · have : i = F.SUM := Fin.ext this
      rw [this, hSk] at hk; exact absurd hk (by decide)
    · omega
  have c2 : B2 (F.cmpSl 2) = frame (binary F.W v1) := by
    have e : F.cmpSl 2 = F.sl1 F.SUM := by apply Fin.ext; rw [sl1_val, if_neg (by rw [hSk]; decide)]; rfl
    rw [e, hB2, RecoveryRootRound.install_slot _ F.sl1_inj, sum1]
  have c4 : B2 (F.cmpSl 4) = frame p := by
    have e : F.cmpSl 4 = F.sl0 F.PFX := rfl
    rw [e, hk1 F.PFX hPk]
    simp [cin]
  have hin : Fin.addCases (motive := fun _ => List Bool)
      (C4Pipe.wblank (cmpSt (frame (binary F.W v0)) (frame (binary F.W v1)) (frame p)))
      (fun _ : Fin 1 => ([] : List Bool)) =
      ![frame (binary F.W v0), [], frame (binary F.W v1), [], frame p, [], [], [], []] := by
    funext j; fin_cases j <;> rfl
  have hB2c : ∀ j : Fin 9, B2 (F.cmpSl j) = Fin.addCases (motive := fun _ => List Bool)
      (C4Pipe.wblank (cmpSt (frame (binary F.W v0))
      (frame (binary F.W v1)) (frame p))) (fun _ : Fin 1 => []) j := by
    intro j
    rw [hin]
    fin_cases j
    · exact c0
    · exact hfar 1 (by show 2 * F.t + 1 ≥ _; omega)
    · exact c2
    · exact hfar 3 (by show 2 * F.t ≥ _; omega)
    · exact c4
    · exact hfar 5 (by show 2 * F.t + 2 ≥ _; omega)
    · exact hfar 6 (by show 2 * F.t + 3 ≥ _; omega)
    · exact hfar 7 (by show 2 * F.t + 4 ≥ _; omega)
    · exact hfar 8 (by show 2 * F.t + 5 ≥ _; omega)
  have d2 := sC.dock F.cmpSl F.cmpSl_inj (fun _ => 0) B2 (fun _ => rfl) hB2c
  rw [C4Pipe.dockH_zero'] at d2
  refine ⟨_, (Step.seq d0 (Step.seq d1 d2)).enlarge ?_, ?_, ?_⟩
  · unfold cellCost
    have := F.cmpCost_mono F.W p (by omega)
    omega
  · have e : F.sl0 F.PFX = F.cmpSl 4 := rfl
    rw [e, RecoveryRootRound.install_slot _ F.cmpSl_inj]
    have := hAC 3
    rw [t3] at this
    exact this
  · intro i hk hiP
    have hiS : i ≠ F.SUM := fun h => by rw [h, hSk] at hk; exact absurd hk (by decide)
    rw [RecoveryRootRound.install_other, hk1 i hk]
    · simp [cin, hiP, hk]
    · intro j hj
      have hv := congrArg Fin.val hj
      rw [cmpSl_val] at hv
      simp only [sl0] at hv
      have hiv : i.val ≠ F.SUM.val := fun h => hiS (Fin.ext h)
      have hiP' : i.val ≠ F.PFX.val := fun h => hiP (Fin.ext h)
      have := i.isLt
      have := j.isLt
      split_ifs at hv <;> omega

/-! ## The loop over the decisions -/

/-- The scratch of a decision: everything but the kept tapes. -/
def cellS : Fin F.T → Bool := fun i => if h : i.val < F.t then !F.keep ⟨i.val, h⟩ else true

/-- The child sums as integers (the greedy's printed sums). -/
def Rv (p : List Bool) : ℤ := (F.val p : ℤ)

/-- The prefix after `j` decisions: `greedyStep` iterated (`greedyLoop`'s form). -/
def gp (j : ℕ) : List Bool := (SeedFix.greedyStep F.Rv)^[j] []

theorem gp_length : ∀ j, (F.gp j).length = j
  | 0 => rfl
  | j + 1 => by
    rw [gp, Function.iterate_succ_apply']
    simp only [SeedFix.greedyStep, List.length_append, List.length_singleton]
    rw [← gp, gp_length j]

theorem gp_succ (j : ℕ) :
    F.gp (j + 1) = F.gp j ++ [decide (F.val (F.gp j ++ [true]) < F.val (F.gp j ++ [false]))] := by
  rw [gp, Function.iterate_succ_apply']
  simp only [SeedFix.greedyStep, Rv, Nat.cast_lt]
  rfl

/-- The decision's bank before decision `j`: the prefix `gp j`, the kept tapes, blank scratch of length `R`. -/
def src (R j : ℕ) : Fin F.T → List Bool := BlockPlatform.Scrub.blank F.cellS (F.cellIn (F.gp j)) R

/-- **One decision from its scrubbed bank** (the stage of `Cells.ofScrub`). -/
theorem cell_stage (R j : ℕ) (hj : j < F.bound) :
    ∃ (H' : Fin F.T → ℕ) (A' : Fin F.T → List Bool), Step F.cellM F.cellCost (fun _ => 0) (F.src R j) H' A' ∧
      (∀ i, F.cellS i = false → A' i = F.src R (j + 1) i) := by
  obtain ⟨A', hs, hpfx, hkeep⟩ := F.cell_step (F.gp j) (by rw [gp_length]; exact hj)
  have hc := BlockPlatform.Scrub.cleared_entry hs F.cellS R (fun i hi => ⟨0, by omega, by
    unfold cellS at hi
    split_ifs at hi with h
    · simp only [cellIn, dif_pos h, cin]
      have hk : F.keep ⟨i.val, h⟩ = false := by simpa using hi
      have hP : (⟨i.val, h⟩ : Fin F.t) ≠ F.PFX := fun e => by rw [e, F.hPFX] at hk; exact absurd hk (by decide)
      rw [if_neg hP, if_neg (by rw [hk]; decide)]; rfl
    · simp only [cellIn, dif_neg h]; rfl⟩)
  refine ⟨_, _, hc, fun i hi => ?_⟩
  by_cases h : i.val < F.t
  · have hk : F.keep ⟨i.val, h⟩ = true := by
      unfold cellS at hi; rw [dif_pos h] at hi; simpa using hi
    have hS : F.cellS i = false := hi
    simp only [hS, Bool.false_eq_true, if_false, ZeroPadding.pad_zero]
    simp only [src, BlockPlatform.Scrub.blank, hS, Bool.false_eq_true, if_false, cellIn, dif_pos h, cin]
    have hA : A' i = A' (F.sl0 ⟨i.val, h⟩) := rfl
    rw [hA]
    by_cases hP : (⟨i.val, h⟩ : Fin F.t) = F.PFX
    · rw [if_pos hP, gp_succ]
      have e : F.sl0 ⟨i.val, h⟩ = F.sl0 F.PFX := congrArg F.sl0 hP
      rw [e, hpfx]
    · rw [if_neg hP, if_pos hk, hkeep _ hk hP]
  · have : F.cellS i = true := by unfold cellS; rw [dif_neg h]
    rw [this] at hi; exact absurd hi (by decide)

/-- **The decision loop**: `bound` decisions from the empty prefix leave the prefix tape holding the greedy's
decisions over the child sums, `greedyLoop bound (val ·)` (P3:3035-3039). -/
theorem loop_run (R L : ℕ) (hR : F.cellCost + 1 ≤ R) (hL : R + 1 ≤ L) :
    ∃ c : BlockPlatform.Cells (F.T + 1 + 1) _,
      Step (CloseoutRowsDegreeLoop.machine c.body) (c.bound * (c.cost + 3) + 3)
        (Fin.addCases (BlockPlatform.Scrub.heads (fun _ : Fin F.T => 0)) (fun _ : Fin 1 => 1))
        (Fin.addCases (BlockPlatform.Scrub.bank (F.src R 0) R L)
          (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word F.bound))
        (Fin.addCases (BlockPlatform.Scrub.heads (fun _ : Fin F.T => 0)) (fun _ : Fin 1 => 1))
        (Fin.addCases (BlockPlatform.Scrub.bank (F.src R F.bound) R L)
          (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word F.bound)) ∧
      c.body = BlockPlatform.Scrub.machine F.cellM (fun _ => true) F.cellS ∧ c.bound = F.bound ∧
      c.cost = 2 * F.cellCost + 2 + 1 + (2 * R + 4) := by
  let c := BlockPlatform.Cells.ofScrub F.cellM (fun _ => true) F.cellS R L F.bound (fun _ _ _ => 0)
    (fun j _ => F.src R j) (fun _ => []) (fun _ _ => rfl) hR hL (fun _ _ _ _ _ => rfl)
    (fun j _ out i hi => by simp [src, BlockPlatform.Scrub.blank, hi])
    (fun j hj out => by
      obtain ⟨H', A', hs, hk⟩ := F.cell_stage R j hj
      exact ⟨H', A', hs, fun i hi => by simpa using hk i hi, fun i hi => absurd hi (by decide)⟩)
  refine ⟨c, ?_, rfl, rfl, rfl⟩
  exact c.loopStep []

theorem src_pfx (R : ℕ) : F.src R F.bound (F.sl0 F.PFX) =
    frame (SeedFix.greedyLoop F.bound F.Rv) := by
  have hlt : (F.sl0 F.PFX).val < F.t := F.PFX.isLt
  have hS : F.cellS (F.sl0 F.PFX) = false := by
    unfold cellS; rw [dif_pos hlt]
    show (!F.keep F.PFX) = false
    simp [F.hPFX]
  unfold src BlockPlatform.Scrub.blank
  rw [hS]
  simp only [Bool.false_eq_true, if_false]
  unfold cellIn
  rw [dif_pos hlt]
  unfold cin
  rw [if_pos (show (⟨(F.sl0 F.PFX).val, hlt⟩ : Fin F.t) = F.PFX from Fin.ext rfl)]
  rfl

end

end ChildFam

/-! ## The greedy reads only the prefixes it decides on -/

theorem iterate_greedyStep_congr (R R' : List Bool → ℤ) (m : ℕ) (h : ∀ p : List Bool, p.length ≤ m → R p = R' p) :
    ∀ j, j ≤ m → (SeedFix.greedyStep R)^[j] [] = (SeedFix.greedyStep R')^[j] [] ∧
      ((SeedFix.greedyStep R)^[j] []).length = j
  | 0, _ => ⟨rfl, rfl⟩
  | j + 1, hj => by
    obtain ⟨ih, hl⟩ := iterate_greedyStep_congr R R' m h j (by omega)
    have hl' : ((SeedFix.greedyStep R')^[j] []).length = j := by rw [← ih]; exact hl
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    refine ⟨?_, ?_⟩
    · simp only [SeedFix.greedyStep]
      rw [h _ (by simp; omega), h _ (by simp; omega)]
    · simp only [SeedFix.greedyStep, List.length_append, List.length_singleton]
      rw [hl']

/-- **The greedy loop depends on the sums of the prefixes of length at most its bound only.** -/
theorem greedyLoop_congr (R R' : List Bool → ℤ) (m : ℕ) (h : ∀ p : List Bool, p.length ≤ m → R p = R' p) :
    SeedFix.greedyLoop m R = SeedFix.greedyLoop m R' :=
  (iterate_greedyStep_congr R R' m h m le_rfl).1

end NearCubicWires.WireExponent3_5.PrimT.C4Loop
