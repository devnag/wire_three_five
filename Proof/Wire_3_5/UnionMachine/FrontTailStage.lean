import Proof.Wire_3_5.UnionMachine.FrontTail
import Proof.Wire_3_5.UnionMachine.FrontWM

/-! # C6 front, the tail stage: the tail's word program on the worker's tapes, then the loop's scratch erased

The front's last stage (P3:3669-3691; `Plan.bankA`, `Plan.bankH`):
* **`wfM0 P`**: a word program with its registers' fill (FrontWM's `wfM` without the rewind: the registers' tapes keep
  their heads at their values, as the loop's registers need); **`wfM0_step`**;
* the tail (`FrontTail.tailW`) docked on the worker's tapes: the writer's sources and the count on the front's tapes,
  the install's streams ON THE LOOP'S KEPT SLOTS (table, cell, `p`, accumulators), its log and its driver;
* base's selected erase (`Scrub.erase_step`, `2R + 4` steps) blanks the loop's scratch to `0^R` with that driver and log;
* **`tailStage_step`**: the loop bank `bankA P capQ RQ (RQ+1) K`, `bankH P K` at `K = ⟨table, 0, p, thresholds⟩`.

Paper quantity of the main type: the loop's entry bank (the table, `p`, the thresholds, the capacities). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTailStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit

/-! ## A word program with its fill, not rewound -/

section WM0
variable {ns nr : ℕ}

theorem encL_inj : Function.Injective (encL (ns := ns) (nr := nr)) := fun a b h =>
  Fin.ext (by simpa [encL_val] using congrArg Fin.val h)

/-- **The program with its registers' fill, not rewound.** -/
noncomputable def wfM0 (P : WM ns nr) :=
  Composition.machine (FrontFill.fillP (cntL (ns := ns) (nr := nr)) mkL tgtL).compile
    (Composition.machine (FrontKit.cellP (encL (ns := ns) (nr := nr) ⟨1, by omega⟩)).compile
      (RecoveryFocus.machine encL P.toProg.compile))

/-- **The program with its fill, as a Step**: the program's tapes end encoded (heads at the exit's), the count kept. -/
theorem wfM0_step (P : WM ns nr) (W n : ℕ) (σ τ : WState ns nr) (hw : WExec (2 * W + 2) P σ τ n)
    (hs0 : ∀ i, σ.sh i = 0) (hv0 : ∀ r, σ.val r = 0) (hc0 : σ.cell = false) :
    ∃ out : Fin (WT ns nr) → List Bool,
      Step (wfM0 P) ((11 * W + 20) + 1 + (1 + 1 + n)) (fun _ => 0) (wfIn σ W)
        (dockH encL (fun _ => 0) (wenc (2 * W + 2) τ).H) out ∧
      (∀ i, out (encL i) = (wenc (2 * W + 2) τ).A i) ∧ out cntL = List.replicate W true := by
  have hca : (cntL (ns := ns) (nr := nr)) ≠ mkL := fun e => by
    have := congrArg Fin.val e; rw [cntL_val, mkL_val] at this; omega
  have hct : tgtL (cntL (ns := ns) (nr := nr)) = false := by simp [tgtL, cntL_val]
  have hat : tgtL (mkL (ns := ns) (nr := nr)) = false := by simp [tgtL, mkL_val]
  have g1 := FrontKit.fill_ready cntL mkL tgtL (wfIn σ W) W hca hct hat
    (by rw [wfIn_val, if_pos cntL_val])
    (fun i hi => by
      rw [side_iff] at hi
      rw [wfIn_val, if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)])
  set A1 : Fin (WT ns nr) → List Bool := fun i =>
      if FrontFill.side mkL tgtL i then List.replicate (2 * W + 3) false else wfIn σ W i with hA1
  have A1s : ∀ i, FrontFill.side mkL tgtL i → A1 i = List.replicate (2 * W + 3) false := fun i hi => by
    simp only [hA1, if_pos hi]
  have A1n : ∀ i, ¬ FrontFill.side mkL tgtL i → A1 i = wfIn σ W i := fun i hi => by
    simp only [hA1, if_neg hi]
  set c1 : Fin (WT ns nr) := encL (ns := ns) (nr := nr) ⟨1, by omega⟩ with hc1
  have c1v : c1.val = 1 := rfl
  have hcell : A1 c1 = [] := by
    rw [A1n c1 (by rw [side_iff, c1v]; omega), wfIn_val]
    simp only [c1v]
    rw [if_neg (by omega), if_neg (by omega)]
    simp
  have g2 := FrontKit.cell_ready c1 A1 hcell
  set A2 := Function.update A1 c1 [false] with hA2
  have hs := (WExec.exec (2 * W + 2) hw).step
  rw [FrontKit.wenc_H_zero _ σ hs0 hv0] at hs
  have hin : ∀ i, A2 (encL i) = (wenc (2 * W + 2) σ).A i := by
    intro i
    rw [wenc_A_v]
    have hi := i.isLt
    have rv : (encL (ns := ns) (nr := nr) i).val = i.val := rfl
    by_cases h1 : i.val = 1
    · have e : encL i = c1 := Fin.ext (by rw [rv, c1v, h1])
      rw [e, hA2, Function.update_self, if_neg (by omega), if_pos h1, hc0]
    · have hne : encL i ≠ c1 := fun e => h1 (by rw [← rv, e, c1v])
      rw [hA2, Function.update_of_ne hne]
      by_cases hr : ns + 2 ≤ i.val
      · rw [A1s _ (by rw [side_iff, rv]; omega), if_neg (by omega), if_neg h1, dif_neg (by omega), hv0,
          regTape_zero']
      · rw [A1n _ (by rw [side_iff, rv]; omega), wfIn_val]
        simp only [rv]
        rw [if_neg (by omega)]
        by_cases h0 : i.val = 0
        · rw [if_pos h0, if_pos h0]
        · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1, dif_pos (by omega), dif_pos (by omega)]
  have g3 := dockAny hs encL encL_inj (fun _ => 0) A2 (fun _ => rfl) hin
  refine ⟨_, Step.seq (step_of_ready g1) (Step.seq (step_of_ready g2) g3), fun i => by rw [install_slot _ encL_inj],
    ?_⟩
  have hn : ∀ j, encL j ≠ (cntL (ns := ns) (nr := nr)) := fun j e => by
    have h1 := congrArg Fin.val e; have hj := j.isLt; rw [encL_val, cntL_val] at h1; omega
  have hne : (cntL (ns := ns) (nr := nr)) ≠ c1 := fun e => by
    have := congrArg Fin.val e; rw [cntL_val, c1v] at this; omega
  rw [install_other _ _ _ _ hn, hA2, Function.update_of_ne hne, A1n _ (by rw [side_iff, cntL_val]; omega),
    wfIn_val, if_pos cntL_val]

end WM0

/-! ## The tail stage on the worker's tapes -/

section Stage
open NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTail NearCubicWires.WireExponent3_5.UnionMachine.FrontInstall
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

theorem na_ge : 31 ≤ Sched.NA P := Nat.le_add_right _ _

/-- The loop slot of the install's stream `m` (`3 … 13`): the table (`0`), the cell (`1`), `p` (`13`), the
accumulators (`24 … 29`), the log, the driver. -/
noncomputable def lslot (m : ℕ) : Fin (NL P) :=
  ⟨if m = 3 then 0 else if m = 4 then 1 else if m = 5 then 13 else if m ≤ 11 then 18 + m
    else if m = 12 then Sched.NA P else Sched.NA P + 1, by
    have h31 := na_ge P
    show _ < Sched.NA P + 1 + 1
    split_ifs <;> omega⟩

theorem lslot_val (m : ℕ) : (lslot P m).val = if m = 3 then 0 else if m = 4 then 1 else if m = 5 then 13
    else if m ≤ 11 then 18 + m else if m = 12 then Sched.NA P else Sched.NA P + 1 := rfl

theorem lslot_inj (m m' : ℕ) (hm : 3 ≤ m ∧ m ≤ 13) (hm' : 3 ≤ m' ∧ m' ≤ 13) (h : lslot P m = lslot P m') : m = m' := by
  have e := congrArg Fin.val h
  rw [lslot_val, lslot_val] at e
  have h31 := na_ge P
  split_ifs at e <;> omega

/-- The local tape of the install's stream `m`. -/
def tapeI (m : ℕ) (hm : m ≤ 13) : Fin (WT 25 105) := ⟨13 + m, by show 13 + m < 135; omega⟩

theorem tapeI_val (m : ℕ) (hm : m ≤ 13) : (tapeI m hm).val = 13 + m := rfl

theorem tapeI_enc (m : ℕ) (hm : 3 ≤ m ∧ m ≤ 13) :
    tapeI m hm.2 = encL (sTape (nr := 105) (St ⟨m, by omega⟩)) := by
  apply Fin.ext
  rw [tapeI_val, encL_val]
  have h := St_val ⟨m, by omega⟩
  simp only at h
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
  show 13 + m = if (St ⟨m, by omega⟩).val = 0 then 0 else (St ⟨m, by omega⟩).val + 1
  rw [h, if_neg (by omega)]
  omega

/-- The tail's shared tapes: the writer's sources, the install's streams on the loop's slots, the count. -/
noncomputable def shT (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (j : Fin (WT 25 105)) :
    Option (Fin (NW P tf)) :=
  if h : 2 ≤ j.val ∧ j.val ≤ 11 then some (srcT ⟨j.val - 2, by omega⟩)
  else if 16 ≤ j.val ∧ j.val ≤ 26 then some (lp P tf (lslot P (j.val - 13)))
  else if j.val = 134 then some cntT else none

theorem shT_cases (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (j : Fin (WT 25 105))
    (y : Fin (NW P tf)) (h : shT P tf srcT cntT j = some y) :
    (∃ hj : 2 ≤ j.val ∧ j.val ≤ 11, y = srcT ⟨j.val - 2, by omega⟩) ∨
      (16 ≤ j.val ∧ j.val ≤ 26 ∧ y = lp P tf (lslot P (j.val - 13))) ∨ (j.val = 134 ∧ y = cntT) := by
  unfold shT at h
  split_ifs at h with h1 h2 h3
  · exact Or.inl ⟨h1, (Option.some.inj h).symm⟩
  · exact Or.inr (Or.inl ⟨h2.1, h2.2, (Option.some.inj h).symm⟩)
  · exact Or.inr (Or.inr ⟨h3, (Option.some.inj h).symm⟩)

/-- The loop's scratch slots. -/
noncomputable def maskT (y : Fin (NW P tf)) : Bool :=
  if h : 2 ≤ y.val ∧ y.val < 2 + Sched.NA P then Sched.scr P ⟨y.val - 2, by omega⟩ else false

/-- **The tail stage**: the tail docked on the worker's tapes, then the loop's scratch erased. -/
noncomputable def tailM (Pw : WM 10 56) (cr K A : ℕ) (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf))
    (k0 : ℕ) (hk : k0 + WT 25 105 ≤ tf) :=
  Composition.machine (RecoveryFocus.machine (sl P tf (shT P tf srcT cntT) k0 hk) (wfM0 (tailW Pw cr K A)))
    (CloseoutWitness.SelectedErase.machine (maskT P tf) (lp P tf Scrub.driverTape) (lp P tf Scrub.logTape))

/-- The writer's entry inside the tail's layout: its streams, everything else blank. -/
def ωOf (σT : WState 10 56) : WState 25 105 :=
  ⟨fun _ => 0, fun i => if h : i.val < 11 then σT.st ⟨i.val, h⟩ else [], fun _ => 0, σT.cell⟩

theorem ωOf_st_fsT (σT : WState 10 56) (i : Fin 11) : (ωOf σT).st (fsT i) = σT.st i := by
  show (if h : (fsT i).val < 11 then σT.st ⟨(fsT i).val, h⟩ else []) = σT.st i
  rw [dif_pos (by rw [fsT_val]; exact i.isLt)]
  rfl

theorem ωOf_st_hi (σT : WState 10 56) (j : Fin 26) (hj : 11 ≤ j.val) : (ωOf σT).st j = [] := by
  show (if h : j.val < 11 then σT.st ⟨j.val, h⟩ else []) = []
  rw [dif_neg (by omega)]

theorem wfIn_ωOf (σT : WState 10 56) (W : ℕ) (j : Fin (WT 25 105)) :
    wfIn (ωOf σT) W j = if j.val = 134 then List.replicate W true
      else if j.val = 0 then σT.st 0 else if h : 2 ≤ j.val ∧ j.val ≤ 11 then σT.st ⟨j.val - 1, by omega⟩ else [] := by
  rw [wfIn_val]
  by_cases h134 : j.val = 134
  · rw [if_pos (by omega), if_pos h134]
  · rw [if_neg (by omega), if_neg h134]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, if_pos h0]; rfl
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : j.val = 1
      · rw [if_pos h1, dif_neg (by omega)]
      · rw [if_neg h1]
        by_cases h2 : 2 ≤ j.val ∧ j.val ≤ 11
        · rw [dif_pos (by omega), dif_pos h2]
          show (if h : j.val - 1 < 11 then σT.st ⟨j.val - 1, h⟩ else []) = _
          rw [dif_pos (by omega)]
        · rw [dif_neg h2]
          by_cases h3 : j.val ≤ 25 + 1
          · rw [dif_pos h3]
            show (if h : j.val - 1 < 11 then σT.st ⟨j.val - 1, h⟩ else []) = _
            rw [dif_neg (by omega)]
          · rw [dif_neg h3]

/-- A kept loop slot is one of the install's streams, whose target is the loop's fixed tape. -/
theorem kept_slot (c R p : ℕ) (a : Fin 6 → ℕ) (s : List Bool) (m : Fin 31) (hm : Sched.keptFx m) :
    ∃ j : ℕ, 3 ≤ j ∧ j ≤ 11 ∧ Scrub.inner (Sched.fx P m) = lslot P j ∧
      wtI c R p a s j = Sched.fixedA c ⟨s, 0, p, a⟩ m ∧ hdI p a j = Sched.fixedH ⟨s, 0, p, a⟩ m := by
  unfold Sched.keptFx at hm
  have hv : m.val = 0 ∨ m.val = 1 ∨ m.val = 13 ∨ m.val = 24 ∨ m.val = 25 ∨ m.val = 26 ∨ m.val = 27 ∨
      m.val = 28 ∨ m.val = 29 := by omega
  have ex : ∀ k : ℕ, (hk : k < 31) → m.val = k → m = ⟨k, hk⟩ := fun k hk h => Fin.ext h
  have sl : ∀ j : ℕ, (lslot P j).val = m.val → Scrub.inner (Sched.fx P m) = lslot P j := fun j h =>
    Fin.ext (by rw [Scrub.inner_val, Sched.fx_val, h])
  rcases hv with h | h | h | h | h | h | h | h | h
  · obtain rfl := ex 0 (by norm_num) h
    exact ⟨3, le_rfl, by norm_num, sl 3 (by rw [lslot_val]; rfl), rfl, rfl⟩
  · obtain rfl := ex 1 (by norm_num) h
    exact ⟨4, by norm_num, by norm_num, sl 4 (by rw [lslot_val]; rfl), rfl, rfl⟩
  · obtain rfl := ex 13 (by norm_num) h
    exact ⟨5, by norm_num, by norm_num, sl 5 (by rw [lslot_val]; rfl), rfl, rfl⟩
  · obtain rfl := ex 24 (by norm_num) h
    exact ⟨6, by norm_num, by norm_num, sl 6 (by rw [lslot_val]; rfl), rfl, rfl⟩
  · obtain rfl := ex 25 (by norm_num) h
    exact ⟨7, by norm_num, by norm_num, sl 7 (by rw [lslot_val]; rfl), rfl, rfl⟩
  · obtain rfl := ex 26 (by norm_num) h
    exact ⟨8, by norm_num, by norm_num, sl 8 (by rw [lslot_val]; rfl), rfl, rfl⟩
  · obtain rfl := ex 27 (by norm_num) h
    exact ⟨9, by norm_num, by norm_num, sl 9 (by rw [lslot_val]; rfl), rfl, rfl⟩
  · obtain rfl := ex 28 (by norm_num) h
    exact ⟨10, by norm_num, by norm_num, sl 10 (by rw [lslot_val]; rfl), rfl, rfl⟩
  · obtain rfl := ex 29 (by norm_num) h
    exact ⟨11, by norm_num, by norm_num, sl 11 (by rw [lslot_val]; rfl), rfl, rfl⟩

theorem scr_eq (x : Fin (Sched.NA P)) :
    Sched.scr P x = true ↔ ¬(x.val = 0 ∨ x.val = 1 ∨ x.val = 13 ∨ (24 ≤ x.val ∧ x.val ≤ 29)) := by
  unfold Sched.scr Sched.keptV
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  constructor <;> intro h <;> omega

theorem maskT_inner (x : Fin (Sched.NA P)) : maskT P tf (lp P tf (Scrub.inner x)) = Sched.scr P x := by
  unfold maskT
  rw [dif_pos (by rw [lp_val, Scrub.inner_val]; have := x.isLt; omega)]
  congr 1
  exact Fin.ext (by show (lp P tf (Scrub.inner x)).val - 2 = x.val; rw [lp_val, Scrub.inner_val]; omega)

/-- **The tail stage's run**: from the front's bank (the writer's sources and the count `1^W` on front tapes below
`k0`, every tape from `k0` on and every loop tape blank at head `0`), the worker's loop slots hold the loop's entry
bank at `K = ⟨table, 0, p, thresholds⟩`, capacity `capQ`, scratch `RQ`, log `RQ + 1`. -/
theorem tailStage_step (Pw : WM 10 56) (capT : ℕ) (σT τT : WState 10 56) (nT : ℕ) (hP : WExec capT Pw σT τT nT)
    (hsT : ∀ i, σT.sh i = 0) (hvT : ∀ r, σT.val r = 0) (hcT : σT.cell = false) (hO : σT.st 0 = [])
    (W : ℕ) (hcap : capT ≤ 2 * W + 2) (cr K A q p : ℕ) (a : Fin 6 → ℕ) (s : List Bool)
    (hq : τT.val 54 = q) (hs : τT.st 0 = s) (hsh : τT.sh 0 = s.length) (hL : τT.val 0 = s.length)
    (hp : τT.val 52 = p) (ha : ∀ i : Fin 6, τT.val ⟨24 + i.val, by omega⟩ = a i)
    (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q) (hK : 1 ≤ K)
    (hcapW : K * (q + 1) ^ A + 1000 * (q + 7) + 2 * cr + 100 ≤ 2 * W + 2)
    (hpc : p ≤ capOf cr K A q) (hac : ∀ i, a i ≤ capOf cr K A q) (hpW : p ≤ 2 * W + 2)
    (haW : ∀ i, a i ≤ 2 * W + 2) (hsc : s.length ≤ 2 * W + 2)
    (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (k0 : ℕ) (hk : k0 + WT 25 105 ≤ tf)
    (hsI : Function.Injective srcT) (hsL : ∀ i, 2 + NL P ≤ (srcT i).val ∧ (srcT i).val < 2 + NL P + k0)
    (hcL : 2 + NL P ≤ cntT.val ∧ cntT.val < 2 + NL P + k0) (hcs : ∀ i, srcT i ≠ cntT)
    (H0 : Fin (NW P tf) → ℕ) (A0 : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H0 A0 k0)
    (hsrc : ∀ i : Fin 10, A0 (srcT i) = σT.st i.succ ∧ H0 (srcT i) = 0)
    (hcnt : A0 cntT = List.replicate W true ∧ H0 cntT = 0) :
    ∃ (H1 : Fin (NW P tf) → ℕ) (A1 : Fin (NW P tf) → List Bool),
      Step (tailM P tf Pw cr K A srcT cntT k0 hk)
        ((11 * W + 20) + 1 + (1 + 1 + (nT + tailCost cr K A q s.length (2 * W + 2))) + 1 + (2 * rOf cr K A q + 4))
        H0 A0 H1 A1 ∧
      (∀ i, H1 (lp P tf i) = bankH P ⟨s, 0, p, a⟩ i) ∧
      (∀ i, A1 (lp P tf i) = bankA P (capOf cr K A q) (rOf cr K A q) (rOf cr K A q + 1) ⟨s, 0, p, a⟩ i) := by
  have h31 := na_ge P
  -- the word program's run
  have hl : LiftW fsT frT (ωOf σT) σT :=
    ⟨fun i => (hsT i).symm, fun i => ωOf_st_fsT σT i, fun r => (hvT r).symm, rfl⟩
  obtain ⟨τ, eτ, hinst⟩ := tailW_spec Pw capT σT τT nT hP (2 * W + 2) hcap (ωOf σT) hl
    (fun j hj => ⟨ωOf_st_hi σT j hj, rfl⟩) (fun _ _ => rfl) cr K A q p a s hq hs hsh hL hp ha hcr h4 hK hcapW
    hpc hac hpW haW hsc
  obtain ⟨out, hst, hout, -⟩ := wfM0_step (tailW Pw cr K A) W _ (ωOf σT) τ eτ (fun _ => rfl) (fun _ => rfl) hcT
  -- the slots
  set sl0 := sl P tf (shT P tf srcT cntT) k0 hk with hsl0
  have hlow : ∀ j y, shT P tf srcT cntT j = some y → y.val < 2 + NL P + k0 := fun j y h => by
    rcases shT_cases P tf srcT cntT j y h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact (hsL _).2
    · rw [lp_val]; have := (lslot P (j.val - 13)).isLt; omega
    · exact hcL.2
  have hshI : ∀ i j y, shT P tf srcT cntT i = some y → shT P tf srcT cntT j = some y → i = j := by
    intro i j y hi hj
    have vi : i.val < 135 := i.isLt
    have vj : j.val < 135 := j.isLt
    rcases shT_cases P tf srcT cntT i y hi with ⟨hi1, ei⟩ | ⟨hi1, hi2, ei⟩ | ⟨hi1, ei⟩ <;>
      rcases shT_cases P tf srcT cntT j y hj with ⟨hj1, ej⟩ | ⟨hj1, hj2, ej⟩ | ⟨hj1, ej⟩ <;>
      have e := ei.symm.trans ej
    · have e2 := congrArg Fin.val (hsI e); simp only at e2; exact Fin.ext (by omega)
    · have e2 := congrArg Fin.val e; rw [lp_val] at e2
      have b1 := (hsL ⟨i.val - 2, by omega⟩).1; have b2 := (lslot P (j.val - 13)).isLt; omega
    · exact absurd e (hcs _)
    · have e2 := congrArg Fin.val e; rw [lp_val] at e2
      have b1 := (hsL ⟨j.val - 2, by omega⟩).1; have b2 := (lslot P (i.val - 13)).isLt; omega
    · have e2 := lslot_inj P _ _ (by omega) (by omega) (lp_inj P tf e); exact Fin.ext (by omega)
    · have e2 := congrArg Fin.val e; rw [lp_val] at e2
      have b1 := hcL.1; have b2 := (lslot P (i.val - 13)).isLt; omega
    · exact absurd e.symm (hcs _)
    · have e2 := congrArg Fin.val e; rw [lp_val] at e2
      have b1 := hcL.1; have b2 := (lslot P (j.val - 13)).isLt; omega
    · exact Fin.ext (by omega)
  have hinj : Function.Injective sl0 := sl_inj P tf _ k0 hk hshI hlow
  have hA : ∀ j, A0 (sl0 j) = wfIn (ωOf σT) W j := by
    intro j
    rw [wfIn_ωOf]
    have vj : j.val < 135 := j.isLt
    by_cases h1 : 2 ≤ j.val ∧ j.val ≤ 11
    · rw [hsl0, sl_some P tf _ k0 hk j (srcT ⟨j.val - 2, by omega⟩) (by unfold shT; rw [dif_pos h1]),
        (hsrc _).1, if_neg (by omega), if_neg (by omega), dif_pos h1]
      congr 1
      exact Fin.ext (by rw [Fin.val_succ]; show j.val - 2 + 1 = j.val - 1; omega)
    · by_cases h2 : 16 ≤ j.val ∧ j.val ≤ 26
      · rw [hsl0, sl_some P tf _ k0 hk j (lp P tf (lslot P (j.val - 13))) (by unfold shT; rw [dif_neg h1, if_pos h2]),
          (hPr.2 _).1, if_neg (by omega), if_neg (by omega), dif_neg h1]
      · by_cases h3 : j.val = 134
        · rw [hsl0, sl_some P tf _ k0 hk j cntT (by unfold shT; rw [dif_neg h1, if_neg h2, if_pos h3]), hcnt.1,
            if_pos h3]
        · rw [hsl0, sl_none P tf _ k0 hk j (by unfold shT; rw [dif_neg h1, if_neg h2, if_neg h3]),
            (hPr.1 _ (by rw [rg_val]; omega)).1, if_neg h3]
          by_cases h0 : j.val = 0
          · rw [if_pos h0, hO]
          · rw [if_neg h0, dif_neg h1]
  have hH : ∀ j, H0 (sl0 j) = 0 := by
    intro j
    have vj : j.val < 135 := j.isLt
    by_cases h1 : 2 ≤ j.val ∧ j.val ≤ 11
    · rw [hsl0, sl_some P tf _ k0 hk j (srcT ⟨j.val - 2, by omega⟩) (by unfold shT; rw [dif_pos h1])]
      exact (hsrc _).2
    · by_cases h2 : 16 ≤ j.val ∧ j.val ≤ 26
      · rw [hsl0, sl_some P tf _ k0 hk j (lp P tf (lslot P (j.val - 13))) (by unfold shT; rw [dif_neg h1, if_pos h2])]
        exact (hPr.2 _).2
      · by_cases h3 : j.val = 134
        · rw [hsl0, sl_some P tf _ k0 hk j cntT (by unfold shT; rw [dif_neg h1, if_neg h2, if_pos h3])]
          exact hcnt.2
        · rw [hsl0, sl_none P tf _ k0 hk j (by unfold shT; rw [dif_neg h1, if_neg h2, if_neg h3])]
          exact (hPr.1 _ (by rw [rg_val]; omega)).2
  have d1 := dockAny hst sl0 hinj H0 A0 hH hA
  set H1 := dockH sl0 H0 (dockH encL (fun _ => 0) (wenc (2 * W + 2) τ).H) with hH1
  set A1 := install sl0 A0 out with hA1
  set R := rOf cr K A q with hR
  -- the install's slots
  have inst : ∀ m : ℕ, (hm : 3 ≤ m ∧ m ≤ 13) →
      A1 (lp P tf (lslot P m)) = wtI (capOf cr K A q) R p a s m ∧ H1 (lp P tf (lslot P m)) = hdI p a m := by
    intro m hm
    have e : sl0 (tapeI m hm.2) = lp P tf (lslot P m) := by
      rw [hsl0, sl_some P tf _ k0 hk _ (lp P tf (lslot P (13 + m - 13)))
        (by unfold shT; rw [dif_neg (by rw [tapeI_val]; omega), if_pos (by rw [tapeI_val]; omega)]; rfl)]
      rw [Nat.add_sub_cancel_left]
    have hi := hinst ⟨m, by omega⟩ hm.1
    rw [← e, hA1, hH1, install_slot _ hinj, dockH_slot _ hinj, tapeI_enc m hm, hout, dockH_slot _ encL_inj,
      wenc_A_s, wenc_H_s]
    exact hi
  -- the loop's other slots are untouched
  have untouched : ∀ y : Fin (NW P tf), y.val < 2 + NL P → (∀ m, 3 ≤ m → m ≤ 13 → y ≠ lp P tf (lslot P m)) →
      A1 y = A0 y ∧ H1 y = H0 y := by
    intro y hy hne
    have hn : ∀ j, sl0 j ≠ y := by
      intro j hj
      rw [hsl0] at hj
      cases hsh' : shT P tf srcT cntT j with
      | none =>
        rw [sl_none P tf _ k0 hk j hsh'] at hj
        have e2 := congrArg Fin.val hj; rw [rg_val] at e2; omega
      | some z =>
        rw [sl_some P tf _ k0 hk j z hsh'] at hj
        subst hj
        rcases shT_cases P tf srcT cntT j z hsh' with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨-, e⟩
        · rw [e] at hy; have b1 := (hsL ⟨j.val - 2, by omega⟩).1; omega
        · exact hne _ (by omega) (by omega) e
        · rw [e] at hy; have b1 := hcL.1; omega
    exact ⟨by rw [hA1, install_other _ _ _ _ hn], by rw [hH1, dockH_other _ _ _ _ hn]⟩
  have hdrvS : lp P tf Scrub.driverTape = lp P tf (lslot P 13) :=
    congrArg (lp P tf) (Fin.ext (by rw [Scrub.driver_val, lslot_val]; simp))
  have hlogS : lp P tf Scrub.logTape = lp P tf (lslot P 12) :=
    congrArg (lp P tf) (Fin.ext (by rw [Scrub.log_val, lslot_val]; simp))
  have iD := inst 13 (by norm_num)
  have iL := inst 12 (by norm_num)
  rw [← hdrvS] at iD
  rw [← hlogS] at iL
  have mD : maskT P tf (lp P tf Scrub.driverTape) = false := by
    unfold maskT; rw [dif_neg]; rw [lp_val, Scrub.driver_val]; omega
  have mL : maskT P tf (lp P tf Scrub.logTape) = false := by
    unfold maskT; rw [dif_neg]; rw [lp_val, Scrub.log_val]; omega
  have hDL : lp P tf Scrub.driverTape ≠ lp P tf Scrub.logTape := fun h => by
    have e2 := congrArg Fin.val h; rw [lp_val, lp_val, Scrub.driver_val, Scrub.log_val] at e2; omega
  -- the masked slots are untouched loop scratch
  have maskU : ∀ y, maskT P tf y = true → A1 y = [] ∧ H1 y = 0 := by
    intro y hy
    unfold maskT at hy
    split_ifs at hy with hyl
    · have hx : ¬((y.val - 2) = 0 ∨ (y.val - 2) = 1 ∨ (y.val - 2) = 13 ∨ (24 ≤ y.val - 2 ∧ y.val - 2 ≤ 29)) :=
        (scr_eq P ⟨y.val - 2, by omega⟩).1 hy
      have hyv : y = lp P tf (Scrub.inner ⟨y.val - 2, by omega⟩) :=
        Fin.ext (by rw [lp_val, Scrub.inner_val]; show y.val = 2 + (y.val - 2); omega)
      have hNL : NL P = Sched.NA P + 1 + 1 := rfl
      have u := untouched y (by omega) (fun m hm1 hm2 e => by
        have hv : y.val = 2 + (lslot P m).val := by rw [e, lp_val]
        rw [lslot_val] at hv
        split_ifs at hv <;> omega)
      have p0 := hPr.2 (Scrub.inner ⟨y.val - 2, by omega⟩)
      rw [← hyv] at p0
      exact ⟨u.1.trans p0.1, u.2.trans p0.2⟩
  -- the erase
  have e2 := Scrub.erase_step (maskT P tf) (lp P tf Scrub.driverTape) (lp P tf Scrub.logTape) mD mL hDL R (R + 1)
    le_rfl H1 A1
    (fun y hy => by
      rcases hy with hy | rfl | rfl
      · exact (maskU y hy).2
      · exact iD.2
      · exact iL.2)
    (fun y hy => by rw [(maskU y hy).1]; simp)
    iD.1 iL.1
  refine ⟨H1, Scrub.blank (maskT P tf) A1 R, Step.seq d1 e2, fun i => ?_, fun i => ?_⟩
  · show H1 (lp P tf i) = Scrub.heads (Sched.iterH P ⟨s, 0, p, a⟩) i
    refine Scrub.cover (motive := fun i => H1 (lp P tf i) = Scrub.heads (Sched.iterH P ⟨s, 0, p, a⟩) i)
      (fun x => ?_) ?_ ?_ i
    · rw [Scrub.heads_inner]
      by_cases hx : Sched.scr P x = true
      · rw [Sched.iterH_scr P _ x hx]
        exact (maskU _ (by rw [maskT_inner]; exact hx)).2
      · obtain ⟨m, rfl, hkm⟩ := Sched.scr_false P x (by simpa using hx)
        obtain ⟨j, hj3, hj11, he, -, hh⟩ := kept_slot P (capOf cr K A q) R p a s m hkm
        rw [Sched.iterH_fx, ← hh, he]
        exact (inst j ⟨hj3, by omega⟩).2
    · rw [Scrub.heads_log]; exact iL.2
    · rw [Scrub.heads_driver]; exact iD.2
  · show Scrub.blank (maskT P tf) A1 R (lp P tf i) =
      Scrub.bank (Scrub.blank (Sched.scr P) (Sched.iterA P (capOf cr K A q) ⟨s, 0, p, a⟩) R) R (R + 1) i
    refine Scrub.cover (motive := fun i => Scrub.blank (maskT P tf) A1 R (lp P tf i) =
      Scrub.bank (Scrub.blank (Sched.scr P) (Sched.iterA P (capOf cr K A q) ⟨s, 0, p, a⟩) R) R (R + 1) i)
      (fun x => ?_) ?_ ?_ i
    · rw [Scrub.bank_inner]
      unfold Scrub.blank
      rw [maskT_inner]
      by_cases hx : Sched.scr P x = true
      · rw [if_pos hx, if_pos hx]
      · rw [if_neg hx, if_neg hx]
        obtain ⟨m, rfl, hkm⟩ := Sched.scr_false P x (by simpa using hx)
        obtain ⟨j, hj3, hj11, he, hw, -⟩ := kept_slot P (capOf cr K A q) R p a s m hkm
        rw [Sched.iterA_fx, ← hw, he]
        exact (inst j ⟨hj3, by omega⟩).1
    · rw [Scrub.bank_log]
      unfold Scrub.blank
      rw [mL, if_neg (by decide)]
      exact iL.1
    · rw [Scrub.bank_driver]
      unfold Scrub.blank
      rw [mD, if_neg (by decide)]
      exact iD.1

end Stage

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTailStage
