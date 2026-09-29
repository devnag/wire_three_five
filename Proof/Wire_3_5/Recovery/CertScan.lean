import Proof.Wire_3_5.Recovery.CertCand

/-! # One round of the prefix's scan (P3:3738-3741; D1.6, the prefix stage)

Realizes one step of "Choose the largest `a` such that `m_a ≤ n/2`" (P3:3740): the scan keeps the current index `S` on
a port (padded with `false` to `total`) and, per round, tests the next candidate `a = S + 1` and adds the test's bit to
`S`. Because `m_a` is monotone in `a` (`coreLen_mono`), `n` such rounds from `S = 0` compute the upward scan
`sliceIdx`. One round: base's `DimensionTemplate` and `UWalkUnary` copy `1^{S+1}` onto the candidate tape, the
candidate test (`candMachine`, this component's `Proof.Wire_3_5.Recovery.CertCand`), the unary sum `S + [flag]`, and a one-port
write-back (erase the port with base's `RecoveryScratchErase`, copy the sum).

Paper quantities: the scan index `S` and the test bit `[m_{S+1} ≤ n/2]`; **`writeOneMachine`** and **`writeOne_ready`**
(the write-back), **`scanWorker`** on `scanTapes D` tapes and **`scanWorker_run`**: the port `S` becomes
`S + [flag(S+1)]`, `1^n` and the inner block are kept in canonical form, within `scanRoundBound`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Writing one value back onto a padded port -/

section WriteOne

def slotsOE : Fin 3 → Fin 7 := ![0, 1, 2]
def slotsOT : Fin 3 → Fin 7 := ![3, 4, 5]
def slotsOC : Fin 3 → Fin 7 := ![4, 0, 6]

/-- **The one-port write-back**: erase tape 0 (driver 1, capacity tape 2), then copy `1^e` (tape 3) onto it. -/
noncomputable def writeOneMachine :=
  Composition.machine (RecoveryFocus.machine slotsOE (RecoveryScratchErase.resetMachine 1))
  (Composition.machine (RecoveryFocus.machine slotsOT
    (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
    (RecoveryFocus.machine slotsOC (UWalkUnary.machine false false)))

def writeOneInput (P : List Bool) (total capT e : ℕ) : Fin 7 → List Bool :=
  ![P, List.replicate total true, List.replicate capT false, List.replicate e true, [], [], []]

def writeOneCost (total e : ℕ) : ℕ := (2 * total + 4) + 1 + ((2 * e + 8) + 1 + (2 * e + 6))

/-- **The write-back is ready**: the port ends as `1^e` padded to `total`; the driver, the capacity tape and `1^e`
are kept. -/
theorem writeOne_ready (P : List Bool) (total capT e : ℕ) (hcap : total + 1 ≤ capT) (hP : P.length ≤ total) :
    ∃ out : Fin 7 → List Bool,
      ClockJoin.ReadyRun writeOneMachine (writeOneCost total e) (writeOneInput P total capT e) out ∧
      out 0 = ZeroPadding.pad total (List.replicate e true) ∧ out 1 = List.replicate total true ∧
      out 2 = List.replicate capT false ∧ out 3 = List.replicate e true := by
  set x := writeOneInput P total capT e with hx
  have hmax : max capT (total + 1) = capT := max_eq_left hcap
  have he := ready_of_root (RecoveryScratchErase.erase_ready total capT ![P] (by
    intro i; fin_cases i; simpa using hP))
  rw [hmax] at he
  have h1 := he.focus slotsOE (by decide) x (by intro j; fin_cases j <;> rfl)
  set a1 := install slotsOE x (Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin 1 => List.replicate total false)
    (fun _ : Fin 1 => List.replicate total true)) (fun _ : Fin 1 => List.replicate capT false)) with ha1
  have hlow : ∀ i : Fin 7, 3 ≤ i.val → a1 i = x i := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsOE] at this; omega))]
  have h2 := (RepairSource.ProjectionNormalization.DimensionTemplate.ready false e).focus slotsOT (by decide) a1 (by
    intro j; fin_cases j
    · show a1 3 = _; rw [hlow _ (by decide)]; rfl
    · show a1 4 = _; rw [hlow _ (by decide)]; rfl
    · show a1 5 = _; rw [hlow _ (by decide)]; rfl)
  set a2 := install slotsOT a1 (RepairSource.ProjectionNormalization.DimensionTemplate.output false e) with ha2
  have hc := ready_pad _ _ _ _ ![0, total, 0] (UWalkUnary.ready false false (e + 2) e)
  have h3 := hc.focus slotsOC (by decide) a2 (by
    intro j; fin_cases j
    · show a2 4 = _
      rw [ha2, show (4 : Fin 7) = slotsOT 1 from rfl, install_slot _ (by decide)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.output, UWalkUnary.input,
        RepairSource.CloseoutCapacity.Power.template_source]
    · show a2 0 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, show (0 : Fin 7) = slotsOE 0 from rfl,
        install_slot _ (by decide)]
      rfl
    · show a2 6 = _; rw [ha2, install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl)
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 h3), ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 7) = slotsOC 1 from rfl, install_slot _ (by decide)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
  · rw [install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
      show (1 : Fin 7) = slotsOE 1 from rfl, install_slot _ (by decide)]; rfl
  · rw [install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
      show (2 : Fin 7) = slotsOE 2 from rfl, install_slot _ (by decide)]; rfl
  · rw [install_other _ _ _ _ (by decide), ha2, show (3 : Fin 7) = slotsOT 0 from rfl, install_slot _ (by decide)]
    rfl

end WriteOne

/-! ## The scan round's layout -/

section Scan
variable (k A u v D : ℕ)

/-- The round's tape count: the candidate test's tapes and 9 more. -/
def scanTapes : ℕ := candTapes D + 9

theorem candTapes_ge : 110 ≤ candTapes D := by unfold candTapes; omega

/-- A fixed position below 36 (0: the port `S`; 1: `1^n`; 2–34: the inner block; 35: the candidate `1^{S+1}`). -/
def spos (m : ℕ) (h : m < 36 := by decide) : Fin (scanTapes D) := ⟨m, by unfold scanTapes candTapes; omega⟩
/-- The extra tapes after the candidate test's tapes. -/
def xpos (j : ℕ) (h : j < 9 := by decide) : Fin (scanTapes D) := ⟨candTapes D + j, by unfold scanTapes; omega⟩
/-- The inner block's positions. -/
def sinner (j : Fin (30 + 2 + 1)) : Fin (scanTapes D) := ⟨2 + j.val, by have := j.isLt; unfold scanTapes candTapes; omega⟩

/-- The candidate test's tapes in the round: its candidate tape at 35, `1^n` and the inner block in place, the rest
shifted past 35. -/
def candFocus (i : Fin (candTapes D)) : Fin (scanTapes D) :=
  ⟨if i.val = 0 then 35 else if i.val < 35 then i.val else i.val + 1,
    by have := i.isLt; have := candTapes_ge D; unfold scanTapes; split_ifs <;> omega⟩

theorem candFocus_inj : Function.Injective (candFocus D) := by
  intro a b h; have := congrArg Fin.val h; simp only [candFocus, Fin.val_mk] at this; apply Fin.ext
  split_ifs at this <;> omega

theorem candFlag_val : (candFlag D).val = Clause.tapes D + 108 := by
  have h : (tl D 16).val = Clause.tapes D + 16 := rfl
  unfold candFlag
  simp only [candC, Fin.val_mk, h]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  omega

theorem candFocus_flag : (candFocus D (candFlag D)).val = Clause.tapes D + 109 := by
  have h := candFlag_val D
  simp only [candFocus, Fin.val_mk, h]
  rw [if_neg (by omega), if_neg (by omega)]

theorem spos_val (m : ℕ) (h : m < 36) : (spos D m h).val = m := rfl
theorem xpos_val (j : ℕ) (h : j < 9) : (xpos D j h).val = candTapes D + j := rfl
theorem sinner_val (j : Fin (30 + 2 + 1)) : (sinner D j).val = 2 + j.val := rfl

/-- Close a value goal about fixed positions of the round. -/
macro "spos_tac" : tactic => `(tactic| (simp only [spos_val, xpos_val, sinner_val, candTapes, tapes_eq] <;> omega))

def slotsW1 : Fin 3 → Fin (scanTapes D) := ![spos D 0, xpos D 1, xpos D 2]
def slotsW2 : Fin 3 → Fin (scanTapes D) := ![xpos D 1, spos D 35, xpos D 3]
def slotsW4 : Fin 4 → Fin (scanTapes D) := ![spos D 0, candFocus D (candFlag D), xpos D 4, xpos D 5]
def slotsW5 : Fin 7 → Fin (scanTapes D) := ![spos D 0, spos D 7, spos D 8, xpos D 4, xpos D 6, xpos D 7, xpos D 8]

/-- Injectivity of a slot vector of the round from its values. -/
theorem scan_inj {m : ℕ} (s : Fin m → Fin (scanTapes D)) (h : ∀ a b, (s a).val = (s b).val → a = b) :
    Function.Injective s := fun a b hab => h a b (congrArg Fin.val hab)

/-- Close injectivity and `≠` goals of the round's layout by values. -/
macro "scan_inj_tac" : tactic => `(tactic| (apply scan_inj; intro a b h; fin_cases a <;> fin_cases b <;>
  simp [slotsW1, slotsW2, slotsW4, slotsW5, spos, xpos, candFocus_flag, tapes_eq, candTapes] at h ⊢ <;> omega))

/-- **One round of the scan**: `1^{S+1}` onto the candidate tape, the candidate test, `S + [flag]`, the write-back. -/
noncomputable def scanWorker :=
  Composition.machine (RecoveryFocus.machine (slotsW1 D)
    (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
  (Composition.machine (RecoveryFocus.machine (slotsW2 D) (UWalkUnary.machine false true))
  (Composition.machine (RecoveryFocus.machine (candFocus D) (candMachine k A u v D))
  (Composition.machine (RecoveryFocus.machine (slotsW4 D) ClockUnarySum.machine)
    (RecoveryFocus.machine (slotsW5 D) writeOneMachine))))

/-- The round's input: the port `S` (padded), `1^n`, the inner block, and empty tapes. -/
def scanInput (S n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) : Fin (scanTapes D) → List Bool :=
  fun i => if i.val = 0 then ZeroPadding.pad total (List.replicate S true) else if i.val = 1 then List.replicate n true
    else if h : 2 ≤ i.val ∧ i.val < 35 then innerTapes Ap Bp Ep p w total capT T capF c ⟨i.val - 2, by omega⟩
    else []

theorem scanInput_fresh (S n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) (i : Fin (scanTapes D))
    (hi : 35 ≤ i.val) : scanInput D S n Ap Bp Ep p w total capT T capF c i = [] := by
  simp only [scanInput]; rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

/-- The candidate's test bit at `a`. -/
def scanFlag (a n p w c : ℕ) : Bool :=
  decide ((widthAt k A a + 1 + clauseWidth D (widthAt k A a)) * (candT k A u v a p w c + 1) * 2 ≤ n)

/-- The round's time bound. -/
def scanRoundBound (S n p w total T c : ℕ) : ℕ :=
  candBound k A v D (S + 1) n p w total T c + 10 * S + 2 * total + 64

/-- **One round of the scan is ready**: from the port `S` (padded to `total`), `1^n` and the inner block, the port
becomes `S + [flag(S+1)]`, `1^n` is kept and the inner block is left in canonical form, within `scanRoundBound`. -/
theorem scanWorker_run (S n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) (hD : 1 ≤ D)
    (hcap : total + 1 ≤ capT) (hS : S ≤ total) (hA : Ap.length ≤ total) (hB : Bp.length ≤ total)
    (hE : Ep.length ≤ total)
    (hbound : ∀ i, i ≤ c → candA0 k A u v (S + 1) * p ^ i ≤ total ∧ candB0 v * w ^ i ≤ total ∧ 1 + i ≤ total)
    (hT : max capT (max (p + 1) (w + 1)) ≤ T) (hTc : roundCostBound p w total + 1 ≤ T) (hcapF : T + 1 ≤ capF) :
    ∃ (cost : ℕ) (out : Fin (scanTapes D) → List Bool), cost ≤ scanRoundBound k A v D S n p w total T c ∧
      ClockJoin.ReadyRun (scanWorker k A u v D) cost (scanInput D S n Ap Bp Ep p w total capT T capF c) out ∧
      out (spos D 0) = ZeroPadding.pad total
        (List.replicate (S + (scanFlag k A u v D (S + 1) n p w c).toNat) true) ∧
      out (spos D 1) = List.replicate n true ∧
      (∀ j, out (sinner D j) =
        innerTapes (ZeroPadding.pad total (List.replicate (candA0 k A u v (S + 1) * p ^ c) true))
          (ZeroPadding.pad total (List.replicate (candB0 v * w ^ c) true))
          (ZeroPadding.pad total (List.replicate (candT k A u v (S + 1) p w c) true)) p w total capT T capF c j) := by
  set x := scanInput D S n Ap Bp Ep p w total capT T capF c with hx
  set f := scanFlag k A u v D (S + 1) n p w c with hf
  have hct := candTapes_ge D
  -- the template of `S`
  have hw1 := ready_pad _ _ _ _ ![total, 0, 0]
    (RepairSource.ProjectionNormalization.DimensionTemplate.ready false S)
  have g1 := hw1.focus (slotsW1 D) (by scan_inj_tac) x (by
    intro j; fin_cases j
    · show x (spos D 0) = _
      simp [hx, scanInput, spos, RepairSource.ProjectionNormalization.DimensionTemplate.input]
    · show x (xpos D 1) = _
      rw [hx, scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.input, ZeroPadding.pad]
    · show x (xpos D 2) = _
      rw [hx, scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.input, ZeroPadding.pad])
  set a1 := install (slotsW1 D) x (fun i => ZeroPadding.pad (![total, 0, 0] i)
    (RepairSource.ProjectionNormalization.DimensionTemplate.output false S i)) with ha1
  have a1_off : ∀ i : Fin (scanTapes D), i.val ≠ 0 → i.val ≠ candTapes D + 1 → i.val ≠ candTapes D + 2 →
      a1 i = x i := by
    intro i h0 h1 h2
    rw [ha1, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (apply fin_ne; simp [slotsW1, spos, xpos]; omega))]
  -- `1^{S+1}` onto the candidate tape
  have g2 := (UWalkUnary.ready false true (S + 2) S).focus (slotsW2 D) (by scan_inj_tac) a1 (by
    intro j; fin_cases j
    · show a1 (xpos D 1) = _
      rw [ha1, show xpos D 1 = slotsW1 D 1 from rfl, install_slot _ (by scan_inj_tac)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.output, UWalkUnary.input, ZeroPadding.pad,
        RepairSource.CloseoutCapacity.Power.template_source]
    · show a1 (spos D 35) = _
      rw [a1_off _ (by spos_tac) (by spos_tac) (by spos_tac), hx,
        scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
      rfl
    · show a1 (xpos D 3) = _
      rw [a1_off _ (by spos_tac) (by spos_tac) (by spos_tac), hx,
        scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
      rfl)
  set a2 := install (slotsW2 D) a1 (UWalkUnary.result false true (S + 2) S) with ha2
  have a2_35 : a2 (spos D 35) = List.replicate (S + 1) true := by
    rw [ha2, show spos D 35 = slotsW2 D 1 from rfl, install_slot _ (by scan_inj_tac)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
  have a2_off : ∀ i : Fin (scanTapes D), i.val ≠ 0 → i.val ≠ 35 → i.val ≤ candTapes D ∨ candTapes D + 4 ≤ i.val →
      a2 i = x i := by
    intro i h0 h35 hr
    rw [ha2, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (apply fin_ne; simp [slotsW2, spos, xpos]; omega)),
      a1_off _ h0 (by omega) (by omega)]
  have a2_0 : a2 (spos D 0) = ZeroPadding.pad total (List.replicate S true) := by
    rw [ha2, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (apply fin_ne; simp [slotsW2, spos, xpos])),
      ha1, show spos D 0 = slotsW1 D 0 from rfl, install_slot _ (by scan_inj_tac)]
    simp [RepairSource.ProjectionNormalization.DimensionTemplate.output]
  -- the candidate test at `S + 1`
  obtain ⟨c3, o3, hc3, r3, o3a, o3n, o3in, o3f⟩ :=
    candMachine_run k A u v D (S + 1) n Ap Bp Ep p w total capT T capF c hD hcap hA hB hE hbound hT hTc hcapF
  have g3 := r3.focus (candFocus D) (candFocus_inj D) a2 (by
    intro i
    have hi := i.isLt
    by_cases h0 : i.val = 0
    · rw [show candFocus D i = spos D 35 from Fin.ext (by simp [candFocus, spos, h0]), a2_35]
      simp [candInput, h0]
    · by_cases h35 : i.val < 35
      · have hv : (candFocus D i).val = i.val := by simp [candFocus, h0, h35]
        rw [a2_off _ (by omega) (by omega) (by omega), hx]
        simp only [scanInput, candInput, hv, if_neg h0]
      · have hv : (candFocus D i).val = i.val + 1 := by simp [candFocus, h0, h35]
        rw [a2_off _ (by omega) (by omega) (by omega), hx,
          scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega),
          candInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)])
  set a3 := install (candFocus D) a2 o3 with ha3
  have a3_away : ∀ i : Fin (scanTapes D), (∀ j : Fin (candTapes D), (candFocus D j).val ≠ i.val) → a3 i = a2 i := by
    intro i h
    rw [ha3, install_other _ _ _ _ (fun j => fin_ne (h j))]
  have a3_0 : a3 (spos D 0) = ZeroPadding.pad total (List.replicate S true) := by
    rw [a3_away _ (by intro j; simp only [candFocus, spos, Fin.val_mk]; split_ifs <;> omega), a2_0]
  have a3_flag : a3 (candFocus D (candFlag D)) = [f] := by
    rw [ha3, install_slot _ (candFocus_inj D), o3f, hf]
    rfl
  have a3_inner : ∀ j, a3 (sinner D j) = innerTapes
      (ZeroPadding.pad total (List.replicate (candA0 k A u v (S + 1) * p ^ c) true))
      (ZeroPadding.pad total (List.replicate (candB0 v * w ^ c) true))
      (ZeroPadding.pad total (List.replicate (candT k A u v (S + 1) p w c) true)) p w total capT T capF c j := by
    intro j
    have hj := j.isLt
    rw [show sinner D j = candFocus D (candI D j) from Fin.ext (by
      simp only [sinner, candFocus, candI, Fin.val_mk]; split_ifs <;> omega), ha3, install_slot _ (candFocus_inj D),
      o3in]
  have a3_1 : a3 (spos D 1) = List.replicate n true := by
    rw [show spos D 1 = candFocus D (cpos D 1) from Fin.ext (by simp [spos, candFocus, cpos]), ha3,
      install_slot _ (candFocus_inj D), o3n]
  have a3_x : ∀ j : ℕ, (h : j < 9) → 4 ≤ j → a3 (xpos D j h) = [] := by
    intro j h h4
    rw [a3_away _ (by intro i; have := i.isLt; simp only [candFocus, xpos, Fin.val_mk]; split_ifs <;> omega),
      a2_off _ (by spos_tac) (by spos_tac) (by spos_tac), hx,
      scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
  -- `S + [flag]`
  have hs := ready_pad _ _ _ _ ![total, 1, 0, 0] (ClockUnarySum.sum_ready S f.toNat)
  have g4 := hs.focus (slotsW4 D) (by scan_inj_tac) a3 (by
    intro j; fin_cases j
    · show a3 (spos D 0) = _; rw [a3_0]; rfl
    · show a3 (candFocus D (candFlag D)) = _; rw [a3_flag]; exact (pad_one_flag f).symm
    · show a3 (xpos D 4) = _; rw [a3_x 4 (by decide) (by decide)]; rfl
    · show a3 (xpos D 5) = _; rw [a3_x 5 (by decide) (by decide)]; rfl)
  set a4 := install (slotsW4 D) a3 (fun i => ZeroPadding.pad (![total, 1, 0, 0] i)
    (![List.replicate S true, List.replicate f.toNat true, List.replicate (S + f.toNat) true,
      List.replicate (S + f.toNat + 2) false] i)) with ha4
  have a4_away : ∀ i : Fin (scanTapes D), i.val ≠ 0 → i.val ≠ Clause.tapes D + 109 → i.val ≠ candTapes D + 4 →
      i.val ≠ candTapes D + 5 → a4 i = a3 i := by
    intro i h0 h1 h2 h3
    rw [ha4, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (apply fin_ne; simp [slotsW4, spos, xpos, candFocus_flag]; omega))]
  have a4_0 : a4 (spos D 0) = ZeroPadding.pad total (List.replicate S true) := by
    rw [ha4, show spos D 0 = slotsW4 D 0 from rfl, install_slot _ (by scan_inj_tac)]; rfl
  have a4_4 : a4 (xpos D 4) = List.replicate (S + f.toNat) true := by
    rw [ha4, show xpos D 4 = slotsW4 D 2 from rfl, install_slot _ (by scan_inj_tac)]
    simp [ZeroPadding.pad]
  -- the write-back
  obtain ⟨o5, r5, o50, o51, o52, o53⟩ := writeOne_ready (ZeroPadding.pad total (List.replicate S true)) total capT
    (S + f.toNat) hcap (by rw [pad_length_total _ _ hS])
  have g5 := r5.focus (slotsW5 D) (by scan_inj_tac) a4 (by
    intro j; fin_cases j
    · show a4 (spos D 0) = _; rw [a4_0]; rfl
    · show a4 (spos D 7) = _
      rw [a4_away _ (by spos_tac) (by spos_tac) (by spos_tac) (by spos_tac),
        show spos D 7 = sinner D 5 from rfl, a3_inner]
      simp [innerTapes, writeOneInput]
    · show a4 (spos D 8) = _
      rw [a4_away _ (by spos_tac) (by spos_tac) (by spos_tac) (by spos_tac),
        show spos D 8 = sinner D 6 from rfl, a3_inner]
      simp [innerTapes, writeOneInput]
    · show a4 (xpos D 4) = _; rw [a4_4]; rfl
    · show a4 (xpos D 6) = _
      rw [a4_away _ (by spos_tac) (by spos_tac) (by spos_tac)
        (by spos_tac), a3_x 6 (by decide) (by decide)]; rfl
    · show a4 (xpos D 7) = _
      rw [a4_away _ (by spos_tac) (by spos_tac) (by spos_tac)
        (by spos_tac), a3_x 7 (by decide) (by decide)]; rfl
    · show a4 (xpos D 8) = _
      rw [a4_away _ (by spos_tac) (by spos_tac) (by spos_tac)
        (by spos_tac), a3_x 8 (by decide) (by decide)]; rfl)
  refine ⟨_, _, ?_, ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.join _ _ _ _ _ _ _ g3 (ClockJoin.join _ _ _ _ _ _ _ g4 g5))), ?_, ?_, ?_⟩
  · have := Bool.toNat_le f
    unfold scanRoundBound writeOneCost
    omega
  · rw [show spos D 0 = slotsW5 D 0 from rfl, install_slot _ (by scan_inj_tac), o50]
  · rw [install_other _ _ _ _ (by
        intro j; fin_cases j <;> (apply fin_ne; simp [slotsW5, spos, xpos])),
      a4_away _ (by spos_tac) (by spos_tac) (by spos_tac) (by spos_tac), a3_1]
  · intro j
    have hj := j.isLt
    by_cases h5 : j.val = 5
    · rw [show sinner D j = slotsW5 D 1 from Fin.ext (by simp [sinner, slotsW5, spos, h5]),
        install_slot _ (by scan_inj_tac), o51]
      simp [innerTapes, h5]
    · by_cases h6 : j.val = 6
      · rw [show sinner D j = slotsW5 D 2 from Fin.ext (by simp [sinner, slotsW5, spos, h6]),
          install_slot _ (by scan_inj_tac), o52]
        simp [innerTapes, h6]
      · rw [install_other _ _ _ _ (by
            intro i; fin_cases i <;> (apply fin_ne; simp [slotsW5, spos, xpos, sinner]; omega)),
          a4_away _ (by spos_tac) (by spos_tac) (by spos_tac)
            (by spos_tac), a3_inner]

end Scan

end NearCubicWires.WireExponent3_5.Transfer
