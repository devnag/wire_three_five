import Proof.Wire_3_5.Primitive.SeedFix.C4KWd

/-! # C4KW, part 9: the B1 framework (rulers, emissions, erasures)

Stage B1 of the kept words writer is one streams-only word program in three phases over a fixed layout: the outputs
`0 … no−1` (blank), the inputs `no … lo−1` (unary counts), the rulers `lo … ns` (blank).
* **Rulers** (`RS`: `mkI` a ruler from an input count, `zero`, `ap` a sum, `mul` a product): step `k` writes the
  marker ruler `mk (rv (lo + k))` from earlier rulers or an unread input (invariant `IR`, step `rs_step`).
* **Emissions** (`Em`: a constant, a unary run `emitU`, the flag `decM`, `bin1M`, `padM`): output `j` receives
  `frame (word j)` from the rulers (invariant `IE`, step `em_step`).
* **Erasures**: each ruler overwritten by falses (invariant `IX`, step `ex_step`).
**`b1_run`**: the whole program from any `IR 0` state to an `IX` state (every output framed, the inputs kept, the rulers
falses) within `b1Cost`, when every ruler value is at most `M`.

Paper quantity of the main type: the Hb printer's static words (P3:2253-2290), written from the call's numbers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B1
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Sequences of steps under an invariant -/

/-- The steps `f 0, …, f (k − 1)` in order. -/
def seqN (f : ℕ → WM ns nr) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (seqN f k) (f k)

theorem seqN_run (f : ℕ → WM ns nr) (I : ℕ → WState ns nr → Prop) (B K : ℕ)
    (hstep : ∀ (k : ℕ) (σ : WState ns nr), k < K → I k σ →
      ∃ (σ' : WState ns nr) (c : ℕ), WExec cap (f k) σ σ' c ∧ c ≤ B ∧ I (k + 1) σ') :
    ∀ k : ℕ, k ≤ K → ∀ σ : WState ns nr, I 0 σ → ∃ σ' : WState ns nr, WExec cap (seqN f k) σ σ' (k * (B + 1)) ∧ I k σ'
  | 0, _, σ, h => ⟨σ, WExec.mono (WExec.skip σ) (Nat.zero_le _), h⟩
  | k + 1, hk, σ, h => by
    obtain ⟨σ1, h1, i1⟩ := seqN_run f I B K hstep k (by omega) σ h
    obtain ⟨σ2, c, h2, hc, i2⟩ := hstep k σ1 (by omega) i1
    refine ⟨σ2, WExec.mono (WExec.seq h1 h2) ?_, i2⟩
    rw [Nat.succ_mul]; omega

/-- The stream `lo + k` (read mod `ns + 1`; the layouts keep it in range). -/
def zOf (lo k : ℕ) : Fin (ns + 1) := ⟨(lo + k) % (ns + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem zOf_val {lo k : ℕ} (h : lo + k < ns + 1) : (zOf (ns := ns) lo k).val = lo + k := Nat.mod_eq_of_lt h

/-! ## Rulers -/

/-- A ruler step: from an input count, the ruler `mk 0`, a sum `x + y + e`, a product `x·y`. -/
inductive RS (ns : ℕ) where
  | mkI (A : Fin (ns + 1))
  | zero
  | ap (X Y : Fin (ns + 1)) (e : ℕ)
  | mul (X Y : Fin (ns + 1))
  deriving DecidableEq

/-- The step's program, writing the ruler `Z`. -/
def RS.prog : RS ns → Fin (ns + 1) → WM ns nr
  | .mkI A, Z => mkM A Z
  | .zero, Z => .seq (wlist Z [false]) (.bwd Z)
  | .ap X Y e, Z => apM X Y Z e
  | .mul X Y, Z => mulM X Y Z

/-- The step's cost. -/
def RS.cost (rv : Fin (ns + 1) → ℕ) (Z : Fin (ns + 1)) : RS ns → ℕ
  | .mkI _ => mkCost (rv Z)
  | .zero => 6
  | .ap X Y e => apCost (rv X) (rv Y) e
  | .mul X Y => mulCost (rv X) (rv Y)

/-- The input `i` is not read by the steps before `k`. -/
def unread (stp : ℕ → RS ns) (k : ℕ) (i : Fin (ns + 1)) : Prop := ∀ j, j < k → stp j ≠ .mkI i

instance unread_dec (stp : ℕ → RS ns) (k : ℕ) (i : Fin (ns + 1)) : Decidable (unread stp k i) :=
  inferInstanceAs (Decidable (∀ j, j < k → stp j ≠ .mkI i))

theorem unread_mono {stp : ℕ → RS ns} {k : ℕ} {i : Fin (ns + 1)} (h : unread stp (k + 1) i) : unread stp k i :=
  fun j hj => h j (by omega)

/-- The step `k`'s side conditions (its operands done, its value). -/
def RS.ok (no lo : ℕ) (inp : Fin (ns + 1) → List Bool) (rv : Fin (ns + 1) → ℕ) (stp : ℕ → RS ns) (k : ℕ) :
    RS ns → Prop
  | .mkI A => no ≤ A.val ∧ A.val < lo ∧ unread stp k A ∧ inp A = List.replicate (rv (zOf lo k)) true
  | .zero => rv (zOf lo k) = 0
  | .ap X Y e => lo ≤ X.val ∧ X.val < lo + k ∧ lo ≤ Y.val ∧ Y.val < lo + k ∧ e ≤ 2 ∧
      rv (zOf lo k) = rv X + rv Y + e
  | .mul X Y => lo ≤ X.val ∧ X.val < lo + k ∧ lo ≤ Y.val ∧ Y.val < lo + k ∧ X ≠ Y ∧ rv (zOf lo k) = rv X * rv Y

/-- **The ruler phase's invariant** after `k` steps. -/
structure IR (no lo : ℕ) (inp : Fin (ns + 1) → List Bool) (rv : Fin (ns + 1) → ℕ) (stp : ℕ → RS ns) (k : ℕ)
    (σ : WState ns nr) : Prop where
  hcell : σ.cell = false
  hout : ∀ i : Fin (ns + 1), i.val < no → σ.st i = [] ∧ σ.sh i = 0
  hinp : ∀ i : Fin (ns + 1), no ≤ i.val → i.val < lo → σ.st i = inp i
  hinh : ∀ i : Fin (ns + 1), no ≤ i.val → i.val < lo → unread stp k i → σ.sh i = 0
  hdone : ∀ i : Fin (ns + 1), lo ≤ i.val → i.val < lo + k → σ.st i = mk (rv i) ∧ σ.sh i = 0
  hblank : ∀ i : Fin (ns + 1), lo + k ≤ i.val → σ.st i = [] ∧ σ.sh i = 0

theorem IR_succ {no lo : ℕ} {inp : Fin (ns + 1) → List Bool} {rv : Fin (ns + 1) → ℕ} {stp : ℕ → RS ns} {k : ℕ}
    {σ σ' : WState ns nr} (h : IR no lo inp rv stp k σ) (hk : lo + k < ns + 1)
    (hst : ∀ i : Fin (ns + 1), i ≠ zOf lo k → σ'.st i = σ.st i) (hZ : σ'.st (zOf lo k) = mk (rv (zOf lo k)))
    (hZ0 : σ'.sh (zOf lo k) = 0)
    (hsh : ∀ i : Fin (ns + 1), i ≠ zOf lo k → (i.val < no ∨ lo ≤ i.val ∨ unread stp (k + 1) i) → σ'.sh i = σ.sh i)
    (hc : σ'.cell = σ.cell) (hlo : no ≤ lo) : IR no lo inp rv stp (k + 1) σ' := by
  have hz := zOf_val (ns := ns) hk
  have ne : ∀ i : Fin (ns + 1), i.val ≠ lo + k → i ≠ zOf lo k := fun i hi e => hi (by rw [e, hz])
  refine ⟨by rw [hc]; exact h.hcell, fun i hi => ?_, fun i h1 h2 => ?_, fun i h1 h2 hu => ?_, fun i h1 h2 => ?_,
    fun i h1 => ?_⟩
  · have hn := ne i (by omega)
    rw [hst i hn, hsh i hn (Or.inl hi)]; exact h.hout i hi
  · rw [hst i (ne i (by omega))]; exact h.hinp i h1 h2
  · rw [hsh i (ne i (by omega)) (Or.inr (Or.inr hu))]; exact h.hinh i h1 h2 (unread_mono hu)
  · by_cases e : i.val = lo + k
    · have e' : i = zOf lo k := Fin.ext (by rw [e, hz])
      subst e'; exact ⟨hZ, hZ0⟩
    · have hn := ne i e
      rw [hst i hn, hsh i hn (Or.inr (Or.inl h1))]; exact h.hdone i h1 (by omega)
  · have hn := ne i (by omega)
    rw [hst i hn, hsh i hn (Or.inr (Or.inl (by omega)))]; exact h.hblank i (by omega)

/-- **One ruler step.** -/
theorem rs_step {no lo : ℕ} (inp : Fin (ns + 1) → List Bool) (rv : Fin (ns + 1) → ℕ) (stp : ℕ → RS ns) (k : ℕ)
    (σ : WState ns nr) (hlo : no ≤ lo) (hk : lo + k < ns + 1) (hok : (stp k).ok no lo inp rv stp k)
    (h : IR no lo inp rv stp k σ) :
    ∃ σ' : WState ns nr, WExec cap ((stp k).prog (zOf lo k)) σ σ' ((stp k).cost rv (zOf lo k)) ∧
      IR no lo inp rv stp (k + 1) σ' := by
  have hz := zOf_val (ns := ns) hk
  have hZb := h.hblank (zOf lo k) (by omega)
  have hrd : ∀ i : Fin (ns + 1), i.val < lo + k → i ≠ zOf lo k := fun i h2 e => by rw [e] at h2; omega
  revert hok
  cases hs : stp k with
  | mkI A =>
    intro hok
    obtain ⟨h1, h2, hu, hin⟩ := hok
    have hAZ : A ≠ zOf lo k := hrd A (by omega)
    have hA := (h.hinp A h1 h2).trans hin
    have hA0 := h.hinh A h1 h2 hu
    refine ⟨_, mkM_spec cap A (zOf lo k) hAZ (rv (zOf lo k)) σ hA hA0 hZb.1 hZb.2,
      IR_succ h hk (fun i hi => ?_) ?_ ?_ (fun i hi hc => ?_) rfl hlo⟩
    · simp only [WState.seth_st]; exact apd_st_ne σ _ i hi _
    · simp only [WState.seth_st]; rw [apd_st_d, hZb.1]; rfl
    · simp only [WState.seth_sh]; rw [Function.update_of_ne hAZ.symm, Function.update_self]
    · have hiA : i ≠ A := by
        rintro rfl
        rcases hc with hc | hc | hc
        · omega
        · omega
        · exact hc k (by omega) hs
      simp only [WState.seth_sh]
      rw [Function.update_of_ne hiA, Function.update_of_ne hi, apd_sh_ne σ _ i hi]
  | zero =>
    intro hok
    have t1 := wlist_spec cap (zOf lo k) [false] σ (by rw [hZb.1, hZb.2]; rfl)
    have t2 := WExec.bwd (cap := cap) (zOf lo k) (apd σ (zOf lo k) [false])
    refine ⟨_, WExec.mono (WExec.seq t1 t2) (by simp [RS.cost]), IR_succ h hk (fun i hi => ?_) ?_ ?_
      (fun i hi _ => ?_) rfl hlo⟩
    · simp only [WState.seth_st]; exact apd_st_ne σ _ i hi _
    · simp only [WState.seth_st]; rw [apd_st_d, hZb.1, hok]; rfl
    · simp only [WState.seth_sh, Function.update_self]; rw [apd_sh_d, hZb.1]; rfl
    · simp only [WState.seth_sh]; rw [Function.update_of_ne hi, apd_sh_ne σ _ i hi]
  | ap X Y e =>
    intro hok
    obtain ⟨hX1, hX2, hY1, hY2, _, hv⟩ := hok
    have hX := h.hdone X hX1 hX2
    have hY := h.hdone Y hY1 hY2
    refine ⟨_, apM_spec cap X Y (zOf lo k) (hrd X hX2) (hrd Y hY2) (rv X) (rv Y) e σ hX.1 hX.2 hY.1 hY.2 hZb.1 hZb.2,
      IR_succ h hk (fun i hi => ?_) ?_ ?_ (fun i hi _ => ?_) rfl hlo⟩
    · simp only [WState.seth_st]; exact apd_st_ne σ _ i hi _
    · simp only [WState.seth_st]; rw [apd_st_d, hZb.1, hv]; rfl
    · simp only [WState.seth_sh, Function.update_self]
    · simp only [WState.seth_sh]; rw [Function.update_of_ne hi, apd_sh_ne σ _ i hi]
  | mul X Y =>
    intro hok
    obtain ⟨hX1, hX2, hY1, hY2, hXY, hv⟩ := hok
    have hX := h.hdone X hX1 hX2
    have hY := h.hdone Y hY1 hY2
    refine ⟨_, mulM_spec cap X Y (zOf lo k) hXY (hrd X hX2) (hrd Y hY2) (rv X) (rv Y) σ hX.1 hX.2 hY.1 hY.2 hZb.1
      hZb.2, IR_succ h hk (fun i hi => ?_) ?_ ?_ (fun i hi _ => ?_) rfl hlo⟩
    · simp only [WState.seth_st]; exact apd_st_ne σ _ i hi _
    · simp only [WState.seth_st]; rw [apd_st_d, hZb.1, hv]; rfl
    · simp only [WState.seth_sh, Function.update_self]
    · simp only [WState.seth_sh]; rw [Function.update_of_ne hi, apd_sh_ne σ _ i hi]

theorem rs_cost_le {no lo : ℕ} {inp : Fin (ns + 1) → List Bool} {rv : Fin (ns + 1) → ℕ} {stp : ℕ → RS ns} {k : ℕ}
    (M : ℕ) (hM : ∀ i, rv i ≤ M) (s : RS ns) (hok : s.ok no lo inp rv stp k) :
    s.cost rv (zOf lo k) ≤ 100 * (M + 1) ^ 2 := by
  have hq : M + 1 ≤ (M + 1) ^ 2 := by nlinarith
  cases s with
  | mkI A => have := hM (zOf lo k); simp only [RS.cost, mkCost]; omega
  | zero => simp only [RS.cost]; omega
  | ap X Y e =>
    have := hM X; have := hM Y; have he := hok.2.2.2.2.1
    simp only [RS.cost, apCost]; omega
  | mul X Y =>
    have hx := hM X; have hy := hM Y
    have hxy : rv X * rv Y ≤ M * M := Nat.mul_le_mul hx hy
    have hsq : (M + 1) ^ 2 = M * M + 2 * M + 1 := by ring
    simp only [RS.cost, mulCost]
    nlinarith

/-! ## Emissions -/

/-- An emission: a constant word, a unary run from a ruler, the flag of three rulers, `frame (binary a 1)`, the pad. -/
inductive Em (ns : ℕ) where
  | c (w : List Bool)
  | u (R : Fin (ns + 1)) (sk : Bool) (u v : List Bool)
  | dec (R1 R2 R3 : Fin (ns + 1))
  | bin (R : Fin (ns + 1))
  | pad (X C : Fin (ns + 1))

/-- The emitted word (written framed). -/
def Em.word (rv : Fin (ns + 1) → ℕ) : Em ns → List Bool
  | .c w => w
  | .u R sk uu vv => repW (rv R - (if sk then 1 else 0)) uu ++ vv
  | .dec R1 R2 R3 => [decide (rv R1 ≠ 0 ∧ rv R2 ≠ 0 ∧ rv R3 ≠ 0)]
  | .bin R => bin1W (rv R)
  | .pad X C => padW (rv X) (rv C)

/-- The emission's program onto the output `O`. -/
def Em.prog (O : Fin (ns + 1)) : Em ns → WM ns nr
  | .c w => wlist O (frame w)
  | .u R sk uu vv => emitU R O sk uu vv
  | .dec R1 R2 R3 => decM R1 R2 R3 O
  | .bin R => bin1M R O
  | .pad X C => padM X C O

/-- The emission's cost. -/
def Em.cost (rv : Fin (ns + 1) → ℕ) : Em ns → ℕ
  | .c w => 4 * (frame w).length
  | .u R _ uu vv => emitCost (rv R) uu vv
  | .dec _ _ _ => 40
  | .bin R => 25 * rv R + 40
  | .pad X C => 20 * rv X + 16 * rv C + 40

/-- The emission's side conditions (its rulers at `lo` or above, short constant words). -/
def Em.okb (lo : ℕ) : Em ns → Bool
  | .c w => decide (w.length ≤ 2)
  | .u R _ uu vv => decide (lo ≤ R.val) && decide (uu.length ≤ 2) && decide (vv.length ≤ 2)
  | .dec R1 R2 R3 => decide (lo ≤ R1.val) && decide (lo ≤ R2.val) && decide (lo ≤ R3.val) && decide (R1 ≠ R2) &&
      decide (R1 ≠ R3) && decide (R2 ≠ R3)
  | .bin R => decide (lo ≤ R.val)
  | .pad X C => decide (lo ≤ X.val) && decide (lo ≤ C.val) && decide (X ≠ C)

theorem frame_length (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  rw [frame_prs, List.length_append, prs_length]; rfl

/-- **One emission** onto a blank-ended output below the rulers. -/
theorem em_run (lo : ℕ) (rv : Fin (ns + 1) → ℕ) (e : Em ns) (O : Fin (ns + 1)) (σ : WState ns nr)
    (hok : e.okb lo = true) (hO : O.val < lo) (hR : ∀ i : Fin (ns + 1), lo ≤ i.val → σ.st i = mk (rv i) ∧ σ.sh i = 0)
    (hOl : σ.sh O = (σ.st O).length) :
    WExec cap (e.prog O) σ (apd σ O (frame (e.word rv))) (e.cost rv) := by
  have neO : ∀ R : Fin (ns + 1), lo ≤ R.val → R ≠ O := fun R h e => by rw [e] at h; omega
  cases e with
  | c w => exact wlist_spec cap O (frame w) σ hOl
  | u R sk uu vv =>
    simp only [Em.okb, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact emitU_spec cap R O (neO R hok.1.1) sk uu vv (rv R) σ (hR R hok.1.1).1 (hR R hok.1.1).2 hOl
  | dec R1 R2 R3 =>
    simp only [Em.okb, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h12⟩, h13⟩, h23⟩ := hok
    exact decM_spec cap R1 R2 R3 O h12 h13 h23 (neO R1 h1) (neO R2 h2) (neO R3 h3) (rv R1) (rv R2) (rv R3) σ
      (hR R1 h1).1 (hR R2 h2).1 (hR R3 h3).1 (hR R1 h1).2 (hR R2 h2).2 (hR R3 h3).2 hOl
  | bin R =>
    simp only [Em.okb, decide_eq_true_eq] at hok
    exact bin1M_spec cap R O (neO R hok) (rv R) σ (hR R hok).1 (hR R hok).2 hOl
  | pad X C =>
    simp only [Em.okb, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hX, hC⟩, hXC⟩ := hok
    exact padM_spec cap X C O hXC (neO X hX) (neO C hC) (rv X) (rv C) σ (hR X hX).1 (hR C hC).1 (hR X hX).2
      (hR C hC).2 hOl

theorem em_cost_le (lo : ℕ) (rv : Fin (ns + 1) → ℕ) (M : ℕ) (hM : ∀ i, rv i ≤ M) (e : Em ns) (hok : e.okb lo = true) :
    e.cost rv ≤ 100 * (M + 1) ^ 2 := by
  have hq : M + 1 ≤ (M + 1) ^ 2 := by nlinarith
  cases e with
  | c w =>
    simp only [Em.okb, decide_eq_true_eq] at hok
    simp only [Em.cost, frame_length]; omega
  | u R sk uu vv =>
    simp only [Em.okb, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hR := hM R
    have h1 : rv R * (8 * uu.length + 4) ≤ M * 20 := Nat.mul_le_mul hR (by omega)
    simp only [Em.cost, emitCost]; omega
  | dec R1 R2 R3 => simp only [Em.cost]; omega
  | bin R => have := hM R; simp only [Em.cost]; omega
  | pad X C => have := hM X; have := hM C; simp only [Em.cost]; omega

/-- **The emission phase's invariant** after `j` emissions. -/
structure IE (no lo : ℕ) (inp : Fin (ns + 1) → List Bool) (rv : Fin (ns + 1) → ℕ) (ems : ℕ → Em ns) (j : ℕ)
    (σ : WState ns nr) : Prop where
  hcell : σ.cell = false
  hdone : ∀ i : Fin (ns + 1), i.val < j → σ.st i = frame ((ems i.val).word rv)
  hout : ∀ i : Fin (ns + 1), j ≤ i.val → i.val < no → σ.st i = [] ∧ σ.sh i = 0
  hinp : ∀ i : Fin (ns + 1), no ≤ i.val → i.val < lo → σ.st i = inp i
  hrul : ∀ i : Fin (ns + 1), lo ≤ i.val → σ.st i = mk (rv i) ∧ σ.sh i = 0

/-- **One emission step.** -/
theorem em_step {no lo : ℕ} (inp : Fin (ns + 1) → List Bool) (rv : Fin (ns + 1) → ℕ) (ems : ℕ → Em ns) (j : ℕ)
    (σ : WState ns nr) (hj : j < no) (hlo : no ≤ lo) (hns : lo ≤ ns + 1) (hok : (ems j).okb lo = true)
    (h : IE no lo inp rv ems j σ) :
    ∃ σ' : WState ns nr, WExec cap ((ems j).prog (zOf 0 j)) σ σ' ((ems j).cost rv) ∧ IE no lo inp rv ems (j + 1) σ' := by
  have hz : (zOf (ns := ns) 0 j).val = j := by rw [zOf_val (by omega)]; omega
  have ne : ∀ i : Fin (ns + 1), i.val ≠ j → i ≠ zOf 0 j := fun i hi e => hi (by rw [e, hz])
  have hOb := h.hout (zOf 0 j) (by omega) (by omega)
  refine ⟨_, em_run cap lo rv (ems j) (zOf 0 j) σ hok (by omega) h.hrul (by rw [hOb.1, hOb.2]; rfl),
    ⟨h.hcell, fun i hi => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 => ?_⟩⟩
  · by_cases e : i.val = j
    · have e' : i = zOf 0 j := Fin.ext (by rw [e, hz])
      subst e'
      rw [apd_st_d, hOb.1, hz]; rfl
    · rw [apd_st_ne σ _ i (ne i e)]; exact h.hdone i (by omega)
  · rw [apd_st_ne σ _ i (ne i (by omega)), apd_sh_ne σ _ i (ne i (by omega))]; exact h.hout i (by omega) h2
  · rw [apd_st_ne σ _ i (ne i (by omega))]; exact h.hinp i h1 h2
  · rw [apd_st_ne σ _ i (ne i (by omega)), apd_sh_ne σ _ i (ne i (by omega))]; exact h.hrul i h1

/-! ## Erasures -/

/-- **The erasure phase's invariant** after `k` erasures. -/
structure IX (no lo : ℕ) (inp : Fin (ns + 1) → List Bool) (rv : Fin (ns + 1) → ℕ) (ems : ℕ → Em ns) (k : ℕ)
    (σ : WState ns nr) : Prop where
  hcell : σ.cell = false
  hout : ∀ i : Fin (ns + 1), i.val < no → σ.st i = frame ((ems i.val).word rv)
  hinp : ∀ i : Fin (ns + 1), no ≤ i.val → i.val < lo → σ.st i = inp i
  hera : ∀ i : Fin (ns + 1), lo ≤ i.val → i.val < lo + k → σ.st i = List.replicate (rv i + 1) false
  hrul : ∀ i : Fin (ns + 1), lo + k ≤ i.val → σ.st i = mk (rv i) ∧ σ.sh i = 0

/-- **One erasure step.** -/
theorem ex_step {no lo : ℕ} (inp : Fin (ns + 1) → List Bool) (rv : Fin (ns + 1) → ℕ) (ems : ℕ → Em ns) (k : ℕ)
    (σ : WState ns nr) (hlo : no ≤ lo) (hk : lo + k < ns + 1) (h : IX no lo inp rv ems k σ) :
    ∃ σ' : WState ns nr, WExec cap (eraseM (zOf lo k)) σ σ' (5 * rv (zOf lo k) + 3) ∧ IX no lo inp rv ems (k + 1) σ' := by
  have hz := zOf_val (ns := ns) hk
  have ne : ∀ i : Fin (ns + 1), i.val ≠ lo + k → i ≠ zOf lo k := fun i hi e => hi (by rw [e, hz])
  have hR := h.hrul (zOf lo k) (by omega)
  have stne : ∀ i : Fin (ns + 1), i ≠ zOf lo k →
      ((σ.sets (zOf lo k) (List.replicate (rv (zOf lo k) + 1) false)).seth (zOf lo k) (rv (zOf lo k) + 1)).st i =
        σ.st i := fun i hi => by
    simp only [WState.seth_st, WState.sets_st]; rw [Function.update_of_ne hi]
  refine ⟨_, eraseM_spec cap (zOf lo k) (rv (zOf lo k)) σ hR.1 hR.2,
    ⟨h.hcell, fun i hi => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 => ?_⟩⟩
  · rw [stne i (ne i (by omega))]; exact h.hout i hi
  · rw [stne i (ne i (by omega))]; exact h.hinp i h1 h2
  · by_cases e : i.val = lo + k
    · have e' : i = zOf lo k := Fin.ext (by rw [e, hz])
      subst e'
      simp only [WState.seth_st, WState.sets_st, Function.update_self]
    · rw [stne i (ne i e)]; exact h.hera i h1 (by omega)
  · have hn := ne i (by omega)
    rw [stne i hn]
    simp only [WState.seth_sh, WState.sets_sh]
    rw [Function.update_of_ne hn]; exact h.hrul i (by omega)

/-! ## The whole program -/

/-- **B1's program shape**: the `K` ruler steps, the `no` emissions, the `K` erasures. -/
def b1Prog (lo K no : ℕ) (stp : ℕ → RS ns) (ems : ℕ → Em ns) : WM ns nr :=
  .seq (seqN (fun k => (stp k).prog (zOf lo k)) K)
    (.seq (seqN (fun j => (ems j).prog (zOf 0 j)) no) (seqN (fun k => eraseM (zOf lo k)) K))

/-- Its cost at ruler bound `M`. -/
def b1Cost (K no M : ℕ) : ℕ :=
  K * (100 * (M + 1) ^ 2 + 1) + 1 + (no * (100 * (M + 1) ^ 2 + 1) + 1 + K * (100 * (M + 1) ^ 2 + 1))

/-- **The B1 run**: from the ruler phase's start, every output framed, the inputs kept, the rulers falses. -/
theorem b1_run {no lo K : ℕ} (inp : Fin (ns + 1) → List Bool) (rv : Fin (ns + 1) → ℕ) (stp : ℕ → RS ns)
    (ems : ℕ → Em ns) (M : ℕ) (hlo : no ≤ lo) (hK : lo + K = ns + 1)
    (hs : ∀ k, k < K → (stp k).ok no lo inp rv stp k) (he : ∀ j, j < no → (ems j).okb lo = true)
    (hM : ∀ i, rv i ≤ M) (σ : WState ns nr) (h0 : IR no lo inp rv stp 0 σ) :
    ∃ τ : WState ns nr, WExec cap (b1Prog lo K no stp ems) σ τ (b1Cost K no M) ∧ IX no lo inp rv ems K τ := by
  obtain ⟨σ1, t1, i1⟩ := seqN_run cap (fun k => (stp k).prog (zOf lo k)) (IR no lo inp rv stp)
    (100 * (M + 1) ^ 2) K (fun k σ hk hI => by
      obtain ⟨σ', t, hI'⟩ := rs_step cap inp rv stp k σ hlo (by omega) (hs k hk) hI
      exact ⟨σ', _, t, rs_cost_le M hM _ (hs k hk), hI'⟩) K le_rfl σ h0
  have e1 : IE no lo inp rv ems 0 σ1 :=
    ⟨i1.hcell, fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ h2 => i1.hout i h2, i1.hinp,
      fun i h1 => i1.hdone i h1 (by omega)⟩
  obtain ⟨σ2, t2, i2⟩ := seqN_run cap (fun j => (ems j).prog (zOf 0 j)) (IE no lo inp rv ems)
    (100 * (M + 1) ^ 2) no (fun j σ hj hI => by
      obtain ⟨σ', t, hI'⟩ := em_step cap inp rv ems j σ hj hlo (by omega) (he j hj) hI
      exact ⟨σ', _, t, em_cost_le lo rv M hM _ (he j hj), hI'⟩) no le_rfl σ1 e1
  have x0 : IX no lo inp rv ems 0 σ2 :=
    ⟨i2.hcell, fun i hi => i2.hdone i hi, i2.hinp, fun i h1 h2 => absurd h2 (by omega),
      fun i h1 => i2.hrul i (by omega)⟩
  obtain ⟨σ3, t3, i3⟩ := seqN_run cap (fun k => eraseM (zOf lo k)) (IX no lo inp rv ems)
    (100 * (M + 1) ^ 2) K (fun k σ hk hI => by
      obtain ⟨σ', t, hI'⟩ := ex_step cap inp rv ems k σ hlo (by omega) hI
      have := hM (zOf lo k)
      have hq : M + 1 ≤ (M + 1) ^ 2 := by nlinarith
      exact ⟨σ', _, t, by omega, hI'⟩) K le_rfl σ2 x0
  exact ⟨σ3, WExec.seq t1 (WExec.seq t2 t3), i3⟩

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B1
