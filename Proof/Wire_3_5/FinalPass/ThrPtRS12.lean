import Proof.Wire_3_5.FinalPass.ThrPtRS11

/-! # S2 (THR per point), part 26: the primes loop, whole (P3:2587-2630)

`RowStepOK`: the row's contract at prime `p` (from `RowReady` at `g`'s index and `p`, the accumulator gains `F`, the
state `RowReady` again, in `C` steps; `rowStep_spec` meets it). `primeLoop`: while stream `8`'s cell is `1` — read
`p`, the row, `p` cleared. **`primeLoop_spec`**: over the primes list `L` (stream `8` = `U ++ unaryList L`, head at
`|U|`), the accumulator gains `Σ_{p ∈ L} F p`, the head moves to the end, the state stays `RowReady`. Paper quantity:
`Σ_p R̂_{g,p}(c, u, v)` for one `g`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ) (σB : WState 16 118)

/-- The fields `RowReady` reads. -/
def rrKey (t : TSt) : List Bool × ℕ × ℕ × List Bool × List Bool × List Bool × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ ×
    List Bool :=
  (t.rw, t.hRw, t.rwH, t.z, t.ss, t.rep, t.hRep, t.rH, t.d, t.dRem, t.kS, t.rS, t.r82, t.w92, t.x)

theorem RowReady.cast {M τ : ℕ} {X : List Bool} {t t' : TSt} (h : RowReady t M τ X) (e : rrKey t' = rrKey t) :
    RowReady t' M τ X := by
  simp only [rrKey, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := e
  exact ⟨by rw [e1]; exact h.rw, by rw [e2]; exact h.hRw, by rw [e3]; exact h.rwH, by rw [e4]; exact h.z,
    by rw [e5]; exact h.ss, by rw [e6]; exact h.rep, by rw [e7]; exact h.hRep, by rw [e8]; exact h.rH,
    by rw [e9]; exact h.d, by rw [e10]; exact h.dRem, by rw [e11]; exact h.kS, by rw [e12]; exact h.rS,
    by rw [e13]; exact h.r82, by rw [e14]; exact h.w92, by rw [e15]; exact h.x⟩

/-- **The row's contract** at prime `p`: gain `F`, `C` steps. -/
def RowStepOK (M τ : ℕ) (X : List Bool) (gi F C p : ℕ) : Prop :=
  ∀ t : TSt, RowReady t M τ X → t.gi = gi → t.p = p → t.acc + 1 ≤ cap →
    ∃ R1 Z1 S1 P1 : List Bool,
      RowReady { t with rw := R1, z := Z1, ss := S1, rep := P1, acc := t.acc + F } M τ X ∧
      WExec cap rowStep (t.w σB) ({ t with rw := R1, z := Z1, ss := S1, rep := P1, acc := t.acc + F }.w σB) C

/-- **The primes loop.** -/
noncomputable def primeLoop : TProg := .whs 8 (.seq (WM.readU 8 110 7) (.seq rowStep (WM.clear 7)))

/-- The primes loop's step bound. -/
def primeLoopCost (C : ℕ → ℕ) : List ℕ → ℕ
  | [] => 1
  | q :: L => 11 * q + 7 + 1 + (C q + 1 + (3 * q + 1)) + 2 + primeLoopCost C L

theorem primeLoop_spec (M τ : ℕ) (X : List Bool) (gi : ℕ) (F C : ℕ → ℕ) (hF : ∀ p, F p ≤ 1) :
    ∀ (L : List ℕ) (U : List Bool) (t : TSt), σB.st 8 = U ++ PrimAsm.Data.unaryList L → (∀ p ∈ L, 0 < p) →
      (∀ p ∈ L, RowStepOK cap σB M τ X gi (F p) (C p) p) → RowReady t M τ X → t.gi = gi → t.p = 0 →
      t.hPr = U.length → t.prH = U.length → t.acc + L.length ≤ cap →
      U.length + (PrimAsm.Data.unaryList L).length ≤ cap →
      ∃ R1 Z1 S1 P1 : List Bool,
        RowReady { t with
          rw := R1, z := Z1, ss := S1, rep := P1, acc := t.acc + (L.map F).sum,
          hPr := U.length + (PrimAsm.Data.unaryList L).length,
          prH := U.length + (PrimAsm.Data.unaryList L).length } M τ X ∧
        WExec cap primeLoop (t.w σB) ({ t with
          rw := R1, z := Z1, ss := S1, rep := P1, acc := t.acc + (L.map F).sum,
          hPr := U.length + (PrimAsm.Data.unaryList L).length,
          prH := U.length + (PrimAsm.Data.unaryList L).length }.w σB) (primeLoopCost C L)
  | [], U, t, hst, _, _, hR, _, _, hh, hH, _, _ => by
    refine ⟨t.rw, t.z, t.ss, t.rep, RowReady.cast hR rfl, ?_⟩
    have hb : wbit (t.w σB) 8 = false := by
      unfold wbit
      rw [tw_st_other σB t 8 (by decide), tw_sh_hPr, hst, hh]
      simpa [PrimAsm.Data.unaryList] using rdEnd U
    refine WExec.cast cap (WExec.whsF hb) (tw_eq ?_) le_rfl
    obtain ⟨⟩ := t
    simp only at hh hH ⊢
    simp [PrimAsm.Data.unaryList, hh, hH]
  | q :: L, U, t, hst, hpos, hstep, hR, hg, hp0, hh, hH, hacc, hcap => by
    have hq : 0 < q := hpos q List.mem_cons_self
    rw [unaryList_cons] at hst hcap
    simp only [List.length_append, List.length_replicate, List.length_cons] at hcap
    simp only [List.length_cons] at hacc
    have hb : wbit (t.w σB) 8 = true := by
      unfold wbit
      rw [tw_st_other σB t 8 (by decide), tw_sh_hPr, hst, hh]
      have := rdOnes U (false :: PrimAsm.Data.unaryList L) q 0 hq
      rwa [Nat.add_zero] at this
    have e1 := readP_spec cap σB t U (PrimAsm.Data.unaryList L) q hst hh (by omega) (by omega)
    obtain ⟨t1, ht1⟩ : ∃ s : TSt, s = { t with hPr := t.hPr + q + 1, prH := t.prH + q + 1, p := t.p + q } :=
      ⟨_, rfl⟩
    rw [← ht1] at e1
    obtain ⟨R1, Z1, S1, P1, hR2, e2⟩ := hstep q List.mem_cons_self t1 (by subst ht1; exact RowReady.cast hR rfl)
      (by subst ht1; exact hg) (by subst ht1; show t.p + q = q; omega) (by subst ht1; show t.acc + 1 ≤ cap; omega)
    obtain ⟨t2, ht2⟩ : ∃ s : TSt, s = { t1 with rw := R1, z := Z1, ss := S1, rep := P1, acc := t1.acc + F q } :=
      ⟨_, rfl⟩
    rw [← ht2] at e2 hR2
    have e3 := clearP_spec cap σB t2 q (by subst ht2 ht1; show t.p + q = q; omega) (by omega)
    obtain ⟨t3, ht3⟩ : ∃ s : TSt, s = { t2 with p := 0 } := ⟨_, rfl⟩
    rw [← ht3] at e3
    have hF1 := hF q
    obtain ⟨R1', Z1', S1', P1', hR3, e4⟩ := primeLoop_spec M τ X gi F C hF L (U ++ (List.replicate q true ++ [false]))
      t3 (by rw [hst]; simp) (fun p hp => hpos p (List.mem_cons_of_mem q hp))
      (fun p hp => hstep p (List.mem_cons_of_mem q hp)) (by subst ht3; exact RowReady.cast hR2 rfl) (by subst ht3 ht2 ht1; exact hg)
      (by subst ht3; rfl) (by subst ht3 ht2 ht1; simp only [List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]; omega)
      (by subst ht3 ht2 ht1; simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]; omega)
      (by subst ht3 ht2 ht1; show t.acc + F q + L.length ≤ cap; omega)
      (by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)
    refine ⟨R1', Z1', S1', P1', by subst ht3 ht2 ht1; exact RowReady.cast hR3 rfl, ?_⟩
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) e4) (tw_eq ?_) (by simp only [primeLoopCost]; omega)
    clear e1 e2 e3 e4 hR2 hR3
    subst ht3 ht2 ht1
    obtain ⟨⟩ := t
    simp only at hh hH hp0 ⊢
    simp only [TSt.mk.injEq, true_and, and_true, unaryList_cons, List.map_cons, List.sum_cons, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    repeat' constructor
    all_goals omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
