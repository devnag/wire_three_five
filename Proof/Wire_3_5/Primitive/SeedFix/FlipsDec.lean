import Proof.Wire_3_5.Primitive.SeedFix.FlipsCorner
import Proof.Wire_3_5.FinalPass.SampleEval
import Proof.Wire_3_5.FinalPass.LiftR

/-! # FLIPS, part 2: a half's error vector from its index (P3:1188-1193, 1220-1222)

"Assign `r/2` whole blocks to each side" (P3:1212-1213); a cell's left (right) errors `u` (`v`) are the error vector of
the half with index `a < (b+1)^{r/2} = 2^{kh}` (`errorsEquiv`, mixed radix: one digit per block). C5's verified decoder
`FinalPass.Sample.dec right` (`dec_spec`, the frame of `decWord b (r/2) tail right (digits)`, which is
`List.ofFn (errorVector side (errorsEquiv.symm a))` by `errorVector_decode`) runs inside any word program through
C5's `WM.liftW`:

* `rew1` / `rew1_spec` (rewind one stream by a counted distance);
* `decStage right I O R` / **`decStage_spec`**: from `frame (binary (s·h) a)` on `I` and a stale frame on `O`, the frame of
  `decWord b h tl right (digitsOf s h (binary (s·h) a))` on `O`; both heads back at `0`, every register restored.

Paper quantity of the main type: the half's error vector (as `decWord`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Dec
variable {ns nr : ℕ} (cap : ℕ)

/-- Rewind one stream by the distance counted in `r`. -/
def rew1 (I : Fin (ns + 1)) (r : Fin nr) : WM ns nr := .whr r (.seq (.bwd I) (.dec r))

theorem rew1_spec (I : Fin (ns + 1)) (r : Fin nr) (c : ℕ) :
    ∀ σ : WState ns nr, σ.val r = c → σ.sh I = c → c ≤ cap →
      ∃ τ, WExec cap (rew1 I r) σ τ (c * 5 + 1) ∧ τ.sh I = 0 ∧ τ.val r = 0 ∧ τ.st = σ.st ∧
        (∀ i, i ≠ I → τ.sh i = σ.sh i) ∧ (∀ q, q ≠ r → τ.val q = σ.val q) ∧ τ.cell = σ.cell := by
  induction c with
  | zero =>
    intro σ hv hI _
    exact ⟨σ, WExec.mono (WExec.whrF hv) (by omega), hI, hv, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  | succ c ih =>
    intro σ hv hI hc
    have s1 := WExec.bwd (cap := cap) I σ
    have s2 := WExec.dec (cap := cap) r (σ.seth I (σ.sh I - 1)) (by show σ.val r ≤ cap; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ x, x = (σ.seth I (σ.sh I - 1)).setv r ((σ.seth I (σ.sh I - 1)).val r - 1) := ⟨_, rfl⟩
    rw [← hσ2] at s2
    have f2 : σ2.val r = c ∧ σ2.sh I = c ∧ σ2.st = σ.st ∧ (∀ i, i ≠ I → σ2.sh i = σ.sh i) ∧
        (∀ q, q ≠ r → σ2.val q = σ.val q) ∧ σ2.cell = σ.cell := by
      rw [hσ2]
      refine ⟨by simp [WState.seth, WState.setv, hv], by simp [WState.seth, WState.setv, hI], rfl,
        fun i hi => by simp [WState.seth, WState.setv, Function.update_apply, hi],
        fun q hq => by simp [WState.seth, WState.setv, Function.update_apply, hq], rfl⟩
    obtain ⟨τ, e, t1, t2, t3, t4, t5, t6⟩ := ih σ2 f2.1 f2.2.1 (by omega)
    exact ⟨τ, WExec.mono (WExec.whrT (by rw [hv]; omega) (WExec.seq s1 s2) e) (by ring_nf; omega), t1, t2,
      t3.trans f2.2.2.1, fun i hi => (t4 i hi).trans (f2.2.2.2.1 i hi), fun q hq => (t5 q hq).trans (f2.2.2.2.2.1 q hq),
      t6.trans f2.2.2.2.2.2⟩

/-- **A half's error vector from its index**: C5's decoder on the streams `I`, `O` and the registers `R`
(`R 0 … R 3` = `s, b, r/2, tail`, read-only), then the index stream rewound. -/
def decStage (right : Bool) (I O : Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq ((FinalPass.Sample.dec right).liftW ![I, O] R) (rew1 I (R 9))

/-- The stage's cost. -/
def decStageCost (s b h tl : ℕ) : ℕ := FinalPass.Sample.decCost s b h tl + 1 + ((2 * (s * h) + 1) * 5 + 1)

theorem decStage_spec (right : Bool) (I O : Fin (ns + 1)) (hIO : I ≠ O) (R : Fin 12 ↪ Fin nr) (ω : WState ns nr)
    (s b h tl kk : ℕ) (hbs : b + 1 = 2 ^ s) (Y : List Bool) (hY : Y.length = h * b + h * b + tl)
    (hI : ω.st I = frameP (binary (s * h) kk) ++ [false]) (hIh : ω.sh I = 0)
    (hO : ω.st O = frameP Y ++ [false]) (hOh : ω.sh O = 0)
    (hs : ω.val (R 0) = s) (hb : ω.val (R 1) = b) (hh : ω.val (R 2) = h) (ht : ω.val (R 3) = tl)
    (hz : ∀ i : Fin 12, 4 ≤ i.val → ω.val (R i) = 0)
    (hcap : 2 * 2 ^ s ≤ cap) (hsc : s ≤ cap) (hih : 2 * (s * h) + 1 ≤ cap) (hYc : 2 * Y.length ≤ cap)
    (hbc : b ≤ cap) (hc : h ≤ cap) (htc : tl ≤ cap) :
    ∃ ω', WExec cap (decStage right I O R) ω ω' (decStageCost s b h tl) ∧
      ω'.st O = frameP (FinalPass.Sample.decWord b h tl right
        (FinalPass.Sample.digitsOf s h (binary (s * h) kk))) ++ [false] ∧ ω'.sh O = 0 ∧
      ω'.st I = ω.st I ∧ ω'.sh I = 0 ∧ (∀ i, i ≠ I → i ≠ O → ω'.st i = ω.st i ∧ ω'.sh i = ω.sh i) ∧
      (∀ r, ω'.val r = ω.val r) ∧ ω'.cell = ω.cell := by
  let x : FinalPass.Sample.DSt := ⟨ω.st I, ω.st O, 0, 0, s, b, h, tl, 0, 0, 0, 0, 0, 0, ω.cell⟩
  have hd := FinalPass.Sample.dec_spec (cap := cap) right x s b h tl hbs kk Y [] [] rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl (by simp [x, hI]) (by simp [x, hO]) hY hcap hsc (by simp [x]; omega) hYc hbc hc htc
  have hfs : Function.Injective (![I, O] : Fin 2 → Fin (ns + 1)) := by
    intro a c e
    fin_cases a <;> fin_cases c <;> simp_all [Ne.symm hIO]
  have hL : LiftW ![I, O] R ω x.w' := by
    refine ⟨fun i => ?_, fun i => ?_, fun r => ?_, rfl⟩
    · fin_cases i
      · simpa [x, FinalPass.Sample.DSt.w'] using hIh
      · simpa [x, FinalPass.Sample.DSt.w'] using hOh
    · fin_cases i <;> simp [x, FinalPass.Sample.DSt.w']
    · fin_cases r
      · simpa [x, FinalPass.Sample.DSt.w'] using hs
      · simpa [x, FinalPass.Sample.DSt.w'] using hb
      · simpa [x, FinalPass.Sample.DSt.w'] using hh
      · simpa [x, FinalPass.Sample.DSt.w'] using ht
      all_goals (simp only [x, FinalPass.Sample.DSt.w']; first | exact hz _ (by decide) | simp [hz _ (by decide)])
  obtain ⟨ω1, e1, hL1, hO1⟩ := WExec.liftW cap cap le_rfl ![I, O] hfs R R.injective hd ω hL
  have v9 : ω1.val (R 9) = 2 * (s * h) + 1 := by
    rw [hL1.val 9]; simp [x, FinalPass.Sample.DSt.w']
  have sI1 : ω1.sh I = 2 * (s * h) + 1 := by
    have := hL1.sh 0; simp [x, FinalPass.Sample.DSt.w'] at this; exact this
  obtain ⟨ω', e2, t1, t2, t3, t4, t5, t6⟩ := rew1_spec cap I (R 9) (2 * (s * h) + 1) ω1 v9 sI1 hih
  refine ⟨ω', WExec.seq e1 e2, ?_, ?_, ?_, t1, ?_, ?_, ?_⟩
  · rw [t3]; have := hL1.st 1; simpa [x, FinalPass.Sample.DSt.w'] using this
  · rw [t4 O (Ne.symm hIO)]; have := hL1.sh 1; simpa [x, FinalPass.Sample.DSt.w'] using this
  · rw [t3]; have := hL1.st 0; simpa [x, FinalPass.Sample.DSt.w'] using this
  · intro i h1 h2
    have hn : ∀ j, (![I, O] : Fin 2 → Fin (ns + 1)) j ≠ i := by
      intro j; fin_cases j <;> simp [Ne.symm h1, Ne.symm h2]
    rw [t3, t4 i h1]
    exact ⟨(hO1.1 i hn).2, (hO1.1 i hn).1⟩
  · intro r
    by_cases hr : r = R 9
    · subst hr; rw [t2]; have := hz 9 (by decide); omega
    · rw [t5 r hr]
      by_cases hin : ∃ q, R q = r
      · obtain ⟨q, rfl⟩ := hin
        rw [hL1.val q]
        have hq9 : q ≠ 9 := fun e => hr (by rw [e])
        fin_cases q
        · simpa [x, FinalPass.Sample.DSt.w'] using hs.symm
        · simpa [x, FinalPass.Sample.DSt.w'] using hb.symm
        · simpa [x, FinalPass.Sample.DSt.w'] using hh.symm
        · simpa [x, FinalPass.Sample.DSt.w'] using ht.symm
        all_goals first | exact absurd rfl hq9 | (simp [x, FinalPass.Sample.DSt.w']; exact (hz _ (by decide)).symm)
      · exact hO1.2 r (fun q e => hin ⟨q, e⟩)
  · rw [t6]; exact hL1.cell

end Dec

end NearCubicWires.WireExponent3_5.PrimT.Flips
