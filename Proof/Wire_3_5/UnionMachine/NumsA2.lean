import Proof.Wire_3_5.UnionMachine.NumsA1

/-! # NW phase (a), part 2: the framed input's length

The data stage needs its register fill `1^W` above every code of the request: phase (a) takes `W` from the input's
own length `|fpIn|`, measured on the framed input `frame fpIn` (markers at the even cells, the closing `false`):

* `flBody`, `frameLenW`, **`frameLen_spec`** (`frame w` on `O` ↦ `R := |w|`, the head back at `0`).

Paper quantity: none (plumbing: the input length bounds the request's fields). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

section Kit
variable {ns nr : ℕ} (cap : ℕ)

theorem frame_mark0 (u : List Bool) (k : ℕ) : readTapeBit (frame u) (2 * k) = decide (k < u.length) := by
  rw [frame_eq_frameP]; exact frameP_mark u k

/-- One round: past a marker and its payload, count. -/
def flBody (O : Fin (ns + 1)) (R P : Fin nr) : WM ns nr :=
  .seq (.fwd O) (.seq (.fwd O) (.seq (.inc R) (.seq (.inc P) (.inc P))))

/-- **The framed word's length** into `R` (moves counted in `P`), the head back at `0`. -/
def frameLenW (O : Fin (ns + 1)) (R P : Fin nr) : WM ns nr := .seq (.whs O (flBody O R P)) (WM.rewind O P)

theorem frameLen_spec (O : Fin (ns + 1)) (R P : Fin nr) (hRP : R ≠ P) (w : List Bool) (σ : WState ns nr)
    (hO : σ.st O = frame w) (hh : σ.sh O = 0) (hR : σ.val R = 0) (hP : σ.val P = 0) (hcap : 2 * w.length + 1 ≤ cap) :
    WExec cap (frameLenW O R P) σ (σ.setv R w.length) (w.length * (17 + 2) + 1 + 1 + (5 * (2 * w.length) + 1)) := by
  have hPR := Ne.symm hRP
  let S : ℕ → WState ns nr := fun k => ((σ.seth O (2 * k)).setv R k).setv P (2 * k)
  have hS0 : S 0 = σ := by
    apply WState.eq
    · funext i
      by_cases hiO : i = O
      · subst hiO; simp [S, hh]
      · simp [S, hiO]
    · rfl
    · funext q
      by_cases hqP : q = P
      · subst hqP; simp [S, hP]
      · by_cases hqR : q = R
        · subst hqR; simp [S, hR, hRP]
        · simp [S, hqP, hqR]
    · rfl
  have l1 := Data.whsLoop cap O (flBody O R P) 17 w.length S
    (fun k hk => by simp only [wbit, S, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
      Function.update_self, hO]; rw [frame_mark0]; simp [hk])
    (by simp only [wbit, S, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hO]
        rw [frame_mark0]; simp)
    (fun k hk => by
      have g1 := WExec.fwd (cap := cap) O (S k)
      have g2 := WExec.fwd (cap := cap) O ((S k).seth O ((S k).sh O + 1))
      have g3 := WExec.inc (cap := cap) R (((S k).seth O ((S k).sh O + 1)).seth O
        (((S k).seth O ((S k).sh O + 1)).sh O + 1)) (by simp [S, hRP]; omega)
      obtain ⟨T3, hT3⟩ : ∃ s, s = (((S k).seth O ((S k).sh O + 1)).seth O
          (((S k).seth O ((S k).sh O + 1)).sh O + 1)).setv R ((((S k).seth O ((S k).sh O + 1)).seth O
          (((S k).seth O ((S k).sh O + 1)).sh O + 1)).val R + 1) := ⟨_, rfl⟩
      rw [← hT3] at g3
      have g4 := WExec.inc (cap := cap) P T3 (by rw [hT3]; simp [S, hPR]; omega)
      have g5 := WExec.inc (cap := cap) P (T3.setv P (T3.val P + 1)) (by rw [hT3]; simp [S, hPR]; omega)
      refine WExec.cast cap (WExec.seq g1 (WExec.seq g2 (WExec.seq g3 (WExec.seq g4 g5)))) ?_ (by omega)
      rw [hT3]
      apply WState.eq
      · funext i
        by_cases hiO : i = O
        · subst hiO; simp [S]; omega
        · simp [S, hiO]
      · rfl
      · funext q
        by_cases hqP : q = P
        · subst hqP; simp [S, hPR]; omega
        · by_cases hqR : q = R
          · subst hqR; simp [S, hRP]
          · simp [S, hqP, hqR]
      · rfl)
  rw [hS0] at l1
  have h2 := wrewind_spec cap O P (2 * w.length) (S w.length) (by simp [S]) (by simp [S]; omega)
  refine WExec.cast cap (WExec.seq l1 h2) ?_ le_rfl
  apply WState.eq
  · funext i
    by_cases hiO : i = O
    · subst hiO; simp [S, hh]
    · simp [S, hiO]
  · rfl
  · funext q
    by_cases hqP : q = P
    · subst hqP; simp [S, hPR, hP]
    · by_cases hqR : q = R
      · subst hqR; simp [S, hRP]
      · simp [S, hqP, hqR]
  · rfl

end Kit

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
