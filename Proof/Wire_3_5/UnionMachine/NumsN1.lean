import Proof.Wire_3_5.UnionMachine.NumsA2
import Proof.Wire_3_5.Primitive.SeedFix.TabRef
import Proof.Wire_3_5.FinalPass.HashCell

/-! # SWn, item 4: the gate table's width `tabH G` from the table itself

The call number `tabH G_j` (`S3.numOf k 1 j`, the SYM numbers `6 … 9`) is the width of the gate table
`Corner.gatesW (tabH G) G` the data stage leaves on the slot tape: a non-empty gate list starts `true` (the first gate's
marker), then the frame of the first threshold half `binary h (…)` of length `h = tabH G`; an empty list's table is
`[false]` (and a blank tape past the tuple). So: test the first cell; if set, step past the marker and measure the frame
(`frameLenAt`, `NumsA2`'s count at an offset), then step back.

* `read_at`, `frameLenAt_spec`, `tabHW`, **`tabHW_spec`** (`R := tabH G`, the head back at `0`).

Paper quantity of the main type: the gate table's width `tabH G_j` (`symNums`, kind `1`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Kit
variable {ns nr : ℕ} (cap : ℕ)

theorem read_at (pre w rest : List Bool) (k : ℕ) (hk : k ≤ w.length) :
    readTapeBit (pre ++ frame w ++ rest) (pre.length + 2 * k) = decide (k < w.length) := by
  rw [FinalPass.Hash4.readDrop, List.append_assoc, List.drop_left]
  unfold readTapeBit
  rw [List.getD_append _ _ _ _ (by rw [frame_length]; omega)]
  have := frame_mark0 w k
  unfold readTapeBit at this
  exact this

/-- **The framed word's length at an offset** (`frameLenW` from a head at the frame's first cell). -/
theorem frameLenAt_spec (O : Fin (ns + 1)) (R P : Fin nr) (hRP : R ≠ P) (pre w rest : List Bool) (σ : WState ns nr)
    (hO : σ.st O = pre ++ frame w ++ rest) (hh : σ.sh O = pre.length) (hR : σ.val R = 0) (hP : σ.val P = 0)
    (hcap : 2 * w.length + 1 ≤ cap) :
    WExec cap (frameLenW O R P) σ (σ.setv R w.length) (w.length * (17 + 2) + 1 + 1 + (5 * (2 * w.length) + 1)) := by
  have hPR := Ne.symm hRP
  let S : ℕ → WState ns nr := fun k => ((σ.seth O (pre.length + 2 * k)).setv R k).setv P (2 * k)
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
    (fun k hk => by
      simp only [wbit, S, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hO]
      rw [read_at pre w rest k (by omega)]; simp [hk])
    (by simp only [wbit, S, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hO]
        rw [read_at pre w rest w.length le_rfl]; simp)
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

/-- **The table width**: if the table's first cell is set, past the marker, measure the first frame, step back. -/
def tabHW (O : Fin (ns + 1)) (R P : Fin nr) : WM ns nr :=
  .ifs O (.seq (.fwd O) (.seq (frameLenW O R P) (.bwd O))) .skip

theorem tabHW_spec (O : Fin (ns + 1)) (R P : Fin nr) (hRP : R ≠ P) {n : ℕ} (G : List (NormalizedThresholdGate n))
    (σ : WState ns nr) (hh : σ.sh O = 0) (hR : σ.val R = 0) (hP : σ.val P = 0)
    (hO : σ.st O = FinalPass.Corner.gatesW (PrimT.tabH G) G ∨ (σ.st O = [] ∧ G = []))
    (hcap : 2 * PrimT.tabH G + 1 ≤ cap) :
    WExec cap (tabHW O R P) σ (σ.setv R (PrimT.tabH G)) (30 * PrimT.tabH G + 10) := by
  cases G with
  | nil =>
    have e0 : PrimT.tabH ([] : List (NormalizedThresholdGate n)) = 0 := rfl
    rw [e0]
    have hb : wbit σ O = false := by
      unfold wbit; rw [hh]
      rcases hO with h1 | ⟨h1, -⟩ <;> rw [h1] <;> rfl
    have e : WExec cap (tabHW O R P) σ σ (0 + 1) := WExec.ifsF hb (WExec.skip σ)
    rw [← hR, wsetv_same]
    exact WExec.mono e (by omega)
  | cons g G =>
    obtain ⟨h, hhd⟩ : ∃ v, v = PrimT.tabH (g :: G) := ⟨_, rfl⟩
    rw [← hhd] at hO hcap ⊢
    have h1 : σ.st O = FinalPass.Corner.gatesW h (g :: G) := by
      rcases hO with h1 | ⟨-, h2⟩
      · exact h1
      · exact absurd h2 (List.cons_ne_nil g G)
    obtain ⟨rest, hrest⟩ : ∃ r, FinalPass.Corner.gatesW h (g :: G) =
        [true] ++ frame (binary h (-g.threshold).toNat) ++ r :=
      ⟨frame (binary h (- -g.threshold).toNat) ++ (List.flatMap (FinalPass.Corner.pairW h) (List.ofFn g.weight) ++
        (List.flatMap (FinalPass.Corner.gateW h) G ++ [false])), by
        simp [FinalPass.Corner.gatesW, FinalPass.Corner.gateW, FinalPass.Corner.pairW]⟩
    rw [hrest] at h1
    have hb : wbit σ O = true := by unfold wbit; rw [hh, h1]; rfl
    have e1 := WExec.fwd (cap := cap) O σ
    have hbl : (binary h (-g.threshold).toNat).length = h := SignedSortKey.binary_length _ _
    have e2 := frameLenAt_spec cap O R P hRP [true] (binary h (-g.threshold).toNat) rest (σ.seth O (σ.sh O + 1))
      (by simp [h1]) (by simp [hh]) (by simp [hR]) (by simp [hP]) (by rw [hbl]; omega)
    rw [hbl] at e2
    have e3 := WExec.bwd (cap := cap) O ((σ.seth O (σ.sh O + 1)).setv R h)
    refine WExec.cast cap (WExec.ifsT hb (WExec.seq e1 (WExec.seq e2 e3))) ?_ (by omega)
    apply WState.eq
    · funext i
      by_cases hi : i = O
      · subst hi; simp [hh]
      · simp [hi]
    · rfl
    · rfl
    · rfl

end Kit

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
