import Proof.Wire_3_5.Primitive.SeedFix.FlipsHead

/-! # FLIPS, part 10: the offset written (P3:1206-1207)

"Use all `2^s` cosets in each block" (P3:1206-1207): the call's translation picks, in block `j`, the coset of the
unit vector at the code `t_j` (`C4Geo.offset`). **`offPart`** reads the `r` codes (`transLoop`), writes the unblocked
coordinates' zeros and the frame's end, and rewinds: `frameP (offW b tl ts) ++ [false]` on `sOFF`
(**`offPart_spec`**), with `offW b tl ts = ts.flatMap (oneHot b) ++ replicate tl false`.

Paper quantity of the main type: the coset offset's word (`offW`). -/

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
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)

/-- **The offset's word**: each code's block (`oneHot b t_j`), then the unblocked coordinates' zeros. -/
def offW (b tl : ℕ) (ts : List ℕ) : List Bool := ts.flatMap (FinalPass.Sample.oneHot b) ++ List.replicate tl false

/-- The registers `r` (`3`) and `tail` (`7`). -/
def rReg : Fin GR := 3
def tReg : Fin GR := 7

/-- **The offset written**: the codes' blocks, the zeros, the frame's end, rewound. -/
def offPart : WM GS GR :=
  .seq (FinalPass.Hash4.wcopyR rReg rJ rTmp) (.seq transLoop (.seq (FinalPass.Hash4.wcopyR tReg rJ rTmp)
    (.seq (zerosW sOFF) (.seq (emitW sOFF false) (.seq (.inc rOc) (rew1 sOFF rOc))))))

/-- Its cost. -/
def offCost (b tl : ℕ) (ts : List ℕ) : ℕ :=
  18 * ts.length + 3 + 1 + (transCost b ts + 1 + (18 * tl + 3 + 1 + (tl * 20 + 1 + 1 + (3 + 1 + (3 + 1 +
    ((2 * b * ts.length + 2 * tl + 1) * 5 + 1))))))

section Off
variable (cap : ℕ)

theorem offPart_spec (b tl : ℕ) (ts : List ℕ) (pre rest : List Bool) (σ : WState GS GR)
    (hst : σ.st gIN = pre ++ marks (ts.flatMap natWord) ++ rest) (hsh : σ.sh gIN = pre.length)
    (hO : σ.st sOFF = []) (hOh : σ.sh sOFF = 0) (hr : σ.val rReg = ts.length) (hb : σ.val bReg = b)
    (ht : σ.val tReg = tl) (hz : ∀ q : Fin GR, 20 ≤ q.val → σ.val q = 0) (htb : ∀ t ∈ ts, t ≤ b)
    (htc : ∀ t ∈ ts, 2 ^ (natBitLength t + 1) ≤ cap) (hcap : 2 * (b * ts.length) + 2 * tl + 2 * b + 4 ≤ cap)
    (hl : ts.length ≤ cap) :
    ∃ τ, WExec cap offPart σ τ (offCost b tl ts) ∧ τ.st sOFF = frameP (offW b tl ts) ++ [false] ∧
      τ.sh sOFF = 0 ∧ τ.st gIN = σ.st gIN ∧ τ.sh gIN = pre.length + 2 * (ts.flatMap natWord).length ∧
      (∀ i, i ≠ sOFF → i ≠ gIN → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ (∀ q, τ.val q = σ.val q) ∧
      τ.cell = σ.cell := by
  have hbl : 2 * b * ts.length = 2 * (b * ts.length) := by ring
  have zJ := hz rJ (by decide)
  have zM := hz rTmp (by decide)
  have zO := hz rOc (by decide)
  -- `rJ := r`
  have s1 := FinalPass.Hash4.wcopyR_spec cap rReg rJ rTmp (by decide) (by decide) (by decide) σ zJ zM
    (by rw [hr]; exact hl)
  rw [hr] at s1
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rJ ts.length := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have v1 : ∀ q, q ≠ rJ → σ1.val q = σ.val q := fun q hq => by rw [hσ1]; simp [WState.setv, Function.update_apply, hq]
  -- the codes
  have T0 : TAt σ1 σ1 [] pre.length ts.length 0 :=
    ⟨by simp, by rw [hσ1]; simp [WState.setv, hO, hOh], rfl, by rw [hσ1]; exact hsh, fun _ _ _ => ⟨rfl, rfl⟩,
      by rw [hσ1]; simp [WState.setv], by rw [v1 _ (by decide)]; exact hz _ (by decide),
      by rw [v1 _ (by decide)]; exact hz _ (by decide), by rw [v1 _ (by decide), zO], fun _ _ => rfl, rfl⟩
  obtain ⟨σ2, e2, T2⟩ := transLoop_spec cap b σ1 (by rw [v1 _ (by decide), hb])
    (by rw [v1 _ (by decide)]; exact hz _ (by decide)) (by rw [v1 _ (by decide)]; exact hz _ (by decide))
    (by rw [v1 _ (by decide)]; exact hz _ (by decide)) (by rw [v1 _ (by decide)]; exact hz _ (by decide))
    (by rw [v1 _ (by decide)]; exact hz _ (by decide)) (by omega) ts pre rest σ1 [] 0
    (by rw [hσ1]; exact hst) T0 htb htc (by omega) hl
  -- `rJ := tail`
  have s3 := FinalPass.Hash4.wcopyR_spec cap tReg rJ rTmp (by decide) (by decide) (by decide) σ2 T2.vJ
    (by rw [T2.frR rTmp (by simp [tR]; decide), v1 _ (by decide), zM])
    (by rw [T2.frR tReg (by simp [tR]; decide), v1 _ (by decide), ht]; omega)
  rw [T2.frR tReg (by simp [tR]; decide), v1 _ (by decide), ht] at s3
  obtain ⟨σ3, hσ3⟩ : ∃ y, y = σ2.setv rJ tl := ⟨_, rfl⟩
  rw [← hσ3] at s3
  -- the zeros
  obtain ⟨σ4, e4, a4, j4, o4, f4⟩ := zerosW_spec cap sOFF tl σ3 (by rw [hσ3]; simp [WState.setv])
    (by rw [hσ3]; exact T2.shO) (by rw [hσ3]; simp [WState.setv, Function.update_apply, oJ, T2.vOc]; omega)
    (by omega)
  -- the frame's end
  have s5 := emitW_spec (cap := cap) sOFF false σ4 a4.sh
  obtain ⟨σ5, hσ5⟩ : ∃ y, y = (σ4.sets sOFF (σ4.st sOFF ++ [false])).seth sOFF ((σ4.st sOFF).length + 1) :=
    ⟨_, rfl⟩
  rw [← hσ5] at s5
  have v5 : σ5.val = σ4.val := by rw [hσ5]; rfl
  have o5 : σ5.val rOc = 2 * b * ts.length + 2 * tl := by
    rw [v5, o4, hσ3]; simp [WState.setv, Function.update_apply, oJ, T2.vOc]
  have s6 := WExec.inc (cap := cap) rOc σ5 (by rw [o5]; nlinarith)
  obtain ⟨σ6, hσ6⟩ : ∃ y, y = σ5.setv rOc (σ5.val rOc + 1) := ⟨_, rfl⟩
  rw [← hσ6] at s6
  have st6 : σ6.st sOFF = frameP (offW b tl ts) ++ [false] := by
    rw [hσ6, hσ5]
    simp only [WState.setv, WState.sets, WState.seth, Function.update_self]
    rw [a4.st, hσ3]
    simp only [WState.setv]
    rw [T2.stO, hσ1]
    simp [WState.setv, hO, offW, frameP, List.flatMap_append, List.append_assoc]
  have sh6 : σ6.sh sOFF = 2 * b * ts.length + 2 * tl + 1 := by
    rw [hσ6, hσ5]
    simp only [WState.setv, WState.sets, WState.seth, Function.update_self]
    rw [a4.st, hσ3]
    simp only [WState.setv]
    rw [T2.stO, hσ1]
    simp only [WState.setv, hO, List.nil_append, List.length_append, frameP_length,
      FinalPass.Sample.length_flatMap_oneHot, List.length_replicate, List.length_cons, List.length_nil]
    ring
  have o6 : σ6.val rOc = 2 * b * ts.length + 2 * tl + 1 := by rw [hσ6]; simp [WState.setv, o5]
  obtain ⟨τ, e7, t1, t2, t3, t4, t5, t6⟩ := rew1_spec cap sOFF rOc _ σ6 o6 sh6 (by nlinarith)
  refine ⟨τ, WExec.seq s1 (WExec.seq e2 (WExec.seq s3 (WExec.seq e4 (WExec.seq s5 (WExec.seq s6 e7))))), ?_, t1, ?_,
    ?_, ?_, fun q => ?_, ?_⟩
  · rw [t3]; exact st6
  · rw [t3, hσ6, hσ5]
    simp only [WState.setv, WState.sets, WState.seth, Function.update_apply, if_neg (show gIN ≠ sOFF by decide)]
    rw [(a4.frS gIN (by decide)).1, hσ3]; simp only [WState.setv]; rw [T2.stI, hσ1]; rfl
  · rw [t4 gIN (by decide), hσ6, hσ5]
    simp only [WState.setv, WState.sets, WState.seth, Function.update_apply, if_neg (show gIN ≠ sOFF by decide)]
    rw [(a4.frS gIN (by decide)).2, hσ3]; simp only [WState.setv]; rw [T2.shI]
  · intro i h1 h2
    rw [t3, t4 i h1, hσ6, hσ5]
    simp only [WState.setv, WState.sets, WState.seth, Function.update_apply, if_neg h1]
    rw [(a4.frS i h1).1, (a4.frS i h1).2, hσ3]; simp only [WState.setv]
    rw [(T2.frS i h1 h2).1, (T2.frS i h1 h2).2, hσ1]; exact ⟨rfl, rfl⟩
  · by_cases hq1 : q = rOc
    · subst hq1; rw [t2, zO]
    · rw [t5 q hq1, hσ6]
      simp only [WState.setv, Function.update_apply, if_neg hq1]
      rw [v5]
      by_cases hq2 : q = rJ
      · subst hq2; rw [j4, zJ]
      · rw [f4 q hq2 hq1, hσ3]
        simp only [WState.setv, Function.update_apply, if_neg hq2]
        by_cases hq3 : tR q
        · rcases hq3 with h | h | h | h
          · exact absurd h hq2
          · subst h; rw [T2.vTv]; exact (hz _ (by decide)).symm
          · subst h; rw [T2.vBc]; exact (hz _ (by decide)).symm
          · exact absurd h hq1
        · rw [T2.frR q hq3, v1 q hq2]
  · rw [t6, hσ6, hσ5]
    simp only [WState.setv, WState.sets, WState.seth]
    rw [a4.cell, hσ3]; simp only [WState.setv]; rw [T2.cell, hσ1]; rfl

end Off

end NearCubicWires.WireExponent3_5.PrimT.Flips
