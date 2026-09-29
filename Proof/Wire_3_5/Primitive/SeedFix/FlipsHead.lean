import Proof.Wire_3_5.Primitive.SeedFix.FlipsInit
import Proof.Wire_3_5.Primitive.Writers.Codec

/-! # FLIPS, part 9: reading the request up to the translation (P3:3119-3120, 1206-1207)

"The algorithm receives polynomial-bit integer circuit descriptions" (P3:3119-3120): the request word is
`natWord n`, the mode bit, `natWord a`, the circuits' codes, the carriers' list, the translation's list (PA's
`Codec.word_eq`). The star numbers (`GeoNums.p1W`) give `n`, `r`, `s`, `b`, `r/2`, `n−rb`, `kh`
(**`nums_spec`**); the header skip reads `a` and the carriers' count and skips every code up to the translation's
codes (**`skipHead_spec`**).

Paper quantity of the main types: the call's star numbers and the position of the translation (`preT`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT σG)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord natListWord)

/-- The request word before the translation's codes. -/
def preT (r : PrimRequest) : List Bool :=
  natWord r.n ++ [PrimAsm.Codec.modeBit r.mode] ++ natWord r.a ++ (PrimAsm.Codec.codeList r).flatMap natWord ++
    natWord (PrimAsm.Codec.carrierCodes r).length ++ (PrimAsm.Codec.carrierCodes r).flatMap natWord ++
    natWord r.translation.length

theorem word_split (r : PrimRequest) : r.word = preT r ++ r.translation.flatMap natWord := by
  rw [PrimAsm.Codec.word_eq]
  simp [preT, natListWord, List.append_assoc]

/-- The star numbers' cost (`readNatM` on `natWord n`, then `starNumsM`). -/
def numsCost (n cr : ℕ) : ℕ :=
  (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 + PrimAsm.StarNums.starCost n cr 0

/-- **The star numbers**: from the writer's start state, the registers `0, 3 … 8` hold `n, r, s, b, r/2, n−rb, kh`,
every register from `20` on is `0`, the request's head is past `natWord n`. -/
theorem nums_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w sfx : List Bool)
    (hw : w = natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ W) :
    ∃ σ2, WExec (2 * W + 2) (PrimAsm.GeoNums.p1W cr) (σG w P.n W) σ2 (numsCost P.n cr) ∧ σ2.st = (σG w P.n W).st ∧
      σ2.sh gIN = 2 * (natWord P.n).length ∧ (∀ i, i ≠ gIN → σ2.sh i = 0) ∧
      σ2.val 0 = P.n ∧ σ2.val 3 = P.r ∧ σ2.val 4 = P.s ∧ σ2.val 5 = P.b ∧ σ2.val 6 = P.r / 2 ∧
      σ2.val 7 = P.n - P.r * P.b ∧ σ2.val 8 = P.s * (P.r / 2) ∧ (∀ q : Fin GR, 20 ≤ q.val → σ2.val q = 0) ∧
      σ2.cell = false := by
  have hpow := PrimAsm.CopyNat.two_pow_natBitLength_le P.n
  have r1 := PrimAsm.ParseNat.readNatM_spec (2 * W + 2) true gIN PrimAsm.GeoNums.rF PrimAsm.GeoNums.rC
    (PrimAsm.GeoNums.SG 0) PrimAsm.GeoNums.rP PrimAsm.GeoNums.rT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) P.n [] (marks sfx ++ [false])
    (σG w P.n W) (by simp only [σG, if_pos rfl]; rw [hw]; exact PrimAsm.GeoNums.frame_splitG _ _) (by rfl)
    rfl rfl rfl rfl (by simp only [σG]; rw [pow_succ]; omega)
  obtain ⟨σ1, hσ1⟩ : ∃ σ, σ = ((σG w P.n W).seth gIN (([] : List Bool).length + PrimAsm.ParseNat.stp true *
      (natWord P.n).length)).setv (PrimAsm.GeoNums.SG 0) ((σG w P.n W).val (PrimAsm.GeoNums.SG 0) + P.n) :=
    ⟨_, rfl⟩
  rw [← hσ1] at r1
  have v1 : ∀ q : Fin GR, q ≠ PrimAsm.GeoNums.SG 0 → σ1.val q = 0 := by
    intro q hq; simp [hσ1, Function.update_apply, hq, σG]
  have v10 : σ1.val (PrimAsm.GeoNums.SG 0) = P.n := by simp [hσ1, σG]
  have r2 := PrimAsm.StarNums.starNums_spec (2 * W + 2) cr 0 PrimAsm.GeoNums.SG P hrP σ1 v10
    (fun i hi => v1 _ (fun e => hi (PrimAsm.GeoNums.SG.injective e))) (by omega)
  obtain ⟨σ2, hσ2⟩ : ∃ σ, σ = PrimAsm.StarNums.starOut σ1 PrimAsm.GeoNums.SG P 0 := ⟨_, rfl⟩
  rw [← hσ2] at r2
  obtain ⟨-, o3, o4, o5, o6, o7, o8, -, -⟩ := PrimAsm.StarNums.starOut_val σ1 PrimAsm.GeoNums.SG P 0
  rw [← hσ2] at o3 o4 o5 o6 o7 o8
  have o0 : σ2.val 0 = P.n := by
    rw [hσ2]
    exact (PrimAsm.StarNums.starOut_val_other σ1 PrimAsm.GeoNums.SG P 0 0 (Or.inl rfl)).trans v10
  refine ⟨σ2, WExec.seq r1 r2, ?_, ?_, ?_, o0, o3, o4, o5, o6, o7, o8, fun q hq => ?_, ?_⟩
  · rw [hσ2]; simp [PrimAsm.StarNums.starOut, hσ1]
  · rw [hσ2]; simp [PrimAsm.StarNums.starOut, hσ1, PrimAsm.ParseNat.stp]
  · intro i hi; rw [hσ2]; simp [PrimAsm.StarNums.starOut, hσ1, Function.update_apply, hi, σG]
  · rw [hσ2, PrimAsm.GeoNums.starOut_hiG _ _ _ _ hq]
    exact v1 q (fun e => by rw [e] at hq; simp [PrimAsm.GeoNums.SG] at hq)
  · rw [hσ2]; simp [PrimAsm.StarNums.starOut, hσ1, σG]

/-! ## The header skipped -/

section Skip
variable (cap : ℕ)

theorem fC : rFf ≠ rCc := by decide
theorem jC : rJ ≠ rCc := by decide
theorem jF : rJ ≠ rFf := by decide

/-- Read a framed `natWord x` into `rJ`. -/
theorem readJ_spec (x : ℕ) (pre rest : List Bool) (σ : WState GS GR)
    (hst : σ.st gIN = pre ++ marks (natWord x) ++ rest) (hsh : σ.sh gIN = pre.length) (hJ : σ.val rJ = 0)
    (hf : σ.val rFf = 0) (hc : σ.val rCc = 0) (hp : σ.val rPp = 0) (ht : σ.val rTt = 0)
    (hcap : 2 ^ (natBitLength x + 1) ≤ cap) :
    WExec cap (PrimAsm.ParseNat.readNatM true gIN rFf rCc rJ rPp rTt) σ
      ((σ.seth gIN (pre.length + 2 * (natWord x).length)).setv rJ x)
      ((natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)) := by
  have h := PrimAsm.ParseNat.readNatM_spec cap true gIN rFf rCc rJ rPp rTt (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x pre rest σ
    (by rw [hst]; rfl) hsh hf hc hp ht (by rw [hJ]; omega)
  rw [hJ, Nat.zero_add] at h
  exact h

/-- The header's skip: the mode bit, `a` and the codes, the carriers' count and codes, the translation's length. -/
def skipHead : WM GS GR :=
  .seq (.fwd gIN) (.seq (.fwd gIN) (.seq (PrimAsm.ParseNat.readNatM true gIN rFf rCc rJ rPp rTt) (.seq skipNats
    (.seq (PrimAsm.ParseNat.readNatM true gIN rFf rCc rJ rPp rTt) (.seq skipNats
    (PrimAsm.ParseNat.skipNatM true gIN rFf rCc))))))

/-- The skip's cost. -/
def skipHeadCost (r : PrimRequest) : ℕ :=
  1 + 1 + (1 + 1 + ((natBitLength r.a + 2) * (40 * 2 ^ natBitLength r.a + 40) + 1 +
    (skipCost (PrimAsm.Codec.codeList r) + 1 + ((natBitLength (PrimAsm.Codec.carrierCodes r).length + 2) *
      (40 * 2 ^ natBitLength (PrimAsm.Codec.carrierCodes r).length + 40) + 1 +
    (skipCost (PrimAsm.Codec.carrierCodes r) + 1 + (20 * natBitLength r.translation.length + 20))))))

theorem skipHead_spec (r : PrimRequest) (σ : WState GS GR)
    (hst : σ.st gIN = marks (preT r ++ r.translation.flatMap natWord) ++ [false])
    (hsh : σ.sh gIN = 2 * (natWord r.n).length) (hz : ∀ q : Fin GR, 20 ≤ q.val → σ.val q = 0)
    (ha : 2 ^ (natBitLength r.a + 1) ≤ cap)
    (hcode : ∀ x ∈ PrimAsm.Codec.codeList r, natBitLength x + 1 ≤ cap) (hcl : r.a ≤ cap)
    (hk : 2 ^ (natBitLength (PrimAsm.Codec.carrierCodes r).length + 1) ≤ cap)
    (hcc : ∀ x ∈ PrimAsm.Codec.carrierCodes r, natBitLength x + 1 ≤ cap) (hkl : (PrimAsm.Codec.carrierCodes r).length ≤ cap)
    (htl : natBitLength r.translation.length + 1 ≤ cap) :
    ∃ τ, WExec cap skipHead σ τ (skipHeadCost r) ∧ τ.st = σ.st ∧ τ.sh gIN = 2 * (preT r).length ∧
      (∀ i, i ≠ gIN → τ.sh i = σ.sh i) ∧ (∀ q, τ.val q = σ.val q) ∧ τ.cell = σ.cell := by
  have hcl' : (PrimAsm.Codec.codeList r).length = r.a := by simp [PrimAsm.Codec.codeList]
  have zJ := hz rJ (by decide)
  have zF := hz rFf (by decide)
  have zC := hz rCc (by decide)
  have zP := hz rPp (by decide)
  have zT := hz rTt (by decide)
  -- the mode bit
  have s1 := WExec.fwd (cap := cap) gIN σ
  have s2 := WExec.fwd (cap := cap) gIN (σ.seth gIN (σ.sh gIN + 1))
  obtain ⟨σ2, hσ2⟩ : ∃ y, y = (σ.seth gIN (σ.sh gIN + 1)).seth gIN ((σ.seth gIN (σ.sh gIN + 1)).sh gIN + 1) :=
    ⟨_, rfl⟩
  rw [← hσ2] at s2
  have f2 : σ2.st = σ.st ∧ σ2.val = σ.val ∧ σ2.cell = σ.cell := by rw [hσ2]; exact ⟨rfl, rfl, rfl⟩
  have h2 : σ2.sh gIN = (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode])).length := by
    rw [hσ2]; simp [WState.seth, hsh]
  have o2 : ∀ i, i ≠ gIN → σ2.sh i = σ.sh i := fun i hi => by rw [hσ2]; simp [WState.seth, Function.update_apply, hi]
  -- `a`
  have s3 := readJ_spec cap r.a (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode]))
    (marks ((PrimAsm.Codec.codeList r).flatMap natWord ++ natWord (PrimAsm.Codec.carrierCodes r).length ++
      (PrimAsm.Codec.carrierCodes r).flatMap natWord ++ natWord r.translation.length ++
      r.translation.flatMap natWord) ++ [false]) σ2
    (by rw [f2.1, hst]; simp only [preT, Streaming.marks_append, List.append_assoc]) h2 (by rw [f2.2.1, zJ]) (by rw [f2.2.1, zF])
    (by rw [f2.2.1, zC]) (by rw [f2.2.1, zP]) (by rw [f2.2.1, zT]) ha
  obtain ⟨σ3, hσ3⟩ : ∃ y, y = (σ2.seth gIN ((marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode])).length +
      2 * (natWord r.a).length)).setv rJ r.a := ⟨_, rfl⟩
  rw [← hσ3] at s3
  have f3 : σ3.st = σ.st ∧ σ3.val rJ = r.a ∧ (∀ q, q ≠ rJ → σ3.val q = σ.val q) ∧ σ3.cell = σ.cell ∧
      σ3.sh gIN = (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode] ++ natWord r.a)).length ∧
      (∀ i, i ≠ gIN → σ3.sh i = σ.sh i) := by
    rw [hσ3]
    refine ⟨f2.1, by simp [WState.setv], fun q hq => by simp [WState.setv, WState.seth, Function.update_apply, hq, f2.2.1],
      f2.2.2, by simp [WState.setv, WState.seth]; ring, fun i hi => by simp [WState.setv, WState.seth,
        Function.update_apply, hi, o2 i hi]⟩
  -- the codes
  obtain ⟨σ4, e4, a4, b4, c4, d4, g4, k4⟩ := skipNats_spec cap (PrimAsm.Codec.codeList r)
    (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode] ++ natWord r.a))
    (marks (natWord (PrimAsm.Codec.carrierCodes r).length ++ (PrimAsm.Codec.carrierCodes r).flatMap natWord ++
      natWord r.translation.length ++ r.translation.flatMap natWord) ++ [false]) σ3
    (by rw [f3.1, hst]; simp only [preT, Streaming.marks_append, List.append_assoc]) f3.2.2.2.2.1 (by rw [f3.2.1, hcl'])
    (by rw [f3.2.2.1 _ (Ne.symm jF), zF]) (by rw [f3.2.2.1 _ (Ne.symm jC), zC]) hcode (by rw [hcl']; exact hcl)
  -- the carriers' count
  have s5 := readJ_spec cap (PrimAsm.Codec.carrierCodes r).length
    (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode] ++ natWord r.a ++
      (PrimAsm.Codec.codeList r).flatMap natWord))
    (marks ((PrimAsm.Codec.carrierCodes r).flatMap natWord ++ natWord r.translation.length ++
      r.translation.flatMap natWord) ++ [false]) σ4
    (by rw [a4, f3.1, hst]; simp only [preT, Streaming.marks_append, List.append_assoc])
    (by rw [b4]; simp only [Streaming.marks_length, List.length_append]; ring) d4
    (by rw [g4 _ (Ne.symm jF), f3.2.2.1 _ (Ne.symm jF), zF]) (by rw [g4 _ (Ne.symm jC), f3.2.2.1 _ (Ne.symm jC), zC])
    (by rw [g4 _ (by decide), f3.2.2.1 _ (by decide), zP]) (by rw [g4 _ (by decide), f3.2.2.1 _ (by decide), zT]) hk
  obtain ⟨σ5, hσ5⟩ : ∃ y, y = (σ4.seth gIN ((marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode] ++ natWord r.a ++
      (PrimAsm.Codec.codeList r).flatMap natWord)).length + 2 * (natWord (PrimAsm.Codec.carrierCodes r).length).length)).setv
      rJ (PrimAsm.Codec.carrierCodes r).length := ⟨_, rfl⟩
  rw [← hσ5] at s5
  -- the carriers' codes
  obtain ⟨σ6, e6, a6, b6, c6, d6, g6, k6⟩ := skipNats_spec cap (PrimAsm.Codec.carrierCodes r)
    (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode] ++ natWord r.a ++ (PrimAsm.Codec.codeList r).flatMap natWord ++
      natWord (PrimAsm.Codec.carrierCodes r).length))
    (marks (natWord r.translation.length ++ r.translation.flatMap natWord) ++ [false]) σ5
    (by rw [hσ5]; show σ4.st gIN = _; rw [a4, f3.1, hst]; simp only [preT, Streaming.marks_append, List.append_assoc])
    (by rw [hσ5]; simp only [WState.setv, WState.seth, Function.update_self, Streaming.marks_length,
      List.length_append]; ring) (by rw [hσ5]; simp [WState.setv])
    (by rw [hσ5]; simp [WState.setv, WState.seth, Function.update_apply, Ne.symm jF, g4 _ (Ne.symm jF),
      f3.2.2.1 _ (Ne.symm jF), zF])
    (by rw [hσ5]; simp [WState.setv, WState.seth, Function.update_apply, Ne.symm jC, g4 _ (Ne.symm jC),
      f3.2.2.1 _ (Ne.symm jC), zC]) hcc hkl
  -- the translation's length
  have s7 := PrimAsm.ParseNat.skipNatM_spec cap true gIN rFf rCc fC r.translation.length
    (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode] ++ natWord r.a ++ (PrimAsm.Codec.codeList r).flatMap natWord ++
      natWord (PrimAsm.Codec.carrierCodes r).length ++ (PrimAsm.Codec.carrierCodes r).flatMap natWord))
    (marks (r.translation.flatMap natWord) ++ [false]) σ6
    (by rw [a6, hσ5]; show σ4.st gIN = _; rw [a4, f3.1, hst]; simp only [preT, PrimAsm.ParseNat.enc, if_true,
      Streaming.marks_append, List.append_assoc])
    (by rw [b6]; simp only [Streaming.marks_length, List.length_append]; ring)
    (by rw [g6 _ (Ne.symm jF), hσ5]; simp [WState.setv, WState.seth, Function.update_apply, Ne.symm jF,
      g4 _ (Ne.symm jF), f3.2.2.1 _ (Ne.symm jF), zF])
    (by rw [g6 _ (Ne.symm jC), hσ5]; simp [WState.setv, WState.seth, Function.update_apply, Ne.symm jC,
      g4 _ (Ne.symm jC), f3.2.2.1 _ (Ne.symm jC), zC]) htl
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq e4 (WExec.seq s5 (WExec.seq e6 s7))))), ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [WState.seth]; rw [a6, hσ5]; show σ4.st = σ.st; rw [a4, f3.1]
  · simp [WState.seth, preT, PrimAsm.ParseNat.stp]; ring
  · intro i hi
    simp only [WState.seth, Function.update_apply, if_neg hi]
    rw [c6 i hi, hσ5]
    simp [WState.setv, WState.seth, Function.update_apply, hi, c4 i hi, f3.2.2.2.2.2 i hi]
  · intro q
    simp only [WState.seth]
    by_cases hq : q = rJ
    · subst hq; rw [d6, zJ]
    · rw [g6 q hq, hσ5]
      simp [WState.setv, WState.seth, Function.update_apply, hq, g4 q hq, f3.2.2.1 q hq]
  · simp only [WState.seth]; rw [k6, hσ5]; simp only [WState.setv, WState.seth]; rw [k4, f3.2.2.2.1]

end Skip

end NearCubicWires.WireExponent3_5.PrimT.Flips
