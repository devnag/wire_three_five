import Proof.Wire_3_5.UnionMachine.FrontCh3

/-! # C6 front, the chain, phase 3 assembled: the counts and the entries' check (P3:3669-3674)

On the valid path after phase 2 (mode `m` fixed by the tag), seven stages on consecutive regions (the wrappers):
the fill count `1^W` (`W = Kw·(q+1)^{Dw}`), the envelope `1^L` (`L = (q+1)^{Dl}`), two counts `1^{|x|}` (the atom stage's
decoder capacity and fill), the request head, the numbers' counts (`1^E`, `1^s`, `1^sys`, `1^aux`, `1^{nv}`, `0 1^{nv}`),
the entries' check `[(entScan E r).isSome]`. **`ch3_step`**.

Paper quantity of the main type: the guess's sizes and the entries' validity (P3:3669-3671). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3P
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWfDock NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc)
open NearCubicWires.RepairRepresentation (natWord)

/-- The numbers' capacities at the register capacity `cap` (every hypothesis of `nums_spec` on numbers). -/
structure NumsCaps (cap : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db Cδ q sys aux cb : ℕ) : Prop where
  hB : 2 * (natWord q).length ≤ Kb * (q + 1) ^ Db
  hK : Kb ≤ cap
  hq4 : q + 4 ≤ cap
  hPw : ∀ k ≤ Db, (q + 1) ^ k ≤ cap
  hBc : Kb * (q + 1) ^ Db ≤ cap
  hB2 : (natWord 3).length + (natWord sys).length + (natWord aux).length + (natWord cb).length ≤ Kb * (q + 1) ^ Db
  cq : 2 ^ (natBitLength q + 1) ≤ cap
  c3 : 2 ^ (natBitLength 3 + 1) ≤ cap
  cs : 2 ^ (natBitLength sys + 1) ≤ cap
  ca : 2 ^ (natBitLength aux + 1) ≤ cap
  cc : 2 ^ (natBitLength cb + 1) ≤ cap
  hsp : PrimAsm.SparseNum.sparseBound ζ Cδ (Ledger.Lq q) (Ledger.rowBt h0 h1 q - 1) ≤ cap
  hc : FrontTW.numCap (Ledger.rowBSparse h0 h1 2 Cδ q) (Ledger.rowBLambda h0 h1 2 q) q sys aux cb ≤ cap
  hs1 : 1 ≤ Ledger.rowBSparse h0 h1 2 Cδ q
  hcE : (sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q + Ledger.rowBSparse h0 h1 2 Cδ q + (sys + aux) + 2 ≤ cap
  hhd : 8 * q + 48 ≤ cap

section Phase
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

noncomputable abbrev tP (D : ℕ) : ℕ := RepairSource.ProjectionNormalization.DimensionPolynomial.tapes D

/-- The phase's size. -/
noncomputable abbrev CH3 (Dw Dl : ℕ) : ℕ := tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56 + FrontEntriesStage.ET

/-- The head's shared stream (`1^q`). -/
noncomputable def insHd (qT : Fin (NW P tf)) (i : Fin 2) : Option (Fin (NW P tf)) :=
  if i.val = 0 then some qT else none

/-- The numbers' shared streams (the head, the PCPP output). -/
noncomputable def insN (hdT poT : Fin (NW P tf)) (i : Fin 11) : Option (Fin (NW P tf)) :=
  if i = FrontTW.sHd then some hdT else if i = FrontTW.sPO then some poT else none

/-- The entries' shared tapes (`frame x`, `frame r`, `1^E`). -/
noncomputable def insE (cx rT eT : Fin (NW P tf)) (i : Fin FrontEntriesStage.ET) : Option (Fin (NW P tf)) :=
  if i.val = 0 then some cx else if i.val = 1 then some rT else if i.val = 2 then some eT else none

end Phase

section Machine
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (Dw Kw Dl : ℕ) (k0 : ℕ) (h : k0 + CH3 Dw Dl ≤ tf)

include h in
theorem hb1 : k0 + tP Dw ≤ tf := by unfold CH3 at h; omega
include h in
theorem hb2 : (k0 + tP Dw) + tP Dl ≤ tf := by unfold CH3 at h; omega
include h in
theorem hb3 : (k0 + tP Dw + tP Dl) + 8 ≤ tf := by unfold CH3 at h; omega
include h in
theorem hb4 : (k0 + tP Dw + tP Dl + 8) + 8 ≤ tf := by unfold CH3 at h; omega
include h in
theorem hb5 : (k0 + tP Dw + tP Dl + 8 + 8) + WT 1 9 ≤ tf := by unfold CH3 at h; omega
include h in
theorem hb6 : (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9) + WT 10 56 ≤ tf := by unfold CH3 at h; omega
include h in
theorem hb7 : (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56) + FrontEntriesStage.ET ≤ tf := by unfold CH3 at h; omega

variable (qT cx rT poT : Fin (NW P tf))

/-- `1^W`. -/
noncomputable def wcT : Fin (NW P tf) :=
  sl P tf (sh1 P tf qT) k0 (hb1 tf Dw Dl k0 h) (PCPSerializerCapacity.Power.outputSlot Dw)
/-- `1^L`. -/
noncomputable def lcT : Fin (NW P tf) :=
  sl P tf (sh1 P tf qT) (k0 + tP Dw) (hb2 tf Dw Dl k0 h) (PCPSerializerCapacity.Power.outputSlot Dl)
/-- The two `1^{|x|}`. -/
noncomputable def x1T : Fin (NW P tf) := sl P tf (sh1 P tf cx) (k0 + tP Dw + tP Dl) (hb3 tf Dw Dl k0 h) 2
noncomputable def x2T : Fin (NW P tf) := sl P tf (sh1 P tf cx) (k0 + tP Dw + tP Dl + 8) (hb4 tf Dw Dl k0 h) 2
/-- The request head. -/
noncomputable def hdT : Fin (NW P tf) :=
  stT P tf (insHd P tf qT) (wcT P tf Dw Dl k0 h qT) (k0 + tP Dw + tP Dl + 8 + 8) (hb5 tf Dw Dl k0 h) 1
/-- The numbers' counts (streams `0, 2, 4, 5, 6, 7`). -/
noncomputable def nuT (i : Fin 11) : Fin (NW P tf) :=
  stT P tf (insN P tf (hdT P tf Dw Dl k0 h qT) poT) (wcT P tf Dw Dl k0 h qT) (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9)
    (hb6 tf Dw Dl k0 h) i
/-- The entries' check. -/
noncomputable def ecT : Fin (NW P tf) :=
  sl P tf (insE P tf cx rT (nuT P tf Dw Dl k0 h qT poT 0)) (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56)
    (hb7 tf Dw Dl k0 h) 11

/-- **Phase 3's machine.** -/
noncomputable def ch3M (mb : Bool) (Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ : ℕ) :=
  Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf qT) k0 (hb1 tf Dw Dl k0 h))
    (PCPSerializerCapacity.Power.machine Dw Kw))
  (Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf qT) (k0 + tP Dw) (hb2 tf Dw Dl k0 h))
    (PCPSerializerCapacity.Power.machine Dl 1))
  (Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf cx) (k0 + tP Dw + tP Dl) (hb3 tf Dw Dl k0 h))
    FrontEntriesStage.countM)
  (Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf cx) (k0 + tP Dw + tP Dl + 8) (hb4 tf Dw Dl k0 h))
    FrontEntriesStage.countM)
  (Composition.machine (wfD P tf (FrontFmtHd.hdW mb) (insHd P tf qT) (wcT P tf Dw Dl k0 h qT)
    (k0 + tP Dw + tP Dl + 8 + 8) (hb5 tf Dw Dl k0 h))
  (Composition.machine (wfD P tf (FrontNums.numsW Kb Db cdf ζ Cδ) (insN P tf (hdT P tf Dw Dl k0 h qT) poT)
    (wcT P tf Dw Dl k0 h qT) (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9) (hb6 tf Dw Dl k0 h))
    (RecoveryFocus.machine (sl P tf (insE P tf cx rT (nuT P tf Dw Dl k0 h qT poT 0))
      (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56) (hb7 tf Dw Dl k0 h)) FrontEntriesStage.esMachine))))))

end Machine

section Step
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (Dw Kw Dl : ℕ) (k0 : ℕ) (h : k0 + CH3 Dw Dl ≤ tf) (qT cx rT poT : Fin (NW P tf))

theorem outSlot_val (D : ℕ) : (PCPSerializerCapacity.Power.outputSlot D).val = 3 + 2 * D := rfl

theorem tP_eq (D : ℕ) : tP D = 14 + 2 * D := rfl

theorem sTape_val' {ns nr : ℕ} (i : Fin (ns + 1)) (hi : i.val ≠ 0) : (sTape (nr := nr) i).val = i.val + 1 := by
  show (if i.val = 0 then 0 else i.val + 1) = _
  rw [if_neg hi]

theorem wcT_val : (wcT P tf Dw Dl k0 h qT).val = 2 + NL P + (k0 + (3 + 2 * Dw)) := by
  unfold wcT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf qT _ (by rw [outSlot_val]; omega)), rg_val, outSlot_val]

theorem hdT_val : (hdT P tf Dw Dl k0 h qT).val = 2 + NL P + (k0 + tP Dw + tP Dl + 8 + 8 + 2) := by
  unfold hdT; rw [stT_none P tf _ _ _ _ 1 (by unfold insHd; rw [if_neg (by decide)])]
  rw [sTape_val' (1 : Fin 2) (by decide)]; rfl

/-- **The request head's stage** (`FrontFmtHd.hdW` docked). -/
theorem hdStageF (mb : Bool) (q W : ℕ) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A (k0 + tP Dw + tP Dl + 8 + 8)) (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0)
    (hq : A qT = List.replicate q true ∧ H qT = 0)
    (hW : A (wcT P tf Dw Dl k0 h qT) = List.replicate W true ∧ H (wcT P tf Dw Dl k0 h qT) = 0)
    (hcap : 8 * q + 48 ≤ 2 * W + 2) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (wfD P tf (FrontFmtHd.hdW mb) (insHd P tf qT) (wcT P tf Dw Dl k0 h qT) (k0 + tP Dw + tP Dl + 8 + 8)
        (hb5 tf Dw Dl k0 h)) ((11 * W + 20) + 1 + (1 + 1 + (2 * FrontFmtHd.hdCost q + 2))) H A H A' ∧
      A' (hdT P tf Dw Dl k0 h qT) = frame (natWord q ++ [mb] ++ natWord 4) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + (k0 + tP Dw + tP Dl + 8 + 8) → A' y = A y) ∧
      PristineH P tf H A' (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9) := by
  have wcv := wcT_val P tf Dw Dl k0 h qT
  obtain ⟨τ5, hw5, e5, e5k, -⟩ := FrontFmtHd.hdW_spec (2 * W + 2) q mb hcap (FrontFmtHd.σH q) rfl rfl
    (fun _ => rfl) (fun _ => rfl)
  obtain ⟨A5, st5, o5, l5, p5⟩ := wfN P tf (FrontFmtHd.hdW mb) W _ (FrontFmtHd.σH q) τ5 hw5 (fun _ => rfl)
    (fun _ => rfl) rfl (insHd P tf qT) (wcT P tf Dw Dl k0 h qT) (k0 + tP Dw + tP Dl + 8 + 8) (hb5 tf Dw Dl k0 h)
    (fun i j b hi hj => by
      unfold insHd at hi hj; split_ifs at hi hj with h1 h2; exact Fin.ext (by omega))
    (fun i b hi => by
      unfold insHd at hi; split_ifs at hi; rw [← Option.some.inj hi]; exact ⟨hqL.1, by omega⟩)
    ⟨by rw [wcv]; omega, by rw [wcv, tP_eq, tP_eq]; omega⟩
    (fun i hi => by
      unfold insHd at hi; split_ifs at hi
      have := congrArg Fin.val (Option.some.inj hi); rw [wcv] at this; omega)
    (fun i b hi => by
      unfold insHd at hi; split_ifs at hi with h1
      have e : i = 0 := Fin.ext h1
      subst e; rw [e5k]; rfl)
    H A hPr
    (fun i b hi => by
      unfold insHd at hi; split_ifs at hi with h1
      rw [← Option.some.inj hi]
      have e : i = 0 := Fin.ext h1
      subst e; exact ⟨hq.1, hq.2⟩)
    (fun i hi => by
      unfold insHd at hi; split_ifs at hi with h1
      have e : i = 1 := Fin.ext (by have := i.isLt; show i.val = 1; omega)
      subst e; rfl)
    hW
  refine ⟨A5, st5, ?_, l5, p5⟩
  unfold hdT; rw [o5 1]; exact e5

end Step

section Step2
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (Dw Kw Dl : ℕ) (k0 : ℕ) (h : k0 + CH3 Dw Dl ≤ tf) (qT cx rT poT : Fin (NW P tf))

/-- The numbers' sources: the request head and the PCPP output, every other stream blank. -/
def srcN (HDw POw : List Bool) (i : Fin 11) : List Bool :=
  if i = FrontTW.sHd then HDw else if i = FrontTW.sPO then POw else []

theorem nuT_val (i : Fin 11) (hi : i ≠ FrontTW.sHd) (hp : i ≠ FrontTW.sPO) (h0 : i.val ≠ 0) :
    (nuT P tf Dw Dl k0 h qT poT i).val = 2 + NL P + (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + (i.val + 1)) := by
  unfold nuT
  rw [stT_none P tf _ _ _ _ i (by unfold insN; rw [if_neg hi, if_neg hp]), sTape_val' i h0]

theorem nuT0_val : (nuT P tf Dw Dl k0 h qT poT 0).val = 2 + NL P + (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + 0) := by
  unfold nuT
  rw [stT_none P tf _ _ _ _ 0 (by unfold insN; rw [if_neg (by decide), if_neg (by decide)])]
  rfl

theorem insN_cases (hdT' poT' : Fin (NW P tf)) (i : Fin 11) (b : Fin (NW P tf)) (h : insN P tf hdT' poT' i = some b) :
    (i = FrontTW.sHd ∧ b = hdT') ∨ (i = FrontTW.sPO ∧ b = poT') := by
  unfold insN at h
  by_cases h1 : i = FrontTW.sHd
  · rw [if_pos h1] at h; exact Or.inl ⟨h1, (Option.some.inj h).symm⟩
  · rw [if_neg h1] at h
    by_cases h2 : i = FrontTW.sPO
    · rw [if_pos h2] at h; exact Or.inr ⟨h2, (Option.some.inj h).symm⟩
    · rw [if_neg h2] at h; exact absurd h (by simp)

theorem insN_none (hdT' poT' : Fin (NW P tf)) (i : Fin 11) (h : insN P tf hdT' poT' i = none) :
    i ≠ FrontTW.sHd ∧ i ≠ FrontTW.sPO := by
  unfold insN at h
  by_cases h1 : i = FrontTW.sHd
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : i = FrontTW.sPO
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · exact ⟨h1, h2⟩

/-- **The numbers' stage** (M44 `numsW` docked). -/
theorem numsStageF {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (mb : Bool) (Kb Db : ℕ) (cdf : Bool) (Cδ : ℕ)
    (q sys aux cb W : ℕ) (restP : List Bool) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9))
    (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0)
    (hHD : A (hdT P tf Dw Dl k0 h qT) = frame (natWord q ++ [mb] ++ natWord 4) ∧ H (hdT P tf Dw Dl k0 h qT) = 0)
    (hp : A poT = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP ∧ H poT = 0)
    (hW : A (wcT P tf Dw Dl k0 h qT) = List.replicate W true ∧ H (wcT P tf Dw Dl k0 h qT) = 0)
    (hN : NumsCaps (2 * W + 2) h0 h1 Kb Db Cδ q sys aux cb) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (wfD P tf (FrontNums.numsW Kb Db cdf ζ Cδ) (insN P tf (hdT P tf Dw Dl k0 h qT) poT) (wcT P tf Dw Dl k0 h qT)
        (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9) (hb6 tf Dw Dl k0 h))
        ((11 * W + 20) + 1 + (1 + 1 + (2 * FrontNums.numsCost (2 * W + 2) h0 h1 Kb Db q sys aux cb
          ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) (Ledger.rowBSparse h0 h1 2 Cδ q) (sys + aux) + 2))) H A H A' ∧
      A' (nuT P tf Dw Dl k0 h qT poT 0) = List.replicate ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 2) = List.replicate (Ledger.rowBSparse h0 h1 2 Cδ q) true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 4) = List.replicate sys true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 5) = List.replicate aux true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 6) = List.replicate (sys + aux) true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 7) = false :: List.replicate (sys + aux) true ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9) → A' y = A y) ∧
      PristineH P tf H A' (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56) := by
  have wcv := wcT_val P tf Dw Dl k0 h qT
  have hdv := hdT_val P tf Dw Dl k0 h qT
  have hWT1 : WT 1 9 = 15 := rfl
  set HDw := frame (natWord q ++ [mb] ++ natWord 4) with hHDw
  set POw := natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP with hPOw
  have hH : srcN HDw POw FrontTW.sHd = enc true (natWord q) ++
      (RepairOrdinary.Streaming.marks [mb] ++ RepairOrdinary.Streaming.marks (natWord 4) ++ [false]) := by
    simp only [srcN, if_true]
    rw [hHDw, FrontFmtHd.frame_marks, FrontFmtHd.marks_app, FrontFmtHd.marks_app]
    simp [PrimAsm.ParseNat.enc, List.append_assoc]
  have hP : srcN HDw POw FrontTW.sPO = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP := by
    unfold srcN; rw [if_neg (by decide), if_pos rfl]
  obtain ⟨τ6, hw6, e0, e2, e4, e5, e6, e7, eH, eP⟩ := FrontNums.nums_spec (2 * W + 2) h0 h1 (srcN HDw POw) false
    Kb Db cdf Cδ q sys aux cb _ restP hH hP hN.hB hN.hK hN.hq4 hN.hPw hN.hBc hN.hB2 hN.cq hN.c3 hN.cs hN.ca hN.cc
    hN.hsp hN.hc hN.hs1 hN.hcE (by simp +decide [srcN])
  have hsH : ∀ i, i ≠ FrontTW.sOut → (FrontTW.ts (srcN HDw POw) 0 [] (fun _ => 0) false).st i = srcN HDw POw i :=
    fun i hi => FrontTW.ts_st _ _ _ _ _ i hi
  obtain ⟨A6, st6, o6, l6, p6⟩ := wfN P tf (FrontNums.numsW Kb Db cdf ζ Cδ) W _
    (FrontTW.ts (srcN HDw POw) 0 [] (fun _ => 0) false) τ6 hw6
    (fun i => by simp [FrontTW.ts])
    (fun r => by simp [FrontTW.ts, Function.update_apply])
    rfl (insN P tf (hdT P tf Dw Dl k0 h qT) poT) (wcT P tf Dw Dl k0 h qT) (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9)
    (hb6 tf Dw Dl k0 h)
    (fun i j b hi hj => by
      rcases insN_cases P tf _ _ i b hi with ⟨ei, eb⟩ | ⟨ei, eb⟩ <;>
        rcases insN_cases P tf _ _ j b hj with ⟨ej, eb'⟩ | ⟨ej, eb'⟩
      · rw [ei, ej]
      · exfalso; have := congrArg Fin.val (eb.symm.trans eb'); rw [hdv] at this; omega
      · exfalso; have := congrArg Fin.val (eb'.symm.trans eb); rw [hdv] at this; omega
      · rw [ei, ej])
    (fun i b hi => by
      rcases insN_cases P tf _ _ i b hi with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rw [hdv, tP_eq, tP_eq, hWT1]; omega
      · exact ⟨hpL.1, by omega⟩)
    ⟨by rw [wcv]; omega, by rw [wcv, tP_eq, tP_eq]; omega⟩
    (fun i hi => by
      rcases insN_cases P tf _ _ i _ hi with ⟨-, e⟩ | ⟨-, e⟩
      · have := congrArg Fin.val e; rw [hdv, wcv, tP_eq, tP_eq] at this; omega
      · have := congrArg Fin.val e; rw [wcv] at this; omega)
    (fun i b hi => by
      rcases insN_cases P tf _ _ i b hi with ⟨ei, -⟩ | ⟨ei, -⟩
      · rw [ei, eH, hsH _ (by decide)]
      · rw [ei, eP, hsH _ (by decide)])
    H A hPr
    (fun i b hi => by
      rcases insN_cases P tf _ _ i b hi with ⟨ei, rfl⟩ | ⟨ei, rfl⟩
      · rw [ei, hsH _ (by decide)]; simp only [srcN, if_true]; exact hHD
      · rw [ei, hsH _ (by decide), hP]; exact hp)
    (fun i hi => by
      obtain ⟨h1, h2⟩ := insN_none P tf _ _ i hi
      by_cases h0 : i = FrontTW.sOut
      · subst h0; simp [FrontTW.ts]
      · rw [hsH i h0]; unfold srcN; rw [if_neg h1, if_neg h2])
    hW
  refine ⟨A6, st6, ?_, ?_, ?_, ?_, ?_, ?_, l6, p6⟩
  · unfold nuT; rw [o6 0]; exact e0
  · unfold nuT; rw [o6 2]; exact e2
  · unfold nuT; rw [o6 4]; exact e4
  · unfold nuT; rw [o6 5]; exact e5
  · unfold nuT; rw [o6 6]; exact e6
  · unfold nuT; rw [o6 7]; exact e7

end Step2

section Step3
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (Dw Kw Dl : ℕ) (k0 : ℕ) (h : k0 + CH3 Dw Dl ≤ tf) (qT cx rT poT : Fin (NW P tf))

theorem insE_cases (cx' rT' eT' : Fin (NW P tf)) (i : Fin FrontEntriesStage.ET) (b : Fin (NW P tf))
    (hi : insE P tf cx' rT' eT' i = some b) :
    (i.val = 0 ∧ b = cx') ∨ (i.val = 1 ∧ b = rT') ∨ (i.val = 2 ∧ b = eT') := by
  unfold insE at hi
  by_cases h0 : i.val = 0
  · rw [if_pos h0] at hi; exact Or.inl ⟨h0, (Option.some.inj hi).symm⟩
  · rw [if_neg h0] at hi
    by_cases h1 : i.val = 1
    · rw [if_pos h1] at hi; exact Or.inr (Or.inl ⟨h1, (Option.some.inj hi).symm⟩)
    · rw [if_neg h1] at hi
      by_cases h2 : i.val = 2
      · rw [if_pos h2] at hi; exact Or.inr (Or.inr ⟨h2, (Option.some.inj hi).symm⟩)
      · rw [if_neg h2] at hi; exact absurd hi (by simp)

theorem insE_none (cx' rT' eT' : Fin (NW P tf)) (i : Fin FrontEntriesStage.ET)
    (hi : insE P tf cx' rT' eT' i = none) : i.val ≠ 0 ∧ i.val ≠ 1 ∧ i.val ≠ 2 := by
  unfold insE at hi
  by_cases h0 : i.val = 0
  · rw [if_pos h0] at hi; exact absurd hi (by simp)
  · rw [if_neg h0] at hi
    by_cases h1 : i.val = 1
    · rw [if_pos h1] at hi; exact absurd hi (by simp)
    · rw [if_neg h1] at hi
      by_cases h2 : i.val = 2
      · rw [if_pos h2] at hi; exact absurd hi (by simp)
      · exact ⟨h0, h1, h2⟩

/-- **The entries' check** (`FrontEntriesStage.entries_ready` docked on `frame x`, `frame r`, `1^E`). -/
theorem entStageF (x r : List Bool) (En : ℕ) (hx : r.length + 1 ≤ x.length) (H : Fin (NW P tf) → ℕ)
    (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56))
    (hcL : 2 + NL P ≤ cx.val ∧ cx.val < 2 + NL P + k0) (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0)
    (hcr : cx ≠ rT) (hX : A cx = frame x ∧ H cx = 0) (hR : A rT = frame r ∧ H rT = 0)
    (hE : A (nuT P tf Dw Dl k0 h qT poT 0) = List.replicate En true ∧ H (nuT P tf Dw Dl k0 h qT poT 0) = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (insE P tf cx rT (nuT P tf Dw Dl k0 h qT poT 0))
        (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56) (hb7 tf Dw Dl k0 h)) FrontEntriesStage.esMachine)
        (FrontEntriesStage.esCost x r) H A H A' ∧
      A' (ecT P tf Dw Dl k0 h qT cx rT poT) = [(FrontEntriesRef.entScan En r).isSome] ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56) → A' y = A y) ∧
      PristineH P tf H A' (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56 + FrontEntriesStage.ET) := by
  have n0 := nuT0_val P tf Dw Dl k0 h qT poT
  have hWT2 : WT 10 56 = 71 := rfl
  obtain ⟨out, hr, o11, o0, o1, o2⟩ := FrontEntriesStage.entries_ready x r En hx
  obtain ⟨st, hsl, hlow, hpr⟩ := readyN P tf _ _ _ out hr (insE P tf cx rT (nuT P tf Dw Dl k0 h qT poT 0))
    (k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56) (hb7 tf Dw Dl k0 h)
    (fun i j b hi hj => by
      apply Fin.ext
      rcases insE_cases P tf _ _ _ i b hi with ⟨ei, eb⟩ | ⟨ei, eb⟩ | ⟨ei, eb⟩ <;>
        rcases insE_cases P tf _ _ _ j b hj with ⟨ej, eb'⟩ | ⟨ej, eb'⟩ | ⟨ej, eb'⟩ <;>
        first
          | omega
          | (exfalso; exact hcr (eb.symm.trans eb'))
          | (exfalso; exact hcr (eb'.symm.trans eb))
          | (exfalso; have e := congrArg Fin.val (eb.symm.trans eb'); omega))
    (fun i b hi => by
      rcases insE_cases P tf _ _ _ i b hi with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨hcL.1, by omega⟩
      · exact ⟨hrL.1, by omega⟩
      · rw [n0, hWT2]; omega)
    (fun j b hj => by
      rcases insE_cases P tf _ _ _ j b hj with ⟨ej, -⟩ | ⟨ej, -⟩ | ⟨ej, -⟩
      · have e : j = 0 := Fin.ext ej
        subst e; rw [o0]; simp [FrontEntriesStage.esIn, FrontEntriesStage.ET]
      · have e : j = 1 := Fin.ext ej
        subst e; rw [o1]; simp [FrontEntriesStage.esIn, FrontEntriesStage.ET]
      · have e : j = 2 := Fin.ext ej
        subst e; rw [o2]; simp [FrontEntriesStage.esIn, FrontEntriesStage.ET])
    H A hPr
    (fun i b hi => by
      rcases insE_cases P tf _ _ _ i b hi with ⟨ei, rfl⟩ | ⟨ei, rfl⟩ | ⟨ei, rfl⟩
      · refine ⟨?_, hX.2⟩; rw [hX.1]; simp [FrontEntriesStage.esIn, ei]
      · refine ⟨?_, hR.2⟩; rw [hR.1]; simp [FrontEntriesStage.esIn, ei]
      · refine ⟨?_, hE.2⟩; rw [hE.1]; simp [FrontEntriesStage.esIn, ei])
    (fun i hi => by
      obtain ⟨a0, a1, a2⟩ := insE_none P tf _ _ _ i hi
      simp [FrontEntriesStage.esIn, a0, a1, a2])
  exact ⟨_, st, by unfold ecT; rw [hsl 11]; exact o11, hlow, hpr⟩

theorem lcT_val : (lcT P tf Dw Dl k0 h qT).val = 2 + NL P + ((k0 + tP Dw) + (3 + 2 * Dl)) := by
  unfold lcT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf qT _ (by rw [outSlot_val]; omega)), rg_val, outSlot_val]

theorem x1T_val : (x1T P tf Dw Dl k0 h cx).val = 2 + NL P + ((k0 + tP Dw + tP Dl) + 2) := by
  unfold x1T; rw [sl_none P tf _ _ _ _ (sh1_ne P tf cx _ (by decide)), rg_val]; rfl

theorem x2T_val : (x2T P tf Dw Dl k0 h cx).val = 2 + NL P + ((k0 + tP Dw + tP Dl + 8) + 2) := by
  unfold x2T; rw [sl_none P tf _ _ _ _ (sh1_ne P tf cx _ (by decide)), rg_val]; rfl

end Step3

/-- **Phase 3's cost.** -/
noncomputable def ch3Cost {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Dw Kw Dl Kb Db Cδ q sys aux cb : ℕ)
    (x r : List Bool) : ℕ :=
  PCPSerializerCapacity.Power.budget Dw Kw q + 1 + (PCPSerializerCapacity.Power.budget Dl 1 q + 1 +
  ((4 * x.length + 5 + 1 + (2 * x.length + 6)) + 1 + ((4 * x.length + 5 + 1 + (2 * x.length + 6)) + 1 +
  (((11 * (Kw * (q + 1) ^ Dw) + 20) + 1 + (1 + 1 + (2 * FrontFmtHd.hdCost q + 2))) + 1 +
  (((11 * (Kw * (q + 1) ^ Dw) + 20) + 1 + (1 + 1 + (2 * FrontNums.numsCost (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1
    Kb Db q sys aux cb ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) (Ledger.rowBSparse h0 h1 2 Cδ q) (sys + aux)
    + 2))) + 1 + FrontEntriesStage.esCost x r)))))

section Step4
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (Dw Kw Dl : ℕ) (k0 : ℕ) (h : k0 + CH3 Dw Dl ≤ tf) (qT cx rT poT : Fin (NW P tf))

/-- **Phase 3** (the seven stages composed): the fill count, the envelope, two copies of `1^{|x|}`, the request head,
the numbers' counts, the entries' verdict; the tapes below the phase kept, the tapes past it blank. -/
theorem ch3_step {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (mb : Bool) (Kb Db : ℕ) (cdf : Bool) (Cδ : ℕ)
    (q sys aux cb : ℕ) (x r restP : List Bool) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hcL : 2 + NL P ≤ cx.val ∧ cx.val < 2 + NL P + k0)
    (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0) (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0)
    (hcr : cx ≠ rT) (hq : A qT = List.replicate q true ∧ H qT = 0) (hX : A cx = frame x ∧ H cx = 0)
    (hR : A rT = frame r ∧ H rT = 0)
    (hp : A poT = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP ∧ H poT = 0)
    (hx : r.length + 1 ≤ x.length) (hN : NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (ch3M P tf Dw Kw Dl k0 h qT cx rT poT mb Kb Db cdf ζ Cδ)
        (ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb x r) H A H A' ∧
      A' (wcT P tf Dw Dl k0 h qT) = List.replicate (Kw * (q + 1) ^ Dw) true ∧
      A' (lcT P tf Dw Dl k0 h qT) = List.replicate ((q + 1) ^ Dl) true ∧
      A' (x1T P tf Dw Dl k0 h cx) = List.replicate x.length true ∧
      A' (x2T P tf Dw Dl k0 h cx) = List.replicate x.length true ∧
      A' (hdT P tf Dw Dl k0 h qT) = frame (natWord q ++ [mb] ++ natWord 4) ∧
      A' (nuT P tf Dw Dl k0 h qT poT 0) = List.replicate ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 2) = List.replicate (Ledger.rowBSparse h0 h1 2 Cδ q) true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 4) = List.replicate sys true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 5) = List.replicate aux true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 6) = List.replicate (sys + aux) true ∧
      A' (nuT P tf Dw Dl k0 h qT poT 7) = false :: List.replicate (sys + aux) true ∧
      A' (ecT P tf Dw Dl k0 h qT cx rT poT) =
        [(FrontEntriesRef.entScan ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) r).isSome] ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A' y = A y) ∧
      PristineH P tf H A' (k0 + CH3 Dw Dl) := by
  have t1 := tP_eq Dw
  have t2 := tP_eq Dl
  have hWT1 : WT 1 9 = 15 := rfl
  have hWT2 : WT 10 56 = 71 := rfl
  have wcv := wcT_val P tf Dw Dl k0 h qT
  have lcv := lcT_val P tf Dw Dl k0 h qT
  have x1v := x1T_val P tf Dw Dl k0 h cx
  have x2v := x2T_val P tf Dw Dl k0 h cx
  have hdv := hdT_val P tf Dw Dl k0 h qT
  have n0 := nuT0_val P tf Dw Dl k0 h qT poT
  obtain ⟨A1, s1, w1, l1, p1⟩ := powStage P tf Dw Kw q k0 (hb1 tf Dw Dl k0 h) qT hqL H A hPr hq
  obtain ⟨A2, s2, w2, l2, p2⟩ := powStage P tf Dl 1 q (k0 + tP Dw) (hb2 tf Dw Dl k0 h) qT ⟨hqL.1, by omega⟩
    H A1 p1 ⟨by rw [l1 qT (by omega)]; exact hq.1, hq.2⟩
  obtain ⟨A3, s3, w3, -, l3, p3⟩ := metaStage P tf x (k0 + tP Dw + tP Dl) (hb3 tf Dw Dl k0 h) cx
    ⟨hcL.1, by omega⟩ H A2 p2 ⟨by rw [l2 cx (by omega), l1 cx (by omega)]; exact hX.1, hX.2⟩
  obtain ⟨A4, s4, w4, -, l4, p4⟩ := metaStage P tf x (k0 + tP Dw + tP Dl + 8) (hb4 tf Dw Dl k0 h) cx
    ⟨hcL.1, by omega⟩ H A3 p3
    ⟨by rw [l3 cx (by omega), l2 cx (by omega), l1 cx (by omega)]; exact hX.1, hX.2⟩
  obtain ⟨A5, s5, w5, l5, p5⟩ := hdStageF P tf Dw Dl k0 h qT mb q (Kw * (q + 1) ^ Dw) H A4 p4 hqL
    ⟨by rw [l4 qT (by omega), l3 qT (by omega), l2 qT (by omega), l1 qT (by omega)]; exact hq.1, hq.2⟩
    ⟨by
      rw [l4 (wcT P tf Dw Dl k0 h qT) (by omega), l3 (wcT P tf Dw Dl k0 h qT) (by omega),
        l2 (wcT P tf Dw Dl k0 h qT) (by omega)]
      exact w1, (hPr.1 (wcT P tf Dw Dl k0 h qT) (by omega)).2⟩ hN.hhd
  obtain ⟨A6, s6, e0, e2, e4, e5, e6, e7, l6, p6⟩ := numsStageF P tf Dw Dl k0 h qT poT h0 h1 mb Kb Db cdf Cδ
    q sys aux cb (Kw * (q + 1) ^ Dw) restP H A5 p5 hpL
    ⟨w5, (hPr.1 (hdT P tf Dw Dl k0 h qT) (by omega)).2⟩
    ⟨by
      rw [l5 poT (by omega), l4 poT (by omega), l3 poT (by omega), l2 poT (by omega), l1 poT (by omega)]
      exact hp.1, hp.2⟩
    ⟨by
      rw [l5 (wcT P tf Dw Dl k0 h qT) (by omega), l4 (wcT P tf Dw Dl k0 h qT) (by omega),
        l3 (wcT P tf Dw Dl k0 h qT) (by omega), l2 (wcT P tf Dw Dl k0 h qT) (by omega)]
      exact w1, (hPr.1 (wcT P tf Dw Dl k0 h qT) (by omega)).2⟩ hN
  obtain ⟨A7, s7, w7, l7, p7⟩ := entStageF P tf Dw Dl k0 h qT cx rT poT x r
    ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) hx H A6 p6 hcL hrL hcr
    ⟨by
      rw [l6 cx (by omega), l5 cx (by omega), l4 cx (by omega), l3 cx (by omega), l2 cx (by omega),
        l1 cx (by omega)]
      exact hX.1, hX.2⟩
    ⟨by
      rw [l6 rT (by omega), l5 rT (by omega), l4 rT (by omega), l3 rT (by omega), l2 rT (by omega),
        l1 rT (by omega)]
      exact hR.1, hR.2⟩
    ⟨e0, (hPr.1 (nuT P tf Dw Dl k0 h qT poT 0) (by omega)).2⟩
  refine ⟨A7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ch3M ch3Cost
    exact Step.seq s1 (Step.seq s2 (Step.seq s3 (Step.seq s4 (Step.seq s5 (Step.seq s6 s7)))))
  · rw [l7 (wcT P tf Dw Dl k0 h qT) (by omega), l6 (wcT P tf Dw Dl k0 h qT) (by omega),
      l5 (wcT P tf Dw Dl k0 h qT) (by omega), l4 (wcT P tf Dw Dl k0 h qT) (by omega),
      l3 (wcT P tf Dw Dl k0 h qT) (by omega), l2 (wcT P tf Dw Dl k0 h qT) (by omega)]
    exact w1
  · rw [l7 (lcT P tf Dw Dl k0 h qT) (by omega), l6 (lcT P tf Dw Dl k0 h qT) (by omega),
      l5 (lcT P tf Dw Dl k0 h qT) (by omega), l4 (lcT P tf Dw Dl k0 h qT) (by omega),
      l3 (lcT P tf Dw Dl k0 h qT) (by omega)]
    rw [Nat.one_mul] at w2
    exact w2
  · rw [l7 (x1T P tf Dw Dl k0 h cx) (by omega), l6 (x1T P tf Dw Dl k0 h cx) (by omega),
      l5 (x1T P tf Dw Dl k0 h cx) (by omega), l4 (x1T P tf Dw Dl k0 h cx) (by omega)]
    exact w3
  · rw [l7 (x2T P tf Dw Dl k0 h cx) (by omega), l6 (x2T P tf Dw Dl k0 h cx) (by omega),
      l5 (x2T P tf Dw Dl k0 h cx) (by omega)]
    exact w4
  · rw [l7 (hdT P tf Dw Dl k0 h qT) (by omega), l6 (hdT P tf Dw Dl k0 h qT) (by omega)]
    exact w5
  · rw [l7 (nuT P tf Dw Dl k0 h qT poT 0) (by omega)]; exact e0
  · rw [l7 (nuT P tf Dw Dl k0 h qT poT 2)
      (by rw [nuT_val P tf Dw Dl k0 h qT poT 2 (by decide) (by decide) (by decide)]; omega)]; exact e2
  · rw [l7 (nuT P tf Dw Dl k0 h qT poT 4)
      (by rw [nuT_val P tf Dw Dl k0 h qT poT 4 (by decide) (by decide) (by decide)]; omega)]; exact e4
  · rw [l7 (nuT P tf Dw Dl k0 h qT poT 5)
      (by rw [nuT_val P tf Dw Dl k0 h qT poT 5 (by decide) (by decide) (by decide)]; omega)]; exact e5
  · rw [l7 (nuT P tf Dw Dl k0 h qT poT 6)
      (by rw [nuT_val P tf Dw Dl k0 h qT poT 6 (by decide) (by decide) (by decide)]; omega)]; exact e6
  · rw [l7 (nuT P tf Dw Dl k0 h qT poT 7)
      (by rw [nuT_val P tf Dw Dl k0 h qT poT 7 (by decide) (by decide) (by decide)]; omega)]; exact e7
  · exact w7
  · intro y hy
    rw [l7 y (by omega), l6 y (by omega), l5 y (by omega), l4 y (by omega), l3 y (by omega), l2 y (by omega),
      l1 y (by omega)]
  · have e : k0 + CH3 Dw Dl = k0 + tP Dw + tP Dl + 8 + 8 + WT 1 9 + WT 10 56 + FrontEntriesStage.ET := by
      unfold CH3; omega
    rw [e]; exact p7

end Step4

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3P
