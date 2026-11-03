import Proof.Wire_3_5.UnionMachine.FsRun
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.SeedIdx

/-! # C6, the FILTER setup, part 6: the FILTER-ready state

From the setup's run (`FsRun.fs_exec`) and the capacity facts **`FsCap`** (the stages' and `FiltReady`'s capacity
inequalities), **`fs_ready`** proves `FiltSetupSpec5`'s run conclusion at the seed `e = (gapSeedEquiv P).symm g`:
the request, counter and flags, the rulers `RW = LW = rulerW P`, `Mlab = off + L + (r4 + 4)·G`, the sample the seed's
copy over the walk bank's side (`SeedIdx.seedCopy`, X1), and every field of `UnitReady.FiltReady` (the unary field
degree, the trace mask's zero words, the walk bank's inputs with the seed's index word (`SeedIdx.seedIndex_cast`),
C5's builder words and registers (`FinalPass.Filt.canon`), the FILTER numbers (`FiltRec.filtDeg_filterTable`,
`tableWord_length`, `cap37_filterTable`), the blank scratch).

Paper quantity of the main type: the regular filter's FILTER-ready unit state at the call's seed (filt:gap). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FsReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.UnionMachine

/-- The words' streams, as indices. -/
def wordsN : List (Fin 161) := [91, 25, 26, 27, 28, 24, 81, 108, 109, 110, 111, 112, 83, 84, 85, 86, 87, 88, 89, 90, 151]

theorem nmem_words (x : ℕ) (i : Fin (LNS x + 1)) (h : i.val ∉ wordsN.map Fin.val) : i ∉ FsWords.wordsOut x := by
  rw [show FsWords.wordsOut x = wordsN.map (sk x) from rfl]
  intro hm
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
  rw [sk_val] at h
  exact h (List.mem_map_of_mem hk)

theorem SmT_val (x : ℕ) (j : Fin 7) : (SmT x j).val = (smv j).val := rfl

/-- **The capacity facts** of the setup's stages and of `FiltReady` at `Mlab = off + L + (r4 + 4)·G`. -/
structure FsCap (cap : ℕ) (P : GapParams) (L r4 G off g : ℕ) : Prop where
  c1 : 1 ≤ cap
  cBc : P.cap * 32 + 2 ≤ cap
  cMc : P.len + 8 ≤ cap
  cEc : P.errExp + 4 ≤ cap
  csc : 2 ^ (P.seedBits + 1) ≤ cap
  clc : P.labelBits + P.fieldBits + P.walkLen + 512 ≤ cap
  ccr : 256 * (2 * P.fieldBits + 3 * P.labelBits) + 160 * P.walkLen + 1000 ≤ cap
  cc0 : P.fieldBits + P.labelBits + (P.labelBits - 1) + P.prefixBits + L + r4 + G + off + 1000 ≤ cap
  ccC : 384 * P.walkLen + 4 * L + 1000 ≤ cap
  ccz : P.walkLen * (L * 256 + 258) + 2 * L + (P.walkLen + 1) / 2 + P.walkLen + 1000 ≤ cap
  ccL : 256 * L + 1000 ≤ cap
  ccw : P.fieldBits + P.labelBits + (P.walkLen - 1) + 128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1)) +
      (2 * (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1))) + 1) + (P.labelBits + (P.labelBits - 1)) + g +
      2 * (160 * (P.walkLen - 1) + 2 * (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1)))) +
      2 * P.fieldBits + 2 * P.labelBits + 2 * (P.labelBits + (P.labelBits - 1)) + 1000 ≤ cap
  cap6 : 2 * (wOf P.fieldBits P.labelBits * 128) + 4 * P.labelBits + 2 * P.fieldBits + L + 10 ≤ cap
  cO6 : (2 * (P.errExp / 4) + 1) * (128 * (2 * L + 2) + 2) + 12 < cap
  capT : 2 * P.fieldBits + 2 ≤ cap
  rd : ∀ e : GapSeed P,
    4 * (8 * (4 * L) + 6) + 30 + 4 * filtDeg (filterTable P e L) + 6 + 4 * L + filtDeg (filterTable P e L) + 10 ≤ cap ∧
    (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6)) +
      ((sliceLabs r4 G off L).flatMap labE).length + 4 * labSum (sliceLabs r4 G off L) + 10 +
      L * (4 * (4 * (off + L + (r4 + 4) * G) + 4)) + L * (4 * (2 * (off + L + (r4 + 4) * G) + 10)) +
      4 * (4 * (off + L + (r4 + 4) * G) + 4) + 4 * (2 * (off + L + (r4 + 4) * G) + 10) +
      7 * (off + L + (r4 + 4) * G) + r4 + G + off + L + labSum (sliceLabs r4 G off L) + 40 ≤ cap ∧
    (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6) +
      (((sliceLabs r4 G off L).flatMap labE).length + 6 + 4 * labSum (sliceLabs r4 G off L) + 4)) +
      4 * (tableWord (filterTable P e L)).length + 2 + (tableWord (filterTable P e L)).length + 5 ≤ cap ∧
    (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6) +
      (((sliceLabs r4 G off L).flatMap labE).length + 6 + 4 * labSum (sliceLabs r4 G off L) + 4) +
      (4 * (tableWord (filterTable P e L)).length + 2)) + 4 * majorityThreshold P.walkLen + 6 +
      8 * (4 * (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 1) + 2) + 7 + majorityThreshold P.walkLen +
      cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 10 ≤ cap ∧
    (frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L))).length ≤ cap

/-- **The FILTER setup's run, FILTER-ready** (`FiltSetupSpec5`'s run conclusion from the capacity facts). -/
theorem fs_ready (W : WalkBankProducer) (cap : ℕ) (P : GapParams) (g : ℕ) (hg : g < Fintype.card (GapSeed P))
    (L r4 G off : ℕ) (w out u : List Bool) (j : ℕ) (σ : WState (LNS W.x) LNR) (hU : 1 ≤ P.cap)
    (hlen : (sliceLabs r4 G off L).length = 4 * L) (hc : FsCap cap P L r4 G off g)
    (hin : FsIn2 W.x σ w out j u P.len P.cap P.errExp g r4 G off L) :
    ∃ τ : WState (LNS W.x) LNR, WExec cap (FsRun.fsProg W.x) σ τ (FsRun.fsCost cap) ∧
      τ.st (sk W.x 0) = frame w ∧ τ.sh (sk W.x 0) = 0 ∧ τ.st (sk W.x 2) = List.replicate j true ∧
      τ.sh (sk W.x 2) = 0 ∧
      τ.st (sk W.x 150) = [] ∧ τ.sh (sk W.x 150) = 0 ∧ τ.st (sk W.x 151) = [true] ∧ τ.sh (sk W.x 151) = 0 ∧
      ∃ (Mlab RW LW : ℕ) (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128))
          (2 * (P.errExp / 4) + 1)),
        RW = rulerW P ∧ LW = rulerW P ∧
        FiltReady cap W τ out P ((Enum.gapSeedEquiv P).symm ⟨g, hg⟩) L r4 G off Mlab RW LW sample := by
  obtain ⟨τ, hx, hsh, hcl, hfr, hlow, v6, v7, v8, v9, v10, v223, v231, v232, v233, v234, v243, v244, v245, v246,
    v247, w91, w25, w26, w27, w28, w24, w81, w108, w109, w110, w111, w112, w83, w84, w85, w86, w87, w88, w89, w90,
    w151⟩ := FsRun.fs_exec cap W.x P g L r4 G off w out u j σ hin hU hc.c1 hc.cBc hc.cMc hc.cEc hc.csc hc.clc hc.ccr
      hc.cc0 hc.ccC hc.ccz hc.ccL hc.ccw
  have kept : ∀ k : Fin 161, k.val ∉ wordsN.map Fin.val → τ.st (sk W.x k) = σ.st (sk W.x k) := fun k hk =>
    hfr _ (nmem_words W.x _ (by rw [sk_val]; exact hk))
  have heads : ∀ i, τ.sh i = σ.sh i := fun i => by rw [hsh]
  have blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → k.val ∉ wordsN.map Fin.val →
      τ.st (sk W.x k) = [] ∧ τ.sh (sk W.x k) = 0 := fun k h0 h1 h2 h3 hw =>
    ⟨by rw [kept k hw]; exact (hin.blank k h0 h1 h2 h3).1, by rw [heads]; exact (hin.blank k h0 h1 h2 h3).2⟩
  have zh : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → τ.sh (sk W.x k) = 0 :=
    fun k h0 h1 h2 h3 => by rw [heads]; exact (hin.blank k h0 h1 h2 h3).2
  have blankV : ∀ i : Fin (LNS W.x + 1), i.val < 161 → i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 113 →
      i.val ∉ wordsN.map Fin.val → τ.st i = [] ∧ τ.sh i = 0 := by
    intro i hi h0 h1 h2 h3 hw
    have e : i = sk W.x ⟨i.val, hi⟩ := Fin.ext (by rw [sk_val])
    rw [e]
    exact blank ⟨i.val, hi⟩ h0 h1 h2 h3 hw
  have headV : ∀ i : Fin (LNS W.x + 1), i.val < 161 → i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 113 →
      τ.sh i = 0 := by
    intro i hi h0 h1 h2 h3
    have e : i = sk W.x ⟨i.val, hi⟩ := Fin.ext (by rw [sk_val])
    rw [e]
    exact zh ⟨i.val, hi⟩ h0 h1 h2 h3
  have hwl1 : P.walkLen - 1 = 2 * (P.errExp / 4) := by unfold GapParams.walkLen; omega
  have hR : 128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1)) = wOf P.fieldBits P.labelBits * 128 := by
    unfold wOf; omega
  set e := (Enum.gapSeedEquiv P).symm ⟨g, hg⟩ with he
  refine ⟨τ, hx, ?_, ?_, ?_, ?_, ?_, ?_, w151, ?_, off + L + (r4 + 4) * G, rulerW P, rulerW P, SeedIdx.seedCopy P e,
    rfl, rfl, ?_⟩
  · rw [kept 0 (by decide)]; exact hin.s0
  · rw [heads]; exact hin.h0
  · rw [kept 2 (by decide)]; exact hin.s2
  · rw [heads]; exact hin.h2
  · exact (blank 150 (by decide) (by decide) (by decide) (by decide) (by decide)).1
  · exact zh 150 (by decide) (by decide) (by decide) (by decide)
  · exact zh 151 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨cA, cB, cC, cD, crw⟩ := hc.rd e
  have hmsc : ∀ j : Fin 17, j.val ≠ 0 → τ.st (tmapM W.x j) = [] := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    all_goals exact (blankV _ (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide)).1
  have hmh : ∀ j : Fin 17, τ.sh (tmapM W.x j) = 0 := by
    intro j
    fin_cases j <;> exact headV _ (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide) (by rw [tmapM_val]; decide)
  have htau : ∀ j : Fin 7, 1 ≤ j.val → τ.st (SmT W.x j) = frame (binary P.fieldBits 0) ∧ τ.sh (SmT W.x j) = 0 := by
    intro j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact ⟨w81, headV _ (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide)⟩
    · exact ⟨w108, headV _ (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide)⟩
    · exact ⟨w109, headV _ (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide)⟩
    · exact ⟨w110, headV _ (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide)⟩
    · exact ⟨w111, headV _ (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide)⟩
    · exact ⟨w112, headV _ (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide) (by rw [SmT_val]; decide)⟩
  have htauR : ∀ j : Fin 9, j ≠ 4 → τ.val (RgT j) = 0 := by
    intro j hj
    fin_cases j
    all_goals first | exact absurd rfl hj | exact hlow _ (by decide) (by decide)
  have hports : ∀ j : Fin 14, τ.st (sk W.x (portT j)) = inPorts (wOf P.fieldBits P.labelBits * 128)
      (2 * (P.errExp / 4)) (rulerW P) (rulerW P) (seedIndexWord (wOf P.fieldBits P.labelBits * 128)
        (2 * (P.errExp / 4)) (SeedIdx.seedCopy P e)) j := by
    intro j
    fin_cases j
    all_goals first
      | exact (blankV _ (by rw [sk_val]; decide) (by rw [sk_val]; decide) (by rw [sk_val]; decide) (by rw [sk_val]; decide) (by rw [sk_val]; decide) (by rw [sk_val]; decide)).1
      | skip
    · show τ.st (sk W.x 24) = frame (seedIndexWord (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4))
        (SeedIdx.seedCopy P e))
      rw [he, SeedIdx.seedIndex_cast, w24, hwl1, hR]
    · show τ.st (sk W.x 25) = List.replicate (wOf P.fieldBits P.labelBits * 128) true
      rw [w25, hR]
    · show τ.st (sk W.x 26) = List.replicate (2 * (P.errExp / 4)) true
      rw [w26, hwl1]
    · show τ.st (sk W.x 27) = List.replicate (rulerW P) true
      rw [w27, hR]; rfl
    · show τ.st (sk W.x 28) = List.replicate (rulerW P) true
      rw [w28, hR]; rfl
  have hh : ∀ j : Fin 14, τ.sh (sk W.x (portT j)) = 0 := by
    intro j
    fin_cases j <;> exact headV _ (by rw [sk_val]; decide) (by rw [sk_val]; decide) (by rw [sk_val]; decide) (by rw [sk_val]; decide) (by rw [sk_val]; decide)
  have hC5 : ∀ i : Fin 12, 4 ≤ i.val → τ.st (fsF W.x i) = (yFC P L (rulerW P) (rulerW P) (SeedIdx.seedCopy P e)).st i ∧
      τ.sh (fsF W.x i) = 0 := by
    intro i hi
    fin_cases i
    all_goals first | exact absurd hi (by decide) | skip
    · exact ⟨by show τ.st (sk W.x 83) = _; rw [w83]; simp [yFC, TSt.w, canon],
        headV _ (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide)⟩
    · exact ⟨by show τ.st (sk W.x 84) = _; rw [w84]; simp [yFC, TSt.w, canon],
        headV _ (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide)⟩
    · exact ⟨by show τ.st (sk W.x 85) = _; rw [w85]; simp [yFC, TSt.w, canon],
        headV _ (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide)⟩
    · exact ⟨by show τ.st (sk W.x 86) = _; rw [w86]; simp [yFC, TSt.w, canon],
        headV _ (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide)⟩
    · exact ⟨by show τ.st (sk W.x 87) = _; rw [w87]; simp [yFC, TSt.w, canon],
        headV _ (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide)⟩
    · exact ⟨by show τ.st (sk W.x 88) = _; rw [w88]; simp [yFC, TSt.w, canon],
        headV _ (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide)⟩
    · exact ⟨by show τ.st (sk W.x 89) = _; rw [w89]; simp [yFC, TSt.w, canon],
        headV _ (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide)⟩
    · exact ⟨by show τ.st (sk W.x 90) = _; rw [w90]; simp [yFC, TSt.w, canon, FinalPass.Tm.binary_zero'],
        headV _ (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide) (by rw [fsF_val]; decide)⟩
  have hC5r : ∀ r : Fin 19, τ.val (frC r) = (yFC P L (rulerW P) (rulerW P) (SeedIdx.seedCopy P e)).val r := by
    intro r
    fin_cases r
    all_goals first
      | (rw [hlow _ (by decide) (by decide)]; simp [yFC, TSt.w, canon, owOf])
      | skip
    · show τ.val 6 = _; rw [v6]; simp [yFC, TSt.w, canon]
    · show τ.val 7 = _; rw [v7]; simp [yFC, TSt.w, canon]
    · show τ.val 8 = _; rw [v8]; simp [yFC, TSt.w, canon]
    · show τ.val 9 = _; rw [v9]; simp [yFC, TSt.w, canon]
    · show τ.val 10 = _; rw [v10]; simp [yFC, TSt.w, canon]
  have hscr : ∀ j : Fin (1 + (1 + (14 + F37.t) + 1)), j.val ≠ 0 → j.val ≠ 12 →
      τ.st (tmapR W.x j) = [] ∧ τ.sh (tmapR W.x j) = 0 := by
    intro j h0 h12
    have hj : j.val < 28 := F28 ▸ j.isLt
    have hv : (tmapR W.x j).val = 29 + j.val := by
      simp only [tmapR, sk_val, portR_val, Fin.val_cast, h0, h12, if_false]
    refine blankV _ (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    rw [hv]
    simp [wordsN]
    omega
  exact {
    hvert := fun i => (SeedIdx.seedCopy_vertex P e i).1
    hU := hU
    hlen := hlen
    hlabs := le_of_eq hlen.symm
    hRW := le_rfl
    hLW := le_rfl
    hcap6 := hc.cap6
    hO6 := hc.cO6
    hcapT := hc.capT
    hout := by rw [kept 1 (by decide)]; exact hin.s1
    houth := by rw [heads]; exact hin.h1
    hrec := (blank 3 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    hrec0 := zh 3 (by decide) (by decide) (by decide) (by decide)
    hmod := w91
    hmsc := hmsc
    hmh := hmh
    htau := htau
    htauR := htauR
    htauR4 := by rw [show RgT 4 = (223 : Fin LNR) from Fin.ext rfl]; exact v223
    hin := hports
    hh := hh
    hsc := fun k => by
      rw [hfr _ (nmem_words W.x _ (by rw [sT_val]; simp [wordsN]; omega))]
      exact (hin.blankT k).1
    hsh := fun k => by rw [heads]; exact (hin.blankT k).2
    hC5 := hC5
    hC51 := blank 80 (by decide) (by decide) (by decide) (by decide) (by decide)
    hC5r := hC5r
    hcell := by rw [hcl]; exact hin.cell
    hF0 := hlow _ (by decide) (by decide)
    hF1 := by rw [show FR 1 = (231 : Fin LNR) from Fin.ext rfl]; exact v231
    hF2 := by rw [show FR 2 = (232 : Fin LNR) from Fin.ext rfl]; exact v232
    hF3 := by rw [show FR 3 = (233 : Fin LNR) from Fin.ext rfl]; exact v233
    hF4 := by rw [show FR 4 = (234 : Fin LNR) from Fin.ext rfl]; exact v234
    hFz := by
      intro i h5 h12
      fin_cases i
      all_goals first | (exfalso; revert h5 h12; decide) | exact hlow _ (by decide) (by decide)
    hF13 := by rw [show FR 13 = (243 : Fin LNR) from Fin.ext rfl]; exact v243
    hF14 := by rw [show FR 14 = (244 : Fin LNR) from Fin.ext rfl, v244, filtDeg_filterTable]
    hF15 := by rw [show FR 15 = (245 : Fin LNR) from Fin.ext rfl, v245]; rfl
    hF16 := by
      rw [show FR 16 = (246 : Fin LNR) from Fin.ext rfl, v246, cap37_filterTable]
      unfold majorityThreshold
      ring
    hF17 := by
      rw [show FR 17 = (247 : Fin LNR) from Fin.ext rfl, v247, tableWord_length]
      ring
    hF18 := hlow _ (by decide) (by decide)
    hF19 := hlow _ (by decide) (by decide)
    hM := le_rfl
    cA := cA
    cB := cB
    cC := cC
    cD := cD
    crw := crw
    hscr := hscr }

end NearCubicWires.WireExponent3_5.UnionMachine.FsReady
