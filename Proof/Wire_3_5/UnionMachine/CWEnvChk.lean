import Proof.Wire_3_5.UnionMachine.CWWords

/-! # C6 front, U5, the code writers: the envelope checks of a named carrier

Every call's named carriers must lie within "the fixed description envelope": at most `(n+1)^deg` atoms, each with
at most `(n+1)^deg` description bits (`Stars.Carrier.WithinEnvelope`, P3:3083-3094). A gate's description bits are
`intBitLength θ + Σ intBitLength wᵢ` (`encodingBits`), and base's gate field stage writes the weights as the raw words
`intWord wᵢ = sign :: 1^Lᵢ 0 payload` and the threshold's magnitude as `natWord |θ| = 1^L 0 payload`. These word
programs (streams only) count those prefixes against a ruler `1^L`:
* **`parseNat_spec`** / **`parseInt_spec`**: move past one raw `natWord` / `intWord`, advancing the pointer `E` by its
  bit length; **`wLoop_spec`**: every weight;
* **`envChkW_spec`**: the flag `[b]` becomes `[b && decide (P ≤ L)]`, `P` the gate's total bit length;
* **`cntChkW_spec`**: the flag `[decide (N ≤ L)]` for a count word `false :: 1^N`;
* **`outW_spec`**: the flag framed on the output, `frame [b]`;
* their Steps (`envChkStage`, `cntChkStage`, `outStage`), heads rewound.

Paper quantity of the main type: the envelope bit of a named carrier's gate (P3:3083-3094). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWEnvChk
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

section Loops
variable {ns nr : ℕ} (cap : ℕ)

/-! ## A raw word's prefix, counted -/

/-- One prefix cell: one cell forward on `S` and on the pointer `E`, one counter cell marked. -/
def pBody (S R E : Fin (ns + 1)) : WM ns nr := .seq (.fwd S) (.seq (.fwd E) (.seq (.wr R true) (.fwd R)))

theorem pLoop_spec (S R E : Fin (ns + 1)) (hSR : S ≠ R) (hSE : S ≠ E) (hRE : R ≠ E) (p L M : ℕ) :
    ∀ (d k : ℕ) (σ : WState ns nr), k + d = L →
      (∀ j < L, readTapeBit (σ.st S) (p + j) = true) → readTapeBit (σ.st S) (p + L) = false →
      σ.sh S = p + k → σ.st R = ruler k M → σ.sh R = k →
      ∃ τ, WExec cap (.whs S (pBody S R E)) σ τ (d * 9 + 1) ∧ τ.st S = σ.st S ∧ τ.sh S = p + L ∧
        τ.st R = ruler L M ∧ τ.sh R = L ∧ τ.st E = σ.st E ∧ τ.sh E = σ.sh E + d ∧
        (∀ j, j ≠ S → j ≠ R → j ≠ E → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, hkd, _, hz, hSh, hR, hRh => by
    have hk : k = L := by omega
    subst hk
    refine ⟨σ, WExec.mono (WExec.whsF (by simpa [wbit, hSh] using hz)) (by omega), rfl, hSh, hR, hRh, rfl,
      by simp, fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | d + 1, k, σ, hkd, hT, hz, hSh, hR, hRh => by
    have hRS : R ≠ S := fun e => hSR e.symm
    have hES : E ≠ S := fun e => hSE e.symm
    have hER : E ≠ R := fun e => hRE e.symm
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap S σ
    obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap E σ1
    have R2 := (o1 R hRS).trans' (o2 R hRE)
    have E1 := o1 E hES
    have S2 := o2 S hSE
    have s3 := WExec.wr (cap := cap) R true σ2
    set σ3 := σ2.sets R (writeTapeBit (σ2.st R) (σ2.sh R) true) with hσ3
    obtain ⟨σ4, s4, a4, a4h, o4, v4, c4⟩ := fwd_facts cap R σ3
    have eR3 : σ3.st R = ruler (k + 1) M := by
      simp only [hσ3, WState.sets_st, Function.update_self]; rw [R2.1, R2.2, hR, hRh, ruler_write_true]
    have S4 := o4 S hSR
    have E4 := o4 E hER
    obtain ⟨τ, s5, eS, eSh, eR, eRh, eE, eEh, oth, v5, c5⟩ := pLoop_spec S R E hSR hSE hRE p L M d (k + 1) σ4
      (by omega)
      (by rw [S4.1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne hSR, S2.1, a1]; exact hT)
      (by rw [S4.1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne hSR, S2.1, a1]; exact hz)
      (by rw [S4.2]; simp only [hσ3, WState.sets_sh]; rw [S2.2, a1h, hSh]; ring)
      (by rw [a4]; exact eR3)
      (by rw [a4h]; simp only [hσ3, WState.sets_sh]; rw [R2.2, hRh])
    have hw : wbit σ S = true := by
      simp only [wbit, hSh]; exact hT k (by omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) s5) (by ring_nf; omega),
      ?_, eSh, eR, eRh, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eS, S4.1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne hSR, S2.1, a1]
    · rw [eE, E4.1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne hER, a2, E1.1]
    · rw [eEh, E4.2]; simp only [hσ3, WState.sets_sh]; rw [a2h, E1.2]; ring
    · intro j h1 h2 h3
      have o3 : Same σ2 σ3 j := ⟨by simp [hσ3, Function.update_of_ne h2], rfl⟩
      exact ((((o1 j h1).trans' (o2 j h3)).trans' o3).trans' (o4 j h2)).trans' (oth j h1 h2 h3)
    · rw [v5, v4]; simp only [hσ3, WState.sets_val]; rw [v2, v1]
    · rw [c5, c4]; simp only [hσ3, WState.sets_cell]; rw [c2, c1]

/-! ## A raw word's payload, skipped along the counter -/

/-- One skipped payload cell: the counter cell erased, one cell forward on `S`. -/
def sBody (S R : Fin (ns + 1)) : WM ns nr := .seq (.wr R false) (.seq (.bwd R) (.fwd S))

theorem sLoop_spec (S R : Fin (ns + 1)) (hSR : S ≠ R) (M : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), k ≤ M → σ.st R = ruler k M → σ.sh R = k - 1 →
      ∃ τ, WExec cap (.whs R (sBody S R)) σ τ (k * 7 + 1) ∧ τ.st S = σ.st S ∧ τ.sh S = σ.sh S + k ∧
        τ.st R = ruler 0 M ∧ τ.sh R = 0 ∧ (∀ j, j ≠ S → j ≠ R → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, σ, _, hR, hRh => by
    have hz : wbit σ R = false := by simp only [wbit, hR, hRh]; exact ruler_read_ge 0 M _ (Nat.zero_le _)
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, by simp, hR, by simpa using hRh,
      fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | k + 1, σ, hkM, hR, hRh => by
    have hRS : R ≠ S := fun e => hSR e.symm
    have hw : wbit σ R = true := by simp only [wbit, hR, hRh]; exact ruler_read_lt _ M _ (by omega)
    have s1 := WExec.wr (cap := cap) R false σ
    set σ1 := σ.sets R (writeTapeBit (σ.st R) (σ.sh R) false) with hσ1
    have e1 : σ1.st R = ruler k M := by
      simp only [hσ1, WState.sets_st, Function.update_self]; rw [hR, hRh]; exact ruler_write_false k M hkM
    have s2 := WExec.bwd (cap := cap) R σ1
    set σ2 := σ1.seth R (σ1.sh R - 1) with hσ2
    obtain ⟨σ3, s3, a3, a3h, o3, v3, c3⟩ := fwd_facts cap S σ2
    have R3 := o3 R hRS
    obtain ⟨τ, s4, eS, eSh, eR, eRh, oth, v4, c4⟩ := sLoop_spec S R hSR M k σ3 (by omega)
      (by rw [R3.1]; simpa [hσ2] using e1)
      (by rw [R3.2]; simp [hσ2, hσ1, hRh])
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) s4) (by ring_nf; omega),
      ?_, ?_, eR, eRh, ?_, ?_, ?_⟩
    · rw [eS, a3]; simp [hσ2, hσ1, Function.update_of_ne hSR]
    · rw [eSh, a3h]; simp [hσ2, hσ1, Function.update_of_ne hSR]; ring
    · intro j h1 h2
      have o12 : Same σ σ2 j := ⟨by simp [hσ2, hσ1, Function.update_of_ne h2], by simp [hσ2, hσ1, Function.update_of_ne h2]⟩
      exact (o12.trans' (o3 j h1)).trans' (oth j h1 h2)
    · rw [v4, v3]; simp [hσ2, hσ1]
    · rw [c4, c3]; simp [hσ2, hσ1]

/-! ## One raw `natWord`, one raw `intWord` -/

theorem raw_one (pre : List Bool) (L : ℕ) (py rest : List Bool) (j : ℕ) (hj : j < L) :
    readTapeBit (pre ++ ((List.replicate L true ++ false :: py) ++ rest)) (pre.length + j) = true := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega), show pre.length + j - pre.length = j by omega, List.append_assoc,
    List.getD_append _ _ _ _ (by simp; omega)]
  simp [hj]

theorem raw_zero (pre : List Bool) (L : ℕ) (py rest : List Bool) :
    readTapeBit (pre ++ ((List.replicate L true ++ false :: py) ++ rest)) (pre.length + L) = false := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega), show pre.length + L - pre.length = L by omega, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- **Move past one raw `natWord`**, the pointer `E` advancing by its bit length; the counter returns to `false`. -/
def parseNat (S R E : Fin (ns + 1)) : WM ns nr :=
  .seq (.whs S (pBody S R E)) (.seq (.fwd S) (.seq (.bwd R) (.whs R (sBody S R))))

theorem parseNat_spec (S R E : Fin (ns + 1)) (hSR : S ≠ R) (hSE : S ≠ E) (hRE : R ≠ E) (x : ℕ)
    (pre rest : List Bool) (r : ℕ) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (natWord x ++ rest)) (hSh : σ.sh S = pre.length) (hR : σ.st R = List.replicate r false)
    (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (parseNat S R E) σ τ (natBitLength x * 16 + 7) ∧ τ.st S = σ.st S ∧
      τ.sh S = pre.length + (natWord x).length ∧ τ.st R = List.replicate (max (natBitLength x) r) false ∧
      τ.sh R = 0 ∧ τ.st E = σ.st E ∧ τ.sh E = σ.sh E + natBitLength x ∧
      (∀ j, j ≠ S → j ≠ R → j ≠ E → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hRS : R ≠ S := fun e => hSR e.symm
  have hES : E ≠ S := fun e => hSE e.symm
  have hER : E ≠ R := fun e => hRE e.symm
  set L := natBitLength x with hL
  have hw : natWord x = List.replicate L true ++ false :: pay x := natWord_pay x
  obtain ⟨σ1, s1, e1, e1h, e1R, e1Rh, e1E, e1Eh, o1, v1, c1⟩ := pLoop_spec cap S R E hSR hSE hRE pre.length L r L 0 σ
    (by omega)
    (fun j hj => by rw [hS, hw]; exact raw_one pre L (pay x) rest j hj)
    (by rw [hS, hw]; exact raw_zero pre L (pay x) rest)
    (by rw [hSh]; omega) (by rw [hR, ruler_zero]) (by rw [hRh])
  obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap S σ1
  have s3 := WExec.bwd (cap := cap) R σ2
  set σ3 := σ2.seth R (σ2.sh R - 1) with hσ3
  have R2 := o2 R hRS
  obtain ⟨τ, s4, e4, e4h, e4R, e4Rh, o4, v4, c4⟩ := sLoop_spec cap S R hSR (max L r) L σ3 (le_max_left _ _)
    (by simp only [hσ3, WState.seth_st]; rw [R2.1, e1R, ruler_max])
    (by simp only [hσ3, WState.seth_sh, Function.update_self]; rw [R2.2, e1Rh])
  have E2 := o2 E hES
  have E4 := o4 E hES hER
  have hlen : (natWord x).length = 2 * L + 1 := natWord_len x
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), ?_, ?_, ?_, e4Rh, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e4]; simp [hσ3, a2, e1]
  · rw [e4h]; simp only [hσ3, WState.seth_sh]; rw [Function.update_of_ne hSR, a2h, e1h, hlen]; omega
  · rw [e4R, ruler_zero]
  · rw [E4.1]; simp only [hσ3, WState.seth_st]; rw [E2.1, e1E]
  · rw [E4.2]; simp only [hσ3, WState.seth_sh]; rw [Function.update_of_ne hER, E2.2, e1Eh]
  · intro j h1 h2 h3
    have o3 : Same σ2 σ3 j := ⟨rfl, by simp [hσ3, Function.update_of_ne h2]⟩
    exact (((o1 j h1 h2 h3).trans' (o2 j h1)).trans' o3).trans' (o4 j h1 h2)
  · rw [v4]; simp [hσ3, v2, v1]
  · rw [c4]; simp [hσ3, c2, c1]

/-- **Move past one raw `intWord`**: its sign, then its magnitude's `natWord`. -/
def parseInt (S R E : Fin (ns + 1)) : WM ns nr := .seq (.fwd S) (parseNat S R E)

theorem parseInt_spec (S R E : Fin (ns + 1)) (hSR : S ≠ R) (hSE : S ≠ E) (hRE : R ≠ E) (z : ℤ)
    (pre rest : List Bool) (r : ℕ) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (intWord z ++ rest)) (hSh : σ.sh S = pre.length) (hR : σ.st R = List.replicate r false)
    (hRh : σ.sh R = 0) :
    ∃ τ r', WExec cap (parseInt S R E) σ τ (natBitLength z.natAbs * 16 + 9) ∧ τ.st S = σ.st S ∧
      τ.sh S = pre.length + (intWord z).length ∧ τ.st R = List.replicate r' false ∧
      τ.sh R = 0 ∧ τ.st E = σ.st E ∧ τ.sh E = σ.sh E + natBitLength z.natAbs ∧
      (∀ j, j ≠ S → j ≠ R → j ≠ E → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hRS : R ≠ S := fun e => hSR e.symm
  have hES : E ≠ S := fun e => hSE e.symm
  obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap S σ
  obtain ⟨τ, s2, e2, e2h, e2R, e2Rh, e2E, e2Eh, o2, v2, c2⟩ := parseNat_spec cap S R E hSR hSE hRE z.natAbs
    (pre ++ [decide (z < 0)]) rest r σ1 (by rw [a1, hS]; unfold intWord; simp)
    (by rw [a1h, hSh]; simp) (by rw [(o1 R hRS).1, hR]) (by rw [(o1 R hRS).2, hRh])
  refine ⟨τ, max (natBitLength z.natAbs) r, WExec.mono (WExec.seq s1 s2) (by omega), by rw [e2, a1], ?_, e2R, e2Rh,
    ?_, ?_, ?_, by rw [v2, v1], by rw [c2, c1]⟩
  · rw [e2h]; unfold intWord; simp; omega
  · rw [e2E, (o1 E hES).1]
  · rw [e2Eh, (o1 E hES).2]
  · intro j h1 h2 h3; exact (o1 j h1).trans' (o2 j h1 h2 h3)

/-- The total bit length of a list of weights. -/
def wbits (ws : List ℤ) : ℕ := (ws.map fun z => natBitLength z.natAbs).sum

/-- **Every weight**: one `intWord` per `1` of the count word `C`. -/
def wLoop (A C R E : Fin (ns + 1)) : WM ns nr := .whs C (.seq (.fwd C) (parseInt A R E))

theorem wLoop_spec (A C R E : Fin (ns + 1)) (hAC : A ≠ C) (hAR : A ≠ R) (hAE : A ≠ E) (hCR : C ≠ R) (hCE : C ≠ E)
    (hRE : R ≠ E) :
    ∀ (ws : List ℤ) (pre rest preC : List Bool) (r : ℕ) (σ : WState ns nr),
      σ.st A = pre ++ (ws.flatMap intWord ++ rest) → σ.sh A = pre.length →
      σ.st C = preC ++ List.replicate ws.length true → σ.sh C = preC.length →
      σ.st R = List.replicate r false → σ.sh R = 0 →
      ∃ τ r', WExec cap (wLoop A C R E) σ τ (wbits ws * 16 + 13 * ws.length + 1) ∧ τ.st A = σ.st A ∧
        τ.st C = σ.st C ∧ τ.st R = List.replicate r' false ∧ τ.sh R = 0 ∧ τ.st E = σ.st E ∧
        τ.sh E = σ.sh E + wbits ws ∧ (∀ j, j ≠ A → j ≠ C → j ≠ R → j ≠ E → Same σ τ j) ∧ τ.val = σ.val ∧
        τ.cell = σ.cell
  | [], pre, rest, preC, r, σ, _, _, hC, hCh, hR, hRh => by
    have hz : wbit σ C = false := by
      unfold wbit; rw [hC, hCh]; unfold readTapeBit; simp
    exact ⟨σ, r, WExec.mono (WExec.whsF hz) (by simp [wbits]), rfl, rfl, hR, hRh, rfl, by simp [wbits],
      fun _ _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | z :: ws, pre, rest, preC, r, σ, hA, hAh, hC, hCh, hR, hRh => by
    have hCA : C ≠ A := fun e => hAC e.symm
    have hRC : R ≠ C := fun e => hCR e.symm
    have hEC : E ≠ C := fun e => hCE e.symm
    have hr : wbit σ C = true := by
      unfold wbit; rw [hC, hCh]; unfold readTapeBit; simp [List.replicate_succ]
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap C σ
    have A1 := o1 A hAC
    obtain ⟨σ2, r2, s2, e2, e2h, e2R, e2Rh, e2E, e2Eh, o2, v2, c2⟩ := parseInt_spec cap A R E hAR hAE hRE z pre
      (ws.flatMap intWord ++ rest) r σ1 (by rw [A1.1, hA]; simp [List.append_assoc]) (by rw [A1.2, hAh])
      (by rw [(o1 R hRC).1, hR]) (by rw [(o1 R hRC).2, hRh])
    have C2 := o2 C hCA hCR hCE
    obtain ⟨τ, r', s3, e3, e3C, e3R, e3Rh, e3E, e3Eh, o3, v3, c3⟩ := wLoop_spec A C R E hAC hAR hAE hCR hCE hRE ws
      (pre ++ intWord z) rest (preC ++ [true]) r2 σ2 (by rw [e2, A1.1, hA]; simp [List.append_assoc])
      (by rw [e2h]; simp) (by rw [C2.1, a1, hC]; simp [List.replicate_succ])
      (by rw [C2.2, a1h, hCh]; simp) e2R e2Rh
    have hwb : wbits (z :: ws) = natBitLength z.natAbs + wbits ws := by simp [wbits]
    refine ⟨τ, r', WExec.mono (WExec.whsT hr (WExec.seq s1 s2) s3) (by rw [hwb]; simp; ring_nf; omega), ?_, ?_, e3R,
      e3Rh, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e3, e2, A1.1]
    · rw [e3C, C2.1, a1]
    · rw [e3E, e2E, (o1 E hEC).1]
    · rw [e3Eh, e2Eh, (o1 E hEC).2, hwb]; ring
    · intro j h1 h2 h3 h4
      exact ((o1 j h2).trans' (o2 j h1 h3 h4)).trans' (o3 j h1 h2 h3 h4)
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

end Loops

/-! ## The gate check -/

/-- The gate check before its test: the weights, then the threshold, then one cell back on the ruler. -/
def envPre : WM 5 0 := .seq (.fwd 2) (.seq (wLoop 0 2 5 3) (.seq (parseNat 1 5 3) (.bwd 3)))

/-- **One gate's envelope check** (streams `0` the weights' `intWord`s, `1` the threshold's `natWord`, `2` the weight
count `false :: 1^k`, `3` the ruler `1^L`, `4` the flag `[b]`, `5` a scratch counter): the pointer on the ruler moves
by the gate's total bit length `P`; the flag is cleared unless `P ≤ L`. -/
def envChkW : WM 5 0 := .seq envPre (.ifs 3 .skip (.wr 4 false))

def envChkCost (ws : List ℤ) (t : ℕ) : ℕ := wbits ws * 16 + 13 * ws.length + natBitLength t * 16 + 20

theorem envPre_spec (cap : ℕ) (ws : List ℤ) (t : ℕ) (b : Bool) (σ : WState 5 0) (h0 : ∀ j, σ.sh j = 0)
    (hA : σ.st 0 = ws.flatMap intWord) (hT : σ.st 1 = natWord t) (hC : σ.st 2 = CompareMachine.word ws.length)
    (hF : σ.st 4 = [b]) (hR : σ.st 5 = []) :
    ∃ σ4, WExec cap envPre σ σ4 (wbits ws * 16 + 13 * ws.length + natBitLength t * 16 + 13) ∧
      σ4.st 0 = σ.st 0 ∧ σ4.st 1 = σ.st 1 ∧ σ4.st 2 = σ.st 2 ∧ σ4.st 3 = σ.st 3 ∧ σ4.st 4 = [b] ∧ σ4.sh 4 = 0 ∧
      σ4.sh 3 = wbits ws + natBitLength t - 1 ∧ σ4.cell = σ.cell := by
  obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap (2 : Fin 6) σ
  obtain ⟨σ2, r2, s2, e2A, e2C, e2R, e2Rh, e2E, e2Eh, o2, v2, c2⟩ := wLoop_spec cap (0 : Fin 6) 2 5 3 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ws [] [] [false] 0 σ1
    (by rw [(o1 0 (by decide)).1, hA]; simp) (by rw [(o1 0 (by decide)).2, h0]; rfl)
    (by rw [a1, hC]; rfl) (by rw [a1h, h0]; rfl)
    (by rw [(o1 5 (by decide)).1, hR]; rfl) (by rw [(o1 5 (by decide)).2, h0])
  have T2 := (o1 1 (by decide)).trans' (o2 1 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨σ3, s3, e3T, -, -, -, e3E, e3Eh, o3, v3, c3⟩ := parseNat_spec cap (1 : Fin 6) 5 3 (by decide)
    (by decide) (by decide) t [] [] r2 σ2 (by rw [T2.1, hT]; simp) (by rw [T2.2, h0]; rfl) e2R e2Rh
  have s4 := WExec.bwd (cap := cap) (3 : Fin 6) σ3
  have F3 := (o2 4 (by decide) (by decide) (by decide) (by decide)).trans' (o3 4 (by decide) (by decide) (by decide))
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]; rw [(o3 0 (by decide) (by decide) (by decide)).1, e2A, (o1 0 (by decide)).1]
  · simp only [WState.seth_st]; rw [e3T, T2.1]
  · simp only [WState.seth_st]; rw [(o3 2 (by decide) (by decide) (by decide)).1, e2C, a1]
  · simp only [WState.seth_st]; rw [e3E, e2E, (o1 3 (by decide)).1]
  · simp only [WState.seth_st]; rw [F3.1, (o1 4 (by decide)).1, hF]
  · simp only [WState.seth_sh]; rw [Function.update_of_ne (by decide), F3.2, (o1 4 (by decide)).2, h0]
  · simp only [WState.seth_sh, Function.update_self]; rw [e3Eh, e2Eh, (o1 3 (by decide)).2, h0]; simp
  · simp only [WState.seth_cell]; rw [c3, c2, c1]

theorem envChkW_spec (cap : ℕ) (ws : List ℤ) (t L : ℕ) (b : Bool) (σ : WState 5 0) (h0 : ∀ j, σ.sh j = 0)
    (hA : σ.st 0 = ws.flatMap intWord) (hT : σ.st 1 = natWord t) (hC : σ.st 2 = CompareMachine.word ws.length)
    (hE : σ.st 3 = List.replicate L true) (hF : σ.st 4 = [b]) (hR : σ.st 5 = []) :
    ∃ τ, WExec cap envChkW σ τ (envChkCost ws t) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = σ.st 1 ∧ τ.st 2 = σ.st 2 ∧
      τ.st 3 = σ.st 3 ∧ τ.st 4 = [b && decide (wbits ws + natBitLength t ≤ L)] ∧ τ.cell = σ.cell := by
  obtain ⟨σ4, s4, e0, e1, e2, e3, e4, e4h, e3h, ec⟩ := envPre_spec cap ws t b σ h0 hA hT hC hF hR
  have hpos : 1 ≤ natBitLength t := natBitLength_pos t
  have hbit : wbit σ4 3 = decide (wbits ws + natBitLength t ≤ L) := by
    unfold wbit; rw [e3, hE, e3h]; unfold readTapeBit
    by_cases h : wbits ws + natBitLength t ≤ L
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp [h]
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [h]
  cases hok : decide (wbits ws + natBitLength t ≤ L)
  · have s5 : WExec cap (.ifs 3 .skip (.wr 4 false)) σ4 (σ4.sets 4 (writeTapeBit (σ4.st 4) (σ4.sh 4) false)) 2 :=
      WExec.ifsF (by rw [hbit, hok]) (WExec.wr 4 false σ4)
    refine ⟨_, WExec.mono (WExec.seq s4 s5) (by unfold envChkCost; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), e0]
    · simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), e1]
    · simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), e2]
    · simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), e3]
    · simp only [WState.sets_st, Function.update_self]; rw [e4, e4h]; simp [writeTapeBit]
    · simp only [WState.sets_cell]; exact ec
  · have s5 : WExec cap (.ifs 3 .skip (.wr 4 false)) σ4 σ4 1 := WExec.ifsT (by rw [hbit, hok]) (WExec.skip σ4)
    exact ⟨σ4, WExec.mono (WExec.seq s4 s5) (by unfold envChkCost; omega), e0, e1, e2, e3, by rw [e4]; simp, ec⟩

/-! ## The count check -/

theorem cLoop_spec {ns nr : ℕ} (cap : ℕ) (C E : Fin (ns + 1)) (hCE : C ≠ E) :
    ∀ (N : ℕ) (pre : List Bool) (σ : WState ns nr), σ.st C = pre ++ List.replicate N true → σ.sh C = pre.length →
      WExec cap (.whs C (.seq (.fwd C) (.fwd E))) σ ((σ.seth C (pre.length + N)).seth E (σ.sh E + N)) (N * 5 + 1)
  | 0, pre, σ, hC, hCh => by
    have hz : wbit σ C = false := by unfold wbit; rw [hC, hCh]; unfold readTapeBit; simp
    have e : (σ.seth C (pre.length + 0)).seth E (σ.sh E + 0) = σ := by
      rw [Nat.add_zero, Nat.add_zero, ← hCh, wseth_same, wseth_same]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by omega)
  | N + 1, pre, σ, hC, hCh => by
    have hr : wbit σ C = true := by unfold wbit; rw [hC, hCh]; unfold readTapeBit; simp [List.replicate_succ]
    have s1 := WExec.fwd (cap := cap) C σ
    have s2 := WExec.fwd (cap := cap) E (σ.seth C (σ.sh C + 1))
    have ih := cLoop_spec cap C E hCE N (pre ++ [true]) ((σ.seth C (σ.sh C + 1)).seth E
      ((σ.seth C (σ.sh C + 1)).sh E + 1)) (by simp [hC, List.replicate_succ]) (by simp [Function.update_of_ne hCE, hCh])
    have e : ((((σ.seth C (σ.sh C + 1)).seth E ((σ.seth C (σ.sh C + 1)).sh E + 1)).seth C
        ((pre ++ [true]).length + N)).seth E
        (((σ.seth C (σ.sh C + 1)).seth E ((σ.seth C (σ.sh C + 1)).sh E + 1)).sh E + N)) =
        (σ.seth C (pre.length + (N + 1))).seth E (σ.sh E + (N + 1)) := by
      apply WState.eq
      · funext j
        by_cases hjE : j = E
        · subst hjE; simp [Function.update_of_ne hCE.symm]; omega
        · by_cases hjC : j = C
          · subst hjC; simp [hjE]; omega
          · simp [hjE, hjC]
      · rfl
      · rfl
      · rfl
    rw [e] at ih
    exact WExec.mono (WExec.whsT hr (WExec.seq s1 s2) ih) (by ring_nf; omega)

/-- The count check before its test. -/
def cntPre : WM 2 0 := .seq (.fwd 0) (.seq (.whs 0 (.seq (.fwd 0) (.fwd 1))) (.bwd 1))

/-- **The count check** (streams `0` the count word `false :: 1^N`, `1` the ruler `1^L`, `2` the flag): the flag
`[decide (N ≤ L)]`. -/
def cntChkW : WM 2 0 := .seq cntPre (.ifs 1 (.wr 2 true) (.wr 2 false))

def cntChkCost (N : ℕ) : ℕ := N * 5 + 8

theorem cntChkW_spec (cap N L : ℕ) (hL : 1 ≤ L) (σ : WState 2 0) (h0 : ∀ j, σ.sh j = 0)
    (hC : σ.st 0 = CompareMachine.word N) (hE : σ.st 1 = List.replicate L true) (hF : σ.st 2 = []) :
    ∃ τ, WExec cap cntChkW σ τ (cntChkCost N) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = σ.st 1 ∧
      τ.st 2 = [decide (N ≤ L)] ∧ τ.cell = σ.cell := by
  have s1 := WExec.fwd (cap := cap) (0 : Fin 3) σ
  set σ1 := σ.seth 0 (σ.sh 0 + 1) with hσ1
  have s2 := cLoop_spec cap (0 : Fin 3) 1 (by decide) N [false] σ1 (by simp [hσ1, hC, CompareMachine.word])
    (by simp [hσ1, h0])
  set σ2 := (σ1.seth 0 ([false].length + N)).seth 1 (σ1.sh 1 + N) with hσ2
  have s3 := WExec.bwd (cap := cap) (1 : Fin 3) σ2
  set σ3 := σ2.seth 1 (σ2.sh 1 - 1) with hσ3
  have h3 : σ3.st = σ.st := by simp [hσ3, hσ2, hσ1]
  have h3h : σ3.sh 1 = N - 1 := by simp [hσ3, hσ2, hσ1, h0]
  have h3F : σ3.sh 2 = 0 := by simp [hσ3, hσ2, hσ1, h0]
  have hbit : wbit σ3 1 = decide (N ≤ L) := by
    unfold wbit; rw [h3, hE, h3h]; unfold readTapeBit
    by_cases h : N ≤ L
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp [h]
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [h]
  have s123 : WExec cap cntPre σ σ3 (1 + 1 + ((N * 5 + 1) + 1 + 1)) := WExec.seq s1 (WExec.seq s2 s3)
  have s4 : WExec cap (.ifs 1 (.wr 2 true) (.wr 2 false)) σ3
      (σ3.sets 2 (writeTapeBit (σ3.st 2) (σ3.sh 2) (decide (N ≤ L)))) 2 := by
    cases hb : decide (N ≤ L)
    · exact WExec.ifsF (by rw [hbit, hb]) (WExec.wr 2 false σ3)
    · exact WExec.ifsT (by rw [hbit, hb]) (WExec.wr 2 true σ3)
  refine ⟨_, WExec.mono (WExec.seq s123 s4) (by unfold cntChkCost; omega), ?_, ?_, ?_, ?_⟩
  · simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), h3]
  · simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), h3]
  · simp only [WState.sets_st, Function.update_self]; rw [h3, hF, h3F]; rfl
  · simp [hσ3, hσ2, hσ1]

/-! ## The output -/

/-- **The output** (streams `0` the flag `[b]`, `1` the output): `frame [b] = [true, b, false]`. -/
def outW : WM 1 0 := .seq (emitW 1 true) (.seq (.ifs 0 (emitW 1 true) (emitW 1 false)) (emitW 1 false))

theorem outW_spec (cap : ℕ) (b : Bool) (σ : WState 1 0) (h0 : ∀ j, σ.sh j = 0) (hF : σ.st 0 = [b])
    (hO : σ.st 1 = []) :
    ∃ τ, WExec cap outW σ τ 12 ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = [true, b, false] ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (1 : Fin 2) true σ (by rw [h0, hO]; rfl)
  have F1 := o1 0 (by decide)
  obtain ⟨σ2, s2', e2, e2h, o2, v2, c2⟩ := emit_facts cap (1 : Fin 2) b σ1 e1h
  have hbit : wbit σ1 0 = b := by unfold wbit; rw [F1.1, F1.2, hF, h0]; rfl
  have s2 : WExec cap (.ifs 0 (emitW 1 true) (emitW 1 false)) σ1 σ2 4 := by
    cases hb : b
    · rw [hb] at s2' hbit; exact WExec.ifsF hbit s2'
    · rw [hb] at s2' hbit; exact WExec.ifsT hbit s2'
  obtain ⟨τ, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap (1 : Fin 2) false σ2 e2h
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ?_, ?_, ?_⟩
  · rw [(o3 0 (by decide)).1, (o2 0 (by decide)).1, F1.1]
  · rw [e3, e2, e1, hO]; rfl
  · rw [c3, c2, c1]

/-! ## The Steps -/

def σEnv (A T C E F : List Bool) : WState 5 0 := ⟨fun _ => 0, ![A, T, C, E, F, []], fun r => r.elim0, false⟩

/-- The gate check's entry bank: the weights, the cell, the threshold, the count, the ruler, the flag, the scratch
counter, the log. -/
def envIn (A T C E F : List Bool) : Fin 8 → List Bool :=
  Fin.addCases (m := 5 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σEnv A T C E F)).A (fun _ => [])

theorem envIn_val (A T C E F : List Bool) (j : Fin 8) :
    envIn A T C E F j = if j.val = 0 then A else if j.val = 1 then [false] else if j.val = 2 then T else
      if j.val = 3 then C else if j.val = 4 then E else if j.val = 5 then F else [] := by
  fin_cases j <;> rfl

/-- **The gate check as a Step.** -/
theorem envChkStage (ws : List ℤ) (t L : ℕ) (b : Bool) : ∃ o : Fin 8 → List Bool,
    Step (Rewind.machine envChkW.toProg.compile) (2 * envChkCost ws t + 2) (fun _ => 0)
      (envIn (ws.flatMap intWord) (natWord t) (CompareMachine.word ws.length) (List.replicate L true) [b])
      (fun _ => 0) o ∧
    o 0 = ws.flatMap intWord ∧ o 1 = [false] ∧ o 2 = natWord t ∧ o 3 = CompareMachine.word ws.length ∧
    o 4 = List.replicate L true ∧ o 5 = [b && decide (wbits ws + natBitLength t ≤ L)] := by
  set σ := σEnv (ws.flatMap intWord) (natWord t) (CompareMachine.word ws.length) (List.replicate L true) [b] with hσ
  obtain ⟨τ, hw, e0, e1, e2, e3, e4, ec⟩ := envChkW_spec 0 ws t L b σ (fun _ => rfl) rfl rfl rfl rfl rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 envChkW σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 8) = Fin.castAdd 1 (0 : Fin 7) from rfl, ho]; exact e0
  · rw [show (1 : Fin 8) = Fin.castAdd 1 (1 : Fin 7) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 8) = Fin.castAdd 1 (2 : Fin 7) from rfl, ho]; exact e1
  · rw [show (3 : Fin 8) = Fin.castAdd 1 (3 : Fin 7) from rfl, ho]; exact e2
  · rw [show (4 : Fin 8) = Fin.castAdd 1 (4 : Fin 7) from rfl, ho]; exact e3
  · rw [show (5 : Fin 8) = Fin.castAdd 1 (5 : Fin 7) from rfl, ho]; exact e4

def σCnt (C E : List Bool) : WState 2 0 := ⟨fun _ => 0, ![C, E, []], fun r => r.elim0, false⟩

/-- The count check's entry bank: the count word, the cell, the ruler, the flag, the log. -/
def cntIn (C E : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (m := 2 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σCnt C E)).A (fun _ => [])

theorem cntIn_val (C E : List Bool) (j : Fin 5) :
    cntIn C E j = if j.val = 0 then C else if j.val = 1 then [false] else if j.val = 2 then E else [] := by
  fin_cases j <;> rfl

/-- **The count check as a Step.** -/
theorem cntChkStage (N L : ℕ) (hL : 1 ≤ L) : ∃ o : Fin 5 → List Bool,
    Step (Rewind.machine cntChkW.toProg.compile) (2 * cntChkCost N + 2) (fun _ => 0)
      (cntIn (CompareMachine.word N) (List.replicate L true)) (fun _ => 0) o ∧
    o 0 = CompareMachine.word N ∧ o 1 = [false] ∧ o 2 = List.replicate L true ∧ o 3 = [decide (N ≤ L)] := by
  set σ := σCnt (CompareMachine.word N) (List.replicate L true) with hσ
  obtain ⟨τ, hw, e0, e1, e2, ec⟩ := cntChkW_spec 0 N L hL σ (fun _ => rfl) rfl rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 cntChkW σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 5) = Fin.castAdd 1 (0 : Fin 4) from rfl, ho]; exact e0
  · rw [show (1 : Fin 5) = Fin.castAdd 1 (1 : Fin 4) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 5) = Fin.castAdd 1 (2 : Fin 4) from rfl, ho]; exact e1
  · rw [show (3 : Fin 5) = Fin.castAdd 1 (3 : Fin 4) from rfl, ho]; exact e2

def σOut (F : List Bool) : WState 1 0 := ⟨fun _ => 0, ![F, []], fun r => r.elim0, false⟩

/-- The output's entry bank: the flag, the cell, the output, the log. -/
def outIn (F : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (m := 1 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σOut F)).A (fun _ => [])

theorem outIn_val (F : List Bool) (j : Fin 4) :
    outIn F j = if j.val = 0 then F else if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

/-- **The output as a Step.** -/
theorem outStage (b : Bool) : ∃ o : Fin 4 → List Bool,
    Step (Rewind.machine outW.toProg.compile) (2 * 12 + 2) (fun _ => 0) (outIn [b]) (fun _ => 0) o ∧
    o 0 = [b] ∧ o 1 = [false] ∧ o 2 = [true, b, false] := by
  set σ := σOut [b] with hσ
  obtain ⟨τ, hw, e0, e1, ec⟩ := outW_spec 0 b σ (fun _ => rfl) rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 outW σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 1 (0 : Fin 3) from rfl, ho]; exact e0
  · rw [show (1 : Fin 4) = Fin.castAdd 1 (1 : Fin 3) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 4) = Fin.castAdd 1 (2 : Fin 3) from rfl, ho]; exact e1

end NearCubicWires.WireExponent3_5.UnionMachine.CWEnvChk
