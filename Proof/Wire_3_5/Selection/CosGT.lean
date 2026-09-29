import Proof.Wire_3_5.Selection.CosOut

/-! # C1.5 parse: the gate table from the request word (P3:1326-1328)

Paper: "polynomially many bottom gates, each gate given by a polynomial-bit integer threshold description"
(P3:1326-1328). The request word `selWord R` (C6's `UnionMachine.Plan.selWord`) carries the gates as native
`intWord`s (sign, `1^L 0`, `L` bits), weights then threshold, gate after gate; it arrives framed on the input stream.
The coset loop reads each gate from the gate table `gateTable W R` (`Cos.gateTable`: each number's sign cell and framed
width-`W` magnitude, C1.4's `wRec`). **`convRec`** converts one framed `intWord z` into `wRec W z` (the sign cell, then
`convNatW` along the ruler `false :: 1^W`); **`recL`** converts `K` of them. `gateTable_eq`: the table is
`(gInts R).flatMap (wRec W)` for the request's numbers `gInts R`, and `gates_word_eq`: the request's gate section is
`(gInts R).flatMap intWord`. Main declarations: `TMv`, `gInts`, `convRec`, **`convRec_spec`**, `recL`,
**`recL_spec`**, `gateTable_eq`, `gates_word_eq`. Paper quantity: the gates' integer threshold descriptions on the
machine's table. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.PrimT (Mv emitW convNatW convNatW_spec fwdI_mv cpyOut cpyNxt cmap_cpy
  frameP_intWord rd_bit)
open NearCubicWires.RepairRepresentation (natWord intWord natListWord)

variable {ns nr : ℕ}

/-! ## A table builder's move -/

/-- `τ` is `σ` with the input head at `pI`, `w` appended to `O` (its head at the new end), and nothing else changed
except the registers in `Rg`. -/
structure TMv (I O : Fin (ns + 1)) (Rg : Fin nr → Prop) (σ τ : WState ns nr) (pI : ℕ) (w : List Bool) : Prop where
  sI : τ.st I = σ.st I
  hI : τ.sh I = pI
  sO : τ.st O = σ.st O ++ w
  hO : τ.sh O = (τ.st O).length
  fr : WFrame (fun i => i = I ∨ i = O) Rg σ τ

theorem TMv.trans {I O : Fin (ns + 1)} {Rg : Fin nr → Prop} {σ τ ρ : WState ns nr} {p p' : ℕ} {w w' : List Bool}
    (h1 : TMv I O Rg σ τ p w) (h2 : TMv I O Rg τ ρ p' w') : TMv I O Rg σ ρ p' (w ++ w') :=
  ⟨h2.sI.trans h1.sI, h2.hI, by rw [h2.sO, h1.sO, List.append_assoc], h2.hO, h1.fr.trans h2.fr⟩

theorem TMv.mono {I O : Fin (ns + 1)} {Rg Rg' : Fin nr → Prop} {σ τ : WState ns nr} {p : ℕ} {w : List Bool}
    (h : TMv I O Rg σ τ p w) (hR : ∀ r, Rg r → Rg' r) : TMv I O Rg' σ τ p w :=
  ⟨h.sI, h.hI, h.sO, h.hO, h.fr.mono (fun _ hi => hi) hR⟩

theorem TMv.refl (I O : Fin (ns + 1)) (Rg : Fin nr → Prop) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) :
    TMv I O Rg σ σ (σ.sh I) [] :=
  ⟨rfl, rfl, by simp, hO, WFrame.refl _ _ σ⟩

theorem TMv.setv {I O : Fin (ns + 1)} {Rg : Fin nr → Prop} {σ τ : WState ns nr} {p : ℕ} {w : List Bool}
    (h : TMv I O Rg σ τ p w) (r : Fin nr) (hr : Rg r) (x : ℕ) : TMv I O Rg σ (τ.setv r x) p w :=
  ⟨h.sI, h.hI, h.sO, h.hO, h.fr.trans (frame_setv _ _ τ r x hr)⟩

theorem TMv.of_setv {I O : Fin (ns + 1)} {Rg : Fin nr → Prop} {σ τ : WState ns nr} {p : ℕ} {w : List Bool}
    (r : Fin nr) (hr : Rg r) (x : ℕ) (h : TMv I O Rg (σ.setv r x) τ p w) : TMv I O Rg σ τ p w :=
  ⟨h.sI, h.hI, h.sO, h.hO, (frame_setv _ _ σ r x hr).trans h.fr⟩

theorem TMv.of_mv {I O R : Fin (ns + 1)} {c f : Fin nr} {σ τ : WState ns nr} {pI cv fv : ℕ} {w : List Bool}
    (h : Mv I O R c f σ τ pI w 0 cv fv) (hR0 : σ.sh R = 0) : TMv I O (fun r => r = c ∨ r = f) σ τ pI w := by
  refine ⟨h.sI, h.hI, h.sO, h.hO, ⟨fun i hi => ?_, h.fr.2.1, h.fr.2.2⟩⟩
  by_cases hiR : i = R
  · subst hiR; exact ⟨h.sR, by rw [h.hR, hR0]⟩
  · exact h.fr.1 i (fun h' => by rcases h' with e | e | e <;> [exact hi (Or.inl e); exact hi (Or.inr e); exact hiR e])

/-! ## One gate number -/

/-- **One number's record** from its framed `intWord`: the sign cell, then the framed width-`h` magnitude. -/
def convRec (I O R : Fin (ns + 1)) (c f : Fin nr) : WM ns nr :=
  .seq (.fwd I) (.seq (.ifs I (emitW O true) (emitW O false)) (.seq (.fwd I) (convNatW I O R c f cpyOut cpyNxt)))

/-- The conversion's cost. -/
def convRecCost (z : ℤ) (h : ℕ) : ℕ :=
  1 + 1 + (3 + 1 + 1 + (1 + 1 + (PrimT.countCost (natBitLength z.natAbs) + 1 + PrimT.wordCost h)))

section Conv
variable (cap : ℕ) (I O R : Fin (ns + 1)) (c f : Fin nr) (hIO : I ≠ O) (hIR : I ≠ R) (hOR : O ≠ R) (hcf : c ≠ f)
include hIO hIR hOR hcf

theorem convRec_spec (hcap : 1 ≤ cap) (pre rest : List Bool) (z : ℤ) (h : ℕ) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP (intWord z) ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = 0)
    (hf : σ.val f = 0) (hkh : natBitLength z.natAbs ≤ h) (hkc : natBitLength z.natAbs ≤ cap)
    (hO : σ.sh O = (σ.st O).length) (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (convRec I O R c f) σ τ (convRecCost z h) ∧
      TMv I O (fun r => r = c ∨ r = f) σ τ (pre.length + 2 * (intWord z).length) (wRec h z) ∧
      τ.val c = 0 ∧ τ.val f = 0 := by
  have hOI : O ≠ I := fun e => hIO e.symm
  have hRI : R ≠ I := fun e => hIR e.symm
  have hRO : R ≠ O := fun e => hOR e.symm
  obtain ⟨s1, m1⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ hO
  set σ1 := σ.seth I (σ.sh I + 1) with hσ1
  have hsign : wbit σ1 I = decide (z < 0) := by
    simp only [wbit, m1.sI, m1.hI, hI, hIh]
    have := rd_bit pre (intWord z) rest 0 (by simp [intWord])
    simpa [intWord] using this
  have e2 := emitW_app cap O (decide (z < 0)) σ1 (by simp [hσ1, Function.update_of_ne hOI, hO])
  have s2 : WExec cap (.ifs I (emitW O true) (emitW O false)) σ1 (appS σ1 O [decide (z < 0)]) (3 + 1) := by
    by_cases hz : z < 0
    · have := emitW_app cap O true σ1 (by simp [hσ1, Function.update_of_ne hOI, hO])
      exact WExec.ifsT (by rw [hsign]; simpa using hz) (by simpa [hz] using this)
    · have := emitW_app cap O false σ1 (by simp [hσ1, Function.update_of_ne hOI, hO])
      exact WExec.ifsF (by rw [hsign]; simpa using hz) (by simpa [hz] using this)
  set σ2 := appS σ1 O [decide (z < 0)] with hσ2
  have s3 := WExec.fwd (cap := cap) I σ2
  set σ3 := σ2.seth I (σ2.sh I + 1) with hσ3
  have hI3 : σ3.st I = (pre ++ [true, decide (z < 0)]) ++ (frameP (natWord z.natAbs) ++ rest) := by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hIO, hI, frameP_intWord]
  have hIh3 : σ3.sh I = (pre ++ [true, decide (z < 0)]).length := by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hIO, hIh]
  have hO3 : σ3.sh O = (σ3.st O).length := by simp [hσ3, hσ2, Function.update_of_ne hOI]
  obtain ⟨τ, s4, m4⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap cpyOut cpyNxt (pre ++ [true, decide (z < 0)])
    rest z.natAbs h false σ3 hI3 hIh3 (by simp [hσ3, hσ2, hσ1, hc]) (by simp [hσ3, hσ2, hσ1, hf]) hkh hkc hO3
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hRO, Function.update_of_ne hRI, hR])
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hRO, Function.update_of_ne hRI, hRh])
  refine ⟨τ, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), ?_, m4.vc, m4.vf⟩
  have t4 := TMv.of_mv m4 (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hRO, Function.update_of_ne hRI, hRh])
  refine ⟨by rw [t4.sI]; simp [hσ3, hσ2, hσ1, Function.update_of_ne hIO], ?_, ?_, t4.hO, ?_⟩
  · rw [t4.hI]; simp [intWord]; omega
  · rw [t4.sO]; simp [hσ3, hσ2, hσ1, Function.update_of_ne hOI, wRec, cmap_cpy]
  · refine ⟨fun i hi => ?_, fun r hr => ?_, ?_⟩
    · have hiI : i ≠ I := fun e => hi (Or.inl e)
      have hiO : i ≠ O := fun e => hi (Or.inr e)
      rw [(t4.fr.1 i hi).1, (t4.fr.1 i hi).2]
      simp [hσ3, hσ2, hσ1, Function.update_of_ne hiI, Function.update_of_ne hiO]
    · rw [t4.fr.2.1 r hr]; simp [hσ3, hσ2, hσ1]
    · rw [t4.fr.2.2]; simp [hσ3, hσ2, hσ1]

/-! ## The gate numbers -/

/-- **`K` numbers' records.** -/
def recL (K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (convRec I O R c f))

theorem recL_spec (hcap : 1 ≤ cap) (K : Fin nr) (hKc : K ≠ c) (hKf : K ≠ f) (h : ℕ) (rest : List Bool)
    (hR : ∀ σ : WState ns nr, σ.st R = σ.st R) :
    ∀ (zs : List ℤ) (σ : WState ns nr) (pre : List Bool), σ.st I = pre ++ (frameP (zs.flatMap intWord) ++ rest) →
      σ.sh I = pre.length → σ.val K = zs.length → zs.length ≤ cap → σ.val c = 0 → σ.val f = 0 →
      (∀ z ∈ zs, natBitLength z.natAbs ≤ h ∧ natBitLength z.natAbs ≤ cap) → σ.sh O = (σ.st O).length →
      σ.st R = false :: List.replicate h true → σ.sh R = 0 →
      ∃ τ, WExec cap (recL I O R c f K) σ τ ((zs.map fun z => convRecCost z h + 4).sum + 1) ∧
        TMv I O (fun r => r = c ∨ r = f ∨ r = K) σ τ (pre.length + 2 * (zs.flatMap intWord).length)
          (zs.flatMap (wRec h)) ∧ τ.val K = 0 ∧ τ.val c = 0 ∧ τ.val f = 0
  | [], σ, pre, _, hIh, hK, _, hc, hf, _, hO, _, _ => by
    refine ⟨σ, WExec.cast cap (WExec.whrF hK) rfl (by simp), ?_, hK, hc, hf⟩
    have := TMv.refl I O (fun r => r = c ∨ r = f ∨ r = K) σ hO
    simpa [hIh] using this
  | z :: zs, σ, pre, hI, hIh, hK, hlc, hc, hf, hz, hO, hRs, hRh => by
    have d := WExec.dec (cap := cap) K σ (by rw [hK]; exact hlc)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    obtain ⟨τ1, x1, m1, c1, f1⟩ := convRec_spec cap I O R c f hIO hIR hOR hcf hcap pre
      (frameP (zs.flatMap intWord) ++ rest) z h σ1 (by simp [hσ1, hI, List.flatMap_cons, frameP, List.append_assoc])
      (by simp [hσ1, hIh]) (by simp [hσ1, Ne.symm hKc, hc]) (by simp [hσ1, Ne.symm hKf, hf])
      (hz z List.mem_cons_self).1 (hz z List.mem_cons_self).2 (by simp [hσ1, hO]) (by simp [hσ1, hRs])
      (by simp [hσ1, hRh])
    have hK1 : τ1.val K = zs.length := by
      rw [m1.fr.2.1 K (fun h' => by rcases h' with e | e <;> [exact hKc e; exact hKf e])]; simp [hσ1, hK]
    obtain ⟨τ, x2, m2, cK, cc, cf⟩ := recL_spec hcap K hKc hKf h rest hR zs τ1 (pre ++ frameP (intWord z))
      (by rw [m1.sI]; simp [hσ1, hI, List.flatMap_cons, frameP, List.append_assoc])
      (by rw [m1.hI]; simp [frameP]; omega) hK1 (by simp at hlc; omega) c1 f1
      (fun y hy => hz y (List.mem_cons_of_mem _ hy)) m1.hO
      (by rw [(m1.fr.1 R (fun h' => by rcases h' with e | e <;> [exact hIR e.symm; exact hOR e.symm])).1]; simp [hσ1, hRs])
      (by rw [(m1.fr.1 R (fun h' => by rcases h' with e | e <;> [exact hIR e.symm; exact hOR e.symm])).2]; simp [hσ1, hRh])
    refine ⟨τ, ?_, ?_, cK, cc, cf⟩
    · refine WExec.cast cap (WExec.whrT (by rw [hK]; simp) (WExec.seq d x1) x2) rfl ?_
      simp only [List.map_cons, List.sum_cons]; omega
    · have m1' : TMv I O (fun r => r = c ∨ r = f ∨ r = K) σ τ1 (pre.length + 2 * (intWord z).length) (wRec h z) :=
        (m1.mono (Rg' := fun r => r = c ∨ r = f ∨ r = K)
          (fun r h' => h'.elim Or.inl (fun e => Or.inr (Or.inl e)))).of_setv K (Or.inr (Or.inr rfl)) (σ.val K - 1)
      have := m1'.trans m2
      refine ⟨this.sI, ?_, by rw [this.sO, List.flatMap_cons], this.hO, this.fr⟩
      rw [this.hI]; simp [List.flatMap_cons, frameP]; omega

end Conv

/-! ## The request's numbers -/

/-- The request's gate numbers: each gate's weights in coordinate order, then its threshold. -/
def gInts (R : SelectionReq) : List ℤ := R.gates.flatMap fun g => List.ofFn g.weights ++ [g.threshold]

theorem wRec_eq (W : ℕ) (z : ℤ) : wRec W z = recBits W (decide (z < 0), z.natAbs) := rfl

/-- **The gate table** is the numbers' records. -/
theorem gateTable_eq (W : ℕ) (R : SelectionReq) : gateTable W R = (gInts R).flatMap (wRec W) := by
  unfold gateTable tbl allRecs gInts
  rw [List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  funext g
  simp only [gRecs, coordRecs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [List.flatMap_def, List.map_ofFn, wRec_eq, gateOf, Function.comp_def]
  rfl

/-- **The request's gate section** is the numbers' native words. -/
theorem gates_word_eq (R : SelectionReq) :
    R.gates.flatMap (fun g => (List.ofFn fun i => intWord (g.weights i)).flatten ++ intWord g.threshold) =
      (gInts R).flatMap intWord := by
  unfold gInts
  rw [List.flatMap_assoc]
  congr 1
  funext g
  rw [List.flatMap_append]
  simp [List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem gInts_length (R : SelectionReq) : (gInts R).length = R.gates.length * (R.n + 1) := by
  unfold gInts
  rw [List.length_flatMap]
  simp [List.sum_replicate]

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
