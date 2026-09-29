import Proof.Wire_3_5.Selection.CosGT

/-! # C1.5 parse: the population table from the request word (P3:1326-1330)

Paper: "nonnegative rational weights `p_X` summing to one, with polynomial-bit descriptions" (P3:1326-1330). The
request word carries each population as `natListWord l ++ ratWord p` (its gate indices, then its weight); the coset
loop reads the population table `popTable W R` (`Cos.popRec W X`: `1^|l| 0`, the index words, the weight's numerator
and denominator words, all of width `W`). **`popRecW`** converts one population: PA's `readNatM` reads `|l|` into a
unary register (a size field, at most the request's length), `1^|l| 0` is written, `convNatW` converts each index,
C6's `ratReadW` converts the weight, and the table's length register gains `|popRec W X|` (the coset loop rewinds the
table by it). **`popsT`** converts every population. Main declarations: `natsL`, **`natsL_spec`**, `addR`, `popRecW`,
**`popRecW_spec`**, `popsT`, **`popsT_spec`**, `pops_word_eq`. Paper quantity: the populations' gate indices and
rational weights on the machine's table. -/

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
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.PrimT (Mv emitW convNatW convNatW_spec cpyOut cpyNxt cmap_cpy)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec)
open NearCubicWires.RepairRepresentation (natWord intWord natListWord)
open NearCubicWires.WireExponent3_5 (ratWord)

variable {ns nr : ℕ}

theorem marks_eq (w : List Bool) : RepairOrdinary.Streaming.marks w = frameP w := rfl

theorem frameP_append' (u v : List Bool) : frameP (u ++ v) = frameP u ++ frameP v := by
  simp [frameP, List.flatMap_append]

theorem frameP_length' (u : List Bool) : (frameP u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [frameP] at ih ⊢; omega

theorem TMv.shrink {I O : Fin (ns + 1)} {Rg Rg' : Fin nr → Prop} {σ τ : WState ns nr} {p : ℕ} {w : List Bool}
    (h : TMv I O Rg σ τ p w) (hR : ∀ r, Rg r → ¬ Rg' r → τ.val r = σ.val r) : TMv I O Rg' σ τ p w := by
  refine ⟨h.sI, h.hI, h.sO, h.hO, ⟨h.fr.1, fun r hr => ?_, h.fr.2.2⟩⟩
  by_cases hg : Rg r
  · exact hR r hg hr
  · exact h.fr.2.1 r hg

/-! ## Index words -/

/-- `K` natural numbers' framed width-`h` words. -/
def natsL (I O R : Fin (ns + 1)) (c f K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (convNatW I O R c f cpyOut cpyNxt))

section Nats
variable (cap : ℕ) (I O R : Fin (ns + 1)) (c f : Fin nr) (hIO : I ≠ O) (hIR : I ≠ R) (hOR : O ≠ R) (hcf : c ≠ f)
include hIO hIR hOR hcf

theorem natsL_spec (hcap : 1 ≤ cap) (K : Fin nr) (hKc : K ≠ c) (hKf : K ≠ f) (h : ℕ) (rest : List Bool) :
    ∀ (l : List ℕ) (σ : WState ns nr) (pre : List Bool), σ.st I = pre ++ (frameP (l.flatMap natWord) ++ rest) →
      σ.sh I = pre.length → σ.val K = l.length → l.length ≤ cap → σ.val c = 0 → σ.val f = 0 →
      (∀ i ∈ l, natBitLength i ≤ h ∧ natBitLength i ≤ cap) → σ.sh O = (σ.st O).length →
      σ.st R = false :: List.replicate h true → σ.sh R = 0 →
      ∃ τ, WExec cap (natsL I O R c f K) σ τ
          ((l.map fun i => PrimT.countCost (natBitLength i) + 1 + PrimT.wordCost h + 4).sum + 1) ∧
        TMv I O (fun r => r = c ∨ r = f ∨ r = K) σ τ (pre.length + 2 * (l.flatMap natWord).length)
          (l.flatMap fun i => frame (binary h i)) ∧ τ.val K = 0 ∧ τ.val c = 0 ∧ τ.val f = 0
  | [], σ, pre, _, hIh, hK, _, hc, hf, _, hO, _, _ => by
    refine ⟨σ, WExec.cast cap (WExec.whrF hK) rfl (by simp), ?_, hK, hc, hf⟩
    have := TMv.refl I O (fun r => r = c ∨ r = f ∨ r = K) σ hO
    simpa [hIh] using this
  | i :: l, σ, pre, hI, hIh, hK, hlc, hc, hf, hz, hO, hRs, hRh => by
    have d := WExec.dec (cap := cap) K σ (by rw [hK]; exact hlc)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    obtain ⟨τ1, x1, m1⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap cpyOut cpyNxt pre
      (frameP (l.flatMap natWord) ++ rest) i h false σ1
      (by simp [hσ1, hI, List.flatMap_cons, frameP_append', List.append_assoc])
      (by simp [hσ1, hIh]) (by simp [hσ1, Ne.symm hKc, hc]) (by simp [hσ1, Ne.symm hKf, hf])
      (hz i List.mem_cons_self).1 (hz i List.mem_cons_self).2 (by simp [hσ1, hO]) (by simp [hσ1, hRs])
      (by simp [hσ1, hRh])
    have t1 := TMv.of_mv m1 (by simp [hσ1, hRh])
    have hK1 : τ1.val K = l.length := by
      rw [t1.fr.2.1 K (fun h' => by rcases h' with e | e <;> [exact hKc e; exact hKf e])]; simp [hσ1, hK]
    obtain ⟨τ, x2, m2, cK, cc, cf⟩ := natsL_spec hcap K hKc hKf h rest l τ1 (pre ++ frameP (natWord i))
      (by rw [t1.sI]; simp [hσ1, hI, List.flatMap_cons, frameP_append', List.append_assoc])
      (by rw [t1.hI]; simp [frameP_length']) hK1 (by simp at hlc; omega) m1.vc m1.vf
      (fun y hy => hz y (List.mem_cons_of_mem _ hy)) m1.hO
      (by rw [m1.sR]; simp [hσ1, hRs]) (by rw [m1.hR])
    refine ⟨τ, ?_, ?_, cK, cc, cf⟩
    · refine WExec.cast cap (WExec.whrT (by rw [hK]; simp) (WExec.seq d x1) x2) rfl ?_
      simp only [List.map_cons, List.sum_cons]; omega
    · have t1' : TMv I O (fun r => r = c ∨ r = f ∨ r = K) σ τ1 (pre.length + 2 * (natWord i).length)
          (frame (binary h i)) := by
        have e : frame (PrimT.cmap cpyOut cpyNxt (binary h i) false) = frame (binary h i) := by rw [cmap_cpy]
        have t1'' := (t1.mono (Rg' := fun r => r = c ∨ r = f ∨ r = K)
          (fun r h' => h'.elim Or.inl (fun e => Or.inr (Or.inl e)))).of_setv K (Or.inr (Or.inr rfl)) (σ.val K - 1)
        rw [e] at t1''
        exact t1''
      have := t1'.trans m2
      refine ⟨this.sI, ?_, by rw [this.sO, List.flatMap_cons], this.hO, this.fr⟩
      rw [this.hI]; simp [List.flatMap_cons, frameP_length']; omega

end Nats

/-! ## `D += K` -/

/-- `D += K` (counted by `K`, scratch `T`; `K` kept). -/
def addR (K T D : Fin nr) : WM ns nr := UnionMachine.FrontTWKit.cloop K T (.inc D)

theorem addR_spec (cap : ℕ) (K T D : Fin nr) (hKT : K ≠ T) (hKD : K ≠ D) (hTD : T ≠ D) (σ : WState ns nr) (k : ℕ)
    (hK : σ.val K = k) (hT : σ.val T = 0) (hk : k ≤ cap) (hD : σ.val D + k ≤ cap) :
    WExec cap (addR K T D) σ (σ.setv D (σ.val D + k)) (k * (3 + 8) + 1 + 1 + (7 * k + 1)) := by
  have h := Point.cloopM cap K T hKT (.inc D) (fun σ' j => σ'.setv D (σ.val D + j)) (fun σ' j v w => by
      rw [wsetv_comm _ _ _ (Ne.symm hKD), wsetv_comm _ _ _ (Ne.symm hTD)])
    σ k 3 hK hT hk (by
      intro j hj v w
      have := WExec.inc (cap := cap) D (((σ.setv K v).setv T w).setv D (σ.val D + j)) (by simp; omega)
      refine WExec.cast cap this ?_ le_rfl
      simp [wsetv_setv]; ring_nf)
  have e0 : σ.setv D (σ.val D + 0) = σ := by rw [Nat.add_zero, wsetv_same]
  rw [e0] at h
  exact h

/-! ## One population -/

/-- The population's registers: `Z = (c, f, K, M, t, p, K2 = 2W+1, PTL)`. -/
def ptlAdd (Z : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (addR (Z 3) (Z 4) (Z 7)) (.seq (.inc (Z 7)) (.seq (FinalPass.Hash4.wcopyR (Z 3) (Z 2) (Z 4))
    (.seq (.inc (Z 2)) (.seq (.inc (Z 2)) (.whr (Z 2) (.seq (.dec (Z 2)) (addR (Z 6) (Z 4) (Z 7))))))))

/-- **One population's record**: `|l|` into `M`, `1^|l| 0`, the index words, the weight's words, `PTL += |record|`. -/
def popRecW (I O R : Fin (ns + 1)) (Z : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (readNatM true I (Z 1) (Z 0) (Z 3) (Z 5) (Z 4)) (.seq (FinalPass.Hash4.wcopyR (Z 3) (Z 2) (Z 4))
    (.seq (onesW O (Z 2)) (.seq (emitW O false) (.seq (FinalPass.Hash4.wcopyR (Z 3) (Z 2) (Z 4))
      (.seq (natsL I O R (Z 0) (Z 1) (Z 2)) (.seq (ratReadW I O R (Z 0) (Z 1)) (.seq (ptlAdd Z) (WM.clear (Z 3)))))))))

theorem ptlAdd_loop (cap : ℕ) (Z : Fin 8 ↪ Fin nr) (a : ℕ) :
    ∀ (j : ℕ) (σ : WState ns nr) (p0 : ℕ), σ.val (Z 2) = j → σ.val (Z 6) = a → σ.val (Z 4) = 0 →
      σ.val (Z 7) = p0 → j ≤ cap → a ≤ cap → p0 + j * a ≤ cap →
      WExec cap (.whr (Z 2) (.seq (.dec (Z 2)) (addR (Z 6) (Z 4) (Z 7)))) σ ((σ.setv (Z 7) (p0 + j * a)).setv (Z 2) 0)
        (j * (a * 11 + 1 + 1 + (7 * a + 1) + 4) + 1)
  | 0, σ, p0, h0, _, _, h7, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ (by omega)
    rw [Nat.zero_mul, Nat.add_zero, ← h7, wsetv_same, ← h0, wsetv_same]
  | j + 1, σ, p0, hj, ha, ht, h7, hjc, hac, hpc => by
    have zne : ∀ i k : Fin 8, i ≠ k → Z i ≠ Z k := fun i k h => Z.injective.ne h
    have d := WExec.dec (cap := cap) (Z 2) σ (by omega)
    set σ1 := σ.setv (Z 2) (σ.val (Z 2) - 1) with hσ1
    have x := addR_spec cap (Z 6) (Z 4) (Z 7) (zne 6 4 (by decide)) (zne 6 7 (by decide)) (zne 4 7 (by decide)) σ1 a
      (by simp [hσ1, zne 6 2 (by decide), ha]) (by simp [hσ1, zne 4 2 (by decide), ht]) hac
      (by simp [hσ1, zne 7 2 (by decide), h7]; nlinarith)
    have hp1 : σ1.val (Z 7) = p0 := by simp [hσ1, zne 7 2 (by decide), h7]
    rw [hp1] at x
    have ih := ptlAdd_loop cap Z a j (σ1.setv (Z 7) (p0 + a)) (p0 + a)
      (by simp [hσ1, zne 2 7 (by decide), hj]) (by simp [hσ1, zne 6 7 (by decide), zne 6 2 (by decide), ha])
      (by simp [hσ1, zne 4 7 (by decide), zne 4 2 (by decide), ht]) (by simp) (by omega) hac (by nlinarith)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d (by simpa [Nat.mul_comm] using x)) ih) ?_ (by nlinarith)
    rw [wsetv_setv]
    apply WState.eq
    · rfl
    · rfl
    · funext r
      by_cases h2 : r = Z 2
      · subst h2; simp
      · by_cases h7' : r = Z 7
        · subst h7'; simp [Function.update_apply, zne 7 2 (by decide)]; ring
        · simp [hσ1, Function.update_apply, h2, h7']
    · rfl

/-! ## Moves as table-builder moves -/

theorem TMv.ofState {I O : Fin (ns + 1)} {Rg : Fin nr → Prop} (σ τ : WState ns nr) (p : ℕ)
    (w : List Bool) (hsI : τ.st I = σ.st I) (hhI : τ.sh I = p) (hsO : τ.st O = σ.st O ++ w)
    (hhO : τ.sh O = (τ.st O).length) (hst : ∀ i, i ≠ I → i ≠ O → τ.st i = σ.st i ∧ τ.sh i = σ.sh i)
    (hv : ∀ r, ¬ Rg r → τ.val r = σ.val r) (hc : τ.cell = σ.cell) : TMv I O Rg σ τ p w :=
  ⟨hsI, hhI, hsO, hhO, ⟨fun i hi => hst i (fun e => hi (Or.inl e)) (fun e => hi (Or.inr e)), hv, hc⟩⟩

theorem TMv.app {I O : Fin (ns + 1)} (Rg : Fin nr → Prop) (σ : WState ns nr) (hIO : I ≠ O) (u : List Bool) :
    TMv I O Rg σ (appS σ O u) (σ.sh I) u :=
  TMv.ofState σ _ _ u (by simp [Function.update_of_ne hIO]) (by simp [Function.update_of_ne hIO]) (by simp)
    (by simp) (fun i h1 h2 => by simp [Function.update_of_ne h2]) (fun _ _ => rfl) rfl

/-- One population's cost bound. -/
def popRecCost (m W bn bd : ℕ) : ℕ :=
  (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) + (18 * m + 3) + (7 * m + 1) + 3 + (18 * m + 3) +
    ((m * (PrimT.countCost W + 1 + PrimT.wordCost W + 4)) + 1) + ratReadCost bn bd W +
    (m * (3 + 8) + 1 + 1 + (7 * m + 1)) + 3 + (18 * m + 3) + 3 + 3 +
    ((m + 2) * ((2 * W + 1) * 11 + 1 + 1 + (7 * (2 * W + 1) + 1) + 4) + 1) + (3 * m + 1) + 20

theorem natsL_cost_le (W : ℕ) : ∀ (l : List ℕ), (∀ i ∈ l, natBitLength i ≤ W) →
    (l.map fun i => PrimT.countCost (natBitLength i) + 1 + PrimT.wordCost W + 4).sum ≤
      l.length * (PrimT.countCost W + 1 + PrimT.wordCost W + 4)
  | [], _ => by simp
  | i :: l, h => by
    have h1 := natsL_cost_le W l (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have h2 : PrimT.countCost (natBitLength i) ≤ PrimT.countCost W := by
      unfold PrimT.countCost; have := h i List.mem_cons_self; omega
    simp only [List.map_cons, List.sum_cons, List.length_cons]; nlinarith

theorem idxWords_eq' (W : ℕ) (l : List ℕ) : idxWords W l = l.flatMap fun i => frame (binary W i) := by
  simp [idxWords, List.flatMap_def]

/-- **One population's record** appended to the table (`O`), the input past the population's words, `PTL += |record|`;
every other register comes back. -/
theorem popRecW_spec (cap : ℕ) (I O R : Fin (ns + 1)) (hIO : I ≠ O) (hIR : I ≠ R) (hOR : O ≠ R) (Z : Fin 8 ↪ Fin nr)
    (W : ℕ) (X : List ℕ × ℚ) (hX : 0 ≤ X.2) (pre rest : List Bool) (σ : WState ns nr) (p0 : ℕ)
    (hI : σ.st I = pre ++ (frameP (natListWord X.1 ++ ratWord X.2) ++ rest)) (hIh : σ.sh I = pre.length)
    (hz : ∀ i : Fin 8, i.val ≤ 5 → σ.val (Z i) = 0) (hK2 : σ.val (Z 6) = 2 * W + 1) (hp : σ.val (Z 7) = p0)
    (hO : σ.sh O = (σ.st O).length) (hR : σ.st R = false :: List.replicate W true) (hRh : σ.sh R = 0)
    (hbits : ∀ i ∈ X.1, natBitLength i ≤ W) (hnum : natBitLength X.2.num.natAbs ≤ W) (hden : natBitLength X.2.den ≤ W)
    (hcap : 2 ^ (X.1.length + 2) + p0 + (X.1.length + 2) * (2 * W + 2) + W + 1 ≤ cap) :
    ∃ τ, WExec cap (popRecW I O R Z) σ τ (popRecCost X.1.length W (natBitLength X.2.num.natAbs) (natBitLength X.2.den)) ∧
      TMv I O (fun r => r = Z 7) σ τ (pre.length + 2 * (natListWord X.1 ++ ratWord X.2).length) (popRec W X) ∧
      τ.val (Z 7) = p0 + (popRec W X).length := by
  have zne : ∀ i k : Fin 8, i ≠ k → Z i ≠ Z k := fun i k h => Z.injective.ne h
  obtain ⟨m, hm⟩ : ∃ m, X.1.length = m := ⟨_, rfl⟩
  rw [hm] at hcap ⊢
  set Rg : Fin nr → Prop := fun r => r = Z 0 ∨ r = Z 1 ∨ r = Z 2 ∨ r = Z 3 ∨ r = Z 4 ∨ r = Z 5 ∨ r = Z 7 with hRg
  have hOI : O ≠ I := fun e => hIO e.symm
  have hRI : R ≠ I := fun e => hIR e.symm
  have hRO : R ≠ O := fun e => hOR e.symm
  have hnb : natBitLength m ≤ m + 1 := natBitLength_le m
  have hpw : 2 ^ (natBitLength m + 1) ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmpow : m + 2 ≤ 2 ^ (m + 2) := by have := Nat.lt_two_pow_self (n := m + 2); omega
  have hW2 : m + 2 ≤ (m + 2) * (2 * W + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have hWm : (m + 2) * (2 * W + 1) ≤ (m + 2) * (2 * W + 2) := Nat.mul_le_mul_left _ (by omega)
  have hW3 : 2 * W + 2 ≤ (m + 2) * (2 * W + 2) := Nat.le_mul_of_pos_left _ (by omega)
  -- |l| into M
  have x1 := readNatM_spec cap true I (Z 1) (Z 0) (Z 3) (Z 5) (Z 4) (zne 1 0 (by decide)) (zne 1 3 (by decide))
    (zne 1 5 (by decide)) (zne 1 4 (by decide)) (zne 0 3 (by decide)) (zne 0 5 (by decide)) (zne 0 4 (by decide))
    (zne 5 3 (by decide)) (zne 5 4 (by decide)) (zne 3 4 (by decide)) m pre
    (frameP (X.1.flatMap natWord ++ ratWord X.2) ++ rest) σ
    (by rw [hI, natListWord, List.append_assoc, frameP_append']
        simp [PrimAsm.ParseNat.enc, marks_eq, List.append_assoc, hm])
    hIh (hz 1 (by decide)) (hz 0 (by decide)) (hz 5 (by decide)) (hz 4 (by decide))
    (by rw [hz 3 (by decide)]; omega)
  rw [hz 3 (by decide), Nat.zero_add] at x1
  simp only [PrimAsm.ParseNat.stp, if_true] at x1
  set σ1 := (σ.seth I (pre.length + 2 * (natWord m).length)).setv (Z 3) m with hσ1
  have t1 : TMv I O Rg σ σ1 (pre.length + 2 * (natWord m).length) [] :=
    TMv.ofState σ σ1 _ [] (by simp [hσ1]) (by simp [hσ1]) (by simp [hσ1])
      (by simp [hσ1, Function.update_of_ne hOI, hO]) (fun i h1 _ => by simp [hσ1, Function.update_of_ne h1])
      (fun r hr => by
        have h3 : r ≠ Z 3 := fun e => hr (Or.inr (Or.inr (Or.inr (Or.inl e))))
        simp [hσ1, Function.update_apply, h3]) rfl
  -- K := m, 1^m 0
  have hm1 : σ1.val (Z 3) = m := by simp [hσ1]
  have x2 := FinalPass.Hash4.wcopyR_spec cap (Z 3) (Z 2) (Z 4) (zne 3 2 (by decide)) (zne 3 4 (by decide))
    (zne 2 4 (by decide)) σ1 (by simp [hσ1, zne 2 3 (by decide), hz 2 (by decide)])
    (by simp [hσ1, zne 4 3 (by decide), hz 4 (by decide)]) (by rw [hm1]; omega)
  rw [hm1] at x2
  set σ2 := σ1.setv (Z 2) m with hσ2
  have x3 := onesW_spec cap O (Z 2) m σ2 (by simp [hσ2]) (by omega) (by simp [hσ2, hσ1, Function.update_of_ne hOI, hO])
  set σ3 := (appS σ2 O (List.replicate m true)).setv (Z 2) 0 with hσ3
  have x4 := emitW_app cap O false σ3 (by simp [hσ3])
  set σ4 := appS σ3 O [false] with hσ4
  have t4 : TMv I O Rg σ1 σ4 (pre.length + 2 * (natWord m).length) (List.replicate m true ++ [false]) := by
    have a := ((TMv.app Rg σ2 hIO (List.replicate m true)).setv (Z 2) (Or.inr (Or.inr (Or.inl rfl))) 0).trans
      (TMv.app Rg σ3 hIO [false])
    have b := a.of_setv (Z 2) (Or.inr (Or.inr (Or.inl rfl))) m
    have e3 : σ3.sh I = pre.length + 2 * (natWord m).length := by
      simp [hσ3, hσ2, hσ1, Function.update_of_ne hIO]
    rw [e3] at b
    exact b
  -- K := m, the index words
  have hm4 : σ4.val (Z 3) = m := by simp [hσ4, hσ3, hσ2, hσ1, zne 3 2 (by decide)]
  have x5 := FinalPass.Hash4.wcopyR_spec cap (Z 3) (Z 2) (Z 4) (zne 3 2 (by decide)) (zne 3 4 (by decide))
    (zne 2 4 (by decide)) σ4 (by simp [hσ4, hσ3]) (by simp [hσ4, hσ3, hσ2, hσ1, zne 4 2 (by decide),
      zne 4 3 (by decide), hz 4 (by decide)]) (by rw [hm4]; omega)
  rw [hm4] at x5
  set σ5 := σ4.setv (Z 2) m with hσ5
  have t5 : TMv I O Rg σ4 σ5 (σ4.sh I) [] :=
    (TMv.refl I O Rg σ4 (by simp [hσ4])).setv (Z 2) (Or.inr (Or.inr (Or.inl rfl))) m
  have hI5 : σ5.st I = (pre ++ frameP (natWord m)) ++ (frameP (X.1.flatMap natWord) ++ (frameP (ratWord X.2) ++ rest)) := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hIO, hI, natListWord, frameP_append', List.append_assoc, hm]
  have hIh5 : σ5.sh I = (pre ++ frameP (natWord m)).length := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hIO, frameP_length']
  have hR5 : σ5.st R = false :: List.replicate W true := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hRO, hR]
  have hRh5 : σ5.sh R = 0 := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hRO, Function.update_of_ne hRI, hRh]
  obtain ⟨τ6, x6, t6, k6, c6, f6⟩ := natsL_spec cap I O R (Z 0) (Z 1) hIO hIR hOR (zne 0 1 (by decide)) (by omega)
    (Z 2) (zne 2 0 (by decide)) (zne 2 1 (by decide)) W (frameP (ratWord X.2) ++ rest) X.1 σ5
    (pre ++ frameP (natWord m)) hI5 hIh5 (by simp [hσ5, hm]) (by omega)
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, zne 0 2 (by decide), zne 0 3 (by decide), hz 0 (by decide)])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, zne 1 2 (by decide), zne 1 3 (by decide), hz 1 (by decide)])
    (fun i hi => ⟨hbits i hi, by have := hbits i hi; omega⟩) (by simp [hσ5, hσ4]) hR5 hRh5
  -- the weight
  have hI6 : τ6.st I = (pre ++ frameP (natWord m) ++ frameP (X.1.flatMap natWord)) ++ (frameP (ratWord X.2) ++ rest) := by
    rw [t6.sI, hI5]; simp [List.append_assoc]
  have hIh6 : τ6.sh I = (pre ++ frameP (natWord m) ++ frameP (X.1.flatMap natWord)).length := by
    rw [t6.hI]; simp [frameP_length']; omega
  have hR6s : τ6.st R = false :: List.replicate W true := by
    rw [(t6.fr.1 R (fun h' => by rcases h' with e | e <;> [exact hRI e; exact hRO e])).1, hR5]
  have hR6h : τ6.sh R = 0 := by
    rw [(t6.fr.1 R (fun h' => by rcases h' with e | e <;> [exact hRI e; exact hRO e])).2, hRh5]
  obtain ⟨τ7, x7, m7⟩ := ratReadW_spec cap I O R (Z 0) (Z 1) hIO hIR hOR (zne 0 1 (by decide)) (by omega)
    (pre ++ frameP (natWord m) ++ frameP (X.1.flatMap natWord)) rest X.2 hX W τ6 hI6 hIh6 c6 f6 hnum hden
    (by omega) (by omega) t6.hO hR6s hR6h
  have t7 := TMv.of_mv m7 hR6h
  -- PTL += |record|
  have v7 : ∀ r, r ≠ Z 0 → r ≠ Z 1 → r ≠ Z 2 → τ7.val r = σ5.val r := by
    intro r h0 h1 h2
    rw [t7.fr.2.1 r (fun h' => by rcases h' with e | e <;> [exact h0 e; exact h1 e]),
      t6.fr.2.1 r (fun h' => by rcases h' with e | e | e <;> [exact h0 e; exact h1 e; exact h2 e])]
  have q3 : τ7.val (Z 3) = m := by
    rw [v7 _ (zne 3 0 (by decide)) (zne 3 1 (by decide)) (zne 3 2 (by decide))]; simp [hσ5, hm4]
  have q4 : τ7.val (Z 4) = 0 := by
    rw [v7 _ (zne 4 0 (by decide)) (zne 4 1 (by decide)) (zne 4 2 (by decide))]
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, zne 4 2 (by decide), zne 4 3 (by decide), hz 4 (by decide)]
  have q5 : τ7.val (Z 5) = 0 := by
    rw [v7 _ (zne 5 0 (by decide)) (zne 5 1 (by decide)) (zne 5 2 (by decide))]
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, zne 5 2 (by decide), zne 5 3 (by decide), hz 5 (by decide)]
  have q6 : τ7.val (Z 6) = 2 * W + 1 := by
    rw [v7 _ (zne 6 0 (by decide)) (zne 6 1 (by decide)) (zne 6 2 (by decide))]
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, zne 6 2 (by decide), zne 6 3 (by decide), hK2]
  have q7 : τ7.val (Z 7) = p0 := by
    rw [v7 _ (zne 7 0 (by decide)) (zne 7 1 (by decide)) (zne 7 2 (by decide))]
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, zne 7 2 (by decide), zne 7 3 (by decide), hp]
  have q2 : τ7.val (Z 2) = 0 := by
    rw [t7.fr.2.1 (Z 2) (fun h' => by rcases h' with e | e <;> [exact zne 2 0 (by decide) e; exact zne 2 1 (by decide) e])]
    exact k6
  have y1 := addR_spec cap (Z 3) (Z 4) (Z 7) (zne 3 4 (by decide)) (zne 3 7 (by decide)) (zne 4 7 (by decide)) τ7 m q3 q4
    (by omega) (by rw [q7]; omega)
  rw [q7] at y1
  set σ8 := τ7.setv (Z 7) (p0 + m) with hσ8
  have y2 := WExec.inc (cap := cap) (Z 7) σ8 (by simp [hσ8]; omega)
  set σ9 := σ8.setv (Z 7) (σ8.val (Z 7) + 1) with hσ9
  have hm9 : σ9.val (Z 3) = m := by simp [hσ9, hσ8, zne 3 7 (by decide), q3]
  have y3 := FinalPass.Hash4.wcopyR_spec cap (Z 3) (Z 2) (Z 4) (zne 3 2 (by decide)) (zne 3 4 (by decide))
    (zne 2 4 (by decide)) σ9 (by simp [hσ9, hσ8, zne 2 7 (by decide), q2])
    (by simp [hσ9, hσ8, zne 4 7 (by decide), q4]) (by rw [hm9]; omega)
  rw [hm9] at y3
  set σ10 := σ9.setv (Z 2) m with hσ10
  have y4 := WExec.inc (cap := cap) (Z 2) σ10 (by simp [hσ10]; omega)
  set σ11 := σ10.setv (Z 2) (σ10.val (Z 2) + 1) with hσ11
  have y5 := WExec.inc (cap := cap) (Z 2) σ11 (by simp [hσ11, hσ10]; omega)
  set σ12 := σ11.setv (Z 2) (σ11.val (Z 2) + 1) with hσ12
  have y6 := ptlAdd_loop cap Z (2 * W + 1) (m + 2) σ12 (p0 + m + 1) (by simp [hσ12, hσ11, hσ10])
    (by simp [hσ12, hσ11, hσ10, hσ9, hσ8, zne 6 2 (by decide), zne 6 7 (by decide), q6])
    (by simp [hσ12, hσ11, hσ10, hσ9, hσ8, zne 4 2 (by decide), zne 4 7 (by decide), q4])
    (by simp [hσ12, hσ11, hσ10, hσ9, hσ8, zne 7 2 (by decide)]) (by omega) (by omega) (by omega)
  set σ13 := (σ12.setv (Z 7) (p0 + m + 1 + (m + 2) * (2 * W + 1))).setv (Z 2) 0 with hσ13
  have hm13 : σ13.val (Z 3) = m := by
    simp [hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, zne 3 2 (by decide), zne 3 7 (by decide), q3]
  have y7 := wclear_spec (cap := cap) (Z 3) m σ13 hm13 (by rw [hm13]; omega)
  set τ := σ13.setv (Z 3) 0 with hτ
  have t8 : TMv I O Rg τ7 τ (τ7.sh I) [] := by
    refine TMv.ofState τ7 τ _ [] (by simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8])
      (by simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8]) (by simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8])
      (by simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, t7.hO])
      (fun i _ _ => by simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8]) (fun r hr => ?_)
      (by simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8])
    have h2 : r ≠ Z 2 := fun e => hr (Or.inr (Or.inr (Or.inl e)))
    have h3 : r ≠ Z 3 := fun e => hr (Or.inr (Or.inr (Or.inr (Or.inl e))))
    have h7 : r ≠ Z 7 := fun e => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))))
    simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, Function.update_apply, h2, h3, h7]
  have T := ((((t1.trans t4).trans t5).trans (t6.mono (Rg' := Rg) (fun r h' => by
    rcases h' with e | e | e <;> [exact Or.inl e; exact Or.inr (Or.inl e); exact Or.inr (Or.inr (Or.inl e))]))).trans
    (t7.mono (Rg' := Rg) (fun r h' => by rcases h' with e | e <;> [exact Or.inl e; exact Or.inr (Or.inl e)]))).trans t8
  have hlen : (popRec W X).length = m + 1 + (m + 2) * (2 * W + 1) := by
    rw [popRec_length, hm]; ring
  have vτ : ∀ r, Rg r → r ≠ Z 7 → τ.val r = σ.val r := by
    intro r hr h7
    rcases hr with e | e | e | e | e | e | e
    · subst e; simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, zne 0 3 (by decide), zne 0 2 (by decide),
        zne 0 7 (by decide), m7.vc, hz 0 (by decide)]
    · subst e; simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, zne 1 3 (by decide), zne 1 2 (by decide),
        zne 1 7 (by decide), m7.vf, hz 1 (by decide)]
    · subst e; simp [hτ, hσ13, zne 2 3 (by decide), hz 2 (by decide)]
    · subst e; simp [hτ, hz 3 (by decide)]
    · subst e; simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, zne 4 3 (by decide), zne 4 2 (by decide),
        zne 4 7 (by decide), q4, hz 4 (by decide)]
    · subst e; simp [hτ, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, zne 5 3 (by decide), zne 5 2 (by decide),
        zne 5 7 (by decide), q5, hz 5 (by decide)]
    · exact absurd e h7
  refine ⟨τ, ?_, ?_, ?_⟩
  · have hc6 := natsL_cost_le W X.1 hbits
    rw [hm] at hc6
    unfold popRecW ptlAdd
    refine WExec.mono (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6
      (WExec.seq x7 (WExec.seq (WExec.seq y1 (WExec.seq y2 (WExec.seq y3 (WExec.seq y4 (WExec.seq y5 y6))))) y7)))))))) ?_
    unfold popRecCost
    omega
  · have T' := T.shrink (Rg' := fun r => r = Z 7) (fun r hr hr' => vτ r hr hr')
    refine ⟨T'.sI, ?_, ?_, T'.hO, T'.fr⟩
    · rw [T'.hI, t7.hI]
      simp [natListWord, List.length_append, hm]; ring
    · rw [T'.sO, popRec_eq, idxWords_eq', hm]
      simp [List.append_assoc, cmap_cpy]
  · simp [hτ, hσ13, zne 7 3 (by decide), zne 7 2 (by decide), hlen]; ring

/-! ## Every population -/

/-- **The population table**: `CP` populations' records. -/
def popsT (I O R : Fin (ns + 1)) (Z : Fin 8 ↪ Fin nr) (CP : Fin nr) : WM ns nr :=
  .whr CP (.seq (.dec CP) (popRecW I O R Z))

/-- The table's cost. -/
def popsTCost (W : ℕ) (ps : List (List ℕ × ℚ)) : ℕ :=
  (ps.map fun X => popRecCost X.1.length W (natBitLength X.2.num.natAbs) (natBitLength X.2.den) + 4).sum + 1

theorem popsT_spec (cap : ℕ) (I O R : Fin (ns + 1)) (hIO : I ≠ O) (hIR : I ≠ R) (hOR : O ≠ R) (Z : Fin 8 ↪ Fin nr)
    (CP : Fin nr) (hCP : ∀ i, Z i ≠ CP) (W Bp : ℕ) (rest : List Bool) :
    ∀ (ps : List (List ℕ × ℚ)) (σ : WState ns nr) (pre : List Bool) (p0 : ℕ),
      σ.st I = pre ++ (frameP (ps.flatMap fun X => natListWord X.1 ++ ratWord X.2) ++ rest) →
      σ.sh I = pre.length → σ.val CP = ps.length → ps.length ≤ cap →
      (∀ i : Fin 8, i.val ≤ 5 → σ.val (Z i) = 0) → σ.val (Z 6) = 2 * W + 1 → σ.val (Z 7) = p0 →
      σ.sh O = (σ.st O).length → σ.st R = false :: List.replicate W true → σ.sh R = 0 →
      p0 + ((ps.map (popRec W)).flatten).length ≤ Bp →
      (∀ X ∈ ps, 0 ≤ X.2 ∧ (∀ i ∈ X.1, natBitLength i ≤ W) ∧ natBitLength X.2.num.natAbs ≤ W ∧
        natBitLength X.2.den ≤ W ∧ 2 ^ (X.1.length + 2) + Bp + (X.1.length + 2) * (2 * W + 2) + W + 1 ≤ cap) →
      ∃ τ, WExec cap (popsT I O R Z CP) σ τ (popsTCost W ps) ∧
        TMv I O (fun r => r = Z 7 ∨ r = CP) σ τ
          (pre.length + 2 * (ps.flatMap fun X => natListWord X.1 ++ ratWord X.2).length) ((ps.map (popRec W)).flatten) ∧
        τ.val (Z 7) = p0 + ((ps.map (popRec W)).flatten).length ∧ τ.val CP = 0
  | [], σ, pre, p0, _, hIh, hC, _, _, _, hp, hO, _, _, _, _ => by
    refine ⟨σ, WExec.cast cap (WExec.whrF hC) rfl (by simp [popsTCost]), ?_, by simpa using hp, hC⟩
    have := TMv.refl I O (fun r => r = Z 7 ∨ r = CP) σ hO
    simpa [hIh] using this
  | X :: ps, σ, pre, p0, hI, hIh, hC, hlc, hz, hK2, hp, hO, hRs, hRh, hB, hX => by
    have zne : ∀ i k : Fin 8, i ≠ k → Z i ≠ Z k := fun i k h => Z.injective.ne h
    have d := WExec.dec (cap := cap) CP σ (by rw [hC]; exact hlc)
    set σ1 := σ.setv CP (σ.val CP - 1) with hσ1
    obtain ⟨hX0, hXb, hXn, hXd, hXc⟩ := hX X List.mem_cons_self
    have hflat : ((X :: ps).map (popRec W)).flatten.length = (popRec W X).length +
        ((ps.map (popRec W)).flatten).length := by simp
    obtain ⟨τ1, x1, t1, v1⟩ := popRecW_spec cap I O R hIO hIR hOR Z W X hX0 pre
      (frameP (ps.flatMap fun X => natListWord X.1 ++ ratWord X.2) ++ rest) σ1 p0
      (by simp [hσ1, hI, List.flatMap_cons, frameP_append', List.append_assoc]) (by simp [hσ1, hIh])
      (fun i hi => by simp [hσ1, hCP i, hz i hi]) (by simp [hσ1, hCP 6, hK2]) (by simp [hσ1, hCP 7, hp])
      (by simp [hσ1, hO]) (by simp [hσ1, hRs]) (by simp [hσ1, hRh]) hXb hXn hXd (by omega)
    have hC1 : τ1.val CP = ps.length := by
      rw [t1.fr.2.1 CP (fun e => hCP 7 e.symm)]; simp [hσ1, hC]
    obtain ⟨τ, x2, t2, v2, c2⟩ := popsT_spec cap I O R hIO hIR hOR Z CP hCP W Bp rest ps τ1
      (pre ++ frameP (natListWord X.1 ++ ratWord X.2)) (p0 + (popRec W X).length)
      (by rw [t1.sI]; simp [hσ1, hI, List.flatMap_cons, frameP_append', List.append_assoc])
      (by rw [t1.hI]; simp [frameP_length']) hC1 (by simp at hlc; omega)
      (fun i hi => by
        rw [t1.fr.2.1 (Z i) (fun e => zne i 7 (by
          intro e'; subst e'; simp at hi) e)]
        simp [hσ1, hCP i, hz i hi])
      (by rw [t1.fr.2.1 (Z 6) (fun e => zne 6 7 (by decide) e)]; simp [hσ1, hCP 6, hK2]) v1 t1.hO
      (by rw [(t1.fr.1 R (fun h' => by rcases h' with e | e <;> [exact hIR e.symm; exact hOR e.symm])).1]
          simp [hσ1, hRs])
      (by rw [(t1.fr.1 R (fun h' => by rcases h' with e | e <;> [exact hIR e.symm; exact hOR e.symm])).2]
          simp [hσ1, hRh])
      (by omega) (fun Y hY => hX Y (List.mem_cons_of_mem _ hY))
    refine ⟨τ, ?_, ?_, by rw [v2, hflat]; ring, c2⟩
    · refine WExec.cast cap (WExec.whrT (by rw [hC]; simp) (WExec.seq d x1) x2) rfl ?_
      simp only [popsTCost, List.map_cons, List.sum_cons]; omega
    · have t1' : TMv I O (fun r => r = Z 7 ∨ r = CP) σ τ1 (pre.length + 2 * (natListWord X.1 ++ ratWord X.2).length)
          (popRec W X) :=
        (t1.mono (Rg' := fun r => r = Z 7 ∨ r = CP) (fun r h' => Or.inl h')).of_setv CP (Or.inr rfl) (σ.val CP - 1)
      have := t1'.trans t2
      refine ⟨this.sI, ?_, by rw [this.sO]; simp, this.hO, this.fr⟩
      rw [this.hI]; simp [List.flatMap_cons, frameP_length']; omega

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
