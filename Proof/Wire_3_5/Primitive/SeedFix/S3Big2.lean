import Proof.Wire_3_5.Primitive.SeedFix.S3Big1
import Proof.Wire_3_5.Primitive.SeedFix.CtrOps

/-! # S3, part 8: one circuit's factor on the evaluator's layout, from scratch that reads alike

C5's stage specs state exact stream contents; the evaluator's scratch only READS like them (`PtIn.sc`, loop-safe
reuse). **`circJ_spec`** runs the lifted circuit program on the idealized state (`idealS`: the scratch replaced by the
exact entry words) and transfers the run to the real state (`ReadEq.wexec_sim`); the streams the program never
writes stay equal (`namesW_liftW`, `circS_writes`, `Ctr.wr_keep`). Result: the factor `[termOk X W R⁺ R⁻]` in `qS 28`,
the circuit registers `qS 0 … 27` at `0`, every other register and every head kept, the six written scratch streams
reading like the circuit program's exit words, every other stream unchanged.

Paper quantity of the main type: one circuit's factor at the point (a conjunct of `R̂`, P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Term NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimT.Ctr (namesW wr_keep)

/-! ## Writes through a lift -/

theorem namesW_liftW {ns nr ns' nr' : ℕ} (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr')
    (s : Fin (ns' + 1)) : ∀ P : WM ns nr, (∀ i, fs i = s → namesW i P = false) → namesW s (P.liftW fs fr) = false
  | .skip, _ => rfl
  | .inc _, _ => rfl
  | .dec _, _ => rfl
  | .fwd _, _ => rfl
  | .bwd _, _ => rfl
  | .wr i b, h => by
    simp only [WM.liftW, namesW, decide_eq_false_iff_not]
    intro e
    have := h i e
    simp [namesW] at this
  | .setc _, _ => rfl
  | .seq P Q, h => by
    simp only [WM.liftW, namesW, Bool.or_eq_false_iff]
    exact ⟨namesW_liftW fs fr s P (fun i e => by have := h i e; simp [namesW] at this; exact this.1),
      namesW_liftW fs fr s Q (fun i e => by have := h i e; simp [namesW] at this; exact this.2)⟩
  | .ifr _ P Q, h => by
    simp only [WM.liftW, namesW, Bool.or_eq_false_iff]
    exact ⟨namesW_liftW fs fr s P (fun i e => by have := h i e; simp [namesW] at this; exact this.1),
      namesW_liftW fs fr s Q (fun i e => by have := h i e; simp [namesW] at this; exact this.2)⟩
  | .ifs _ P Q, h => by
    simp only [WM.liftW, namesW, Bool.or_eq_false_iff]
    exact ⟨namesW_liftW fs fr s P (fun i e => by have := h i e; simp [namesW] at this; exact this.1),
      namesW_liftW fs fr s Q (fun i e => by have := h i e; simp [namesW] at this; exact this.2)⟩
  | .whr _ P, h => by
    simp only [WM.liftW, namesW]
    exact namesW_liftW fs fr s P (fun i e => by have := h i e; simp [namesW] at this; exact this)
  | .whs _ P, h => by
    simp only [WM.liftW, namesW]
    exact namesW_liftW fs fr s P (fun i e => by have := h i e; simp [namesW] at this; exact this)

/-- The circuit program writes only the accumulators, the corner word, the population, the template and the
compared state. -/
theorem circS_writes : ∀ i : Fin 14, i ∉ [sPos, sNeg, sX, sZ, sT5, sSS] → namesW i circS = false := by
  decide

/-! ## Reads past a length -/

theorem read_ge (l : List Bool) (p : ℕ) (hp : l.length ≤ p) : readTapeBit l p = false := by
  unfold readTapeBit
  exact List.getD_eq_default l false hp

theorem read_app_false (l : List Bool) (p : ℕ) (hp : l.length ≤ p) : readTapeBit (l ++ [false]) p = false := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ hp]
  cases h : p - l.length with
  | zero => rfl
  | succ m => simp

theorem blank_rep (m : ℕ) : ∀ b ∈ List.replicate m false, b = false := fun _ hb => (List.mem_replicate.1 hb).2

/-! ## The idealized scratch -/

/-- The evaluator's streams with the scratch replaced by the circuit program's exact entry words. -/
def idealSt (st : Fin 28 → List Bool) (h g : ℕ) (T5 FT : List Bool) : Fin 28 → List Bool := fun i =>
  if i.val = 19 then frameP (binary h 0) ++ [false]
  else if i.val = 20 then frameP (binary h 0) ++ [false]
  else if i.val = 21 then List.replicate (8 * g + 1) false
  else if i.val = 22 then List.replicate (2 * g + 1) false
  else if i.val = 23 then [true]
  else if i.val = 24 then []
  else if i.val = 25 then T5
  else if i.val = 26 then []
  else if i.val = 27 then FT
  else st i

theorem idealSt_low (st : Fin 28 → List Bool) (h g : ℕ) (T5 FT : List Bool) (i : Fin 28) (hi : i.val < 19) :
    idealSt st h g T5 FT i = st i := by
  unfold idealSt
  split_ifs <;> first | omega | rfl

theorem bW_lt (w : Fin 16) : (bW w).val < 19 := by
  show 3 + w.val < 19
  omega

theorem fsJ_0 (j : Fin 4) : fsJ j sG = bW (wIdx 0 j) := rfl
theorem fsJ_1 (j : Fin 4) : fsJ j sC = bC := rfl
theorem fsJ_2 (j : Fin 4) : fsJ j sU = bU := rfl
theorem fsJ_3 (j : Fin 4) : fsJ j sV = bV := rfl
theorem fsJ_4 (j : Fin 4) : fsJ j sPos = bPos := rfl
theorem fsJ_5 (j : Fin 4) : fsJ j sNeg = bNeg := rfl
theorem fsJ_6 (j : Fin 4) : fsJ j sX = bX := rfl
theorem fsJ_7 (j : Fin 4) : fsJ j sZ = bZ := rfl
theorem fsJ_8 (j : Fin 4) : fsJ j sSp = bSp := rfl
theorem fsJ_9 (j : Fin 4) : fsJ j sSm = bSm := rfl
theorem fsJ_10 (j : Fin 4) : fsJ j sT5 = bT5 := rfl
theorem fsJ_11 (j : Fin 4) : fsJ j sSS = bSS := rfl
theorem fsJ_12 (j : Fin 4) : fsJ j sFT = bFT := rfl
theorem fsJ_13 (j : Fin 4) : fsJ j sTop = bW (wIdx 1 j) := rfl

/-! ## One circuit's factor -/

/-- **One circuit's factor on the evaluator's layout** (a conjunct of `R̂`, P3:3170-3178): from the gates' and the top's
words on circuit `j`'s word streams, the point on `0 … 2`, scratch that READS like the circuit program's entry, its heads
at `0` and its registers zero, the lifted circuit program leaves the factor `[termOk X W R⁺ R⁻]` in `qS 28` and every
other register, every head and every unwritten stream as it found them; the written scratch reads `false` past the
entry lengths. -/
theorem circJ_spec (cap : ℕ) (Pl : FlatListParams) (el : Pl.FlatSeed) {n : ℕ} (G : List (NormalizedThresholdGate n))
    (c u v : BitInput n) (W : List Bool) (j : Fin 4) (ω : BS)
    (hG : ω.st (bW (wIdx 0 j)) = gatesW (tabH G) G) (hTop : ω.st (bW (wIdx 1 j)) = frame W)
    (hC : ω.st bC = frameP (List.ofFn c) ++ [false]) (hU : ω.st bU = frameP (List.ofFn u) ++ [false])
    (hV : ω.st bV = frameP (List.ofFn v) ++ [false])
    (hpos : RdEq (ω.st bPos) (frameP (binary (tabH G) 0) ++ [false]))
    (hneg : RdEq (ω.st bNeg) (frameP (binary (tabH G) 0) ++ [false]))
    (hX : RdEq (ω.st bX) []) (hZ : RdEq (ω.st bZ) []) (hSp : RdEq (ω.st bSp) [true]) (hSm : RdEq (ω.st bSm) [])
    (hT5 : RdEq (ω.st bT5) (levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false)))
    (hSS : RdEq (ω.st bSS) []) (hFT : RdEq (ω.st bFT) (flatTable Pl el G.length))
    (hsh : ∀ i, ω.sh (fsJ j i) = 0) (hr : ∀ q : Fin 32, q.val < 29 → ω.val (qS q) = 0)
    (hcap : CircCap cap Pl el n G W.length) :
    ∃ τ, WExec cap (circJ j) ω τ (costA (tabH G) n G.length Pl el + 1 + costB G.length Pl el W.length) ∧
      τ.val = Function.update ω.val (qS 28) (termOk (cornerWord (G.map NormalizedThresholdGate.eval) c u v) W
        (flatReportFast Pl el (popBits true (cornerWord (G.map NormalizedThresholdGate.eval) c u v)))
        (flatReportFast Pl el (popBits false (cornerWord (G.map NormalizedThresholdGate.eval) c u v)))).toNat ∧
      τ.sh = ω.sh ∧
      (∀ i, i ≠ bPos → i ≠ bNeg → i ≠ bX → i ≠ bZ → i ≠ bT5 → i ≠ bSS → τ.st i = ω.st i) ∧
      (∀ p, 2 * tabH G ≤ p → readTapeBit (τ.st bPos) p = false) ∧
      (∀ p, 2 * tabH G ≤ p → readTapeBit (τ.st bNeg) p = false) ∧
      (∀ p, 8 * G.length ≤ p → readTapeBit (τ.st bX) p = false) ∧ RdEq (τ.st bZ) [] ∧ RdEq (τ.st bSS) [] ∧
      (∀ p, (levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false)).length ≤ p →
        readTapeBit (τ.st bT5) p = false) := by
  obtain ⟨T5, hT5d⟩ : ∃ y, y = levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false) :=
    ⟨_, rfl⟩
  rw [← hT5d] at hT5 ⊢
  obtain ⟨ωs, hωs⟩ : ∃ y : BS, y = ⟨ω.sh, idealSt ω.st (tabH G) G.length T5 (flatTable Pl el G.length), ω.val,
      ω.cell⟩ := ⟨_, rfl⟩
  have hsim : SimW ωs ω := by
    subst hωs
    refine ⟨rfl, rfl, rfl, fun i => ?_⟩
    show RdEq (idealSt ω.st _ _ _ _ i) (ω.st i)
    unfold idealSt
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
    · rw [show i = bPos from Fin.ext h1]; exact hpos.symm
    · rw [show i = bNeg from Fin.ext h2]; exact hneg.symm
    · rw [show i = bX from Fin.ext h3]; exact (rdEq_blank _ (blank_rep _)).trans hX.symm
    · rw [show i = bZ from Fin.ext h4]; exact (rdEq_blank _ (blank_rep _)).trans hZ.symm
    · rw [show i = bSp from Fin.ext h5]; exact hSp.symm
    · rw [show i = bSm from Fin.ext h6]; exact hSm.symm
    · rw [show i = bT5 from Fin.ext h7]; exact hT5.symm
    · rw [show i = bSS from Fin.ext h8]; exact hSS.symm
    · rw [show i = bFT from Fin.ext h9]; exact hFT.symm
    · exact RdEq.refl _
  obtain ⟨x, hx⟩ : ∃ y : SS, y = ⟨fun i => ωs.sh (fsJ j i), fun i => ωs.st (fsJ j i), fun q => ωs.val (qS q),
      ωs.cell⟩ := ⟨_, rfl⟩
  have hL : LiftW (fsJ j) qS ωs x := by subst hx; exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  have hxst : ∀ i, x.st i = idealSt ω.st (tabH G) G.length T5 (flatTable Pl el G.length) (fsJ j i) := by
    intro i; subst hx; subst hωs; rfl
  have hlow : ∀ i : Fin 14, (fsJ j i).val < 19 → x.st i = ω.st (fsJ j i) := fun i hi => by
    rw [hxst, idealSt_low _ _ _ _ _ _ hi]
  obtain ⟨ω1, e1, k1, z1, w1, h1, x1, ⟨A, B, p1, n1⟩, zz1, ss1, ⟨rowsF, hrF, t51⟩, o1⟩ :=
    circS_spec cap Pl el G c u v W x
      (by rw [hlow sG (bW_lt _), fsJ_0]; exact hG) (by rw [hlow sC (by rw [fsJ_1]; decide), fsJ_1]; exact hC)
      (by rw [hlow sU (by rw [fsJ_2]; decide), fsJ_2]; exact hU) (by rw [hlow sV (by rw [fsJ_3]; decide), fsJ_3]; exact hV)
      (by rw [hxst, fsJ_4]; rfl) (by rw [hxst, fsJ_5]; rfl) (by rw [hxst, fsJ_6]; rfl) (by rw [hxst, fsJ_7]; rfl)
      (by rw [hxst, fsJ_8]; rfl) (by rw [hxst, fsJ_9]; rfl) (by rw [hxst, fsJ_10, hT5d]; rfl)
      (by rw [hxst, fsJ_11]; rfl) (by rw [hxst, fsJ_12]; rfl)
      (by rw [hlow sTop (bW_lt _), fsJ_13]; exact hTop)
      (fun i => by subst hx; subst hωs; exact hsh i) (fun q hq => by subst hx; subst hωs; exact hr q hq) hcap
  obtain ⟨τs, eS, hLS, hOS⟩ := WExec.liftW cap cap le_rfl (fsJ j) (fsJ_inj j) qS qS_inj e1 ωs hL
  obtain ⟨τ, eT, hST⟩ := wexec_sim eS ω hsim
  have hωv : ωs.val = ω.val := by subst hωs; rfl
  have hωh : ωs.sh = ω.sh := by subst hωs; rfl
  have hxv : ∀ q, x.val q = ω.val (qS q) := fun q => by subst hx; rw [hωv]
  have rd : ∀ i : Fin 14, ∀ p, readTapeBit (τ.st (fsJ j i)) p = readTapeBit (ω1.st i) p := fun i p => by
    rw [← hST.st (fsJ j i) p, hLS.st i]
  refine ⟨τ, eT, ?_, ?_, fun i n1' n2' n3' n4' n5' n6' => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_,
    fun p => ?_, fun p => ?_, fun p hp => ?_⟩
  · rw [hST.val]
    funext r
    by_cases hr' : ∃ q, qS q = r
    · obtain ⟨q, rfl⟩ := hr'
      rw [hLS.val q]
      by_cases h28 : q = 28
      · subst h28; rw [Function.update_self]; exact k1
      · rw [Function.update_of_ne (fun e => h28 (qS_inj e))]
        have hq28 : q.val ≠ 28 := fun e => h28 (Fin.ext e)
        by_cases hlt : q.val < 28
        · rw [z1 q hlt, hr q (by omega)]
        · rw [w1 q (by omega), hxv]
    · simp only [not_exists] at hr'
      rw [(hOS.2 r hr'), hωv, Function.update_of_ne (fun e => hr' 28 e.symm)]
  · rw [hST.sh]
    funext i
    by_cases hi : ∃ i', fsJ j i' = i
    · obtain ⟨i', rfl⟩ := hi
      rw [hLS.sh i', h1 i', hsh i']
    · simp only [not_exists] at hi
      rw [(hOS.1 i hi).1, hωh]
  · refine wr_keep eT i (namesW_liftW (fsJ j) qS i circS (fun i' e => circS_writes i' ?_))
    intro hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact n1' e.symm
    · exact n2' e.symm
    · exact n3' e.symm
    · exact n4' e.symm
    · exact n5' e.symm
    · exact n6' e.symm
  · rw [← fsJ_4 j, rd, p1]
    exact read_app_false _ _ (by rw [frameP_length, binary_length']; omega)
  · rw [← fsJ_5 j, rd, n1]
    exact read_app_false _ _ (by rw [frameP_length, binary_length']; omega)
  · rw [← fsJ_6 j, rd, x1]
    exact read_app_false _ _ (by rw [frameP_length, cornerWord_length, List.length_map]; omega)
  · rw [← fsJ_7 j, rd, zz1]
    exact rdEq_blank _ (blank_rep _) p
  · rw [← fsJ_11 j, rd, ss1]
    exact rdEq_blank _ (fun b hb => by
      rcases List.mem_append.1 hb with h | h <;> exact (List.mem_replicate.1 h).2) p
  · rw [← fsJ_10 j, rd, t51]
    refine read_ge _ _ ?_
    rw [Maj.lw_len _ _ _ _ _ hrF]
    rw [hT5d] at hp
    exact hp

end NearCubicWires.WireExponent3_5.PrimT.S3
