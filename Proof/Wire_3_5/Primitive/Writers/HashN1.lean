import Proof.Wire_3_5.Primitive.Writers.ThrN4

/-! # HASH setup (A), part 1: the HASH numbers machine (`bigWTH`)

The HASH stage's free numbers are `Fp` on `hashX = {thrX with a := t}` (`FinalPass.HashFr.hashX`, the moment
count `t = thrCallT`, the data word's entry `12`). The THR numbers machine (`numsTW`) leaves `t` in `Hb 12`
(**`numsTH_spec`**, `numsT_spec` with that clause); **`aTW`** sets `a := t` (`dA ← Hb 12`) and **`bigWTH`** runs the
free program's words there (**`bigTH_spec`**, the twin of `bigT_spec` at `hashX`).

Paper quantity of the main type: the HASH stage's free numbers `h, Q', m, pr, ρ` at the HASH call's `FreeIn`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimT.C4Set (KB KB_val)

variable (cap : ℕ)

/-- **The THR call's numbers, run**, with the data word's entry `12` (the moment count `t`) kept in `Hb 12`
(`numsT_spec` verbatim plus that clause). -/
theorem numsTH_spec (cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w : List Bool)
    (codes cc : List ℕ) (tl : List Bool) (hs xs : List ℕ) (tg Kb : ℕ)
    (hw : w = Data.reqW P.n true codes cc tl) (hhs : hs.length = 16) (hxs : xs.length ≤ 2)
    (h0v : hs.getD 0 0 = xs.length) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb)
    (cW : 2 * w.length + 2 ≤ cap)
    (cP : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
      Kb + P.n + codes.length + 1 ≤ cap)
    (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (capT err g cu pS I Q : ℕ) (hT : hs.getD 1 0 = capT) (hg : hs.getD 2 0 = g) (hcu : hs.getD 4 0 = cu)
    (hp : hs.getD 6 0 = pS) (herr : err = fe * Nat.clog 2 (P.n + 2))
    (cT1 : 1 ≤ capT) (cT : capT * 32 + 2 ≤ cap) (cL : 2 * (P.n + 1) ^ 26 + 8 ≤ cap) (cE : err + 4 ≤ cap)
    (cSB : 2 ^ ((gP P.n capT err).seedBits + 1) ≤ cap)
    (cLB : (gP P.n capT err).labelBits + (gP P.n capT err).fieldBits + (gP P.n capT err).walkLen + 512 ≤ cap)
    (cB : 2 * (g * cu) + 2 ≤ cap)
    (hI : I = g * pS * 2 ^ (gP P.n capT err).seedBits * (2 * (g * cu) + 1) * (2 * (g * cu) + 1) + 1)
    (hQ : Q = 2 ^ ((P.s * (P.r / 2) * 5 + 3) / 2 / 2) * (I * 8192 * P.n * P.n)) (hn : 2 ≤ P.n)
    (cQ : 2 * Q ≤ cap) :
    ∃ τ co, WExec cap (numsTW cr fe) (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))) τ co ∧
      co ≤ numsTCost cap P.n codes.length cc.length Kb ∧
      τ.val dN = P.n ∧ τ.val dA = codes.length ∧ τ.val dNC = cc.length ∧ τ.val dMS = hs.getD 7 0 ∧
      τ.val (SGb 1) = Nat.clog 2 (P.n + 2) ∧ τ.val (SGb 3) = P.r ∧ τ.val (SGb 4) = P.s ∧ τ.val (SGb 5) = P.b ∧
      τ.val (SGb 6) = P.r / 2 ∧ τ.val (SGb 8) = P.s * (P.r / 2) ∧ τ.val (SGb 9) = P.k ∧ τ.val (SGb 10) = err ∧
      τ.val (Hb 13) = capT ∧ τ.val (G 21) = 2 ^ (gP P.n capT err).seedBits ∧ τ.val (G 41) = g ∧
      τ.val (G 52) = pS ∧ τ.val (KB 52) = Q ∧ (∀ q : Fin LNR, 64 ≤ q.val → q.val < 250 → τ.val q = 0) ∧
      τ.st = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))).st ∧
      (∀ s, s ≠ sk 0 113 → τ.sh s = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))).sh s) ∧
      τ.cell = false ∧ τ.val (Hb 12) = hs.getD 12 0 := by
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨τ1, c1, e1, c1le, v1N, v1A, v1NC, v1LEN, v1H, v1XA, v1XB, v1z, v1st, v1sh, v1cl⟩ :=
    p1T_spec cap w P.n codes cc tl hs xs tg Kb hw hhs hxs h0v hKb cW cP hcl hcs
  have z1 : ∀ r : Fin LNR, (r.val < 320 ∨ (327 < r.val ∧ r.val < 337) ∨ 371 < r.val) → τ1.val r = 0 :=
    fun r h => v1z r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hcl' : ∀ k, k < 16 → hs.getD k 0 ≤ cap := fun k hk => by
    have := hcl k; rwa [List.getD_append _ _ _ _ (by omega)] at this
  have hnc : P.n ≤ cap := by
    have : P.n + 1 ≤ (P.n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
    omega
  -- the star numbers
  have e2 := sT_spec cap cr fe P hrP τ1 v1N (fun i => z1 _ (by rw [SGb_val]; have := i.isLt; omega))
    (z1 _ (by rw [rv_xT]; omega)) hcS
  obtain ⟨τ2, g2⟩ : ∃ y, y = StarNums.starOut (τ1.setv (SGb 0) P.n) SGb P fe := ⟨_, rfl⟩
  rw [← g2] at e2
  have ⟨s1, s3, s4, s5, s6, _, s8, s9, s10⟩ := StarNums.starOut_val (τ1.setv (SGb 0) P.n) SGb P fe
  rw [← g2] at s1 s3 s4 s5 s6 s8 s9 s10
  have k2 : ∀ r : Fin LNR, (r.val < 250 ∨ 270 ≤ r.val) → τ2.val r = τ1.val r := fun r h => by
    have h' : ∀ i : Fin 20, SGb i ≠ r := fun i e => by
      have := congrArg Fin.val e; rw [SGb_val] at this; have := i.isLt; omega
    rw [g2, starOut_outside 0 _ P fe r h', WState.setv_val, Function.update_of_ne (h' 0).symm]
  have st2 : τ2.st = τ1.st ∧ τ2.sh = τ1.sh ∧ τ2.cell = τ1.cell := by rw [g2]; simp [StarNums.starOut]
  -- the THR cap, `Σ|X_j|`
  have e3 := hT_spec cap τ2 (hs.getD 13 0) capT (hs.getD 7 0)
    (by rw [k2 _ (by decide)]; exact v1H 13 (by decide))
    (by rw [k2 _ (by decide), ← hT]; exact v1H 1 (by decide))
    (by rw [k2 _ (by decide)]; exact v1H 7 (by decide))
    (by rw [k2 _ (by decide)]; exact z1 _ (by decide))
    (by rw [k2 _ (by decide)]; exact z1 _ (by decide))
    (hcl' 13 (by decide)) (by rw [← hT]; exact hcl' 1 (by decide)) (hcl' 7 (by decide))
  obtain ⟨τ3, g3⟩ : ∃ y, y = ((τ2.setv (Hb 13) 0).setv (Hb 13) capT).setv dMS (hs.getD 7 0) := ⟨_, rfl⟩
  rw [← g3] at e3
  have k3 : ∀ r : Fin LNR, r ≠ Hb 13 → r ≠ dMS → τ3.val r = τ2.val r := fun r a b => by
    rw [g3]; simp [Function.update_of_ne a, Function.update_of_ne b]
  have n13 : (Hb 13 : Fin LNR) ≠ dMS := by decide
  have v3T : τ3.val (Hb 13) = capT := by rw [g3]; simp [Function.update_of_ne n13]
  have v3M : τ3.val dMS = hs.getD 7 0 := by rw [g3]; simp
  have st3 : τ3.st = τ2.st ∧ τ3.sh = τ2.sh ∧ τ3.cell = τ2.cell := by rw [g3]; simp
  -- the THR filter's gap numbers
  have v3N : τ3.val dN = P.n := by rw [k3 _ (by decide) (by decide), k2 _ (by decide)]; exact v1N
  have v3E : τ3.val (SGb 10) = err := by rw [k3 _ (by decide) (by decide), herr]; exact s10
  have v3G : ∀ i, τ3.val (G i) = 0 := fun i => by
    rw [k3 _ (G_ne i (Hb 13) (by decide)).symm (G_ne i dMS (by decide)).symm, k2 _ (by rw [G_val]; omega)]
    exact z1 _ (by rw [G_val]; omega)
  have e4 := nAT_spec cap τ3 P.n capT err v3T v3N v3E v3G cT1 cT cL cE cSB cLB
  obtain ⟨τ4, g4⟩ : ∃ y, y = aOut 0 τ3 P.n capT err := ⟨_, rfl⟩
  rw [← g4] at e4
  have k4 : ∀ r : Fin LNR, (r.val < 408 ∨ 472 ≤ r.val) → τ4.val r = τ3.val r := fun r h => by
    rw [g4]; exact aOut_other τ3 P.n capT err r h
  have v4_21 : τ4.val (G 21) = 2 ^ (gP P.n capT err).seedBits := by rw [g4]; unfold aOut; simp
  have v4_41 : τ4.val (G 41) = 0 := by rw [g4]; unfold aOut; simp [Function.update_apply, v3G]
  have v4_52 : τ4.val (G 52) = 0 := by rw [g4]; unfold aOut; simp [Function.update_apply, v3G]
  have v4_63 : τ4.val (G 63) = 0 := by rw [g4]; unfold aOut; simp [Function.update_apply, v3G]
  have st4 : τ4.st = τ3.st ∧ τ4.sh = τ3.sh ∧ τ4.cell = τ3.cell := by rw [g4]; unfold aOut; simp
  -- `|𝒢|`, `Σp`
  have v4_2 : τ4.val (Hb 2) = g := by
    rw [k4 _ (by decide), k3 _ (by decide) (by decide), k2 _ (by decide), ← hg]; exact v1H 2 (by decide)
  have v4_6 : τ4.val (Hb 6) = pS := by
    rw [k4 _ (by decide), k3 _ (by decide) (by decide), k2 _ (by decide), ← hp]; exact v1H 6 (by decide)
  have e5 := gT_spec cap τ4 g pS v4_2 v4_6 v4_41 v4_52 v4_63 (by rw [← hg]; exact hcl' 2 (by decide))
    (by rw [← hp]; exact hcl' 6 (by decide))
  obtain ⟨τ5, g5⟩ : ∃ y, y = (τ4.setv (G 41) g).setv (G 52) pS := ⟨_, rfl⟩
  rw [← g5] at e5
  have k5 : ∀ r : Fin LNR, r ≠ G 41 → r ≠ G 52 → τ5.val r = τ4.val r := fun r a b => by
    rw [g5]; simp [Function.update_of_ne a, Function.update_of_ne b]
  have v5_41 : τ5.val (G 41) = g := by rw [g5]; simp [Function.update_apply]
  have v5_52 : τ5.val (G 52) = pS := by rw [g5]; simp [Function.update_apply]
  have st5 : τ5.st = τ4.st ∧ τ5.sh = τ4.sh ∧ τ5.cell = τ4.cell := by rw [g5]; simp
  -- `I`
  have e21' : τ5.val (G 21) = 2 ^ (gP P.n capT err).seedBits := by
    rw [k5 _ (by decide) (by decide)]; exact v4_21
  have e2' : τ5.val (Hb 2) = g := by rw [k5 _ (by decide) (by decide)]; exact v4_2
  have e6' : τ5.val (Hb 6) = pS := by rw [k5 _ (by decide) (by decide)]; exact v4_6
  have e4' : τ5.val (Hb 4) = cu := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide), k3 _ (by decide) (by decide), k2 _ (by decide), ← hcu]
    exact v1H 4 (by decide)
  have e8' : τ5.val (SGb 8) = P.s * (P.r / 2) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide), k3 _ (by decide) (by decide)]; exact s8
  have eN' : τ5.val dN = P.n := by rw [k5 _ (by decide) (by decide), k4 _ (by decide)]; exact v3N
  have hz5 : ∀ r : Fin LNR, 472 ≤ r.val → τ5.val r = 0 := fun r h => by
    rw [k5 r (fun e => by subst e; exact absurd h (by decide)) (fun e => by subst e; exact absurd h (by decide)),
      k4 r (Or.inr h), k3 r (fun e => by subst e; exact absurd h (by decide))
        (fun e => by subst e; exact absurd h (by decide)), k2 r (Or.inr (by omega))]
    exact z1 r (by omega)
  have hsb1 : 1 ≤ 2 ^ (gP P.n capT err).seedBits := Nat.one_le_two_pow
  have hsbc : 2 ^ (gP P.n capT err).seedBits ≤ cap := by
    have := pow_succ 2 (gP P.n capT err).seedBits; omega
  have hI1 : 1 ≤ I := by omega
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    qW_caps cap (P.s * (P.r / 2)) P.n I hn hI1 (by rw [← hQ]; exact cQ)
  have e6 := qI_spec cap τ5 g pS (2 ^ (gP P.n capT err).seedBits) cu (P.s * (P.r / 2)) P.n e2' e4' e6' e21' e8' eN'
    hz5 hsb1 (by rw [← hg]; exact hcl' 2 (by decide)) (by rw [← hp]; exact hcl' 6 (by decide))
    (by rw [← hcu]; exact hcl' 4 (by decide)) hsbc q9 hnc cB (by rw [← hI]; exact q8)
  obtain ⟨τ6, g6⟩ : ∃ y, y = qIOut τ5 g pS (2 ^ (gP P.n capT err).seedBits) cu (P.s * (P.r / 2)) P.n := ⟨_, rfl⟩
  rw [← g6] at e6
  -- `Q`
  have e7 := SymQM.qW_spec cap qS τ6 I (P.s * (P.r / 2)) P.n
    (by rw [g6, qIOut_q0, hI]) (by rw [g6, qIOut_q1]) (by rw [g6, qIOut_q2])
    (fun i hi => by rw [g6, qIOut_qS _ _ _ _ _ _ _ i hi]; exact hz5 _ (by rw [qS_val]; omega))
    q1 q2 q3 q4 q5 q6 q7
  rw [← hQ] at e7
  have e8 := copy1 cap (qS 3) (KB 52) tqT (by decide) (by decide) (by decide) Q (τ6.setv (qS 3) Q) (by simp)
    (by
      rw [WState.setv_val, Function.update_of_ne (show (KB 52 : Fin LNR) ≠ qS 3 by decide), g6,
        qIOut_low _ _ _ _ _ _ _ _ (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
        k3 _ (by decide) (by decide), k2 _ (by decide)]
      exact z1 _ (by decide))
    (by
      rw [WState.setv_val, Function.update_of_ne (show tqT ≠ qS 3 by decide), g6, qIOut_tqT]
      exact hz5 _ (by decide))
    (by omega)
  obtain ⟨τ8, g8⟩ : ∃ y, y = (τ6.setv (qS 3) Q).setv (KB 52) Q := ⟨_, rfl⟩
  rw [← g8] at e8
  have k8 : ∀ r : Fin LNR, r ≠ KB 52 → r ≠ qS 3 → r.val < 472 → τ8.val r = τ5.val r := fun r a b c => by
    rw [g8, WState.setv_val, Function.update_of_ne a, WState.setv_val, Function.update_of_ne b, g6,
      qIOut_low _ _ _ _ _ _ _ _ c]
  have st8 : τ8.st = τ5.st ∧ τ8.sh = τ5.sh ∧ τ8.cell = τ5.cell := by
    have := qIOut_st τ5 g pS (2 ^ (gP P.n capT err).seedBits) cu (P.s * (P.r / 2)) P.n
    rw [g8, g6]; simpa using this
  refine ⟨τ8, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8)))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · unfold numsTCost; omega
  · rw [k8 _ (by decide) (by decide) (by decide)]; exact eN'
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide), k2 _ (by decide)]; exact v1A
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide), k2 _ (by decide)]; exact v1NC
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide)]; exact v3M
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide)]; exact s1
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide)]; exact s3
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide)]; exact s4
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide)]; exact s5
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide)]; exact s6
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide)]; exact s8
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide)]; exact s9
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide), herr]; exact s10
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide)]; exact v3T
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide)]; exact v4_21
  · rw [k8 _ (by decide) (by decide) (by decide)]; exact v5_41
  · rw [k8 _ (by decide) (by decide) (by decide)]; exact v5_52
  · rw [g8]; simp
  · intro q h1 h2
    rw [k8 q (fun e => by subst e; exact absurd h1 (by decide)) (fun e => by subst e; exact absurd h2 (by decide))
        (by omega),
      k5 q (fun e => by subst e; exact absurd h2 (by decide)) (fun e => by subst e; exact absurd h2 (by decide)),
      k4 q (Or.inl (by omega)),
      k3 q (fun e => by subst e; exact absurd h2 (by decide)) (fun e => by subst e; exact absurd h2 (by decide)),
      k2 q (Or.inl h2)]
    exact z1 q (Or.inl (by omega))
  · rw [st8.1, st5.1, st4.1, st3.1, st2.1, v1st]
  · intro s hs; rw [st8.2.1, st5.2.1, st4.2.1, st3.2.1, st2.2.1, v1sh s hs]
  · rw [st8.2.2, st5.2.2, st4.2.2, st3.2.2, st2.2.2, v1cl]
  · rw [k8 _ (by decide) (by decide) (by decide), k5 _ (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide), k2 _ (by decide)]; exact v1H 12 (by decide)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
