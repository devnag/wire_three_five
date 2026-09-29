import Proof.Wire_3_5.Primitive.SeedFix.S3Big6

/-! # S3, part 13: a guarded circuit step at one list seed, at the call's words

`R̂_{e'}(c,u,v) = ⋀_{j<a} [termOk …]` over the tuple's `a ≤ 4` circuits (P3:3170-3178, `rhat4`: slot `j ≥ a` is
`true`). The evaluator counts the tuple down in `qAc` and runs circuit `j`'s step only while `qAc ≠ 0` (**`guardJ`**).
At the call's words and numbers (`symWords`, `symNums`) and table offsets `off` (**`BodyInv`**), **`guardJ_spec`**:
the running product times `circAt j` (the slot's factor at the seed `seedOf k i`), `qAc` counted down, circuit `j`'s
table offset advanced by `λ_j` (if `j < a`), every other register and head as found, the scratch blank again.

Also: the cost of the circuit program does not depend on the list seed (`majBound_seed`, `costA_seed`, `costB_seed`:
the seed enters only through the flat table's length, `flatTable_len`), and the call words' and numbers' values by
kind (`words_0 … words_3`, `nums_0 … nums_3`).

Paper quantity of the main type: `R̂`'s running product times the slot's factor `circAt j` at the seed. -/

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
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall)

/-! ## The seed does not change the circuit program's cost -/

theorem majBound_seed (P : FlatListParams) (e e' : P.FlatSeed) (L : ℕ) : Maj.majBound P e L = Maj.majBound P e' L := by
  unfold Maj.majBound Maj.sBodyBound
  rw [flatTable_len, flatTable_len]

theorem costA_seed (h n g : ℕ) (P : FlatListParams) (e e' : P.FlatSeed) : costA h n g P e = costA h n g P e' := by
  unfold costA
  rw [majBound_seed P e e' g]

theorem costB_seed (g : ℕ) (P : FlatListParams) (e e' : P.FlatSeed) (W : ℕ) : costB g P e W = costB g P e' W := by
  unfold costB
  rw [majBound_seed P e e' g]

theorem tabLen_eq (k : SymCall) (j : Fin 4) (el : k.Pl.FlatSeed) :
    (flatTable k.Pl el (gatesJ k j).length).length = tabLen k j := by
  unfold tabLen
  rw [flatTable_len, flatTable_len]

/-! ## The call words and numbers by kind -/

theorem words_0 (k : SymCall) (j : Fin 4) : symWords k (wIdx 0 j) = gatesW (tabH (gatesJ k j)) (gatesJ k j) := by
  rw [symWords_idx]; rfl
theorem words_1 (k : SymCall) (j : Fin 4) : symWords k (wIdx 1 j) = frame (topJ k j) := by
  rw [symWords_idx]; rfl
theorem words_2 (k : SymCall) (j : Fin 4) : symWords k (wIdx 2 j) = tablesJ k j := by
  rw [symWords_idx]; rfl
theorem words_3 (k : SymCall) (j : Fin 4) : symWords k (wIdx 3 j) = templJ k j := by
  rw [symWords_idx]; rfl
theorem nums_0 (k : SymCall) (j : Fin 4) : symNums k (nIdx 0 j) = (gatesJ k j).length := by
  rw [symNums_idx]; rfl
theorem nums_1 (k : SymCall) (j : Fin 4) : symNums k (nIdx 1 j) = tabH (gatesJ k j) := by
  rw [symNums_idx]; rfl
theorem nums_2 (k : SymCall) (j : Fin 4) : symNums k (nIdx 2 j) = tabLen k j := by
  rw [symNums_idx]; rfl
theorem nums_3 (k : SymCall) (j : Fin 4) : symNums k (nIdx 3 j) = (templJ k j).length := by
  rw [symNums_idx]; rfl

theorem wIdx_ne (t : Fin 4) (ht : t ≠ 2) (j j' : Fin 4) : wIdx t j ≠ wIdx 2 j' := fun h => by
  have e := congrArg Fin.val h
  have : t.val ≠ 2 := fun e' => ht (Fin.ext e')
  simp only [wIdx] at e
  omega

theorem bW_inj {w w' : Fin 16} (h : bW w = bW w') : w = w' := by
  have := congrArg Fin.val h
  simp only [bW] at this
  exact Fin.ext (by omega)

theorem wIdx2_inj {j j' : Fin 4} (h : wIdx 2 j = wIdx 2 j') : j = j' := by
  have := congrArg Fin.val h
  simp only [wIdx] at this
  exact Fin.ext (by omega)

theorem qOff_inj {j j' : Fin 4} (h : qOff j = qOff j') : j = j' := by
  have := congrArg Fin.val h
  simp only [qOff] at this
  exact Fin.ext (by omega)

/-! ## The body's invariant -/

/-- **The evaluator between circuit steps**, at the call's words and numbers, the point, the table offsets `off`:
the scratch blank at head `0`, the circuit and writer registers zero. -/
structure BodyInv (k : SymCall) (c eu ev : BitInput k.P.n) (off : Fin 4 → ℕ) (ω : BS) : Prop where
  words : ∀ w, ω.st (bW w) = symWords k w
  ptC : ω.st bC = frameP (List.ofFn c) ++ [false]
  ptU : ω.st bU = frameP (List.ofFn eu) ++ [false]
  ptV : ω.st bV = frameP (List.ofFn ev) ++ [false]
  nums : ∀ i, ω.val (qN i) = symNums k i
  sc : ∀ i : Fin 28, 19 ≤ i.val → RdEq (ω.st i) []
  scs : ∀ i : Fin 28, 19 ≤ i.val → ω.sh i = 0
  whead : ∀ w : Fin 16, (∀ j, w ≠ wIdx 2 j) → ω.sh (bW w) = 0
  thead : ∀ j, ω.sh (bW (wIdx 2 j)) = off j
  toff : ∀ j, ω.val (qOff j) = off j
  pth : ω.sh bC = 0 ∧ ω.sh bU = 0 ∧ ω.sh bV = 0
  hq : ∀ q : Fin 32, ω.val (qS q) = 0
  hct : ω.val qCt = 0
  htp : ω.val qTp = 0
  hbk : ω.val qBk = 0
  hsk : ω.val qSk = 0

theorem BodyInv.fsh {k : SymCall} {c eu ev : BitInput k.P.n} {off : Fin 4 → ℕ} {ω : BS}
    (hI : BodyInv k c eu ev off ω) (j : Fin 4) (i : Fin 14) : ω.sh (fsJ j i) = 0 := by
  fin_cases i
  · exact hI.whead _ (wIdx_ne 0 (by decide) j)
  · exact hI.pth.1
  · exact hI.pth.2.1
  · exact hI.pth.2.2
  · exact hI.scs bPos (by decide)
  · exact hI.scs bNeg (by decide)
  · exact hI.scs bX (by decide)
  · exact hI.scs bZ (by decide)
  · exact hI.scs bSp (by decide)
  · exact hI.scs bSm (by decide)
  · exact hI.scs bT5 (by decide)
  · exact hI.scs bSS (by decide)
  · exact hI.scs bFT (by decide)
  · exact hI.whead _ (wIdx_ne 1 (by decide) j)

/-! ## The guarded step -/

/-- **Circuit `j`'s guarded step**: while the tuple counter `qAc` is nonzero, the step, then count down. -/
def guardJ (j : Fin 4) : BM := .ifr qAc (.seq (stepJ j) (.dec qAc)) .skip

/-- The seed-free cost bound of circuit `j`'s guarded step (the list seed `0` stands for all, `costA_seed`). -/
def guardCost (k : SymCall) (j : Fin 4) : ℕ :=
  costA (tabH (gatesJ k j)) k.P.n (gatesJ k j).length k.Pl (seedOf k ⟨0, PrimAsm.Enum.card_flatSeed_pos k.Pl⟩) + 1 +
    costB (gatesJ k j).length k.Pl (seedOf k ⟨0, PrimAsm.Enum.card_flatSeed_pos k.Pl⟩) (topJ k j).length +
    200 * ((templJ k j).length + tabLen k j + tabH (gatesJ k j) + (gatesJ k j).length) + 104

/-- The table advance of circuit `j` at one seed (`λ_j` inside the tuple, `0` past it). -/
def adv (k : SymCall) (j : Fin 4) : ℕ := if j.val < k.a then tabLen k j else 0

theorem pt_ne_bW {i : Fin 28} (hi : i.val < 3) (w : Fin 16) : i ≠ bW w := fun h => by
  have := congrArg Fin.val h
  simp only [bW] at this
  omega

theorem qS_ne_hi (q : Fin 32) {r : Fin 67} (hr : 51 ≤ r.val) : qS q ≠ r := fun h => by
  have := congrArg Fin.val h
  simp only [qS] at this
  omega

theorem guardJ_spec (cap : ℕ) (k : SymCall) (c eu ev : BitInput k.P.n) (i : Fin (Fintype.card k.Pl.FlatSeed))
    (j : Fin 4) (off : Fin 4 → ℕ) (ω : BS) (hI : BodyInv k c eu ev off ω)
    (hoff : j.val < k.a → off j = i.val * tabLen k j) (hac : ω.val qAc = k.a - j.val) (hrh : ω.val qRh ≤ 1)
    (hcap : j.val < k.a → CircCap cap k.Pl (seedOf k i) k.P.n (gatesJ k j) (topJ k j).length)
    (c1 : (templJ k j).length ≤ cap) (c2 : (i.val + 1) * tabLen k j ≤ cap) (c4 : 4 ≤ cap) :
    ∃ τ, WExec cap (guardJ j) ω τ (guardCost k j) ∧ BodyInv k c eu ev (Function.update off j (off j + adv k j)) τ ∧
      τ.val qRh = ω.val qRh * (circAt k (seedOf k i) c eu ev j).toNat ∧ τ.val qAc = k.a - (j.val + 1) ∧
      (∀ r, r ≠ qRh → r ≠ qAc → r ≠ qOff j → τ.val r = ω.val r) ∧ τ.sh = Function.update ω.sh (bW (wIdx 2 j))
        (ω.sh (bW (wIdx 2 j)) + adv k j) ∧ (∀ i : Fin 28, i.val < 19 → τ.st i = ω.st i) := by
  by_cases hj : j.val < k.a
  · have hadv : adv k j = tabLen k j := by unfold adv; rw [if_pos hj]
    have hcirc : circAt k (seedOf k i) c eu ev j =
        termOk (cornerWord ((gatesJ k j).map NormalizedThresholdGate.eval) c eu ev) (topJ k j)
          (flatReportFast k.Pl (seedOf k i) (popBits true (cornerWord ((gatesJ k j).map NormalizedThresholdGate.eval)
            c eu ev)))
          (flatReportFast k.Pl (seedOf k i) (popBits false (cornerWord ((gatesJ k j).map NormalizedThresholdGate.eval)
            c eu ev))) := by
      unfold circAt; rw [if_pos hj]
    have hTL := tabLen_eq k j (seedOf k i)
    have hTm : (templJ k j).length =
        (levelWord k.Pl.M k.Pl.base.J k.Pl.base.W (fun _ => List.replicate (gatesJ k j).length false)).length := rfl
    have hoj : off j = i.val * tabLen k j := hoff hj
    obtain ⟨τ1, e1, v1, sh1, lo1, sc1⟩ := stepJ_spec cap k.Pl (seedOf k i) (gatesJ k j) c eu ev (topJ k j) j ω
      (by rw [hI.words, words_0]) (by rw [hI.words, words_1]) (by rw [hI.words, words_3]; rfl) hI.ptC hI.ptU hI.ptV
      (fun p hp => by
        rw [hI.words, words_2, hI.thead, hoj]
        rw [hTL] at hp
        exact tables_read k j i p hp)
      (by rw [hI.nums, nums_0]) (by rw [hI.nums, nums_1]) (by rw [hI.nums, nums_2, hTL])
      (by rw [hI.nums, nums_3]; rfl) hI.sc hI.scs (hI.fsh j) (hI.whead _ (wIdx_ne 3 (by decide) j)) hI.hq hI.hct
      hI.htp hI.hbk hI.hsk hrh (hcap hj) (by rw [← hTm]; exact c1)
      (by rw [hI.toff, hoj, hTL]; rw [Nat.succ_mul] at c2; exact c2)
    rw [← hcirc, hTL] at v1
    rw [hTL] at sh1
    have hac1 : τ1.val qAc = k.a - j.val := by
      rw [v1, Function.update_of_ne (by decide), Function.update_of_ne (ne_qOff j (by decide)), hac]
    have hka := k.ha
    have e2 := WExec.dec (cap := cap) qAc τ1 (by rw [hac1]; omega)
    obtain ⟨τ2, hτ2⟩ : ∃ y, y = τ1.setv qAc (τ1.val qAc - 1) := ⟨_, rfl⟩
    rw [← hτ2] at e2
    have hne : ω.val qAc ≠ 0 := by rw [hac]; omega
    have ex := WExec.ifrT (Q := WM.skip) hne (WExec.seq e1 e2)
    have v2 : ∀ r, r ≠ qAc → τ2.val r = τ1.val r := fun r hr => by
      rw [hτ2, WState.setv_val, Function.update_of_ne hr]
    have sh2 : τ2.sh = τ1.sh := by rw [hτ2]; rfl
    have st2 : τ2.st = τ1.st := by rw [hτ2]; rfl
    have v21 : ∀ r, r ≠ qAc → r ≠ qRh → r ≠ qOff j → τ2.val r = ω.val r := fun r h1 h2 h3 => by
      rw [v2 r h1, v1, Function.update_of_ne h2, Function.update_of_ne h3]
    have tsh : ∀ i, i ≠ bW (wIdx 2 j) → τ2.sh i = ω.sh i := fun i hi => by
      rw [sh2, sh1, Function.update_of_ne hi]
    refine ⟨τ2, WExec.mono ex ?_, ⟨fun w => ?_, ?_, ?_, ?_, fun i' => ?_, fun i' hi' => ?_, fun i' hi' => ?_,
      fun w hw => ?_, fun j' => ?_, fun j' => ?_, ⟨?_, ?_, ?_⟩, fun q => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun r h1 h2 h3 => ?_,
      ?_, fun i' hi' => ?_⟩
    · rw [costA_seed _ _ _ k.Pl (seedOf k i) (seedOf k ⟨0, PrimAsm.Enum.card_flatSeed_pos k.Pl⟩),
        costB_seed _ k.Pl (seedOf k i) (seedOf k ⟨0, PrimAsm.Enum.card_flatSeed_pos k.Pl⟩), hTL, ← hTm]
      unfold guardCost
      omega
    · rw [st2, lo1 _ (bW_lt w)]; exact hI.words w
    · rw [st2, lo1 _ (by decide)]; exact hI.ptC
    · rw [st2, lo1 _ (by decide)]; exact hI.ptU
    · rw [st2, lo1 _ (by decide)]; exact hI.ptV
    · rw [v21 _ (qN_ne _ (by decide)) (qN_ne _ (by decide)) (ne_qOff j (by have := qN_lt i'; omega))]
      exact hI.nums i'
    · rw [st2]; exact sc1 i' hi'
    · rw [tsh _ (bW_ne _ hi').symm]; exact hI.scs i' hi'
    · rw [tsh _ (fun e => hw j (bW_inj e))]; exact hI.whead w hw
    · by_cases hjj : j' = j
      · subst hjj
        rw [sh2, sh1, Function.update_self, Function.update_self, hI.thead, hadv]
      · rw [tsh _ (fun e => hjj (wIdx2_inj (bW_inj e))), Function.update_of_ne hjj]
        exact hI.thead j'
    · rw [v2 _ (qOff_ne j' (by decide)), v1, Function.update_of_ne (qOff_ne j' (by decide))]
      by_cases hjj : j' = j
      · subst hjj
        rw [Function.update_self, Function.update_self, hI.toff, hadv]
      · rw [Function.update_of_ne (fun e => hjj (qOff_inj e)), Function.update_of_ne hjj]
        exact hI.toff j'
    · rw [tsh _ (pt_ne_bW (i := bC) (by decide) _)]; exact hI.pth.1
    · rw [tsh _ (pt_ne_bW (i := bU) (by decide) _)]; exact hI.pth.2.1
    · rw [tsh _ (pt_ne_bW (i := bV) (by decide) _)]; exact hI.pth.2.2
    · rw [v21 _ (qS_ne_hi q (by decide)) (qS_ne_hi q (by decide)) (qS_ne_qOff q j)]; exact hI.hq q
    · rw [v21 _ (by decide) (by decide) (ne_qOff j (by decide))]; exact hI.hct
    · rw [v21 _ (by decide) (by decide) (ne_qOff j (by decide))]; exact hI.htp
    · rw [v21 _ (by decide) (by decide) (ne_qOff j (by decide))]; exact hI.hbk
    · rw [v21 _ (by decide) (by decide) (ne_qOff j (by decide))]; exact hI.hsk
    · rw [v2 _ (by decide), v1, Function.update_self]
    · rw [hτ2, WState.setv_val, Function.update_self, hac1]; omega
    · exact v21 r h2 h1 h3
    · rw [sh2, sh1, hadv]
    · rw [st2, lo1 i' hi']
  · have hadv : adv k j = 0 := by unfold adv; rw [if_neg hj]
    have hcirc : circAt k (seedOf k i) c eu ev j = true := by unfold circAt; rw [if_neg hj]
    have hac0 : ω.val qAc = 0 := by rw [hac]; omega
    have ex := WExec.ifrF (P := WM.seq (stepJ j) (WM.dec qAc)) hac0 (WExec.skip (cap := cap) ω)
    have hoffe : Function.update off j (off j + adv k j) = off := by
      rw [hadv, Nat.add_zero, Function.update_eq_self]
    refine ⟨ω, WExec.mono ex (by unfold guardCost; omega), by rw [hoffe]; exact hI, by rw [hcirc]; simp, by omega,
      fun r _ _ _ => rfl, by
        rw [show ω.sh (bW (wIdx 2 j)) + adv k j = ω.sh (bW (wIdx 2 j)) by rw [hadv]; rfl, Function.update_eq_self],
      fun _ _ => rfl⟩

end NearCubicWires.WireExponent3_5.PrimT.S3
