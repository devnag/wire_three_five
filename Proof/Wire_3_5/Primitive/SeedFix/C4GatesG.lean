import Proof.Wire_3_5.Primitive.SeedFix.C4GatesP

/-! # G1, the gate converter, part 3: copying words between the converter's streams (P3:1655-1664)

A gate's native word is `natWord n`, the weights' `intWord`s, then `intWord (θ − 1)` (`tabGW`), while the table has
`−θ`'s pair first: the converter writes the threshold's word on its own scratch `TS` and copies it after the
weights. This part is the copy loop (`copyL`: `k` cells from a stream, each re-encoded by `m`), with
* **`copyNQ_spec`**: the arity's word `marks (natWord n)` (kept on `NQ`) copied framed: `quad (natWord n)`;
* **`copyTS_spec`**: the last threshold word copied from `TS`.

Paper quantity of the main types: the native words `natWord n` (the arity field of every pool gate) and
`intWord (θ − 1)` copied into the gate's native word. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Gates
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

theorem marks_marks (x : List Bool) : Streaming.marks (Streaming.marks x) = quad x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [Streaming.marks, List.flatMap_cons] at ih ⊢
    rw [quad_cons, ← ih]
    rfl

/-! ## The copy loop -/

section Copy
variable (cap : ℕ) (src O : Fin 12) (OP r : Fin 20) (m : Bool → List Bool)

/-- Copy `r` cells of `src` onto `O`, each cell `b` as `m b`. -/
def copyL : CW := .whr r (.seq (.dec r) (.seq (.ifs src (PrimAsm.Emit.emitW O OP (m true))
  (PrimAsm.Emit.emitW O OP (m false))) (.fwd src)))

variable (hsO : src ≠ O) (hOr : OP ≠ r)
variable (hm : ∀ b, (m b).length ≤ 2)

include hsO hOr hm in
theorem copyL_spec : ∀ (sfx pre rest : List Bool) (σ : CS),
    σ.st src = pre ++ (sfx ++ rest) → σ.sh src = pre.length → σ.val r = sfx.length →
    σ.sh O = (σ.st O).length → σ.val OP + 2 * sfx.length ≤ cap → sfx.length ≤ cap →
    WExec cap (copyL src O OP r m) σ
      (((PrimAsm.WriteNat.appendO σ O OP (sfx.flatMap m)).seth src (pre.length + sfx.length)).setv r 0)
      (23 * sfx.length + 1)
  | [], pre, rest, σ, _, hsh, hr, _, _, _ => by
    have e : ((PrimAsm.WriteNat.appendO σ O OP (([] : List Bool).flatMap m)).seth src
        (pre.length + ([] : List Bool).length)).setv r 0 = σ := by
      simp only [List.flatMap_nil, PrimAsm.WriteNat.appendO_nil, List.length_nil, Nat.add_zero]
      rw [← hsh, wseth_same, show (0 : ℕ) = σ.val r by simpa using hr.symm, wsetv_same]
    rw [e]; exact WExec.whrF (by simpa using hr)
  | b :: sfx, pre, rest, σ, hst, hsh, hr, hO, hc, hk => by
    simp only [List.length_cons] at hr hc hk
    have s1 := WExec.dec (cap := cap) r σ (by omega)
    set σ1 := σ.setv r (σ.val r - 1) with hσ1
    have hb : wbit σ1 src = b := by
      simp only [wbit, σ1, WState.setv_st, WState.setv_sh, hst, hsh]
      have := rd_shift pre (b :: sfx ++ rest) 0
      simp only [Nat.add_zero] at this; rw [this]; rfl
    have hmb := hm b
    have s2 : WExec cap (.ifs src (PrimAsm.Emit.emitW O OP (m true)) (PrimAsm.Emit.emitW O OP (m false))) σ1
        (PrimAsm.WriteNat.appendO σ1 O OP (m b)) 17 := by
      have e := PrimAsm.Emit.emitW_spec cap O OP (m b) σ1 (by simp [σ1, hO])
        (by simp [σ1, Function.update_apply, hOr]; omega)
      cases b
      · exact WExec.mono (WExec.ifsF hb e) (by omega)
      · exact WExec.mono (WExec.ifsT hb e) (by omega)
    have s3 := WExec.fwd (cap := cap) src (PrimAsm.WriteNat.appendO σ1 O OP (m b))
    set σ3 := (PrimAsm.WriteNat.appendO σ1 O OP (m b)).seth src ((PrimAsm.WriteNat.appendO σ1 O OP (m b)).sh src + 1)
      with hσ3
    have s4 := copyL_spec sfx (pre ++ [b]) rest σ3
      (by simp [σ3, σ1, Function.update_apply, hsO, hst])
      (by simp [σ3, σ1, Function.update_apply, hsO, hsh])
      (by simp [σ3, σ1, Function.update_apply, hOr.symm, hr])
      (by simp [σ3, σ1, Function.update_apply, hsO.symm, hO])
      (by simp [σ3, σ1, Function.update_apply, hOr]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2 s3)) s4) ?_
      (by simp only [List.length_cons]; omega)
    simp only [σ3, σ1]
    rw [appendO_seth O _ src _ _ hsO, PrimAsm.WriteNat.appendO_append, PrimAsm.WriteNat.appendO_setv _ O OP r hOr.symm]
    apply WState.eq
    · funext i; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
      by_cases h1 : i = src
      · subst h1; simp [hsO]; omega
      · simp [h1]
    · rfl
    · funext q; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
      by_cases h1 : q = r
      · subst h1; simp [hOr.symm]
      · simp [h1]
    · rfl

end Copy

/-! ## The arity word and the threshold word -/

/-- Copy the arity's word `marks (natWord n)` (on `NQ`, length in `rOq`) onto `S`, framed once more. -/
def copyNQ : CW :=
  .seq (FinalPass.Hash4.wcopyR rOq rX rT) (.seq (copyL sNQ sS rOs rX (fun b => [true, b]))
    (.seq (FinalPass.Hash4.wcopyR rOq rX rT) (rewW sNQ rX)))

theorem copyNQ_spec (cap : ℕ) (x : List Bool) (σ : CS) (hst : σ.st sNQ = x) (hsh : σ.sh sNQ = 0)
    (hq : σ.val rOq = x.length) (hX : σ.val rX = 0) (hT : σ.val rT = 0) (hO : σ.sh sS = (σ.st sS).length)
    (hc : σ.val rOs + 2 * x.length ≤ cap) (hc2 : x.length ≤ cap) :
    WExec cap copyNQ σ (PrimAsm.WriteNat.appendO σ sS rOs (Streaming.marks x)) (70 * x.length + 20) := by
  have s1 := FinalPass.Hash4.wcopyR_spec cap rOq rX rT (by decide) (by decide) (by decide) σ hX hT (by omega)
  rw [hq] at s1
  have s2 := copyL_spec cap sNQ sS rOs rX (fun b => [true, b]) (by decide) (by decide) (fun b => by simp) x [] []
    (σ.setv rX x.length) (by simp [hst]) (by simp [hsh]) (by simp) (by simp [hO])
    (by simp +decide [Function.update_apply]; omega) hc2
  set σ2 := ((PrimAsm.WriteNat.appendO (σ.setv rX x.length) sS rOs (x.flatMap fun b => [true, b])).seth sNQ
    (([] : List Bool).length + x.length)).setv rX 0 with hσ2
  have s3 := FinalPass.Hash4.wcopyR_spec cap rOq rX rT (by decide) (by decide) (by decide) σ2 (by simp [σ2])
    (by simp +decide [σ2, Function.update_apply, hT]) (by simp +decide [σ2, Function.update_apply, hq]; omega)
  have hq2 : σ2.val rOq = x.length := by simp +decide [σ2, Function.update_apply, hq]
  rw [hq2] at s3
  have s4 := rewW_spec cap sNQ rX x.length (σ2.setv rX x.length) (by simp) (by simp [σ2]) hc2
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (by omega)
  simp only [σ2]
  rw [PrimAsm.WriteNat.appendO_setv _ sS rOs rX (by decide)]
  apply WState.eq
  · funext i; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
    by_cases h1 : i = sNQ
    · subst h1; simp +decide [hsh]
    · by_cases h2 : i = sS
      · subst h2; simp +decide; omega
      · simp [h1, h2]
  · rfl
  · funext q; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
    by_cases h1 : q = rX
    · subst h1; simp +decide [hX]
    · by_cases h2 : q = rOs
      · subst h2; simp +decide; omega
      · simp [h1, h2]
  · rfl

/-- Copy the last `rOt` cells of `TS` (the threshold's word) onto `S`. -/
def copyTS : CW :=
  .seq (FinalPass.Hash4.wcopyR rOt rX rT) (.seq (rewW sTS rX) (copyL sTS sS rOs rOt (fun b => [b])))

theorem flatMap_single (x : List Bool) : x.flatMap (fun b => [b]) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [ih]

theorem copyTS_spec (cap : ℕ) (y wt : List Bool) (σ : CS) (hst : σ.st sTS = y ++ wt)
    (hsh : σ.sh sTS = y.length + wt.length) (ht : σ.val rOt = wt.length) (hX : σ.val rX = 0) (hT : σ.val rT = 0)
    (hO : σ.sh sS = (σ.st sS).length) (hc : σ.val rOs + 2 * wt.length ≤ cap) (hc2 : wt.length ≤ cap) :
    WExec cap copyTS σ ((PrimAsm.WriteNat.appendO σ sS rOs wt).setv rOt 0) (50 * wt.length + 20) := by
  have s1 := FinalPass.Hash4.wcopyR_spec cap rOt rX rT (by decide) (by decide) (by decide) σ hX hT (by omega)
  rw [ht] at s1
  have s2 := rewW_spec cap sTS rX wt.length (σ.setv rX wt.length) (by simp) (by simp [hsh]) hc2
  set σ2 := ((σ.setv rX wt.length).seth sTS ((σ.setv rX wt.length).sh sTS - wt.length)).setv rX 0 with hσ2
  have s3 := copyL_spec cap sTS sS rOs rOt (fun b => [b]) (by decide) (by decide) (fun b => by simp) wt y [] σ2
    (by simp [σ2, hst]) (by simp [σ2, hsh]) (by simp +decide [σ2, Function.update_apply, ht])
    (by simp +decide [σ2, Function.update_apply, hO]) (by simp +decide [σ2, Function.update_apply]; omega) hc2
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by omega)
  rw [flatMap_single]
  simp only [σ2]
  rw [PrimAsm.WriteNat.appendO_setv _ sS rOs rX (by decide), appendO_seth sS _ sTS _ _ (by decide),
    PrimAsm.WriteNat.appendO_setv _ sS rOs rX (by decide)]
  apply WState.eq
  · funext i; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
    by_cases h1 : i = sTS
    · subst h1; simp +decide [hsh]
    · by_cases h2 : i = sS
      · subst h2; simp +decide
      · simp [h1, h2]
  · rfl
  · funext q; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
    by_cases h1 : q = rOt
    · subst h1; simp
    · by_cases h2 : q = rX
      · subst h2; simp +decide [hX]
      · simp [h1, h2]
  · rfl

/-! ## The weights of a gate -/

/-- The weight loop: `K` weights' pairs. -/
def wLoop (T : Fin 12) : CW := .whr rK (.seq (.dec rK) (wPair T))

theorem wLoop_spec (cap : ℕ) (hcap : 1 ≤ cap) (j : Fin 6) (h : ℕ) (hh : 1 ≤ h) :
    ∀ (ws : List ℤ) (pre rest : List Bool) (σ : CS), (∀ w ∈ ws, w.natAbs < 2 ^ h) →
    σ.st (tbl j) = pre ++ (ws.flatMap (pairW h) ++ rest) → σ.sh (tbl j) = pre.length → σ.val rK = ws.length →
    σ.val rL = 0 → σ.val rL2 = 0 → σ.val rZ = 0 → σ.val rF = 0 → σ.val rH = 0 → σ.val rX = 0 →
    σ.sh sS = (σ.st sS).length → σ.val rOs + (8 * h + 8) * ws.length ≤ cap → 2 * h + 2 ≤ cap → ws.length ≤ cap →
    WExec cap (wLoop (tbl j)) σ
      (((PrimAsm.WriteNat.appendO σ sS rOs (quad (ws.flatMap intWord))).seth (tbl j)
        (pre.length + (ws.flatMap (pairW h)).length)).setv rK 0)
      (ws.length * (pairCost h + 4) + 1)
  | [], pre, rest, σ, _, _, hsh, hk, _, _, _, _, _, _, _, _, _, _ => by
    have e : ((PrimAsm.WriteNat.appendO σ sS rOs (quad (([] : List ℤ).flatMap intWord))).seth (tbl j)
        (pre.length + (([] : List ℤ).flatMap (pairW h)).length)).setv rK 0 = σ := by
      simp only [List.flatMap_nil, quad_nil, PrimAsm.WriteNat.appendO_nil, List.length_nil, Nat.add_zero]
      rw [← hsh, wseth_same, show (0 : ℕ) = σ.val rK by simpa using hk.symm, wsetv_same]
    rw [e]; exact WExec.mono (WExec.whrF (by simpa using hk)) (by simp)
  | w :: ws, pre, rest, σ, hws, hst, hsh, hk, hL, hL2, hZ, hF, hH, hX, hO, hc, hc2, hk2 => by
    simp only [List.length_cons] at hk hc hk2
    have s1 := WExec.dec (cap := cap) rK σ (by omega)
    set σ1 := σ.setv rK (σ.val rK - 1) with hσ1
    have s2 := wPair_spec cap hcap j h w pre (ws.flatMap (pairW h) ++ rest) σ1 hh (hws w (by simp))
      (by simp [σ1, hst, List.flatMap_cons, List.append_assoc]) (by simp [σ1, hsh])
      (by simp +decide [σ1, Function.update_apply, hL]) (by simp +decide [σ1, Function.update_apply, hL2])
      (by simp +decide [σ1, Function.update_apply, hZ]) (by simp +decide [σ1, Function.update_apply, hF])
      (by simp +decide [σ1, Function.update_apply, hH]) (by simp +decide [σ1, Function.update_apply, hX])
      (by simp [σ1, hO]) (by simp +decide [σ1, Function.update_apply]; nlinarith) hc2
    set σ2 := (PrimAsm.WriteNat.appendO σ1 sS rOs (quad (intWord w))).seth (tbl j) (pre.length + (pairW h w).length)
      with hσ2
    have hne : ∀ s : Fin 12, s = sS → tbl j ≠ s := fun s e => tbl_ne j s (by rw [e]; decide)
    have hwl : (quad (intWord w)).length ≤ 8 * h + 8 := by
      rw [quad_length, intWord_length']
      have := CompilerMachine.Pool.natBitLength_le w.natAbs h hh (hws w (by simp))
      omega
    have hv2 : σ2.val rOs = σ.val rOs + (quad (intWord w)).length := by
      simp only [σ2, σ1, WState.seth_val, PrimAsm.WriteNat.appendO_val, WState.setv_val, Function.update_apply,
        if_pos rfl, if_neg (show rOs ≠ rK by decide), ite_true]
    have s3 := wLoop_spec cap hcap j h hh ws (pre ++ pairW h w) rest σ2 (fun x hx => hws x (by simp [hx]))
      (by simp [σ2, σ1, Function.update_apply, hne sS rfl, hst, List.flatMap_cons, List.append_assoc])
      (by simp [σ2])
      (by simp +decide [σ2, σ1, Function.update_apply, hk])
      (by simp +decide [σ2, σ1, Function.update_apply, hL]) (by simp +decide [σ2, σ1, Function.update_apply, hL2])
      (by simp +decide [σ2, σ1, Function.update_apply, hZ]) (by simp +decide [σ2, σ1, Function.update_apply, hF])
      (by simp +decide [σ2, σ1, Function.update_apply, hH]) (by simp +decide [σ2, σ1, Function.update_apply, hX])
      (by simp [σ2, σ1, Function.update_apply, (hne sS rfl).symm, hO])
      (by rw [hv2]; nlinarith) hc2 (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 s2) s3) ?_ (by simp only [List.length_cons]; nlinarith)
    simp only [σ2, σ1]
    rw [appendO_seth sS _ (tbl j) _ _ (hne sS rfl), PrimAsm.WriteNat.appendO_append,
      PrimAsm.WriteNat.appendO_setv _ sS rOs rK (by decide), ← quad_append, ← List.flatMap_cons]
    apply WState.eq
    · funext i; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
      by_cases h1 : i = tbl j
      · subst h1; simp [hne sS rfl, List.flatMap_cons]; omega
      · simp [h1]
    · rfl
    · funext q; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
      by_cases h1 : q = rK
      · subst h1; simp +decide
      · simp [h1]
    · rfl

theorem flatMap_intWord_le (h : ℕ) (hh : 1 ≤ h) : ∀ (ws : List ℤ), (∀ w ∈ ws, w.natAbs < 2 ^ h) →
    (ws.flatMap intWord).length ≤ ws.length * (2 * h + 2)
  | [], _ => by simp
  | w :: ws, hws => by
    have ih := flatMap_intWord_le h hh ws (fun x hx => hws x (by simp [hx]))
    have hb := CompilerMachine.Pool.natBitLength_le w.natAbs h hh (hws w (by simp))
    simp only [List.flatMap_cons, List.length_append, intWord_length', List.length_cons]
    nlinarith


end NearCubicWires.WireExponent3_5.PrimT.C4Gates
