import Proof.Wire_3_5.Primitive.Writers.DataRun
import Proof.Wire_3_5.Primitive.Writers.Emit

/-! # W6, part 1: the numbers machine's streams and the top word `frame tw`

P3:2543-2558 (row:threshold-rows): the family `𝒢` and its magnitude envelope are read by proof 1's verified program
from the circuits' payloads (the top word `tw = (List.ofFn Cs).flatMap payOf`, `W6Meta.tw_payOf`), so the numbers
machine writes `frame tw` from the front end's payload streams. On a word layout of 192 streams and 80 registers
(registers `0 … 47` are `e`/`W_j` stage's; the two programs' 61 tapes each are streams):
* the stream and register names (`sReq`, `sCnt`, …; `rN`, `rNG`, …);
* **`payW`** / **`payW_spec`**: one payload `frame y` (head `0`) appended to `O` as `y.flatMap m2 ++ [true, false]`
  (= `frameP (frame y)`), the payload's head back at `0`;
* **`twW`** / **`twW_spec`**: the `a' ≤ 4` payloads, then `false`: `O` holds `frame ((List.ofFn …).flatMap frame)`.

Paper quantity of the main type: the top word `frame tw` of the THR tuple (the input of `|𝒢|` and the envelope). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_nil appendO_append appendO_setv)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec (m2)

/-- The numbers machine's states and programs (the layout `W6Lay`). -/
abbrev WL : Type := WState 191 80
abbrev WP : Type := WM 191 80

variable (cap : ℕ)

/-! ## Streams -/

/-- The framed request (port `0`). -/
def sReq : Fin 192 := 0
/-- The count `1^V` (port `20`, the fill's source, `W6Lay.sV`). -/
def sCnt : Fin 192 := 1
/-- `1^{ncar}` (port `1`). -/
def sNc : Fin 192 := 2
/-- `1^{cap_T}` (port `2`). -/
def sCap : Fin 192 := 3
/-- The fourteen unary values (ports `3 … 16`). -/
def sVal (k : Fin 14) : Fin 192 := ⟨5 + k.val, by omega⟩
/-- The primes (port `17`). -/
def sPr : Fin 192 := 19
/-- The modulus word (port `19`). -/
def sMod : Fin 192 := 21
/-- The front end's payload streams. -/
def sPay (i : Fin 4) : Fin 192 := ⟨22 + i.val, by omega⟩
/-- The first program's block (`|𝒢|`): its tape `k` is stream `30 + k` (`0` the top word, `1` the output, `2` the native
word, `60` the reset counter). -/
def sBC (k : Fin 61) : Fin 192 := ⟨30 + k.val, by omega⟩
/-- The second program's block (the envelope). -/
def sBE (k : Fin 61) : Fin 192 := ⟨91 + k.val, by omega⟩

/-! ## Appending and moving -/

theorem emitC_app (O : Fin 192) (OP : Fin 80) (b : Bool) (σ : WL) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val OP < cap) : WExec cap (emitC O OP b) σ (appendO σ O OP [b]) 7 :=
  emitC_spec cap O OP b σ hO hc

/-! ## One payload -/

/-- One payload bit pair `(true, b)`, each bit doubly marked: `[t,t,t,t]` then `[t,t,t,b]`… as `m2 true ++ m2 b`
reduced: the marker bit's `m2 true` is `[t,t,t,t]`; we write `(t,t)` for the marker and `(t,b)` for the data bit. -/
def payBody (S O : Fin 192) (OP SP : Fin 80) : WP :=
  .seq (emitC O OP true) (.seq (emitC O OP true) (.seq (WM.fwdC S SP) (.seq (emitC O OP true)
    (.seq (.ifs S (emitC O OP true) (emitC O OP false)) (WM.fwdC S SP)))))

theorem payBody_spec (S O : Fin 192) (hSO : S ≠ O) (OP SP : Fin 80) (hPS : OP ≠ SP) (σ : WL) (b : Bool)
    (hb : readTapeBit (σ.st S) (σ.sh S + 1) = b) (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + 4 ≤ cap)
    (hs : σ.val SP + 2 ≤ cap) :
    WExec cap (payBody S O OP SP) σ ((appendO σ O OP (m2 b)).seth S (σ.sh S + 2) |>.setv SP (σ.val SP + 2)) 44 := by
  have e1 := emitC_app cap O OP true σ hO (by omega)
  have e2 := emitC_app cap O OP true (appendO σ O OP [true]) (by simp [hO]) (by simp; omega)
  rw [appendO_append] at e2
  obtain ⟨σ2, hσ2⟩ : ∃ y, y = appendO σ O OP ([true] ++ [true]) := ⟨_, rfl⟩
  rw [← hσ2] at e2
  have e3 := wfwdC_spec cap S SP σ2 (by rw [hσ2]; simp [Function.update_of_ne hPS.symm]; omega)
  obtain ⟨σ3, hσ3⟩ : ∃ y, y = (σ2.seth S (σ2.sh S + 1)).setv SP (σ2.val SP + 1) := ⟨_, rfl⟩
  rw [← hσ3] at e3
  have h3O : σ3.sh O = (σ3.st O).length := by
    rw [hσ3, hσ2]; simp [Function.update_of_ne hSO.symm, hO]
  have e4 := emitC_app cap O OP true σ3 h3O (by rw [hσ3, hσ2]; simp [Function.update_of_ne hPS]; omega)
  have hbit : wbit (appendO σ3 O OP [true]) S = b := by
    unfold wbit
    rw [appendO_st, appendO_sh, Function.update_of_ne hSO, Function.update_of_ne hSO, hσ3]
    simp only [WState.setv_st, WState.setv_sh, WState.seth_st, WState.seth_sh, Function.update_self]
    rw [hσ2, appendO_st, appendO_sh, Function.update_of_ne hSO, Function.update_of_ne hSO]
    exact hb
  have h4O : (appendO σ3 O OP [true]).sh O = ((appendO σ3 O OP [true]).st O).length := by simp [h3O]
  have h4c : (appendO σ3 O OP [true]).val OP < cap := by
    rw [appendO_val, Function.update_self, hσ3, hσ2]; simp [Function.update_of_ne hPS]; omega
  have e5 : WExec cap (.ifs S (emitC O OP true) (emitC O OP false)) (appendO σ3 O OP [true])
      (appendO (appendO σ3 O OP [true]) O OP [b]) 8 := by
    cases hb' : b
    · rw [hb'] at hbit
      exact WExec.ifsF hbit (emitC_app cap O OP false _ h4O h4c)
    · rw [hb'] at hbit
      exact WExec.ifsT hbit (emitC_app cap O OP true _ h4O h4c)
  rw [appendO_append] at e5
  obtain ⟨σ5, hσ5⟩ : ∃ y, y = appendO σ3 O OP ([true] ++ [b]) := ⟨_, rfl⟩
  rw [← hσ5] at e5
  have v3 : σ3.val SP = σ.val SP + 1 := by
    rw [hσ3, WState.setv_val, Function.update_self, hσ2, appendO_val, Function.update_of_ne hPS.symm]
  have v5 : σ5.val SP = σ3.val SP := by rw [hσ5, appendO_val, Function.update_of_ne hPS.symm]
  have e6 := wfwdC_spec cap S SP σ5 (by rw [v5, v3]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ (by omega)
  apply WState.eq
  · funext j
    rw [hσ5, hσ3, hσ2]
    simp only [WState.setv_sh, WState.seth_sh, appendO_sh]
    by_cases h1 : j = S
    · subst h1
      simp [Function.update_of_ne hSO] <;> omega
    · by_cases h2 : j = O
      · subst h2
        simp [Function.update_of_ne hSO.symm, m2] <;> omega
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · funext j
    rw [hσ5, hσ3, hσ2]
    simp only [WState.setv_st, WState.seth_st, appendO_st]
    by_cases h2 : j = O
    · subst h2
      simp [Function.update_of_ne hSO.symm, m2]
    · simp [Function.update_of_ne h2]
  · funext r
    rw [hσ5, hσ3, hσ2]
    simp only [WState.setv_val, WState.seth_val, appendO_val]
    by_cases h1 : r = SP
    · subst h1
      simp [Function.update_of_ne hPS.symm] <;> omega
    · by_cases h2 : r = OP
      · subst h2
        simp [Function.update_of_ne hPS, m2] <;> omega
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · rw [hσ5, hσ3, hσ2]; simp

/-- The payload loop: while the payload's marker bit is `true`. -/
def payLoop (S O : Fin 192) (OP SP : Fin 80) : WP := .whs S (payBody S O OP SP)

theorem frameP_cons (b : Bool) (y : List Bool) : frameP (b :: y) = true :: b :: frameP y := rfl

theorem frameP_app (l l' : List Bool) : frameP (l ++ l') = frameP l ++ frameP l' := by
  simp [frameP, List.flatMap_append]

theorem payLoop_spec (S O : Fin 192) (hSO : S ≠ O) (OP SP : Fin 80) (hPS : OP ≠ SP) :
    ∀ (y p : List Bool) (σ : WL), σ.st S = frameP p ++ frameP y ++ [false] → σ.sh S = 2 * p.length →
      σ.val SP = 2 * p.length → σ.sh O = (σ.st O).length → σ.val OP + 4 * y.length ≤ cap →
      2 * p.length + 2 * y.length ≤ cap →
      WExec cap (payLoop S O OP SP) σ (((appendO σ O OP (y.flatMap m2)).seth S (2 * (p.length + y.length))).setv SP
        (2 * (p.length + y.length))) (46 * y.length + 1)
  | [], p, σ, hst, hsh, hsp, hO, hc, hs => by
    have hb : wbit σ S = false := by
      unfold wbit
      rw [hst, hsh, show frameP ([] : List Bool) = [] from rfl, List.append_nil]
      unfold readTapeBit
      rw [List.getD_append_right _ _ _ _ (by simp [frameP_length])]
      simp [frameP_length]
    have e : ((appendO σ O OP (([] : List Bool).flatMap m2)).seth S (2 * (p.length + 0))).setv SP
        (2 * (p.length + 0)) = σ := by
      rw [List.flatMap_nil, appendO_nil, Nat.add_zero, ← hsh]
      apply WState.eq
      · funext j; by_cases h : j = S
        · subst h; simp
        · simp [Function.update_of_ne h]
      · simp
      · funext r; by_cases h : r = SP
        · subst h; simp [hsp, hsh]
        · simp [Function.update_of_ne h]
      · simp
    simp only [List.length_nil]
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by omega)
  | b :: y, p, σ, hst, hsh, hsp, hO, hc, hs => by
    have hlen : (frameP p).length = 2 * p.length := frameP_length p
    have hb : wbit σ S = true := by
      unfold wbit
      rw [hst, hsh, frameP_cons]
      unfold readTapeBit
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), show 2 * p.length - (frameP p).length = 0 by
        omega]
      rfl
    have hb1 : readTapeBit (σ.st S) (σ.sh S + 1) = b := by
      rw [hst, hsh, frameP_cons]
      unfold readTapeBit
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), show 2 * p.length + 1 - (frameP p).length = 1
        by omega]
      rfl
    simp only [List.length_cons] at hc hs
    have e1 := payBody_spec cap S O hSO OP SP hPS σ b hb1 hO (by omega) (by omega)
    obtain ⟨τ, hτ⟩ : ∃ y', y' = ((appendO σ O OP (m2 b)).seth S (σ.sh S + 2)).setv SP (σ.val SP + 2) := ⟨_, rfl⟩
    rw [← hτ] at e1
    have hτS : τ.st S = frameP (p ++ [b]) ++ frameP y ++ [false] := by
      rw [hτ]
      simp only [WState.setv_st, WState.seth_st, appendO_st, Function.update_of_ne hSO, hst, frameP_app,
        frameP_cons]
      simp [frameP]
    have ih := payLoop_spec S O hSO OP SP hPS y (p ++ [b]) τ hτS
      (by rw [hτ]; simp [hsh, Function.update_of_ne hSO]; omega)
      (by rw [hτ]; simp [hsp]; omega)
      (by rw [hτ]; simp [Function.update_of_ne hSO.symm, hO])
      (by rw [hτ]; simp [Function.update_of_ne hPS]; simp [m2] at hc ⊢; omega)
      (by simp; omega)
    refine WExec.cast cap (WExec.whsT hb e1 ih) ?_ (by simp; omega)
    rw [hτ]
    apply WState.eq
    · funext j
      simp only [WState.setv_sh, WState.seth_sh, appendO_sh]
      by_cases h1 : j = S
      · subst h1; simp [Function.update_of_ne hSO]; omega
      · by_cases h2 : j = O
        · subst h2; simp [Function.update_of_ne hSO.symm, m2]; omega
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
    · funext j
      simp only [WState.setv_st, WState.seth_st, appendO_st]
      by_cases h2 : j = O
      · subst h2; simp [Function.update_of_ne hSO.symm, m2]
      · simp [Function.update_of_ne h2]
    · funext r
      simp only [WState.setv_val, WState.seth_val, appendO_val]
      by_cases h1 : r = SP
      · subst h1; simp [Function.update_of_ne hPS.symm]; omega
      · by_cases h2 : r = OP
        · subst h2; simp [Function.update_of_ne hPS, m2]; omega
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
    · simp

/-- **One payload**: the loop, the terminator's pair `(true, false)`, the payload rewound. -/
def payW (S O : Fin 192) (OP SP : Fin 80) : WP :=
  .seq (payLoop S O OP SP) (.seq (PrimAsm.Emit.emitW O OP [true, false]) (WM.rewind S SP))

theorem payW_spec (S O : Fin 192) (hSO : S ≠ O) (OP SP : Fin 80) (hPS : OP ≠ SP) (y : List Bool) (σ : WL)
    (hst : σ.st S = frame y) (hsh : σ.sh S = 0) (hsp : σ.val SP = 0) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val OP + 4 * y.length + 2 ≤ cap) (hs : 2 * y.length ≤ cap) :
    WExec cap (payW S O OP SP) σ (appendO σ O OP (y.flatMap m2 ++ [true, false])) (60 * y.length + 20) := by
  have e1 := payLoop_spec cap S O hSO OP SP hPS y [] σ (by rw [hst, frame_eq_frameP]; rfl) (by simp [hsh])
    (by simp [hsp]) hO (by omega) (by simp; omega)
  simp only [List.length_nil, Nat.zero_add] at e1
  obtain ⟨τ, hτ⟩ : ∃ y', y' = ((appendO σ O OP (y.flatMap m2)).seth S (2 * y.length)).setv SP (2 * y.length) :=
    ⟨_, rfl⟩
  rw [← hτ] at e1
  have hml : (y.flatMap m2).length = 4 * y.length := by
    rw [List.length_flatMap]
    simp [m2]
    ring
  have e2 := PrimAsm.Emit.emitW_spec cap O OP [true, false] τ (by rw [hτ]; simp [Function.update_of_ne hSO.symm, hO])
    (by rw [hτ]; simp [Function.update_of_ne hPS, hml]; omega)
  have e3 := wrewind_spec cap S SP (2 * y.length) (appendO τ O OP [true, false])
    (by rw [appendO_val, Function.update_of_ne hPS.symm, hτ]; simp)
    (by rw [appendO_val, Function.update_of_ne hPS.symm, hτ]; simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by simp; omega)
  rw [hτ]
  apply WState.eq
  · funext j
    simp only [WState.setv_sh, WState.seth_sh, appendO_sh]
    by_cases h1 : j = S
    · subst h1; simp [Function.update_of_ne hSO, hsh]
    · by_cases h2 : j = O
      · subst h2; simp [Function.update_of_ne hSO.symm, hml]; omega
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · funext j
    simp only [WState.setv_st, WState.seth_st, appendO_st]
    by_cases h2 : j = O
    · subst h2; simp
    · simp [Function.update_of_ne h2]
  · funext r
    simp only [WState.setv_val, WState.seth_val, appendO_val]
    by_cases h1 : r = SP
    · subst h1; simp [Function.update_of_ne hPS.symm, hsp]
    · by_cases h2 : r = OP
      · subst h2; simp [Function.update_of_ne hPS, hml]; omega
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · simp

theorem frameP_frame (y : List Bool) : frameP (frame y) = y.flatMap m2 ++ [true, false] := by
  rw [frame_eq_frameP, frameP_app]
  have h := PrimAsm.FiltRec.marks2 y
  simp only [Streaming.marks] at h
  simp only [frameP] at h ⊢
  rw [h]
  rfl

/-- Circuit `i`'s guarded payload. -/
def gP (i : Fin 4) (O : Fin 192) (OP SP qa : Fin 80) : WP := .ifr qa (.seq (payW (sPay i) O OP SP) (.dec qa)) .skip

theorem gP_spec (i : Fin 4) (O : Fin 192) (hO : ∀ j, sPay j ≠ O) (OP SP qa : Fin 80) (hPS : OP ≠ SP) (hqO : qa ≠ OP)
    (hqS : qa ≠ SP) (a : ℕ) (pl : Fin 4 → List Bool) (hpl : ∀ j : Fin 4, j.val < a → ∃ y, pl j = frame y)
    (hpl0 : ∀ j : Fin 4, a ≤ j.val → pl j = []) (σ : WL) (hst : σ.st (sPay i) = pl i) (hsh : σ.sh (sPay i) = 0)
    (hsp : σ.val SP = 0) (hq : σ.val qa = a - i.val) (hOe : σ.sh O = (σ.st O).length)
    (hc : σ.val OP + 2 * (pl i).length + 2 ≤ cap) (hs : (pl i).length ≤ cap) (hqc : σ.val qa ≤ cap) :
    WExec cap (gP i O OP SP qa) σ ((appendO σ O OP (frameP (pl i))).setv qa (a - (i.val + 1)))
      (30 * (pl i).length + 30) := by
  by_cases hi : i.val < a
  · obtain ⟨y, hy⟩ := hpl i hi
    have hyl : (pl i).length = 2 * y.length + 1 := by rw [hy, frame_eq_frameP]; simp [frameP_length]
    have e1 := payW_spec cap (sPay i) O (hO i) OP SP hPS y σ (by rw [hst, hy]) hsh hsp hOe (by omega) (by omega)
    have e2 := WExec.dec (cap := cap) qa (appendO σ O OP (y.flatMap m2 ++ [true, false]))
      (by rw [appendO_val, Function.update_of_ne hqO]; exact hqc)
    have ex := WExec.ifrT (Q := WM.skip) (by rw [hq]; omega) (WExec.seq e1 e2)
    refine WExec.cast cap ex ?_ (by omega)
    rw [hy, frameP_frame, appendO_val, Function.update_of_ne hqO, hq, show a - i.val - 1 = a - (i.val + 1) by omega]
  · have hq0 : σ.val qa = 0 := by rw [hq]; omega
    have ex := WExec.ifrF (P := WM.seq (payW (sPay i) O OP SP) (WM.dec qa)) hq0 (WExec.skip (cap := cap) σ)
    refine WExec.cast cap ex ?_ (by omega)
    rw [hpl0 i (by omega), show frameP ([] : List Bool) = [] from rfl, appendO_nil,
      show a - (i.val + 1) = 0 by omega, ← hq0, wsetv_same]

/-- **The top word `frame tw`** on `O` from the four payload streams (the first `a` hold payloads). -/
def twW (O : Fin 192) (OP SP qa : Fin 80) : WP :=
  .seq (gP 0 O OP SP qa) (.seq (gP 1 O OP SP qa) (.seq (gP 2 O OP SP qa) (.seq (gP 3 O OP SP qa)
    (.seq (emitC O OP false) (WM.rewind O OP)))))

theorem sPay_ne (i j : Fin 4) (h : i ≠ j) : sPay i ≠ sPay j := fun e => h (by
  have := congrArg Fin.val e
  simp only [sPay] at this
  exact Fin.ext (by omega))

/-- The state after the first guards: `O` holds `frameP acc` (head and counter at its end), `qa = q`. -/
def twForm (σ0 : WL) (O : Fin 192) (OP qa : Fin 80) (acc : List Bool) (q : ℕ) : WL :=
  (((σ0.sets O (frameP acc)).seth O (frameP acc).length).setv OP (frameP acc).length).setv qa q

theorem twForm_st (σ0 : WL) (O : Fin 192) (OP qa : Fin 80) (acc : List Bool) (q : ℕ) (j : Fin 192) :
    (twForm σ0 O OP qa acc q).st j = if j = O then frameP acc else σ0.st j := by
  unfold twForm; by_cases h : j = O
  · subst h; simp
  · simp [Function.update_of_ne h, h]

theorem twForm_sh (σ0 : WL) (O : Fin 192) (OP qa : Fin 80) (acc : List Bool) (q : ℕ) (j : Fin 192) :
    (twForm σ0 O OP qa acc q).sh j = if j = O then (frameP acc).length else σ0.sh j := by
  unfold twForm; by_cases h : j = O
  · subst h; simp
  · simp [Function.update_of_ne h, h]

theorem twForm_val (σ0 : WL) (O : Fin 192) (OP qa : Fin 80) (hqO : qa ≠ OP) (acc : List Bool) (q : ℕ) (r : Fin 80) :
    (twForm σ0 O OP qa acc q).val r = if r = qa then q else if r = OP then (frameP acc).length else σ0.val r := by
  unfold twForm; by_cases h : r = qa
  · subst h; simp
  · by_cases h2 : r = OP
    · subst h2; simp [Function.update_of_ne h, h]
    · simp [Function.update_of_ne h, Function.update_of_ne h2, h, h2]

theorem twForm_app (σ0 : WL) (O : Fin 192) (OP qa : Fin 80) (hqO : qa ≠ OP) (acc l : List Bool) (q q' : ℕ) :
    (appendO (twForm σ0 O OP qa acc q) O OP (frameP l)).setv qa q' = twForm σ0 O OP qa (acc ++ l) q' := by
  apply WState.eq
  · funext j; by_cases h : j = O
    · subst h; simp [twForm, frameP_app]
    · simp [twForm, Function.update_of_ne h]
  · funext j; by_cases h : j = O
    · subst h; simp [twForm, frameP_app]
    · simp [twForm, Function.update_of_ne h]
  · funext r; by_cases h : r = qa
    · subst h; simp [twForm]
    · by_cases h2 : r = OP
      · subst h2; simp [twForm, Function.update_of_ne h, Function.update_of_ne hqO.symm, frameP_app]
      · simp [twForm, Function.update_of_ne h, Function.update_of_ne h2]
  · simp [twForm]

theorem twW_spec (O : Fin 192) (hO : ∀ j, sPay j ≠ O) (OP SP qa : Fin 80) (hPS : OP ≠ SP) (hqO : qa ≠ OP)
    (hqS : qa ≠ SP) (a : ℕ) (ha : a ≤ 4) (pl : Fin 4 → List Bool) (hpl : ∀ j : Fin 4, j.val < a → ∃ y, pl j = frame y)
    (hpl0 : ∀ j : Fin 4, a ≤ j.val → pl j = []) (σ : WL) (hst : ∀ j, σ.st (sPay j) = pl j)
    (hsh : ∀ j, σ.sh (sPay j) = 0) (hsp : σ.val SP = 0) (hq : σ.val qa = a) (hOst : σ.st O = []) (hOsh : σ.sh O = 0)
    (hop : σ.val OP = 0) (hc : 2 * (pl 0 ++ pl 1 ++ pl 2 ++ pl 3).length + 4 ≤ cap) (h4 : 4 ≤ cap) :
    ∃ τ, WExec cap (twW O OP SP qa) σ τ (40 * (pl 0 ++ pl 1 ++ pl 2 ++ pl 3).length + 200) ∧
      τ = (σ.sets O (frame (pl 0 ++ pl 1 ++ pl 2 ++ pl 3))).setv qa 0 := by
  have fl : ∀ l : List Bool, (frameP l).length = 2 * l.length := frameP_length
  have hlen : (pl 0 ++ pl 1 ++ pl 2 ++ pl 3).length = (pl 0).length + (pl 1).length + (pl 2).length + (pl 3).length :=
    by simp only [List.length_append]
  have hO' : ∀ j : Fin 4, (sPay j = O) = False := fun j => eq_false (hO j)
  have hSq : SP ≠ qa := hqS.symm
  have hSO : SP ≠ OP := hPS.symm
  have h0 : twForm σ O OP qa [] a = σ := by
    apply WState.eq
    · funext j; rw [twForm_sh]; split_ifs with h
      · subst h; simp [hOsh]
      · rfl
    · funext j; rw [twForm_st]; split_ifs with h
      · subst h; simp [hOst]
      · rfl
    · funext r; rw [twForm_val σ O OP qa hqO]; split_ifs with h h2
      · subst h; exact hq.symm
      · subst h2; simp [hop]
      · rfl
    · simp [twForm]
  -- one guard
  have step : ∀ (k : Fin 4) (acc : List Bool), acc.length + (pl k).length ≤ (pl 0 ++ pl 1 ++ pl 2 ++ pl 3).length →
      WExec cap (gP k O OP SP qa) (twForm σ O OP qa acc (a - k.val))
        (twForm σ O OP qa (acc ++ pl k) (a - (k.val + 1))) (30 * (pl k).length + 30) := by
    intro k acc hk
    have e := gP_spec cap k O hO OP SP qa hPS hqO hqS a pl hpl hpl0 (twForm σ O OP qa acc (a - k.val))
      (by rw [twForm_st, if_neg (hO k), hst]) (by rw [twForm_sh, if_neg (hO k), hsh])
      (by rw [twForm_val σ O OP qa hqO, if_neg hSq, if_neg hSO, hsp])
      (by rw [twForm_val σ O OP qa hqO, if_pos rfl])
      (by rw [twForm_sh, twForm_st, if_pos rfl, if_pos rfl])
      (by rw [twForm_val σ O OP qa hqO, if_neg hqO.symm, if_pos rfl, fl]; omega)
      (by omega) (by rw [twForm_val σ O OP qa hqO, if_pos rfl]; omega)
    rwa [twForm_app σ O OP qa hqO] at e
  have e0 := step 0 [] (by simp only [List.length_nil]; omega)
  rw [show a - (0 : Fin 4).val = a by simp, h0] at e0
  have e1 := step 1 (pl 0) (by simp only [List.length_append] at hlen ⊢; omega)
  have e2 := step 2 (pl 0 ++ pl 1) (by simp only [List.length_append] at hlen ⊢; omega)
  have e3 := step 3 (pl 0 ++ pl 1 ++ pl 2) (by simp only [List.length_append] at hlen ⊢; omega)
  simp only [List.nil_append] at e0
  obtain ⟨σ4, hσ4⟩ : ∃ y, y = twForm σ O OP qa (pl 0 ++ pl 1 ++ pl 2 ++ pl 3) (a - ((3 : Fin 4).val + 1)) := ⟨_, rfl⟩
  rw [← hσ4] at e3
  have v4 : σ4.val OP = (frameP (pl 0 ++ pl 1 ++ pl 2 ++ pl 3)).length := by
    rw [hσ4, twForm_val σ O OP qa hqO, if_neg hqO.symm, if_pos rfl]
  have e4 := emitC_app cap O OP false σ4 (by rw [hσ4, twForm_sh, twForm_st, if_pos rfl, if_pos rfl])
    (by rw [v4, fl]; omega)
  have e5 := wrewind_spec cap O OP ((frameP (pl 0 ++ pl 1 ++ pl 2 ++ pl 3)).length + 1)
    (appendO σ4 O OP [false]) (by rw [appendO_val, Function.update_self, v4]; rfl)
    (by rw [appendO_val, Function.update_self, v4, fl]; simp; omega)
  refine ⟨_, WExec.mono (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))))
    (by have fe := fl (pl 0 ++ pl 1 ++ pl 2 ++ pl 3); omega), ?_⟩
  have q0 : a - ((3 : Fin 4).val + 1) = 0 := by show a - 4 = 0; omega
  apply WState.eq
  · funext j
    simp only [WState.seth_sh, WState.setv_sh, appendO_sh, WState.sets_sh]
    by_cases hj : j = O
    · subst hj
      rw [Function.update_self, Function.update_self, hσ4, twForm_sh, if_pos rfl]
      simp [hOsh]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, hσ4, twForm_sh, if_neg hj]
  · funext j
    simp only [WState.seth_st, WState.setv_st, appendO_st, WState.sets_st]
    by_cases hj : j = O
    · subst hj
      rw [Function.update_self, Function.update_self, hσ4, twForm_st, if_pos rfl, frame_eq_frameP]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, hσ4, twForm_st, if_neg hj]
  · funext r
    simp only [WState.seth_val, WState.setv_val, appendO_val, WState.sets_val]
    by_cases hr : r = OP
    · subst hr
      rw [Function.update_self, Function.update_of_ne hqO.symm, hop]
    · rw [Function.update_of_ne hr, Function.update_of_ne hr, hσ4, twForm_val σ O OP qa hqO]
      by_cases hr2 : r = qa
      · subst hr2; rw [if_pos rfl, Function.update_self, q0]
      · rw [if_neg hr2, if_neg hr, Function.update_of_ne hr2]
  · rw [hσ4]; simp [twForm]

end NearCubicWires.WireExponent3_5.PrimT.W6
