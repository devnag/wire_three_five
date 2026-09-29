import Proof.Wire_3_5.Primitive.SeedFix.C4Gates

/-! # G1, the gate converter, part 2: the P/N pairs to native signed words (P3:1645-1650, 1655-1664)

Part 1 (`C4Gates.convWord_spec`) turns one table number into `quad (natWord v')`. A table stores a signed integer as
its P/N pair `pairW h z = frame (binary h z⁺) ++ frame (binary h z⁻)`; C3a's native word stores it as
`intWord z = [z < 0] ++ natWord |z|`, and a gate's threshold as `intWord (θ − 1)` while the table has the pair of
`−θ`. This part, on the converter's fixed layout (`CS = WState 11 20`):
* `skipC` (skip a framed word, counting its cells), `nzW` (the zero test of a table number: the length pass alone);
* **`wPair_spec`**: a weight's pair becomes `quad (intWord w)` on the gate scratch `S`;
* **`tPair_spec`**: the pair of `−θ` becomes `quad (intWord (θ − 1))` on the threshold scratch `TS` (decrement if
  `θ ≥ 1`, increment of `−θ` otherwise; TabRef's `cmap_dec`, `cmap_inc`).

Paper quantity of the main types: the native signed words `intWord w`, `intWord (θ − 1)` of a gate. -/

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

/-! ## The converter's layout -/

/-- The converter's state: 12 streams, 20 registers. -/
abbrev CS := WState 11 20
/-- The converter's programs. -/
abbrev CW := WM 11 20

/-- The table streams `1 … 6` (the carriers' two slots, then the four circuits'). -/
def tbl (j : Fin 6) : Fin 12 := ⟨j.val + 1, by omega⟩

/-- The gate scratch, the arity word, the threshold scratch, the arity ruler. -/
abbrev sS : Fin 12 := 7
abbrev sNQ : Fin 12 := 8
abbrev sTS : Fin 12 := 9
abbrev sNS : Fin 12 := 10
/-- The output. -/
abbrev sO : Fin 12 := 0

abbrev rN : Fin 20 := 0
abbrev rOo : Fin 20 := 1
abbrev rOs : Fin 20 := 2
abbrev rOt : Fin 20 := 3
abbrev rCNT : Fin 20 := 4
abbrev rK : Fin 20 := 5
abbrev rL : Fin 20 := 6
abbrev rL2 : Fin 20 := 7
abbrev rZ : Fin 20 := 8
abbrev rF : Fin 20 := 9
abbrev rH : Fin 20 := 10
abbrev rX : Fin 20 := 11
abbrev rT : Fin 20 := 12
abbrev rOq : Fin 20 := 13

theorem tbl_val (j : Fin 6) : (tbl j).val = j.val + 1 := rfl
theorem tbl_ne (j : Fin 6) (s : Fin 12) (hs : 7 ≤ s.val ∨ s.val = 0) : tbl j ≠ s := by
  intro e; have := congrArg Fin.val e; rw [tbl_val] at this; have := j.isLt; omega

/-! ## Skipping a framed word, counting its cells -/

/-- Skip one framed word, `X += 2|bs| + 1`. -/
def skipC (T : Fin 12) : CW :=
  .seq (.whs T (.seq (.fwd T) (.seq (.fwd T) (.seq (.inc rX) (.inc rX))))) (.seq (.fwd T) (.inc rX))

theorem skipC_loop (cap : ℕ) (T : Fin 12) : ∀ (sfx pre rest : List Bool) (σ : CS) (x : ℕ),
    σ.st T = pre ++ (frameP sfx ++ false :: rest) → σ.sh T = pre.length → σ.val rX = x →
    x + 2 * sfx.length ≤ cap →
    WExec cap (.whs T (.seq (.fwd T) (.seq (.fwd T) (.seq (.inc rX) (.inc rX))))) σ
      ((σ.seth T (pre.length + 2 * sfx.length)).setv rX (x + 2 * sfx.length)) (13 * sfx.length + 1)
  | [], pre, rest, σ, x, hst, hsh, hx, _ => by
    have hr : wbit σ T = false := by
      simp only [wbit, hst, hsh]
      have := rd_shift pre (frameP [] ++ false :: rest) 0
      simp only [Nat.add_zero] at this
      rw [this]; rfl
    have e : (σ.seth T (pre.length + 2 * ([] : List Bool).length)).setv rX (x + 2 * ([] : List Bool).length) = σ := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]; rw [← hsh, wseth_same, ← hx, wsetv_same]
    rw [e]; exact WExec.whsF hr
  | b :: sfx, pre, rest, σ, x, hst, hsh, hx, hc => by
    have hm : wbit σ T = true := by
      simp only [wbit, hst, hsh]
      have := rd_marker pre (b :: sfx) (false :: rest) 0 (by simp)
      simpa using this
    simp only [List.length_cons] at hc
    have s1 := WExec.fwd (cap := cap) T σ
    have s2 := WExec.fwd (cap := cap) T (σ.seth T (σ.sh T + 1))
    have s3 := WExec.inc (cap := cap) rX ((σ.seth T (σ.sh T + 1)).seth T ((σ.seth T (σ.sh T + 1)).sh T + 1))
      (by simp; omega)
    have s4 := WExec.inc (cap := cap) rX ((((σ.seth T (σ.sh T + 1)).seth T ((σ.seth T (σ.sh T + 1)).sh T + 1))).setv
      rX (((σ.seth T (σ.sh T + 1)).seth T ((σ.seth T (σ.sh T + 1)).sh T + 1)).val rX + 1)) (by simp; omega)
    set σ' := ((((σ.seth T (σ.sh T + 1)).seth T ((σ.seth T (σ.sh T + 1)).sh T + 1))).setv
      rX (((σ.seth T (σ.sh T + 1)).seth T ((σ.seth T (σ.sh T + 1)).sh T + 1)).val rX + 1)).setv rX
      (((((σ.seth T (σ.sh T + 1)).seth T ((σ.seth T (σ.sh T + 1)).sh T + 1))).setv
      rX (((σ.seth T (σ.sh T + 1)).seth T ((σ.seth T (σ.sh T + 1)).sh T + 1)).val rX + 1)).val rX + 1) with hσ'
    have s5 := skipC_loop cap T sfx (pre ++ [true, b]) rest σ' (x + 2) (by simp [hσ', hst, frameP])
      (by simp [hσ', hsh] <;> omega) (by simp [hσ', hx] <;> omega) (by omega)
    refine WExec.cast cap (WExec.whsT hm (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) s5) ?_
      (by simp only [List.length_cons]; omega)
    apply WState.eq
    · funext j; simp only [hσ', WState.setv_sh, WState.seth_sh, Function.update_apply]
      all_goals (try split_ifs) <;> simp_all <;> omega
    · rfl
    · funext r; simp only [hσ', WState.setv_val, WState.seth_val, Function.update_apply]
      all_goals (try split_ifs) <;> simp_all <;> omega
    · rfl

theorem skipC_spec (cap : ℕ) (T : Fin 12) (bs pre rest : List Bool) (σ : CS)
    (hst : σ.st T = pre ++ (frameP bs ++ false :: rest)) (hsh : σ.sh T = pre.length) (hx : σ.val rX = 0)
    (hc : 2 * bs.length + 2 ≤ cap) :
    WExec cap (skipC T) σ ((σ.seth T (pre.length + 2 * bs.length + 1)).setv rX (2 * bs.length + 1))
      (13 * bs.length + 7) := by
  have s1 := skipC_loop cap T bs pre rest σ 0 hst hsh hx (by omega)
  have s2 := WExec.fwd (cap := cap) T ((σ.seth T (pre.length + 2 * bs.length)).setv rX (0 + 2 * bs.length))
  have s3 := WExec.inc (cap := cap) rX (((σ.seth T (pre.length + 2 * bs.length)).setv rX (0 + 2 * bs.length)).seth T
    (((σ.seth T (pre.length + 2 * bs.length)).setv rX (0 + 2 * bs.length)).sh T + 1)) (by simp; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by omega)
  apply WState.eq
  · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
    all_goals (try split_ifs) <;> simp_all <;> omega
  · rfl
  · funext r; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    all_goals (try split_ifs) <;> simp_all <;> omega
  · rfl

/-! ## The zero test of a table number -/

/-- The length pass alone, the head back: `L = 0` iff the number is `0`. -/
def nzW (T : Fin 12) : CW := .seq (lenPass T rL rZ rF rH cpyOut cpyNxt) (.seq (WM.clear rZ) (rewW T rH))

theorem cfin_cpy : ∀ (bs : List Bool), cfin cpyNxt bs false = false
  | [] => rfl
  | _ :: bs => cfin_cpy bs

theorem nzW_spec (cap : ℕ) (hcap : 1 ≤ cap) (T : Fin 12) (h v : ℕ) (pre rest : List Bool) (σ : CS)
    (hst : σ.st T = pre ++ (frameP (binary h v) ++ false :: rest)) (hsh : σ.sh T = pre.length)
    (hL : σ.val rL = 0) (hZ : σ.val rZ = 0) (hF : σ.val rF = 0) (hH : σ.val rH = 0) (hc2 : 2 * h + 2 ≤ cap) :
    WExec cap (nzW T) σ (σ.setv rL (accLZ (binary h v) (0, 0)).1) (7 * h * h + 60 * h + 20) := by
  have hb : (binary h v).length = h := binary_length h v
  have s1 := lenPass_spec cap T cpyOut cpyNxt (L := rL) (Z := rZ) (F := rF) (H2 := rH) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hcap (binary h v) pre rest σ false h hst hsh hL hZ (by simpa using hF)
    hH (by rw [hb]; omega) (by rw [hb])
  rw [cmap_cpy, cfin_cpy, hb] at s1
  set σ1 := u1 T rL rZ rF rH σ (pre.length + 2 * h + 1) (accLZ (binary h v) (0, 0)).1 (accLZ (binary h v) (0, 0)).2
    (false : Bool).toNat (2 * h + 1) with hσ1
  have hz1 : σ1.val rZ = (accLZ (binary h v) (0, 0)).2 := by simp +decide [σ1, u1, Function.update_apply]
  have hzle : (accLZ (binary h v) (0, 0)).2 ≤ h := by have := accLZ_le (binary h v) 0 0; rw [hb] at this; omega
  have s2 := wclear_spec cap rZ _ σ1 hz1 (by omega)
  have s3 := rewW_spec cap T rH (2 * h + 1) (σ1.setv rZ 0) (by simp +decide [σ1, u1, Function.update_apply])
    (by simp [σ1, u1]) (by omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ ?_
  · apply WState.eq
    · funext j; simp only [σ1, u1, WState.setv_sh, WState.seth_sh, Function.update_apply]
      all_goals (try split_ifs) <;> simp_all <;> omega
    · rfl
    · funext r; simp only [σ1, u1, WState.setv_val, WState.seth_val, Function.update_apply]
      all_goals (try split_ifs) <;> simp_all +decide
    · rfl
  · nlinarith

/-! ## A weight's pair -/

theorem pair_shape (h : ℕ) (z : ℤ) (pre rest : List Bool) :
    pre ++ (pairW h z ++ rest) = pre ++ (frameP (binary h z.toNat) ++ false ::
      (frameP (binary h (-z).toNat) ++ false :: rest)) := by
  simp [pairW, frame_eq_frameP, List.append_assoc]

theorem pairW_length (h : ℕ) (z : ℤ) : (pairW h z).length = 2 * (2 * h + 1) := by
  simp [pairW, frame_eq_frameP, frameP_length', binary_length]; omega

/-- **A P/N pair to a native signed word** on the output `O`: if the N number is nonzero, the sign `sgN` and the
native word of the N number through the map `(outN, nxtN, cN)`; else the sign `sgP` and the P number's through
`(outP, nxtP, cP)`. -/
def pairG (T O : Fin 12) (OP : Fin 20) (sgN : Bool) (outN nxtN : Bool → Bool → Bool) (cN : Bool) (sgP : Bool)
    (outP nxtP : Bool → Bool → Bool) (cP : Bool) : CW :=
  .seq (skipC T) (.seq (nzW T) (.ifr rL
    (.seq (WM.clear rL) (.seq (PrimAsm.Emit.emitW O OP [true, true, true, sgN])
      (.seq (convWord T O OP rL rL2 rZ rF rH outN nxtN cN) (WM.clear rX))))
    (.seq (PrimAsm.Emit.emitW O OP [true, true, true, sgP]) (.seq (rewW T rX)
      (.seq (convWord T O OP rL rL2 rZ rF rH outP nxtP cP) (skipRest T))))))

/-- The pair program's cost bound. -/
def pairCost (h : ℕ) : ℕ := 20 * h * h + 700 * h + 700

theorem pairG_spec (cap : ℕ) (hcap : 1 ≤ cap) (j : Fin 6) (O : Fin 12) (OP : Fin 20) (hO7 : O.val = 7 ∨ O.val = 9)
    (hOP : OP = rOs ∨ OP = rOt) (sgN : Bool) (outN nxtN : Bool → Bool → Bool) (cN : Bool) (sgP : Bool)
    (outP nxtP : Bool → Bool → Bool) (cP : Bool) (h P N vN vP : ℕ) (pre rest : List Bool) (σ : CS)
    (hh : 1 ≤ h) (hN : N ≠ 0 → cmap outN nxtN (binary h N) cN = binary h vN ∧ vN < 2 ^ h)
    (hP : N = 0 → cmap outP nxtP (binary h P) cP = binary h vP ∧ vP < 2 ^ h) (hNh : N < 2 ^ h)
    (hst : σ.st (tbl j) = pre ++ (frameP (binary h P) ++ false :: (frameP (binary h N) ++ false :: rest)))
    (hsh : σ.sh (tbl j) = pre.length)
    (hL : σ.val rL = 0) (hL2 : σ.val rL2 = 0) (hZ : σ.val rZ = 0) (hF : σ.val rF = 0) (hH : σ.val rH = 0)
    (hX : σ.val rX = 0) (hOe : σ.sh O = (σ.st O).length) (hc : σ.val OP + 8 * h + 8 ≤ cap) (hc2 : 2 * h + 2 ≤ cap) :
    WExec cap (pairG (tbl j) O OP sgN outN nxtN cN sgP outP nxtP cP) σ
      ((PrimAsm.WriteNat.appendO σ O OP (quad (if N = 0 then sgP :: natWord vP else sgN :: natWord vN))).seth
        (tbl j) (pre.length + 2 * (2 * h + 1)))
      (pairCost h) := by
  have hb : ∀ v, (binary h v).length = h := fun v => binary_length h v
  have hTO : tbl j ≠ O := tbl_ne j O (by omega)
  have hOP' : OP ≠ rL ∧ OP ≠ rL2 ∧ OP ≠ rZ ∧ OP ≠ rF ∧ OP ≠ rH ∧ OP ≠ rX := by
    rcases hOP with h | h <;> subst h <;> decide
  obtain ⟨hOL, hOL2, hOZ, hOF, hOH, hOX⟩ := hOP'
  -- 1: skip the P word
  have s1 := skipC_spec cap (tbl j) (binary h P) pre (frameP (binary h N) ++ false :: rest) σ hst hsh hX
    (by rw [hb]; omega)
  rw [hb] at s1
  set σ1 := (σ.seth (tbl j) (pre.length + 2 * h + 1)).setv rX (2 * h + 1) with hσ1
  set pre' := pre ++ (frameP (binary h P) ++ [false]) with hpre'
  have hpl : pre'.length = pre.length + 2 * h + 1 := by simp [pre', frameP_length', hb]; omega
  have hst1 : σ1.st (tbl j) = pre' ++ (frameP (binary h N) ++ false :: rest) := by simp [σ1, hst, pre']
  -- 2: the zero test of the N word
  have s2 := nzW_spec cap hcap (tbl j) h N pre' rest σ1 hst1 (by simp [σ1, hpl])
    (by simp +decide [σ1, Function.update_apply, hL]) (by simp +decide [σ1, Function.update_apply, hZ])
    (by simp +decide [σ1, Function.update_apply, hF]) (by simp +decide [σ1, Function.update_apply, hH]) hc2
  set σ2 := σ1.setv rL (accLZ (binary h N) (0, 0)).1 with hσ2
  have hacc := accLZ_binary h N hh hNh
  by_cases hN0 : N = 0
  · -- the N number is 0: the P number's word
    have ha0 : (accLZ (binary h N) (0, 0)).1 = 0 := by rw [hacc, if_pos hN0]
    have hσ21 : σ2 = σ1 := by rw [hσ2, ha0, show (0 : ℕ) = σ1.val rL by simp +decide [σ1, Function.update_apply, hL],
      wsetv_same]
    obtain ⟨hmap, hvP⟩ := hP hN0
    have e3 := PrimAsm.Emit.emitW_spec cap O OP [true, true, true, sgP] σ2
      (by rw [hσ21]; simp [σ1, Function.update_apply, hTO.symm, hOe])
      (by rw [hσ21]; simp +decide [σ1, Function.update_apply, hOX]; omega)
    set σ3 := PrimAsm.WriteNat.appendO σ2 O OP [true, true, true, sgP] with hσ3
    have e4 := rewW_spec cap (tbl j) rX (2 * h + 1) σ3 (by simp +decide [σ3, hσ21, σ1, Function.update_apply, hOX.symm])
      (by simp [σ3, hσ21, σ1, Function.update_apply, hTO] <;> omega) (by omega)
    set σ4 := (σ3.seth (tbl j) (σ3.sh (tbl j) - (2 * h + 1))).setv rX 0 with hσ4
    have hσ4sh : σ4.sh (tbl j) = pre.length := by simp [σ4, σ3, hσ21, σ1, Function.update_apply, hTO]
    have hσ4st : σ4.st (tbl j) = pre ++ (frameP (binary h P) ++ false :: (frameP (binary h N) ++ false :: rest)) := by
      simp [σ4, σ3, hσ21, σ1, Function.update_apply, hTO, hst]
    have e5 := convWord_spec cap (tbl j) O outP nxtP (OP := OP) (L := rL) (L2 := rL2) (Z := rZ) (F := rF) (H2 := rH)
      (hIO := hTO) (hLZ := by decide) (hLF := by decide) (hLH := by decide) (hZF := by decide) (hZH := by decide)
      (hFH := by decide) (hOL := hOL) (hOL2 := hOL2) (hOF := hOF) (hLL := by decide) (hL2F := by decide) (hOZ := hOZ)
      (hOH := hOH) (hL2Z := by decide) (hL2H := by decide) hcap cP h P vP pre
      (frameP (binary h N) ++ false :: rest) σ4 hh hvP hmap hσ4st hσ4sh
      (by simp +decide [σ4, σ3, hσ21, σ1, Function.update_apply, hOL.symm, hL])
      (by simp +decide [σ4, σ3, hσ21, σ1, Function.update_apply, hOL2.symm, hL2])
      (by simp +decide [σ4, σ3, hσ21, σ1, Function.update_apply, hOZ.symm, hZ])
      (by simp +decide [σ4, σ3, hσ21, σ1, Function.update_apply, hOF.symm, hF])
      (by simp +decide [σ4, σ3, hσ21, σ1, Function.update_apply, hOH.symm, hH])
      (by simp [σ4, σ3, hσ21, σ1, Function.update_apply, hTO.symm, hOe])
      (by simp +decide [σ4, σ3, hσ21, σ1, Function.update_apply, hOX]; omega) hc2
    set σ5 := (PrimAsm.WriteNat.appendO σ4 O OP (quad (natWord vP))).seth (tbl j) (pre.length + 2 * h + 1) with hσ5
    have e6 := skipRest_spec cap (tbl j) (binary h N) pre' rest σ5
      (by simp [σ5, σ4, σ3, hσ21, σ1, Function.update_apply, hTO, hst, pre'])
      (by simp [σ5, hpl])
    rw [hb] at e6
    refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.mono (WExec.ifrF (by rw [hσ2]; simp +decide [ha0])
      (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6)))) le_rfl))) ?_ ?_
    · rw [if_pos hN0, quad_cons]
      simp only [σ5, σ4, σ3, hσ21, σ1]
      apply WState.eq
      · funext i; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
        by_cases h1 : i = tbl j
        · subst h1; simp [hTO]; omega
        · by_cases h2 : i = O
          · subst h2; simp [h1]; omega
          · simp [h1, h2]
      · funext i; simp only [WState.setv_st, WState.seth_st, PrimAsm.WriteNat.appendO_st, Function.update_apply]
        by_cases h2 : i = O
        · subst h2; simp [List.append_assoc]
        · simp [h2]
      · funext r; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
        by_cases h1 : r = OP
        · subst h1; simp +decide [hOX, hOL, hOL2, hOZ, hOF, hOH]; omega
        · by_cases h2 : r = rX
          · subst h2; simp +decide [h1, hX]
          · simp +decide [h1, h2]
      · rfl
    · unfold pairCost; simp only [List.length_cons, List.length_nil]; nlinarith
  · -- the N number is nonzero: its word
    obtain ⟨hmap, hvN⟩ := hN hN0
    have hnl : natBitLength N ≤ h := CompilerMachine.Pool.natBitLength_le N h hh hNh
    have ha : (accLZ (binary h N) (0, 0)).1 = natBitLength N := by rw [hacc, if_neg hN0]
    have hnz : σ2.val rL ≠ 0 := by
      rw [hσ2]; simp +decide [ha]; unfold natBitLength; omega
    have e3 := wclear_spec cap rL (σ2.val rL) σ2 rfl (by rw [hσ2]; simp +decide [ha]; omega)
    have hσ3 : σ2.setv rL 0 = σ1 := by
      rw [hσ2, wsetv_setv, show (0 : ℕ) = σ1.val rL by simp +decide [σ1, Function.update_apply, hL], wsetv_same]
    rw [hσ3] at e3
    have e4 := PrimAsm.Emit.emitW_spec cap O OP [true, true, true, sgN] σ1
      (by simp [σ1, Function.update_apply, hTO.symm, hOe])
      (by simp +decide [σ1, Function.update_apply, hOX]; omega)
    set σ4 := PrimAsm.WriteNat.appendO σ1 O OP [true, true, true, sgN] with hσ4
    have e5 := convWord_spec cap (tbl j) O outN nxtN (OP := OP) (L := rL) (L2 := rL2) (Z := rZ) (F := rF) (H2 := rH)
      (hIO := hTO) (hLZ := by decide) (hLF := by decide) (hLH := by decide) (hZF := by decide) (hZH := by decide)
      (hFH := by decide) (hOL := hOL) (hOL2 := hOL2) (hOF := hOF) (hLL := by decide) (hL2F := by decide) (hOZ := hOZ)
      (hOH := hOH) (hL2Z := by decide) (hL2H := by decide) hcap cN h N vN pre' rest σ4 hh hvN hmap
      (by simp [σ4, σ1, Function.update_apply, hTO, hst1, hst, pre'])
      (by simp [σ4, σ1, Function.update_apply, hTO, hpl])
      (by simp +decide [σ4, σ1, Function.update_apply, hOL.symm, hL])
      (by simp +decide [σ4, σ1, Function.update_apply, hOL2.symm, hL2])
      (by simp +decide [σ4, σ1, Function.update_apply, hOZ.symm, hZ])
      (by simp +decide [σ4, σ1, Function.update_apply, hOF.symm, hF])
      (by simp +decide [σ4, σ1, Function.update_apply, hOH.symm, hH])
      (by simp [σ4, σ1, Function.update_apply, hTO.symm, hOe])
      (by simp +decide [σ4, σ1, Function.update_apply, hOX]; omega) hc2
    set σ5 := (PrimAsm.WriteNat.appendO σ4 O OP (quad (natWord vN))).seth (tbl j) (pre'.length + 2 * h + 1) with hσ5
    have e6 := wclear_spec cap rX (σ5.val rX) σ5 rfl
      (by simp +decide [σ5, σ4, σ1, Function.update_apply, hOX, hOX.symm]; omega)
    refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.mono (WExec.ifrT hnz
      (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6)))) le_rfl))) ?_ ?_
    · rw [if_neg hN0, quad_cons]
      simp only [σ5, σ4, σ1]
      apply WState.eq
      · funext i; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
        by_cases h1 : i = tbl j
        · subst h1; simp [hTO]; omega
        · by_cases h2 : i = O
          · subst h2; simp [h1]; omega
          · simp [h1, h2]
      · funext i; simp only [WState.setv_st, WState.seth_st, PrimAsm.WriteNat.appendO_st, Function.update_apply]
        by_cases h2 : i = O
        · subst h2; simp [List.append_assoc]
        · simp [h2]
      · funext r; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
        by_cases h1 : r = OP
        · subst h1; simp +decide [hOX, hOL, hOL2, hOZ, hOF, hOH]; omega
        · by_cases h2 : r = rX
          · subst h2; simp +decide [h1, hX]
          · simp +decide [h1, h2]
      · rfl
    · unfold pairCost
      have : 3 * σ2.val rL ≤ 3 * h := by rw [hσ2]; simp +decide [ha]; omega
      have : 3 * σ5.val rX ≤ 3 * (2 * h + 1) := by
        simp +decide [σ5, σ4, σ1, Function.update_apply, hOX, hOX.symm]
      simp only [List.length_cons, List.length_nil]
      nlinarith

/-- **A weight's pair to its native signed word** on the gate scratch. -/
def wPair (T : Fin 12) : CW := pairG T sS rOs true cpyOut cpyNxt false false cpyOut cpyNxt false

/-- **The pair of `−θ` to the native word of `θ − 1`** on the threshold scratch. -/
def tPair (T : Fin 12) : CW := pairG T sTS rOt false decOut decNxt true true incOut incNxt true

theorem wPair_spec (cap : ℕ) (hcap : 1 ≤ cap) (j : Fin 6) (h : ℕ) (w : ℤ) (pre rest : List Bool) (σ : CS)
    (hh : 1 ≤ h) (hw : w.natAbs < 2 ^ h)
    (hst : σ.st (tbl j) = pre ++ (pairW h w ++ rest)) (hsh : σ.sh (tbl j) = pre.length)
    (hL : σ.val rL = 0) (hL2 : σ.val rL2 = 0) (hZ : σ.val rZ = 0) (hF : σ.val rF = 0) (hH : σ.val rH = 0)
    (hX : σ.val rX = 0) (hOe : σ.sh sS = (σ.st sS).length) (hc : σ.val rOs + 8 * h + 8 ≤ cap)
    (hc2 : 2 * h + 2 ≤ cap) :
    WExec cap (wPair (tbl j)) σ
      ((PrimAsm.WriteNat.appendO σ sS rOs (quad (intWord w))).seth (tbl j) (pre.length + (pairW h w).length))
      (pairCost h) := by
  rw [pair_shape] at hst
  have hP : w.toNat < 2 ^ h := by omega
  have hN : (-w).toNat < 2 ^ h := by omega
  have s := pairG_spec cap hcap j sS rOs (by decide) (by decide) true cpyOut cpyNxt false false cpyOut cpyNxt false h
    w.toNat (-w).toNat (-w).toNat w.toNat pre rest σ hh (fun _ => ⟨cmap_cpy _ _, hN⟩) (fun _ => ⟨cmap_cpy _ _, hP⟩)
    hN hst hsh hL hL2 hZ hF hH hX hOe hc hc2
  rw [pairW_length]
  refine WExec.cast cap s ?_ le_rfl
  unfold intWord
  by_cases hw0 : w < 0
  · rw [if_neg (show (-w).toNat ≠ 0 by omega), decide_eq_true hw0, show (-w).toNat = w.natAbs by omega]
  · rw [if_pos (show (-w).toNat = 0 by omega), decide_eq_false hw0, show w.toNat = w.natAbs by omega]

theorem tPair_spec (cap : ℕ) (hcap : 1 ≤ cap) (j : Fin 6) (h : ℕ) (θ : ℤ) (pre rest : List Bool) (σ : CS)
    (hh : 1 ≤ h) (ht : (θ - 1).natAbs + 1 < 2 ^ h) (ht' : θ.natAbs < 2 ^ h)
    (hst : σ.st (tbl j) = pre ++ (pairW h (-θ) ++ rest)) (hsh : σ.sh (tbl j) = pre.length)
    (hL : σ.val rL = 0) (hL2 : σ.val rL2 = 0) (hZ : σ.val rZ = 0) (hF : σ.val rF = 0) (hH : σ.val rH = 0)
    (hX : σ.val rX = 0) (hOe : σ.sh sTS = (σ.st sTS).length) (hc : σ.val rOt + 8 * h + 8 ≤ cap)
    (hc2 : 2 * h + 2 ≤ cap) :
    WExec cap (tPair (tbl j)) σ
      ((PrimAsm.WriteNat.appendO σ sTS rOt (quad (intWord (θ - 1)))).seth (tbl j)
        (pre.length + (pairW h (-θ)).length))
      (pairCost h) := by
  rw [pair_shape] at hst
  have hP : (-θ).toNat < 2 ^ h := by omega
  have hN : (-(-θ)).toNat < 2 ^ h := by omega
  have s := pairG_spec cap hcap j sTS rOt (by decide) (by decide) false decOut decNxt true true incOut incNxt true h
    (-θ).toNat (-(-θ)).toNat ((-(-θ)).toNat - 1) ((-θ).toNat + 1) pre rest σ hh
    (fun hn => ⟨cmap_dec h _ (by omega) hN, by omega⟩)
    (fun hn => ⟨cmap_inc h _ (by omega), by omega⟩)
    hN hst hsh hL hL2 hZ hF hH hX hOe hc hc2
  rw [pairW_length]
  refine WExec.cast cap s ?_ le_rfl
  unfold intWord
  by_cases hθ : θ ≤ 0
  · rw [if_pos (show (-(-θ)).toNat = 0 by omega), decide_eq_true (show θ - 1 < 0 by omega),
      show (-θ).toNat + 1 = (θ - 1).natAbs by omega]
  · rw [if_neg (show (-(-θ)).toNat ≠ 0 by omega), decide_eq_false (show ¬ θ - 1 < 0 by omega),
      show (-(-θ)).toNat - 1 = (θ - 1).natAbs by omega]

end NearCubicWires.WireExponent3_5.PrimT.C4Gates
