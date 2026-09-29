import Proof.Wire_3_5.Primitive.SeedFix.TabConv

/-! # FLIPS, part 1: one corner's flip pattern (P3:1224, 1655-1664)

"The four corner points `c+u+v`, `c+u`, `c+v`, `c`" of `star:delta` (P3:1224) are C3a's flip patterns
(`alg:pullback`, P3:1655-1664): corner `k` of a cell is the coset offset XOR the cell's left errors (corners `0, 1`)
XOR its right errors (corners `0, 2`). On three framed `n`-bit words (the offset `A`, the left errors `B`, the right
errors `C`, heads at `0`), **`cornerW u v`** appends `frame (xw u v A B C)` to the output stream (bit
`a ⊕ (u ∧ b) ⊕ (v ∧ c)` per coordinate, through a toggled register), and puts the three heads back at `0`.

* `condTog_spec`, `emitBit_spec`; `xorStep` / **`xorStep_spec`**; `xorLoop_spec`; `rew3_spec`; **`cornerW_spec`**.

Paper quantity of the main type: the corner's point `c ⊕ u ⊕ v` (as `xw`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- **The corner bit**: `a ⊕ (u ∧ b) ⊕ (v ∧ c)`. -/
def xb (u v a b c : Bool) : Bool := xor (xor a (u && b)) (v && c)

/-- **The corner word** of three words. -/
def xw (u v : Bool) : List Bool → List Bool → List Bool → List Bool
  | a :: as, b :: bs, c :: cs => xb u v a b c :: xw u v as bs cs
  | _, _, _ => []

theorem xw_length (u v : Bool) : ∀ (as bs cs : List Bool),
    (xw u v as bs cs).length = min as.length (min bs.length cs.length)
  | [], _, _ => by simp [xw]
  | _ :: _, [], _ => by simp [xw]
  | _ :: _, _ :: _, [] => by simp [xw]
  | a :: as, b :: bs, c :: cs => by
    simp only [xw, List.length_cons, xw_length u v as bs cs]
    omega

theorem xw_getD (u v : Bool) : ∀ (as bs cs : List Bool) (k : ℕ), k < as.length → k < bs.length → k < cs.length →
    (xw u v as bs cs).getD k false = xb u v (as.getD k false) (bs.getD k false) (cs.getD k false)
  | a :: as, b :: bs, c :: cs, 0, _, _, _ => rfl
  | a :: as, b :: bs, c :: cs, k + 1, h1, h2, h3 => by
    simp only [xw, List.getD_cons_succ]
    exact xw_getD u v as bs cs k (by simp at h1; omega) (by simp at h2; omega) (by simp at h3; omega)
  | [], _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h => by simp at h

theorem xw_take_succ (u v : Bool) (as bs cs : List Bool) (k : ℕ) (h1 : k < as.length) (h2 : k < bs.length)
    (h3 : k < cs.length) :
    (xw u v as bs cs).take (k + 1) = (xw u v as bs cs).take k ++
      [xb u v (as.getD k false) (bs.getD k false) (cs.getD k false)] := by
  have hk : k < (xw u v as bs cs).length := by rw [xw_length]; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some]
  rw [← List.getD_eq_getElem _ false hk, xw_getD u v as bs cs k h1 h2 h3]

theorem rd_end (ws rest : List Bool) : readTapeBit (frameP ws ++ false :: rest) (2 * ws.length) = false := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

section Corner
variable {ns nr : ℕ} (cap : ℕ)

theorem setv_self (σ : WState ns nr) (r : Fin nr) : σ.setv r (σ.val r) = σ :=
  WState.eq rfl rfl (by simp) rfl

/-- Toggle a `0/1` register. -/
def togW (acc : Fin nr) : WM ns nr := .ifr acc (.dec acc) (.inc acc)

/-- Toggle `acc` when `u` and the stream's cell holds `1`. -/
def condTog (u : Bool) (X : Fin (ns + 1)) (acc : Fin nr) : WM ns nr := if u then .ifs X (togW acc) .skip else .skip

theorem condTog_spec (u : Bool) (X : Fin (ns + 1)) (acc : Fin nr) (a x : Bool) (σ : WState ns nr)
    (hacc : σ.val acc = a.toNat) (hx : wbit σ X = x) (hcap : 1 ≤ cap) :
    WExec cap (condTog u X acc) σ (σ.setv acc (xor a (u && x)).toNat) 5 := by
  cases u
  · simp only [condTog, Bool.false_and, Bool.xor_false]
    rw [← hacc, setv_self]
    exact WExec.mono (WExec.skip σ) (by omega)
  · simp only [condTog, Bool.true_and, if_true]
    cases x
    · rw [Bool.xor_false, ← hacc, setv_self]
      exact WExec.mono (WExec.ifsF hx (WExec.skip σ)) (by omega)
    · cases a
      · have h1 := WExec.inc (cap := cap) acc σ (by rw [hacc]; simp; omega)
        rw [hacc] at h1
        exact WExec.mono (WExec.ifsT hx (WExec.ifrF (by rw [hacc]; rfl) h1)) (by omega)
      · have h1 := WExec.dec (cap := cap) acc σ (by rw [hacc]; simp; omega)
        rw [hacc] at h1
        exact WExec.mono (WExec.ifsT hx (WExec.ifrT (by rw [hacc]; simp) h1)) (by omega)

/-- Emit the register's bit (`acc ∈ {0,1}`) and clear it. -/
def emitBit (O : Fin (ns + 1)) (acc : Fin nr) : WM ns nr := .ifr acc (.seq (emitW O true) (.dec acc)) (emitW O false)

theorem emitBit_spec (O : Fin (ns + 1)) (acc : Fin nr) (b : Bool) (σ : WState ns nr) (hacc : σ.val acc = b.toNat)
    (hO : σ.sh O = (σ.st O).length) (hcap : 1 ≤ cap) :
    WExec cap (emitBit O acc) σ (((σ.sets O (σ.st O ++ [b])).seth O ((σ.st O).length + 1)).setv acc 0) 6 := by
  cases b
  · have h1 := emitW_spec (cap := cap) O false σ hO
    have e : ((σ.sets O (σ.st O ++ [false])).seth O ((σ.st O).length + 1)).setv acc 0 =
        (σ.sets O (σ.st O ++ [false])).seth O ((σ.st O).length + 1) := by
      have : ((σ.sets O (σ.st O ++ [false])).seth O ((σ.st O).length + 1)).val acc = 0 := by
        simp [WState.sets, WState.seth, hacc]
      rw [← this, setv_self]
    rw [e]
    exact WExec.mono (WExec.ifrF (by rw [hacc]; rfl) h1) (by omega)
  · have h1 := emitW_spec (cap := cap) O true σ hO
    have h2 := WExec.dec (cap := cap) acc ((σ.sets O (σ.st O ++ [true])).seth O ((σ.st O).length + 1))
      (by simp [WState.sets, WState.seth, hacc]; omega)
    have e : ((σ.sets O (σ.st O ++ [true])).seth O ((σ.st O).length + 1)).val acc - 1 = 0 := by
      simp [WState.sets, WState.seth, hacc]
    rw [e] at h2
    exact WExec.mono (WExec.ifrT (by rw [hacc]; simp) (WExec.seq h1 h2)) (by omega)

/-- **One coordinate of a corner**: read the three bits, emit `[1, a ⊕ (u ∧ b) ⊕ (v ∧ c)]`, step past the pairs. -/
def xorStep (u v : Bool) (O A B C : Fin (ns + 1)) (acc cnt : Fin nr) : WM ns nr :=
  .seq (.fwd A) (.seq (.fwd B) (.seq (.fwd C) (.seq (condTog true A acc) (.seq (condTog u B acc)
    (.seq (condTog v C acc) (.seq (emitW O true) (.seq (emitBit O acc) (.seq (.fwd A) (.seq (.fwd B)
    (.seq (.fwd C) (.seq (.inc cnt) (.inc cnt))))))))))))

/-- The corner loop's state after `k` coordinates: the output `out` appended, the heads at `2k`, the count `2k`. -/
structure CAt (O A B C : Fin (ns + 1)) (acc cnt : Fin nr) (σ0 σ : WState ns nr) (out : List Bool) (k : ℕ) :
    Prop where
  sO : σ.st O = σ0.st O ++ out
  hO : σ.sh O = (σ.st O).length
  sA : σ.st A = σ0.st A
  sB : σ.st B = σ0.st B
  sC : σ.st C = σ0.st C
  hA : σ.sh A = 2 * k
  hB : σ.sh B = 2 * k
  hC : σ.sh C = 2 * k
  vacc : σ.val acc = 0
  vcnt : σ.val cnt = 2 * k
  frS : ∀ i, i ≠ O → i ≠ A → i ≠ B → i ≠ C → σ.st i = σ0.st i ∧ σ.sh i = σ0.sh i
  frR : ∀ r, r ≠ acc → r ≠ cnt → σ.val r = σ0.val r
  cell : σ.cell = σ0.cell

variable {O A B C : Fin (ns + 1)} {acc cnt : Fin nr}

theorem xorStep_spec (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hac : acc ≠ cnt) (u v : Bool) (XA XB XC rA rB rC : List Bool) (σ0 σ : WState ns nr) (out : List Bool) (k : ℕ)
    (hA0 : σ0.st A = frameP XA ++ false :: rA) (hB0 : σ0.st B = frameP XB ++ false :: rB)
    (hC0 : σ0.st C = frameP XC ++ false :: rC) (hk : k < XA.length) (hkB : k < XB.length) (hkC : k < XC.length)
    (hcap : 2 * k + 2 ≤ cap) (h : CAt O A B C acc cnt σ0 σ out k) :
    ∃ τ, WExec cap (xorStep u v O A B C acc cnt) σ τ 70 ∧
      CAt O A B C acc cnt σ0 τ (out ++ [true, xb u v (XA.getD k false) (XB.getD k false) (XC.getD k false)])
        (k + 1) := by
  have hBA : B ≠ A := Ne.symm hAB
  have hCA : C ≠ A := Ne.symm hAC
  have hCB : C ≠ B := Ne.symm hBC
  have hAO : A ≠ O := Ne.symm hOA
  have hBO : B ≠ O := Ne.symm hOB
  have hCO : C ≠ O := Ne.symm hOC
  have hca : cnt ≠ acc := Ne.symm hac
  -- three steps forward
  have s1 := WExec.fwd (cap := cap) A σ
  have s2 := WExec.fwd (cap := cap) B (σ.seth A (σ.sh A + 1))
  have s3 := WExec.fwd (cap := cap) C ((σ.seth A (σ.sh A + 1)).seth B ((σ.seth A (σ.sh A + 1)).sh B + 1))
  obtain ⟨σ3, hσ3⟩ : ∃ x, x = ((σ.seth A (σ.sh A + 1)).seth B ((σ.seth A (σ.sh A + 1)).sh B + 1)).seth C
      (((σ.seth A (σ.sh A + 1)).seth B ((σ.seth A (σ.sh A + 1)).sh B + 1)).sh C + 1) := ⟨_, rfl⟩
  rw [← hσ3] at s3
  have f3 : σ3.st = σ.st ∧ σ3.val = σ.val ∧ σ3.cell = σ.cell := by rw [hσ3]; exact ⟨rfl, rfl, rfl⟩
  have f3A : σ3.sh A = 2 * k + 1 := by rw [hσ3]; simp [WState.seth, Function.update_apply, hAB, hAC, h.hA]
  have f3B : σ3.sh B = 2 * k + 1 := by rw [hσ3]; simp [WState.seth, Function.update_apply, hBA, hBC, h.hB]
  have f3C : σ3.sh C = 2 * k + 1 := by rw [hσ3]; simp [WState.seth, Function.update_apply, hCA, hCB, h.hC]
  have f3O : σ3.sh O = σ.sh O := by rw [hσ3]; simp [WState.seth, Function.update_apply, hOA, hOB, hOC]
  have f3X : ∀ i, i ≠ A → i ≠ B → i ≠ C → σ3.sh i = σ.sh i := by
    intro i h1 h2 h3; rw [hσ3]; simp [WState.seth, Function.update_apply, h1, h2, h3]
  -- the three bits
  have bA : wbit σ3 A = XA.getD k false := by
    unfold wbit; rw [f3.1, f3A, h.sA, hA0]; exact readTapeBit_frameP XA _ k hk
  have t4 := condTog_spec cap true A acc false (XA.getD k false) σ3 (by rw [f3.2.1, h.vacc]; rfl) bA (by omega)
  obtain ⟨σ4, hσ4⟩ : ∃ x, x = σ3.setv acc (xor false (true && XA.getD k false)).toNat := ⟨_, rfl⟩
  rw [← hσ4] at t4
  have bB : wbit σ4 B = XB.getD k false := by
    rw [hσ4]
    show readTapeBit (σ3.st B) (σ3.sh B) = _
    rw [f3.1, f3B, h.sB, hB0]; exact readTapeBit_frameP XB _ k hkB
  have t5 := condTog_spec cap u B acc (xor false (true && XA.getD k false)) (XB.getD k false) σ4
    (by rw [hσ4]; simp [WState.setv]) bB (by omega)
  obtain ⟨σ5, hσ5⟩ : ∃ x, x = σ4.setv acc (xor (xor false (true && XA.getD k false)) (u && XB.getD k false)).toNat :=
    ⟨_, rfl⟩
  rw [← hσ5] at t5
  have bC : wbit σ5 C = XC.getD k false := by
    rw [hσ5, hσ4]
    show readTapeBit (σ3.st C) (σ3.sh C) = _
    rw [f3.1, f3C, h.sC, hC0]; exact readTapeBit_frameP XC _ k hkC
  have t6 := condTog_spec cap v C acc (xor (xor false (true && XA.getD k false)) (u && XB.getD k false))
    (XC.getD k false) σ5 (by rw [hσ5]; simp [WState.setv]) bC (by omega)
  have e6 : xor (xor (xor false (true && XA.getD k false)) (u && XB.getD k false)) (v && XC.getD k false) =
      xb u v (XA.getD k false) (XB.getD k false) (XC.getD k false) := by
    simp [xb]
  rw [e6] at t6
  obtain ⟨σ6, hσ6⟩ : ∃ x, x = σ5.setv acc (xb u v (XA.getD k false) (XB.getD k false) (XC.getD k false)).toNat :=
    ⟨_, rfl⟩
  rw [← hσ6] at t6
  have f6 : σ6.st = σ3.st ∧ σ6.sh = σ3.sh ∧ σ6.cell = σ3.cell := by rw [hσ6, hσ5, hσ4]; exact ⟨rfl, rfl, rfl⟩
  have f6v : ∀ r, r ≠ acc → σ6.val r = σ.val r := by
    intro r hr; rw [hσ6, hσ5, hσ4]; simp [WState.setv, Function.update_apply, hr, f3.2.1]
  -- the marker and the bit
  have hO6 : σ6.sh O = (σ6.st O).length := by rw [f6.1, f6.2.1, f3O, f3.1]; exact h.hO
  have t7 := emitW_spec (cap := cap) O true σ6 hO6
  obtain ⟨σ7, hσ7⟩ : ∃ x, x = (σ6.sets O (σ6.st O ++ [true])).seth O ((σ6.st O).length + 1) := ⟨_, rfl⟩
  rw [← hσ7] at t7
  have t8 := emitBit_spec cap O acc (xb u v (XA.getD k false) (XB.getD k false) (XC.getD k false)) σ7
    (by rw [hσ7, hσ6]; simp [WState.sets, WState.seth, WState.setv]) (by rw [hσ7]; simp [WState.sets, WState.seth])
    (by omega)
  obtain ⟨σ8, hσ8⟩ : ∃ x, x = ((σ7.sets O (σ7.st O ++ [xb u v (XA.getD k false) (XB.getD k false)
      (XC.getD k false)])).seth O ((σ7.st O).length + 1)).setv acc 0 := ⟨_, rfl⟩
  rw [← hσ8] at t8
  have f8O : σ8.st O = σ.st O ++ [true, xb u v (XA.getD k false) (XB.getD k false) (XC.getD k false)] ∧
      σ8.sh O = (σ8.st O).length := by
    rw [hσ8, hσ7]
    simp [WState.sets, WState.seth, WState.setv, f6.1, f3.1, List.append_assoc]
  have f8X : ∀ i, i ≠ O → σ8.st i = σ.st i ∧ σ8.sh i = σ3.sh i := by
    intro i hi
    rw [hσ8, hσ7]
    simp [WState.sets, WState.seth, WState.setv, Function.update_apply, hi, f6.1, f6.2.1, f3.1]
  have f8v : σ8.val acc = 0 ∧ ∀ r, r ≠ acc → σ8.val r = σ.val r := by
    rw [hσ8, hσ7]
    refine ⟨by simp [WState.setv], fun r hr => ?_⟩
    simp [WState.sets, WState.seth, WState.setv, Function.update_apply, hr, f6v r hr]
  have f8c : σ8.cell = σ.cell := by rw [hσ8, hσ7]; simp [WState.sets, WState.seth, WState.setv, f6.2.2, f3.2.2]
  -- three steps forward, the count
  have s9 := WExec.fwd (cap := cap) A σ8
  have s10 := WExec.fwd (cap := cap) B (σ8.seth A (σ8.sh A + 1))
  have s11 := WExec.fwd (cap := cap) C ((σ8.seth A (σ8.sh A + 1)).seth B ((σ8.seth A (σ8.sh A + 1)).sh B + 1))
  obtain ⟨σ11, hσ11⟩ : ∃ x, x = ((σ8.seth A (σ8.sh A + 1)).seth B ((σ8.seth A (σ8.sh A + 1)).sh B + 1)).seth C
      (((σ8.seth A (σ8.sh A + 1)).seth B ((σ8.seth A (σ8.sh A + 1)).sh B + 1)).sh C + 1) := ⟨_, rfl⟩
  rw [← hσ11] at s11
  have f11 : σ11.st = σ8.st ∧ σ11.val = σ8.val ∧ σ11.cell = σ8.cell := by rw [hσ11]; exact ⟨rfl, rfl, rfl⟩
  have f11A : σ11.sh A = 2 * k + 2 := by
    rw [hσ11]; simp [WState.seth, Function.update_apply, hAB, hAC, (f8X A hAO).2, f3A]
  have f11B : σ11.sh B = 2 * k + 2 := by
    rw [hσ11]; simp [WState.seth, Function.update_apply, hBA, hBC, (f8X B hBO).2, f3B]
  have f11C : σ11.sh C = 2 * k + 2 := by
    rw [hσ11]; simp [WState.seth, Function.update_apply, hCA, hCB, (f8X C hCO).2, f3C]
  have f11X : ∀ i, i ≠ A → i ≠ B → i ≠ C → σ11.sh i = σ8.sh i := by
    intro i h1 h2 h3; rw [hσ11]; simp [WState.seth, Function.update_apply, h1, h2, h3]
  have v11 : σ11.val cnt = 2 * k := by rw [f11.2.1, (f8v.2 cnt hca), h.vcnt]
  have s12 := WExec.inc (cap := cap) cnt σ11 (by rw [v11]; omega)
  have s13 := WExec.inc (cap := cap) cnt (σ11.setv cnt (σ11.val cnt + 1)) (by simp [WState.setv, v11]; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq t4 (WExec.seq t5 (WExec.seq t6
    (WExec.seq t7 (WExec.seq t8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 (WExec.seq s12 s13)))))))))))) (by omega),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show σ11.st O = _
    rw [f11.1, f8O.1, h.sO, List.append_assoc]
  · show σ11.sh O = (σ11.st O).length
    rw [f11X O hOA hOB hOC, f11.1]; exact f8O.2
  · show σ11.st A = _; rw [f11.1, (f8X A hAO).1, h.sA]
  · show σ11.st B = _; rw [f11.1, (f8X B hBO).1, h.sB]
  · show σ11.st C = _; rw [f11.1, (f8X C hCO).1, h.sC]
  · show σ11.sh A = _; rw [f11A]; ring
  · show σ11.sh B = _; rw [f11B]; ring
  · show σ11.sh C = _; rw [f11C]; ring
  · show (Function.update (Function.update σ11.val cnt (σ11.val cnt + 1)) cnt _) acc = 0
    simp [Function.update_apply, hac, f11.2.1, f8v.1]
  · show (Function.update (Function.update σ11.val cnt (σ11.val cnt + 1)) cnt _) cnt = _
    simp [Function.update_apply, v11]; ring
  · intro i h1 h2 h3 h4
    show σ11.st i = σ0.st i ∧ σ11.sh i = σ0.sh i
    rw [f11.1, f11X i h2 h3 h4, (f8X i h1).1, (f8X i h1).2, f3X i h2 h3 h4]
    exact h.frS i h1 h2 h3 h4
  · intro r h1 h2
    show (Function.update (Function.update σ11.val cnt (σ11.val cnt + 1)) cnt _) r = σ0.val r
    simp [Function.update_apply, h2, f11.2.1, f8v.2 r h1]
    exact h.frR r h1 h2
  · show σ11.cell = σ0.cell
    rw [f11.2.2, f8c]; exact h.cell

theorem frameP_snoc (l : List Bool) (x : Bool) : frameP (l ++ [x]) = frameP l ++ [true, x] := by
  simp [frameP, List.flatMap_append]

theorem xorLoop_spec (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hac : acc ≠ cnt) (u v : Bool) (XA XB XC rA rB rC : List Bool) (σ0 : WState ns nr)
    (hA0 : σ0.st A = frameP XA ++ false :: rA) (hB0 : σ0.st B = frameP XB ++ false :: rB)
    (hC0 : σ0.st C = frameP XC ++ false :: rC) (n : ℕ) (hlA : XA.length = n) (hlB : XB.length = n)
    (hlC : XC.length = n) (hcap : 2 * n + 2 ≤ cap) (m : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), k + m = n → CAt O A B C acc cnt σ0 σ (frameP ((xw u v XA XB XC).take k)) k →
      ∃ τ, WExec cap (.whs A (xorStep u v O A B C acc cnt)) σ τ (m * 72 + 1) ∧
        CAt O A B C acc cnt σ0 τ (frameP (xw u v XA XB XC)) n := by
  induction m with
  | zero =>
    intro k σ hkm h
    have hkn : k = n := by omega
    subst hkn
    have hb : wbit σ A = false := by unfold wbit; rw [h.sA, h.hA, hA0, ← hlA]; exact rd_end XA rA
    have e : (xw u v XA XB XC).take k = xw u v XA XB XC := List.take_of_length_le (by rw [xw_length]; omega)
    rw [e] at h
    exact ⟨σ, WExec.mono (WExec.whsF hb) (by omega), h⟩
  | succ m ih =>
    intro k σ hkm h
    have hb : wbit σ A = true := by
      unfold wbit; rw [h.sA, h.hA, hA0]; exact readTapeBit_frameP_marker XA _ k (by omega)
    obtain ⟨τ1, e1, h1⟩ := xorStep_spec cap hOA hOB hOC hAB hAC hBC hac u v XA XB XC rA rB rC σ0 σ _ k hA0 hB0 hC0
      (by omega) (by omega) (by omega) (by omega) h
    have e : frameP ((xw u v XA XB XC).take (k + 1)) = frameP ((xw u v XA XB XC).take k) ++
        [true, xb u v (XA.getD k false) (XB.getD k false) (XC.getD k false)] := by
      rw [xw_take_succ u v XA XB XC k (by omega) (by omega) (by omega), frameP_snoc]
    obtain ⟨τ, e2, h2⟩ := ih (k + 1) τ1 (by omega) (by rw [e]; exact h1)
    exact ⟨τ, WExec.mono (WExec.whsT hb e1 e2) (by ring_nf; omega), h2⟩

/-- Put the three heads back at `0` (the count `cnt` records the distance). -/
def rew3 (A B C : Fin (ns + 1)) (cnt : Fin nr) : WM ns nr :=
  .whr cnt (.seq (.bwd A) (.seq (.bwd B) (.seq (.bwd C) (.dec cnt))))

theorem rew3_spec (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (c : ℕ) :
    ∀ σ : WState ns nr, σ.val cnt = c → σ.sh A = c → σ.sh B = c → σ.sh C = c → c ≤ cap →
      ∃ τ, WExec cap (rew3 A B C cnt) σ τ (c * 9 + 1) ∧ τ.sh A = 0 ∧ τ.sh B = 0 ∧ τ.sh C = 0 ∧ τ.val cnt = 0 ∧
        τ.st = σ.st ∧ (∀ i, i ≠ A → i ≠ B → i ≠ C → τ.sh i = σ.sh i) ∧ (∀ r, r ≠ cnt → τ.val r = σ.val r) ∧
        τ.cell = σ.cell := by
  have hBA : B ≠ A := Ne.symm hAB
  have hCA : C ≠ A := Ne.symm hAC
  have hCB : C ≠ B := Ne.symm hBC
  induction c with
  | zero =>
    intro σ hv hA hB hC _
    exact ⟨σ, WExec.whrF hv, hA, hB, hC, hv, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl⟩
  | succ c ih =>
    intro σ hv hA hB hC hc
    have s1 := WExec.bwd (cap := cap) A σ
    have s2 := WExec.bwd (cap := cap) B (σ.seth A (σ.sh A - 1))
    have s3 := WExec.bwd (cap := cap) C ((σ.seth A (σ.sh A - 1)).seth B ((σ.seth A (σ.sh A - 1)).sh B - 1))
    obtain ⟨σ3, hσ3⟩ : ∃ x, x = ((σ.seth A (σ.sh A - 1)).seth B ((σ.seth A (σ.sh A - 1)).sh B - 1)).seth C
        (((σ.seth A (σ.sh A - 1)).seth B ((σ.seth A (σ.sh A - 1)).sh B - 1)).sh C - 1) := ⟨_, rfl⟩
    rw [← hσ3] at s3
    have s4 := WExec.dec (cap := cap) cnt σ3 (by rw [hσ3]; show σ.val cnt ≤ cap; omega)
    obtain ⟨σ4, hσ4⟩ : ∃ x, x = σ3.setv cnt (σ3.val cnt - 1) := ⟨_, rfl⟩
    rw [← hσ4] at s4
    have f4 : σ4.val cnt = c ∧ σ4.sh A = c ∧ σ4.sh B = c ∧ σ4.sh C = c ∧ σ4.st = σ.st ∧
        (∀ i, i ≠ A → i ≠ B → i ≠ C → σ4.sh i = σ.sh i) ∧ (∀ r, r ≠ cnt → σ4.val r = σ.val r) ∧
        σ4.cell = σ.cell := by
      rw [hσ4, hσ3]
      refine ⟨by simp [WState.seth, WState.setv, hv], by simp [WState.seth, WState.setv, Function.update_apply,
        hAB, hAC, hA], by simp [WState.seth, WState.setv, Function.update_apply, hBA, hBC, hB],
        by simp [WState.seth, WState.setv, Function.update_apply, hCA, hCB, hC], rfl, fun i h1 h2 h3 => ?_,
        fun r hr => ?_, rfl⟩
      · simp [WState.seth, WState.setv, Function.update_apply, h1, h2, h3]
      · simp [WState.seth, WState.setv, Function.update_apply, hr]
    obtain ⟨τ, e, t1, t2, t3, t4, t5, t6, t7, t8⟩ := ih σ4 f4.1 f4.2.1 f4.2.2.1 f4.2.2.2.1 (by omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by rw [hv]; omega)
      (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) e) (by ring_nf; omega), t1, t2, t3, t4,
      t5.trans f4.2.2.2.2.1, fun i h1 h2 h3 => (t6 i h1 h2 h3).trans (f4.2.2.2.2.2.1 i h1 h2 h3),
      fun r hr => (t7 r hr).trans (f4.2.2.2.2.2.2.1 r hr), t8.trans f4.2.2.2.2.2.2.2⟩

/-- **One corner's flip pattern**: the corner word of the three framed words appended to `O` as a frame, the
heads back at `0`. -/
def cornerW (u v : Bool) (O A B C : Fin (ns + 1)) (acc cnt : Fin nr) : WM ns nr :=
  .seq (.whs A (xorStep u v O A B C acc cnt)) (.seq (emitW O false) (rew3 A B C cnt))

/-- The corner's effect: `w` appended to the output, the three words kept and rewound, the two registers `0`. -/
structure COut (O A B C : Fin (ns + 1)) (acc cnt : Fin nr) (σ τ : WState ns nr) (w : List Bool) : Prop where
  sO : τ.st O = σ.st O ++ w
  hO : τ.sh O = (τ.st O).length
  sA : τ.st A = σ.st A
  sB : τ.st B = σ.st B
  sC : τ.st C = σ.st C
  hA : τ.sh A = 0
  hB : τ.sh B = 0
  hC : τ.sh C = 0
  vacc : τ.val acc = 0
  vcnt : τ.val cnt = 0
  frS : ∀ i, i ≠ O → i ≠ A → i ≠ B → i ≠ C → τ.st i = σ.st i ∧ τ.sh i = σ.sh i
  frR : ∀ r, r ≠ acc → r ≠ cnt → τ.val r = σ.val r
  cell : τ.cell = σ.cell

/-- The corner's cost bound. -/
def cornerCost (n : ℕ) : ℕ := n * 72 + 1 + 1 + (3 + 1 + (2 * n * 9 + 1))

theorem cornerW_spec (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hac : acc ≠ cnt) (u v : Bool) (XA XB XC rA rB rC : List Bool) (σ : WState ns nr)
    (hA0 : σ.st A = frameP XA ++ false :: rA) (hB0 : σ.st B = frameP XB ++ false :: rB)
    (hC0 : σ.st C = frameP XC ++ false :: rC) (n : ℕ) (hlA : XA.length = n) (hlB : XB.length = n)
    (hlC : XC.length = n) (hsA : σ.sh A = 0) (hsB : σ.sh B = 0) (hsC : σ.sh C = 0)
    (hO : σ.sh O = (σ.st O).length) (hacc : σ.val acc = 0) (hcnt : σ.val cnt = 0) (hcap : 2 * n + 2 ≤ cap) :
    ∃ τ, WExec cap (cornerW u v O A B C acc cnt) σ τ (cornerCost n) ∧
      COut O A B C acc cnt σ τ (frame (xw u v XA XB XC)) := by
  have hAO : A ≠ O := Ne.symm hOA
  have hBO : B ≠ O := Ne.symm hOB
  have hCO : C ≠ O := Ne.symm hOC
  have h0 : CAt O A B C acc cnt σ σ (frameP ((xw u v XA XB XC).take 0)) 0 :=
    ⟨by simp, hO, rfl, rfl, rfl, by rw [hsA], by rw [hsB], by rw [hsC], hacc, by rw [hcnt],
      fun _ _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, rfl⟩
  obtain ⟨τ1, e1, h1⟩ := xorLoop_spec cap hOA hOB hOC hAB hAC hBC hac u v XA XB XC rA rB rC σ hA0 hB0 hC0 n hlA hlB
    hlC hcap n 0 σ (by omega) h0
  have e2 := emitW_spec (cap := cap) O false τ1 h1.hO
  obtain ⟨τ2, hτ2⟩ : ∃ x, x = (τ1.sets O (τ1.st O ++ [false])).seth O ((τ1.st O).length + 1) := ⟨_, rfl⟩
  rw [← hτ2] at e2
  have f2 : τ2.st O = σ.st O ++ frame (xw u v XA XB XC) ∧ τ2.sh O = (τ2.st O).length ∧
      (∀ i, i ≠ O → τ2.st i = τ1.st i ∧ τ2.sh i = τ1.sh i) ∧ τ2.val = τ1.val ∧ τ2.cell = τ1.cell := by
    rw [hτ2]
    refine ⟨by simp [WState.sets, WState.seth, h1.sO, frame_eq_frameP, List.append_assoc],
      by simp [WState.sets, WState.seth], fun i hi => ?_, rfl, rfl⟩
    simp [WState.sets, WState.seth, Function.update_apply, hi]
  obtain ⟨τ, e3, t1, t2, t3, t4, t5, t6, t7, t8⟩ := rew3_spec cap hAB hAC hBC (2 * n) τ2
    (by rw [f2.2.2.2.1, h1.vcnt]) (by rw [(f2.2.2.1 A hAO).2, h1.hA]) (by rw [(f2.2.2.1 B hBO).2, h1.hB])
    (by rw [(f2.2.2.1 C hCO).2, h1.hC]) (by omega)
  refine ⟨τ, WExec.seq e1 (WExec.seq e2 e3), ⟨?_, ?_, ?_, ?_, ?_, t1, t2, t3, ?_, t4, ?_, ?_, ?_⟩⟩
  · rw [t5]; exact f2.1
  · rw [t6 O hOA hOB hOC, t5]; exact f2.2.1
  · rw [t5, (f2.2.2.1 A hAO).1, h1.sA]
  · rw [t5, (f2.2.2.1 B hBO).1, h1.sB]
  · rw [t5, (f2.2.2.1 C hCO).1, h1.sC]
  · rw [t7 acc hac, f2.2.2.2.1, h1.vacc]
  · intro i h1' h2 h3 h4
    rw [t5, t6 i h2 h3 h4, (f2.2.2.1 i h1').1, (f2.2.2.1 i h1').2]
    exact h1.frS i h1' h2 h3 h4
  · intro r h1' h2
    rw [t7 r h2, f2.2.2.2.1]
    exact h1.frR r h1' h2
  · rw [t8, f2.2.2.2.2]; exact h1.cell

end Corner

end NearCubicWires.WireExponent3_5.PrimT.Flips
