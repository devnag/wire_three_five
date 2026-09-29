import Proof.Wire_3_5.UnionMachine.CWWords

/-! # C6 front, U5, the code writers: a binary counter as a serializer's field list

The encoding parity of a systematic variable (P3:3092-3094, 3409-3410; `unionParityAtom`) is a circuit of
`k = |S|` staircase bottoms `[Σ_{i∈S} x_i ≥ j+1]`, and its code carries `encodeNat (j+1)` for every `j < k` and
`encodeNat k`. `encodeNat n` is the balanced list of the bits of `n` (`encodeBits n.bits`), which base's serializer
writes from the fields `[b]`, one per bit. This module keeps the counter in exactly that form: the stream
`sgl n.bits` (one framed singleton per bit, least significant first) and its count word `false :: 1^|n.bits|`.
* **`bits_succ`**: `(n+1).bits = incBits n.bits` (carry through the low ones);
* **`incW_spec`**: one increment of the counter in place, streams only.

Paper quantity of the main type: the bits of `j + 1` of the parity's `j`-th bottom threshold, as serializer fields. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-! ## The bits of a successor -/

/-- Binary increment of a least-significant-first bit list. -/
def incBits : List Bool → List Bool
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: incBits r

theorem bits_succ : ∀ n : ℕ, (n + 1).bits = incBits n.bits := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · decide
      · have h1 : (2 * m).bits = false :: m.bits := by
          have := Nat.bits_append_bit m false (by intro h; omega)
          rwa [Nat.bit_val] at this
        have h2 : (2 * m + 1).bits = true :: m.bits := by
          have := Nat.bits_append_bit m true (by simp)
          rwa [Nat.bit_val] at this
        rw [h1, h2]; rfl
    · have h1 : (2 * m + 1).bits = true :: m.bits := by
        have := Nat.bits_append_bit m true (by simp)
        rwa [Nat.bit_val] at this
      have h2 : (2 * m + 1 + 1).bits = false :: (m + 1).bits := by
        have := Nat.bits_append_bit (m + 1) false (by intro h; omega)
        rw [Nat.bit_val] at this
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) + (false).toNat by simp; ring]; exact this
      rw [h1, h2, ih m (by omega)]; rfl

/-- The in-place part of an increment: the list with its low ones cleared and its first zero set, and whether a
zero was found. -/
def incCore : List Bool → List Bool × Bool
  | [] => ([], false)
  | false :: r => (true :: r, true)
  | true :: r => (false :: (incCore r).1, (incCore r).2)

theorem incCore_len : ∀ l : List Bool, (incCore l).1.length = l.length
  | [] => rfl
  | false :: r => rfl
  | true :: r => by simp [incCore, incCore_len r]

theorem incBits_core : ∀ l : List Bool,
    incBits l = if (incCore l).2 then (incCore l).1 else (incCore l).1 ++ [true]
  | [] => rfl
  | false :: r => rfl
  | true :: r => by
    rw [incBits, incBits_core r]
    by_cases h : (incCore r).2 = true
    · simp [incCore, h]
    · simp [incCore, h]

/-! ## The fields -/

/-- One framed singleton per bit. -/
def sgl (l : List Bool) : List Bool := l.flatMap fun b => [true, b, false]

theorem sgl_eq (l : List Bool) : sgl l = (l.map fun b => [b]).flatMap frame := by
  unfold sgl; rw [List.flatMap_map]; rfl

theorem sgl_length (l : List Bool) : (sgl l).length = 3 * l.length := by
  unfold sgl
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.flatMap_cons, ih] at *; omega

theorem sgl_cons (b : Bool) (l : List Bool) : sgl (b :: l) = [true, b, false] ++ sgl l := rfl

theorem sgl_append (l l' : List Bool) : sgl (l ++ l') = sgl l ++ sgl l' := by
  unfold sgl; rw [List.flatMap_append]

section Loop
variable {ns nr : ℕ} (cap : ℕ)

/-- Walk every remaining triple. -/
def skipT (C : Fin (ns + 1)) : WM ns nr := .whs C (.seq (.fwd C) (.seq (.fwd C) (.fwd C)))

theorem skipT_spec (C : Fin (ns + 1)) :
    ∀ (l pre : List Bool) (σ : WState ns nr), σ.st C = pre ++ sgl l → σ.sh C = pre.length →
      WExec cap (skipT C) σ (σ.seth C (pre.length + 3 * l.length)) (l.length * 7 + 1)
  | [], pre, σ, hC, hCh => by
    have hz : wbit σ C = false := by unfold wbit; rw [hC, hCh]; unfold readTapeBit; simp [sgl]
    have e : σ.seth C (pre.length + 3 * ([] : List Bool).length) = σ := by
      rw [List.length_nil, Nat.mul_zero, Nat.add_zero, ← hCh, wseth_same]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by omega)
  | b :: l, pre, σ, hC, hCh => by
    have hr : wbit σ C = true := by unfold wbit; rw [hC, hCh, sgl_cons]; unfold readTapeBit; simp
    have s1 := WExec.fwd (cap := cap) C σ
    have s2 := WExec.fwd (cap := cap) C (σ.seth C (σ.sh C + 1))
    have s3 := WExec.fwd (cap := cap) C ((σ.seth C (σ.sh C + 1)).seth C ((σ.seth C (σ.sh C + 1)).sh C + 1))
    have ih := skipT_spec C l (pre ++ [true, b, false])
      (((σ.seth C (σ.sh C + 1)).seth C ((σ.seth C (σ.sh C + 1)).sh C + 1)).seth C
        (((σ.seth C (σ.sh C + 1)).seth C ((σ.seth C (σ.sh C + 1)).sh C + 1)).sh C + 1))
      (by simp [hC, sgl_cons]) (by simp [hCh])
    have e : (((((σ.seth C (σ.sh C + 1)).seth C ((σ.seth C (σ.sh C + 1)).sh C + 1)).seth C
        (((σ.seth C (σ.sh C + 1)).seth C ((σ.seth C (σ.sh C + 1)).sh C + 1)).sh C + 1))).seth C
        ((pre ++ [true, b, false]).length + 3 * l.length)) = σ.seth C (pre.length + 3 * (b :: l).length) := by
      simp only [wseth_seth]; congr 1; simp; ring
    rw [e] at ih
    exact WExec.mono (WExec.whsT hr (WExec.seq s1 (WExec.seq s2 s3)) ih) (by simp; ring_nf; omega)

/-! ## The increment loop -/

/-- On a bit `1`: clear it and move to the next triple; on a bit `0`: set it, raise the flag `K`, walk to the end. -/
def bodyI (C K : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd C) (.ifs C (.seq (.wr C false) (.seq (.fwd C) (.fwd C)))
    (.seq (.wr C true) (.seq (.wr K true) (.seq (.fwd C) (.seq (.fwd C) (skipT C))))))

theorem incLoop_spec (C K : Fin (ns + 1)) (hCK : C ≠ K) :
    ∀ (l pre : List Bool) (σ : WState ns nr), σ.st C = pre ++ sgl l → σ.sh C = pre.length → σ.st K = [false] →
      σ.sh K = 0 →
      ∃ τ, WExec cap (.whs C (bodyI C K)) σ τ (l.length * 20 + 20) ∧ τ.st C = pre ++ sgl (incCore l).1 ∧
        τ.sh C = pre.length + 3 * l.length ∧ τ.st K = [(incCore l).2] ∧ τ.sh K = 0 ∧
        (∀ j, j ≠ C → j ≠ K → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, σ, hC, hCh, hK, hKh => by
    have hz : wbit σ C = false := by unfold wbit; rw [hC, hCh]; unfold readTapeBit; simp [sgl]
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by rw [hC]; rfl, by simp [hCh], by rw [hK]; rfl, hKh,
      fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | false :: r, pre, σ, hC, hCh, hK, hKh => by
    have hKC : K ≠ C := fun e => hCK e.symm
    have hr : wbit σ C = true := by unfold wbit; rw [hC, hCh, sgl_cons]; unfold readTapeBit; simp
    have s1 := WExec.fwd (cap := cap) C σ
    set σ1 := σ.seth C (σ.sh C + 1) with hσ1
    have hb : wbit σ1 C = false := by
      unfold wbit; simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hC, hCh, sgl_cons]; unfold readTapeBit; simp
    have s2 := WExec.wr (cap := cap) C true σ1
    set σ2 := σ1.sets C (writeTapeBit (σ1.st C) (σ1.sh C) true) with hσ2
    have e2 : σ2.st C = (pre ++ [true]) ++ true :: (false :: sgl r) := by
      simp only [hσ2, hσ1, WState.sets_st, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hC, hCh, sgl_cons]
      have := writeTapeBit_mid (pre ++ [true]) (false :: sgl r) false true
      simp only [List.length_append, List.length_singleton] at this
      simpa [List.append_assoc] using this
    have s3 := WExec.wr (cap := cap) K true σ2
    set σ3 := σ2.sets K (writeTapeBit (σ2.st K) (σ2.sh K) true) with hσ3
    have s4 := WExec.fwd (cap := cap) C σ3
    set σ4 := σ3.seth C (σ3.sh C + 1) with hσ4
    have s5 := WExec.fwd (cap := cap) C σ4
    set σ5 := σ4.seth C (σ4.sh C + 1) with hσ5
    have e5 : σ5.st C = (pre ++ [true, true, false]) ++ sgl r := by
      simp only [hσ5, hσ4, hσ3, WState.seth_st, WState.sets_st]; rw [Function.update_of_ne hCK, e2]; simp
    have e5h : σ5.sh C = (pre ++ [true, true, false]).length := by
      simp only [hσ5, hσ4, hσ3, hσ2, hσ1, WState.seth_sh, WState.sets_sh, Function.update_self]; rw [hCh]; simp
    have s6 := skipT_spec cap C r (pre ++ [true, true, false]) σ5 e5 e5h
    set σ6 := σ5.seth C ((pre ++ [true, true, false]).length + 3 * r.length) with hσ6
    have hz : wbit σ6 C = false := by
      unfold wbit; simp only [hσ6, WState.seth_st, WState.seth_sh, Function.update_self]; rw [e5]
      unfold readTapeBit; rw [List.getD_eq_default _ _ (by simp [sgl_length]; omega)]
    have body := WExec.seq s1 (WExec.ifsF (Q := .seq (.wr C true) (.seq (.wr K true) (.seq (.fwd C) (.seq (.fwd C)
      (skipT C))))) (P := .seq (.wr C false) (.seq (.fwd C) (.fwd C))) hb
      (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6)))))
    have loop := WExec.whsT hr body (WExec.whsF hz)
    have hK2 : σ2.st K = σ.st K ∧ σ2.sh K = σ.sh K := by
      simp [hσ2, hσ1, Function.update_of_ne hKC]
    refine ⟨σ6, WExec.mono loop (by simp; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hσ6, WState.seth_st]; rw [e5]; simp [incCore, sgl_cons]
    · simp only [hσ6, WState.seth_sh, Function.update_self]; simp; omega
    · simp only [hσ6, hσ5, hσ4, hσ3, WState.seth_st, WState.sets_st, Function.update_self]
      rw [hK2.1, hK2.2, hK, hKh]; rfl
    · simp only [hσ6, hσ5, hσ4, hσ3, WState.seth_sh, WState.sets_sh]
      rw [Function.update_of_ne hKC, Function.update_of_ne hKC, Function.update_of_ne hKC, hK2.2, hKh]
    · intro j h1 h2
      refine ⟨?_, ?_⟩
      · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]
      · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1]
    · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
    · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
  | true :: r, pre, σ, hC, hCh, hK, hKh => by
    have hKC : K ≠ C := fun e => hCK e.symm
    have hr : wbit σ C = true := by unfold wbit; rw [hC, hCh, sgl_cons]; unfold readTapeBit; simp
    have s1 := WExec.fwd (cap := cap) C σ
    set σ1 := σ.seth C (σ.sh C + 1) with hσ1
    have hb : wbit σ1 C = true := by
      unfold wbit; simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hC, hCh, sgl_cons]; unfold readTapeBit; simp
    have s2 := WExec.wr (cap := cap) C false σ1
    set σ2 := σ1.sets C (writeTapeBit (σ1.st C) (σ1.sh C) false) with hσ2
    have e2 : σ2.st C = (pre ++ [true]) ++ false :: (false :: sgl r) := by
      simp only [hσ2, hσ1, WState.sets_st, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hC, hCh, sgl_cons]
      have := writeTapeBit_mid (pre ++ [true]) (false :: sgl r) true false
      simp only [List.length_append, List.length_singleton] at this
      simpa [List.append_assoc] using this
    have s3 := WExec.fwd (cap := cap) C σ2
    set σ3 := σ2.seth C (σ2.sh C + 1) with hσ3
    have s4 := WExec.fwd (cap := cap) C σ3
    set σ4 := σ3.seth C (σ3.sh C + 1) with hσ4
    have e4 : σ4.st C = (pre ++ [true, false, false]) ++ sgl r := by
      simp only [hσ4, hσ3, WState.seth_st]; rw [e2]; simp
    have e4h : σ4.sh C = (pre ++ [true, false, false]).length := by
      simp only [hσ4, hσ3, hσ2, hσ1, WState.seth_sh, WState.sets_sh, Function.update_self]; rw [hCh]; simp
    have e4K : σ4.st K = [false] := by
      simp only [hσ4, hσ3, hσ2, hσ1, WState.seth_st, WState.sets_st]; rw [Function.update_of_ne hKC, hK]
    have e4Kh : σ4.sh K = 0 := by
      simp only [hσ4, hσ3, hσ2, hσ1, WState.seth_sh, WState.sets_sh]
      rw [Function.update_of_ne hKC, Function.update_of_ne hKC, Function.update_of_ne hKC, hKh]
    obtain ⟨τ, s5, eC, eCh, eK, eKh, oth, v5, c5⟩ := incLoop_spec C K hCK r (pre ++ [true, false, false]) σ4 e4 e4h
      e4K e4Kh
    have body := WExec.seq s1 (WExec.ifsT (P := .seq (.wr C false) (.seq (.fwd C) (.fwd C)))
      (Q := .seq (.wr C true) (.seq (.wr K true) (.seq (.fwd C) (.seq (.fwd C) (skipT C))))) hb
      (WExec.seq s2 (WExec.seq s3 s4)))
    refine ⟨τ, WExec.mono (WExec.whsT hr body s5) (by simp; ring_nf; omega), ?_, ?_, ?_, eKh, ?_, ?_, ?_⟩
    · rw [eC]; simp [incCore, sgl_cons]
    · rw [eCh]; simp; omega
    · rw [eK]; rfl
    · intro j h1 h2
      have o4 : Same σ σ4 j := ⟨by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1],
        by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1]⟩
      exact o4.trans' (oth j h1 h2)
    · rw [v5]; simp [hσ4, hσ3, hσ2, hσ1]
    · rw [c5]; simp [hσ4, hσ3, hσ2, hσ1]

end Loop

/-! ## The increment -/

/-- The carry out of the top bit: a new top bit `1`, one more `1` on the count word. -/
def tailW : WM 2 0 :=
  .seq (emitW 0 true) (.seq (emitW 0 true) (.seq (emitW 0 false) (.seq (.fwd 1) (.seq (.whs 1 (.fwd 1)) (emitW 1 true)))))

/-- **The counter's increment** (streams `0` the fields `sgl l`, `1` the count word, `2` a flag). -/
def incW : WM 2 0 := .seq (.wr 2 false) (.seq (.whs 0 (bodyI 0 2)) (.ifs 2 .skip tailW))

theorem tailW_spec (cap : ℕ) (l : List Bool) (σ : WState 2 0) (hC : σ.sh 0 = (σ.st 0).length)
    (hN : σ.st 1 = CompareMachine.word l.length) (hNh : σ.sh 1 = 0) :
    ∃ τ, WExec cap tailW σ τ (l.length * 3 + 21) ∧ τ.st 0 = σ.st 0 ++ [true, true, false] ∧
      τ.st 1 = CompareMachine.word (l.length + 1) ∧ τ.cell = σ.cell := by
  obtain ⟨σa, sa, ea, eah, oa, va, ca⟩ := emit_facts cap (0 : Fin 3) true σ hC
  obtain ⟨σb, sb, eb, ebh, ob, vb, cb⟩ := emit_facts cap (0 : Fin 3) true σa eah
  obtain ⟨σc, sc, ec, ech, oc, vc, cc⟩ := emit_facts cap (0 : Fin 3) false σb ebh
  have N3 := ((oa 1 (by decide)).trans' (ob 1 (by decide))).trans' (oc 1 (by decide))
  obtain ⟨σd, sd, ed, edh, od, vd, cd⟩ := fwd_facts cap (1 : Fin 3) σc
  have se := CWWords.onesSkip_spec cap (1 : Fin 3) [false] l.length σd
    (by rw [ed, N3.1, hN]; rfl) (by rw [edh, N3.2, hNh]; rfl)
  set σe := σd.seth 1 ([false].length + l.length) with hσe
  obtain ⟨τ, sf, ef, efh, of, vf, cf⟩ := emit_facts cap (1 : Fin 3) true σe
    (by simp [hσe, ed, N3.1, hN, CompareMachine.word]; omega)
  refine ⟨τ, WExec.mono (WExec.seq sa (WExec.seq sb (WExec.seq sc (WExec.seq sd (WExec.seq se sf))))) (by omega),
    ?_, ?_, ?_⟩
  · rw [(of 0 (by decide)).1]
    simp only [hσe, WState.seth_st]
    rw [(od 0 (by decide)).1, ec, eb, ea]; simp
  · rw [ef]; simp only [hσe, WState.seth_st]; rw [ed, N3.1, hN]
    show (false :: List.replicate l.length true) ++ [true] = false :: List.replicate (l.length + 1) true
    rw [List.replicate_succ']; rfl
  · rw [cf]; simp only [hσe, WState.seth_cell]; rw [cd, cc, cb, ca]

theorem incW_spec (cap : ℕ) (l : List Bool) (σ : WState 2 0) (h0 : ∀ j, σ.sh j = 0) (hC : σ.st 0 = sgl l)
    (hN : σ.st 1 = CompareMachine.word l.length) (hK : σ.st 2 = []) :
    ∃ τ, WExec cap incW σ τ (l.length * 23 + 50) ∧ τ.st 0 = sgl (incBits l) ∧
      τ.st 1 = CompareMachine.word (incBits l).length ∧ τ.cell = σ.cell := by
  have s1 := WExec.wr (cap := cap) (2 : Fin 3) false σ
  set σ1 := σ.sets 2 (writeTapeBit (σ.st 2) (σ.sh 2) false) with hσ1
  have e1K : σ1.st 2 = [false] := by simp [hσ1, hK, h0, writeTapeBit]
  obtain ⟨σ2, s2, eC, eCh, eK, eKh, oth, v2, c2⟩ := incLoop_spec cap (0 : Fin 3) 2 (by decide) l [] σ1
    (by simp [hσ1, hC]) (by simp [hσ1, h0]) e1K (by simp [hσ1, h0])
  have N2 := oth 1 (by decide) (by decide)
  have hbit : wbit σ2 2 = (incCore l).2 := by unfold wbit; rw [eK, eKh]; rfl
  have hcore := incBits_core l
  have hlen := incCore_len l
  cases hf : (incCore l).2
  · rw [hf] at hbit hcore
    simp only [Bool.false_eq_true, if_false] at hcore
    obtain ⟨τ, st, e0, e1, ec⟩ := tailW_spec cap l σ2 (by rw [eC, eCh]; simp [sgl_length, hlen])
      (by rw [N2.1]; simp [hσ1, hN]) (by rw [N2.2]; simp [hσ1, h0])
    refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.ifsF hbit st))) (by omega), ?_, ?_, ?_⟩
    · rw [e0, eC, hcore, sgl_append]; rfl
    · rw [e1, hcore, List.length_append, hlen]; rfl
    · rw [ec, c2]; simp [hσ1]
  · rw [hf] at hbit hcore
    simp only [if_true] at hcore
    refine ⟨σ2, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.ifsT hbit (WExec.skip σ2)))) (by omega), ?_, ?_, ?_⟩
    · rw [eC, hcore]; rfl
    · rw [N2.1, hcore, hlen]; simp [hσ1, hN]
    · rw [c2]; simp [hσ1]

end NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt
