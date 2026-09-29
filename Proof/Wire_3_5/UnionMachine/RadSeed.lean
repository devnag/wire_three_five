import Proof.Wire_3_5.UnionMachine.RadWin

/-! # RADIX, stage 5a (2): the fixed hash's bits, unframed from the request (P3:2150-2157)

The unit's request stream holds `frame (reqWord ++ frame hashBits)` (`RsIn4.s0`); the fixed hash's seed converter
(`HashSeed.seed_spec`, X5) reads `frame hashBits` from a stream of its own. **`tailP`** copies the request frame's last
`|frame l| = 2|l| + 1` payload bits (`|l| = 2·t·ℓ₀`) onto a blank stream and rewinds both:

* `toEndC` / **`toEndC_spec`**: to the end of a frame, counting;
* `pairP` / **`pairP_spec`**: the payload bits of the next `K` pairs, appended to another stream;
* `tailP` / **`tailP_spec`**: from `frame (A ++ frame l)` (`|l| = t·ℓ₀·2`), the blank stream becomes `frame l`.

Paper quantity of the main type: the fixed hash's bits `s` (the THR call's seed word's tail). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.UnionMachine.RadFields NearCubicWires.WireExponent3_5.UnionMachine.RadWin

variable {ns nr : ℕ} (cap : ℕ)

/-- The head of `I` to the end of its frame, counting in `c`. -/
def toEndC (I : Fin (ns + 1)) (c : Fin nr) : WM ns nr := .whs I (.seq (WM.fwdC I c) (WM.fwdC I c))

theorem toEndC_spec (I : Fin (ns + 1)) (c : Fin nr) (l : List Bool) : ∀ (k : ℕ) (σ : WState ns nr), σ.st I = frame l →
    σ.sh I + 2 * k = 2 * l.length → σ.val c + 2 * k ≤ cap →
    WExec cap (toEndC I c) σ ((σ.seth I (2 * l.length)).setv c (σ.val c + 2 * k)) (13 * k + 1)
  | 0, σ, hs, hh, _ => by
    have hb : wbit σ I = false := by
      unfold wbit; rw [hs, show σ.sh I = 2 * l.length by omega, FinalPass.HashSeed.read_frame_even]; simp
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    rw [show 2 * l.length = σ.sh I by omega, FinalPass.HashSeed.seth_same, Nat.mul_zero, Nat.add_zero, wsetv_same]
  | k + 1, σ, hs, hh, hc => by
    have hb : wbit σ I = true := by
      unfold wbit
      rw [hs, show σ.sh I = 2 * (l.length - (k + 1)) by omega, FinalPass.HashSeed.read_frame_even]
      simp; omega
    have h1 := wfwdC_spec cap I c σ (by omega)
    have h2 := wfwdC_spec cap I c ((σ.seth I (σ.sh I + 1)).setv c (σ.val c + 1)) (by simp; omega)
    have ih := toEndC_spec I c l k ((((σ.seth I (σ.sh I + 1)).setv c (σ.val c + 1)).seth I
      (((σ.seth I (σ.sh I + 1)).setv c (σ.val c + 1)).sh I + 1)).setv c
      (((σ.seth I (σ.sh I + 1)).setv c (σ.val c + 1)).val c + 1)) (by simpa using hs) (by simp; omega) (by simp; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) ih) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = I
      · subst hj; simp
      · simp [Function.update_apply, hj]
    · rfl
    · funext j; by_cases hj : j = c
      · subst hj; simp; omega
      · simp [Function.update_apply, hj]
    · rfl

/-- The payload bits of the next `K` pairs of `S` (`[marker, bit]`), appended to `O`, consuming `K`. -/
def pairP (O S : Fin (ns + 1)) (OP K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (.fwd S) (.seq (.ifs S (emitW O OP [true]) (emitW O OP [false])) (.fwd S))))

theorem pairP_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP K : Fin nr) (hKO : K ≠ OP) (w : List Bool)
    (σ : WState ns nr) (hKn : σ.val K = w.length)
    (hw : ∀ i < w.length, readTapeBit (σ.st S) (σ.sh S + 2 * i + 1) = w.getD i false)
    (ho : σ.sh O = (σ.st O).length) (hc : σ.val OP + w.length ≤ cap) (hn : w.length ≤ cap) :
    WExec cap (pairP O S OP K) σ (((appendO σ O OP w).seth S (σ.sh S + 2 * w.length)).setv K 0)
      (w.length * (8 + 1 + 1 + 1 + 1 + 1 + 1 + 4) + 1) := by
  let S' : ℕ → WState ns nr := fun k =>
    ((appendO σ O OP (w.take k)).seth S (σ.sh S + 2 * k)).setv K (w.length - k)
  have hS0 : S' 0 = σ := by
    simp only [S', List.take_zero, appendO_nil, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, ← hKn]
    apply WState.eq <;> simp [Function.update_eq_self]
  have hloop := UnionMachine.Round.wloop cap K
    (.seq (.fwd S) (.seq (.ifs S (emitW O OP [true]) (emitW O OP [false])) (.fwd S))) (8 + 1 + 1 + 1 + 1 + 1 + 1)
    w.length S' (fun k _ => by simp [S']) hn
    (fun k hk => by
      set τ := ((appendO σ O OP (w.take k)).seth S (σ.sh S + 2 * k)).setv K (w.length - k - 1) with hτ
      have hτS : (S' k).setv K (w.length - k - 1) = τ := by simp only [S', hτ, wsetv_setv]
      rw [hτS]
      have hlen : (w.take k).length = k := by rw [List.length_take, min_eq_left (by omega)]
      have d1 := WExec.fwd (cap := cap) S τ
      set τ1 := τ.seth S (τ.sh S + 1) with hτ1
      have hbit : wbit τ1 S = w.getD k false := by
        simp only [hτ1, hτ, wbit]
        simp [hOS.symm, Function.update_apply]
        have := hw k hk
        rw [show σ.sh S + 2 * k + 1 = σ.sh S + 2 * k + 1 from rfl] at this
        exact this
      have hoτ : τ1.sh O = (τ1.st O).length := by simp [hτ1, hτ, hOS, ho]
      have hcτ : τ1.val OP + [w.getD k false].length ≤ cap := by
        simp only [hτ1, hτ]
        simp [Function.update_apply, Ne.symm hKO, hlen]
        omega
      have hE : WExec cap (.ifs S (emitW O OP [true]) (emitW O OP [false])) τ1
          (appendO τ1 O OP [w.getD k false]) (8 + 1) := by
        cases hb : w.getD k false
        · rw [hb] at hbit hcτ
          exact WExec.ifsF hbit (emitW_spec cap O OP [false] τ1 hoτ hcτ)
        · rw [hb] at hbit hcτ
          exact WExec.ifsT hbit (emitW_spec cap O OP [true] τ1 hoτ hcτ)
      have d3 := WExec.fwd (cap := cap) S (appendO τ1 O OP [w.getD k false])
      refine WExec.cast cap (WExec.seq d1 (WExec.seq hE d3)) ?_ (by omega)
      have htake : w.take (k + 1) = w.take k ++ [w.getD k false] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.getD_eq_getElem _ _ hk]
      simp only [S', hτ1, hτ, htake]
      apply WState.eq
      · funext j
        by_cases hjS : j = S
        · subst hjS; simp [Function.update_apply, Ne.symm hOS]; omega
        · by_cases hj : j = O
          · subst hj; simp [Function.update_apply, hjS]; try omega
          · simp [Function.update_apply, hj, hjS]
      · funext j; by_cases hj : j = O
        · subst hj; simp [hOS]
        · simp [Function.update_apply, hj]
      · funext j; by_cases hj : j = K
        · subst hj; simp [Function.update_apply, hKO]; omega
        · by_cases hjO : j = OP
          · subst hjO; simp [Function.update_apply, hj]; omega
          · simp [Function.update_apply, hj, hjO]
      · simp)
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  simp only [S', List.take_length, Nat.sub_self]

section Tail
variable (R : Fin 10 ↪ Fin nr)

theorem rne {i j : Fin 10} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

/-- The multiply-add block inside `R`: `R 0 · R 1` into `R 2`, temporaries `R 3`, `R 4`. -/
def e5 : Fin 5 ↪ Fin 10 := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The frame's pair count `|frame l| = 4·t·ℓ₀ + 1` into `R 9` (`R 2 … R 8` back to `0`). -/
def numsT : WM ns nr :=
  .seq (PrimAsm.UnaryArith.mulAddW (e5.trans R)) (.seq (PrimAsm.ParseNat.addTo (R 2) (R 9) (R 8))
    (.seq (PrimAsm.ParseNat.addTo (R 2) (R 9) (R 8)) (.seq (PrimAsm.ParseNat.addTo (R 2) (R 9) (R 8))
      (.seq (PrimAsm.ParseNat.addTo (R 2) (R 9) (R 8)) (.seq (.inc (R 9)) (WM.clear (R 2)))))))

theorem numsT_spec (σ : WState ns nr) (t ℓ : ℕ) (h0 : σ.val (R 0) = t) (h1 : σ.val (R 1) = ℓ)
    (hz : ∀ i : Fin 10, 2 ≤ i.val → σ.val (R i) = 0) (hc : 4 * (t * ℓ) + 1 < cap) (ht : t ≤ cap) (hl : ℓ ≤ cap) :
    WExec cap (numsT R) σ (σ.setv (R 9) (4 * (t * ℓ) + 1)) (ℓ * (18 * t + 8) + 18 * ℓ + 100 * (t * ℓ) + 60) := by
  have z2 := hz 2 (by decide)
  have z3 := hz 3 (by decide)
  have z4 := hz 4 (by decide)
  have z8 := hz 8 (by decide)
  have z9 := hz 9 (by decide)
  have htl : t * ℓ ≤ 4 * (t * ℓ) := by omega
  have s1 := PrimAsm.UnaryArith.mulAddW_spec cap (e5.trans R) σ (by exact z3) (by exact z4)
    (by show σ.val (R 1) ≤ cap; omega) (by show σ.val (R 2) + σ.val (R 0) * σ.val (R 1) ≤ cap; rw [z2, h0, h1]; omega)
    (by show σ.val (R 0) ≤ cap; omega)
  have q0 : (e5.trans R) 0 = R 0 := rfl
  have q1 : (e5.trans R) 1 = R 1 := rfl
  have q2 : (e5.trans R) 2 = R 2 := rfl
  rw [q0, q1, q2, z2, h0, h1, Nat.zero_add] at s1
  set σ1 := σ.setv (R 2) (t * ℓ) with hσ1
  have v2 : ∀ x : ℕ, (σ1.setv (R 9) x).val (R 2) = t * ℓ := fun x => by
    simp [σ1, Function.update_apply, rne R (show (2 : Fin 10) ≠ 9 by decide)]
  have v8 : ∀ x : ℕ, (σ1.setv (R 9) x).val (R 8) = 0 := fun x => by
    simp [σ1, Function.update_apply, rne R (show (8 : Fin 10) ≠ 9 by decide),
      rne R (show (8 : Fin 10) ≠ 2 by decide), z8]
  have a1 := PrimAsm.ParseNat.addTo_spec cap (R 2) (R 9) (R 8) (rne R (by decide)) (rne R (by decide)) (rne R (by decide))
    (σ1.setv (R 9) 0) (v8 0) (by rw [v2]; omega) (by rw [v2]; simp; omega)
  have e1 : σ1.setv (R 9) 0 = σ1 := by
    rw [hσ1]; refine WState.eq rfl rfl ?_ rfl
    funext q; by_cases hq : q = R 9
    · subst hq; simp [Function.update_apply, rne R (show (9 : Fin 10) ≠ 2 by decide), z9]
    · simp [Function.update_apply, hq]
  rw [e1] at a1
  have w1 : σ1.val (R 9) + σ1.val (R 2) = t * ℓ := by
    simp [σ1, Function.update_apply, rne R (show (9 : Fin 10) ≠ 2 by decide), z9]
  rw [w1] at a1
  have v2' : σ1.val (R 2) = t * ℓ := by simp [σ1]
  rw [v2'] at a1
  have a2 := PrimAsm.ParseNat.addTo_spec cap (R 2) (R 9) (R 8) (rne R (by decide)) (rne R (by decide)) (rne R (by decide))
    (σ1.setv (R 9) (t * ℓ)) (v8 _) (by rw [v2]; omega) (by rw [v2]; simp; omega)
  rw [v2, WState.setv_val, Function.update_self, wsetv_setv] at a2
  have a3 := PrimAsm.ParseNat.addTo_spec cap (R 2) (R 9) (R 8) (rne R (by decide)) (rne R (by decide)) (rne R (by decide))
    (σ1.setv (R 9) (t * ℓ + t * ℓ)) (v8 _) (by rw [v2]; omega) (by rw [v2]; simp; omega)
  rw [v2, WState.setv_val, Function.update_self, wsetv_setv] at a3
  have a4 := PrimAsm.ParseNat.addTo_spec cap (R 2) (R 9) (R 8) (rne R (by decide)) (rne R (by decide)) (rne R (by decide))
    (σ1.setv (R 9) (t * ℓ + t * ℓ + t * ℓ)) (v8 _) (by rw [v2]; omega) (by rw [v2]; simp; omega)
  rw [v2, WState.setv_val, Function.update_self, wsetv_setv] at a4
  have a5 := WExec.inc (cap := cap) (R 9) (σ1.setv (R 9) (t * ℓ + t * ℓ + t * ℓ + t * ℓ)) (by simp; omega)
  rw [WState.setv_val, Function.update_self, wsetv_setv] at a5
  have a6 := wclear_spec cap (R 2) (t * ℓ) (σ1.setv (R 9) (t * ℓ + t * ℓ + t * ℓ + t * ℓ + 1)) (v2 _) (by rw [v2]; omega)
  have e6 : (σ1.setv (R 9) (t * ℓ + t * ℓ + t * ℓ + t * ℓ + 1)).setv (R 2) 0 = σ.setv (R 9) (4 * (t * ℓ) + 1) := by
    rw [hσ1]; refine WState.eq rfl rfl ?_ rfl
    funext q
    by_cases hq : q = R 2
    · subst hq; simp [Function.update_apply, rne R (show (2 : Fin 10) ≠ 9 by decide), z2]
    · by_cases hq9 : q = R 9
      · subst hq9; simp [Function.update_apply, hq]; ring
      · simp [Function.update_apply, hq, hq9]
  rw [e6] at a6
  refine WExec.mono (WExec.seq s1 (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 (WExec.seq a4 (WExec.seq a5 a6)))))) ?_
  omega

/-- The tail's copy: to the frame's end (`R 5` counts), `|frame l|` pairs back, their payload onto `O` (position `R 6`),
both rewound; the pair count in `R 9` is kept, `R 7`, `R 8` are its working copies. -/
def tailT (I O : Fin (ns + 1)) : WM ns nr :=
  .seq (toEndC I (R 5)) (.seq (FinalPass.Hash4.wcopyR (R 9) (R 7) (R 8)) (.seq (FinalPass.HashSeed.backW I (R 7))
    (.seq (FinalPass.Hash4.wcopyR (R 9) (R 7) (R 8)) (.seq (pairP O I (R 6) (R 7)) (.seq (WM.rewind I (R 5))
      (WM.rewind O (R 6)))))))

/-- The tail's cost. -/
def tailCost (v f : ℕ) : ℕ :=
  (13 * v + 1) + 1 + ((18 * f + 3) + 1 + ((7 * f + 1) + 1 + ((18 * f + 3) + 1 + ((f * 18 + 1) + 1 +
    ((5 * (2 * v) + 1) + 1 + (5 * f + 1))))))

theorem tailT_spec (I O : Fin (ns + 1)) (hIO : I ≠ O) (σ : WState ns nr) (A l : List Bool)
    (hs : σ.st I = frame (A ++ frame l)) (hsh : σ.sh I = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0)
    (h9 : σ.val (R 9) = (frame l).length) (hz : ∀ i : Fin 10, 5 ≤ i.val → i.val ≤ 8 → σ.val (R i) = 0)
    (hc : 2 * (A ++ frame l).length + 1 ≤ cap) :
    WExec cap (tailT R I O) σ (σ.sets O (frame l)) (tailCost (A ++ frame l).length (frame l).length) := by
  have z5 := hz 5 (by decide) (by decide)
  have z6 := hz 6 (by decide) (by decide)
  have z7 := hz 7 (by decide) (by decide)
  have z8 := hz 8 (by decide) (by decide)
  set v := A ++ frame l with hv
  set f := (frame l).length with hf
  have hvl : v.length = A.length + f := by simp [v, f]
  have hfl : f = 2 * l.length + 1 := by simp [f]
  -- 1: to the end
  have s1 := toEndC_spec cap I (R 5) v v.length σ hs (by omega) (by omega)
  rw [z5, Nat.zero_add] at s1
  set σ1 := (σ.seth I (2 * v.length)).setv (R 5) (2 * v.length) with hσ1
  have n57 := rne R (show (5 : Fin 10) ≠ 7 by decide)
  have n58 := rne R (show (5 : Fin 10) ≠ 8 by decide)
  have n59 := rne R (show (5 : Fin 10) ≠ 9 by decide)
  have n67 := rne R (show (6 : Fin 10) ≠ 7 by decide)
  have n69 := rne R (show (6 : Fin 10) ≠ 9 by decide)
  have n56 := rne R (show (5 : Fin 10) ≠ 6 by decide)
  have n78 := rne R (show (7 : Fin 10) ≠ 8 by decide)
  have n79 := rne R (show (7 : Fin 10) ≠ 9 by decide)
  have n89 := rne R (show (8 : Fin 10) ≠ 9 by decide)
  -- 2: the count
  have s2 := FinalPass.Hash4.wcopyR_spec cap (R 9) (R 7) (R 8) (Ne.symm n79) (Ne.symm n89) n78 σ1
    (by simp [σ1, Function.update_apply, Ne.symm n57, z7]) (by simp [σ1, Function.update_apply, Ne.symm n58, z8])
    (by simp [σ1, Function.update_apply, Ne.symm n59, h9]; omega)
  have v9 : σ1.val (R 9) = f := by simp [σ1, Function.update_apply, Ne.symm n59, h9]
  rw [v9] at s2
  -- 3: back
  have s3 := FinalPass.HashSeed.back_spec cap I (R 7) f (σ1.setv (R 7) f) (by simp) (by omega)
    (by simp [σ1]; omega)
  set σ3 := ((σ1.setv (R 7) f).seth I ((σ1.setv (R 7) f).sh I - 2 * f)).setv (R 7) 0 with hσ3
  -- 4: the count again
  have s4 := FinalPass.Hash4.wcopyR_spec cap (R 9) (R 7) (R 8) (Ne.symm n79) (Ne.symm n89) n78 σ3
    (by simp [σ3]) (by simp [σ3, σ1, Function.update_apply, Ne.symm n78, Ne.symm n58, z8])
    (by simp [σ3, σ1, Function.update_apply, Ne.symm n79, Ne.symm n59, h9]; omega)
  have v9' : σ3.val (R 9) = f := by simp [σ3, σ1, Function.update_apply, Ne.symm n79, Ne.symm n59, h9]
  rw [v9'] at s4
  -- 5: the pairs' payload
  have hsh3 : (σ3.setv (R 7) f).sh I = 2 * A.length := by simp [σ3, σ1]; omega
  have s5 := pairP_spec cap O I (Ne.symm hIO) (R 6) (R 7) (Ne.symm n67) (frame l) (σ3.setv (R 7) f) (by simp [f])
    (fun i hi => by
      rw [hsh3]
      have hst : (σ3.setv (R 7) f).st I = frame v := by simp [σ3, σ1, hs]
      rw [hst, show 2 * A.length + 2 * i + 1 = 2 * (A.length + i) + 1 by ring,
        FinalPass.HashSeed.read_frame_odd v (A.length + i) (by rw [hvl]; omega), hv,
        List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left])
    (by simp [σ3, σ1, hIO.symm, hO, hOh]) (by simp [σ3, σ1, Function.update_apply, n67, n56, z6]; omega)
    (by omega)
  have hf' : (frame l).length = f := rfl
  rw [hsh3, hf'] at s5
  set σ5 := ((appendO (σ3.setv (R 7) f) O (R 6) (frame l)).seth I (2 * A.length + 2 * f)).setv (R 7) 0 with hσ5
  -- 6, 7: rewind
  have r5 : σ5.val (R 5) = 2 * v.length := by simp [σ5, σ3, σ1, Function.update_apply, n57, n56]
  have hI5 : σ5.sh I = 2 * v.length := by simp [σ5, hvl]; omega
  have s6 := wrewind_spec cap I (R 5) (2 * v.length) σ5 r5 (by rw [r5]; omega)
  have r6 : ((σ5.setv (R 5) 0).seth I (σ5.sh I - 2 * v.length)).val (R 6) = f := by
    simp [σ5, σ3, σ1, Function.update_apply, n67, Ne.symm n56, z6]; omega
  have s7 := wrewind_spec cap O (R 6) f ((σ5.setv (R 5) 0).seth I (σ5.sh I - 2 * v.length)) r6 (by rw [r6]; omega)
  have efin : (((σ5.setv (R 5) 0).seth I (σ5.sh I - 2 * v.length)).setv (R 6) 0).seth O
      (((σ5.setv (R 5) 0).seth I (σ5.sh I - 2 * v.length)).sh O - f) = σ.sets O (frame l) := by
    apply WState.eq
    · funext j
      by_cases hjO : j = O
      · subst hjO; simp [σ5, σ3, σ1, Function.update_apply, hIO.symm, hOh, f]
      · by_cases hjI : j = I
        · subst hjI; simp [σ5, σ3, σ1, Function.update_apply, hjO, hsh]; omega
        · simp [σ5, σ3, σ1, Function.update_apply, hjO, hjI]
    · funext j
      by_cases hjO : j = O
      · subst hjO; simp [σ5, σ3, σ1, hIO.symm, hO]
      · simp [σ5, σ3, σ1, Function.update_apply, hjO]
    · funext q
      by_cases h6 : q = R 6
      · subst h6; simp [σ5, σ3, σ1, Function.update_apply, z6]
      · by_cases h5 : q = R 5
        · subst h5; simp [σ5, σ3, σ1, Function.update_apply, h6, z5]
        · by_cases h7 : q = R 7
          · subst h7; simp [σ5, σ3, σ1, Function.update_apply, h6, h5, z7]
          · simp [σ5, σ3, σ1, Function.update_apply, h6, h5, h7]
    · simp [σ5, σ3, σ1]
  rw [efin] at s7
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7)))))) ?_
  unfold tailCost
  simp only [f] at *
  omega

/-- **The hash's seed word**: the tail `frame l` onto `I'`, then X5's converter onto `O'`
(`HashSeed.seedW`, registers `R 1 = ℓ₀`, `R 0 = t`, scratch `R 2 … R 5`). -/
def hashSeedP (S I' O' : Fin (ns + 1)) : WM ns nr :=
  .seq (numsT R) (.seq (tailT R S I') (.seq (WM.clear (R 9))
    (FinalPass.HashSeed.seedW I' O' (R 1) (R 0) (R 2) (R 3) (R 4) (R 5))))

/-- The seed word's cost. -/
def hashSeedCost (t ℓ v : ℕ) : ℕ :=
  (ℓ * (18 * t + 8) + 18 * ℓ + 100 * (t * ℓ) + 60) + 1 + (tailCost v (4 * (t * ℓ) + 1) + 1 +
    ((3 * (4 * (t * ℓ) + 1) + 1) + 1 + FinalPass.HashSeed.seedCost ℓ t))

theorem hashSeedP_spec (S I' O' : Fin (ns + 1)) (hSI : S ≠ I') (hIO : I' ≠ O') (σ : WState ns nr)
    (A l : List Bool) (t ℓ : ℕ) (hl : l.length = 2 * t * ℓ)
    (hs : σ.st S = frame (A ++ frame l)) (hsh : σ.sh S = 0) (hI : σ.st I' = []) (hIh : σ.sh I' = 0)
    (hO : σ.st O' = []) (hOh : σ.sh O' = 0) (h0 : σ.val (R 0) = t) (h1 : σ.val (R 1) = ℓ)
    (hz : ∀ i : Fin 10, 2 ≤ i.val → σ.val (R i) = 0)
    (hc : 2 * (A ++ frame l).length + 2 * t * (2 * ℓ + 2) + 4 * (t * ℓ) + ℓ + t + 2 ≤ cap) :
    WExec cap (hashSeedP R S I' O') σ ((σ.sets I' (frame l)).sets O' (FinalPass.HashSeed.revWord l ℓ (2 * t)))
      (hashSeedCost t ℓ (A ++ frame l).length) := by
  have hvl : (A ++ frame l).length = A.length + (2 * l.length + 1) := by simp
  have hfl : (frame l).length = 4 * (t * ℓ) + 1 := by simp [hl]; ring
  have htl : t ≤ cap := by nlinarith
  have hll : ℓ ≤ cap := by omega
  have s1 := numsT_spec cap R σ t ℓ h0 h1 hz (by omega) htl hll
  set σ1 := σ.setv (R 9) (4 * (t * ℓ) + 1) with hσ1
  have s2 := tailT_spec cap R S I' hSI σ1 A l (by simp [σ1, hs]) (by simp [σ1, hsh]) (by simp [σ1, hI])
    (by simp [σ1, hIh]) (by simp [σ1, hfl]) (fun i hi5 hi8 => by
      have hi9 : i ≠ 9 := by intro e; subst e; simp at hi8
      simp [σ1, Function.update_apply, R.injective.ne hi9]; exact hz i (by omega)) (by omega)
  rw [hfl] at s2
  have s3 := wclear_spec cap (R 9) (4 * (t * ℓ) + 1) (σ1.sets I' (frame l)) (by simp [σ1]) (by simp [σ1]; omega)
  have e3 : (σ1.sets I' (frame l)).setv (R 9) 0 = σ.sets I' (frame l) := by
    refine WState.eq rfl rfl ?_ rfl
    funext q; by_cases hq : q = R 9
    · subst hq; simp [σ1, hz 9 (by decide)]
    · simp [σ1, Function.update_apply, hq]
  rw [e3] at s3
  have n : ∀ {i j : Fin 10}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have s4 := FinalPass.HashSeed.seed_spec cap I' O' (R 1) (R 0) (R 2) (R 3) (R 4) (R 5) hIO (n (by decide))
    (n (by decide)) (n (by decide)) (n (by decide)) (n (by decide)) (n (by decide)) (n (by decide)) (n (by decide))
    (n (by decide)) (n (by decide)) (n (by decide)) (n (by decide)) (n (by decide)) l ℓ t hl
    (σ.sets I' (frame l)) (by simp) (by simp [hIh]) (by simp [hIO.symm, hO]) (by simp [hOh]) (by simp [h1])
    (by simp [h0]) (by simp [hz 2 (by decide)]) (by simp [hz 3 (by decide)]) (by simp [hz 4 (by decide)])
    (by simp [hz 5 (by decide)]) (by nlinarith)
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_
  unfold hashSeedCost
  omega

end Tail

end NearCubicWires.WireExponent3_5.UnionMachine.RadSeed
