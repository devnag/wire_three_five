import Proof.Wire_3_5.FinalPass.SdPrep3

/-! # S4 (the seeds phase), part 26: filling and measuring streams (P3:3170-3178)

The setup's stream pieces, over any word machine: **`flFill o OP K bs e`** (from an empty stream: `K` copies of the
bits `bs`, then `e`, the stream rewound; `flFill_spec`), `flFillC` (the count copied from a register first), and
**`flMeas s K C`** (across a framed word `frameP w ++ false :: …`: `K += |w|`, `C += 2|w|`, the head past it;
`flMeas_spec`). `flZ`: `n` copies of `[true, false]` then `false` is `frame (replicate n false)`.

Paper quantity of the main type: the seeds phase's formatted working streams (the halves, the counters, the carriers'
accumulators), and the lengths it reads (the carriers' weight width, the tables' length). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

theorem flRead (l : List Bool) (p : ℕ) (b : Bool) (r : List Bool) (h : l.drop p = b :: r) :
    readTapeBit l p = b := by
  have := TabW.getD_drop' l p 0
  rw [Nat.add_zero, h] at this
  unfold readTapeBit
  exact this.trans rfl

theorem flZ (n : ℕ) : (List.replicate n [true, false]).flatten = frameP (List.replicate n false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_succ]
    rfl

theorem flZf (n : ℕ) : (List.replicate n [true, false]).flatten ++ [false] = frame (List.replicate n false) := by
  rw [flZ, frame_eq_frameP]

section Fill
variable {ns nr : ℕ} (cap : ℕ) (o : Fin (ns + 1))

/-- Raw bits appended. -/
def flBits (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | b :: bs => .seq (emitC o OP b) (flBits OP bs)

theorem flBits_spec (OP : Fin nr) : ∀ (bs : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length →
    σ.val OP + bs.length ≤ cap → WExec cap (flBits o OP bs) σ (WriteNat.appendO σ o OP bs) (8 * bs.length)
  | [], σ, _, _ => by
    rw [WriteNat.appendO_nil]
    exact WExec.skip σ
  | b :: bs, σ, ho, hc => by
    simp only [List.length_cons] at hc
    have e1 : WExec cap (emitC o OP b) σ (WriteNat.appendO σ o OP [b]) 7 := emitC_spec cap o OP b σ ho (by omega)
    have e2 := flBits_spec OP bs (WriteNat.appendO σ o OP [b]) (rqAp_sh o σ OP _ ho)
      (by rw [rqAp_op]; simp only [List.length_cons, List.length_nil]; omega)
    rw [WriteNat.appendO_append] at e2
    exact WExec.cast cap (WExec.seq e1 e2) rfl (by simp only [List.length_cons]; omega)

/-- `K` times the bits `bs`. -/
def flLoop (OP K : Fin nr) (bs : List Bool) : WM ns nr := .whr K (.seq (.dec K) (flBits o OP bs))

theorem flLoop_spec (OP K : Fin nr) (hK : K ≠ OP) (bs : List Bool) (n : ℕ) (σ : WState ns nr)
    (hKn : σ.val K = n) (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + n * bs.length ≤ cap) (hn : n ≤ cap) :
    WExec cap (flLoop o OP K bs) σ ((WriteNat.appendO σ o OP (List.replicate n bs).flatten).setv K 0)
      (n * (8 * bs.length + 4) + 1) := by
  let S : ℕ → WState ns nr := fun k => (WriteNat.appendO σ o OP (List.replicate k bs).flatten).setv K (n - k)
  have hS0 : S 0 = σ := by
    simp only [S, List.replicate_zero, List.flatten_nil]
    rw [WriteNat.appendO_nil, Nat.sub_zero, ← hKn, wsetv_same]
  have hloop := UnionMachine.Round.wloop cap K (flBits o OP bs) (8 * bs.length) n S
    (fun k _ => by simp [S]) hn
    (fun k hk => by
      have e1 : (S k).setv K (n - k - 1) =
          (WriteNat.appendO σ o OP (List.replicate k bs).flatten).setv K (n - k - 1) := by
        simp only [S, wsetv_setv]
      rw [e1]
      have hlen : ((List.replicate k bs).flatten).length = k * bs.length := by simp
      have hkn : k * bs.length + bs.length ≤ n * bs.length := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
      have h := flBits_spec cap o OP bs
        ((WriteNat.appendO σ o OP (List.replicate k bs).flatten).setv K (n - k - 1))
        (by simp [ho]) (by simp [Function.update_apply, Ne.symm hK, hlen]; omega)
      refine WExec.cast cap h ?_ le_rfl
      simp only [S]
      rw [← WriteNat.appendO_setv _ o OP K hK, WriteNat.appendO_append, WriteNat.appendO_setv _ o OP K hK,
        show n - k - 1 = n - (k + 1) by omega]
      simp only [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil])
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  simp [S]

/-- The fill's step bound. -/
def flCost (n l : ℕ) : ℕ := n * (8 * l + 4) + 1 + 1 + (7 + 1 + (5 * (n * l + 1) + 1))

/-- **Fill an empty stream**: `K` times the bits `bs`, then `e`, rewound. -/
def flFill (OP K : Fin nr) (bs : List Bool) (e : Bool) : WM ns nr :=
  .seq (flLoop o OP K bs) (.seq (emitC o OP e) (WM.rewind o OP))

theorem flFill_spec (OP K : Fin nr) (hK : K ≠ OP) (bs : List Bool) (e : Bool) (n : ℕ) (σ : WState ns nr)
    (hKn : σ.val K = n) (hst : σ.st o = []) (hsh : σ.sh o = 0) (hOP : σ.val OP = 0)
    (hc : n * bs.length + 1 ≤ cap) (hn : n ≤ cap) :
    WExec cap (flFill o OP K bs e) σ ((σ.setv K 0).sets o ((List.replicate n bs).flatten ++ [e]))
      (flCost n bs.length) := by
  have ho : σ.sh o = (σ.st o).length := by rw [hst, hsh]; rfl
  have hlen : ((List.replicate n bs).flatten).length = n * bs.length := by simp
  have e1 := flLoop_spec cap o OP K hK bs n σ hKn ho (by rw [hOP]; omega) hn
  obtain ⟨τ1, h1⟩ : ∃ y : WState ns nr,
      y = (WriteNat.appendO σ o OP (List.replicate n bs).flatten).setv K 0 := ⟨_, rfl⟩
  rw [← h1] at e1
  have t1h : τ1.sh o = (τ1.st o).length := by rw [h1]; simp [ho]
  have t1v : τ1.val OP = n * bs.length := by rw [h1]; simp [Function.update_apply, Ne.symm hK, hOP, hlen]
  have e2 : WExec cap (emitC o OP e) τ1 (WriteNat.appendO τ1 o OP [e]) 7 :=
    emitC_spec cap o OP e τ1 t1h (by rw [t1v]; omega)
  have e3 := wrewind_spec cap o OP (n * bs.length + 1) (WriteNat.appendO τ1 o OP [e])
    (by rw [rqAp_op, t1v]; rfl) (by rw [rqAp_op, t1v]; simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by unfold flCost; omega)
  rw [h1]
  apply WState.eq
  · funext j
    by_cases hj : j = o
    · rw [hj]; simp [hsh, hlen]
    · simp [Function.update_of_ne hj]
  · funext j
    by_cases hj : j = o
    · rw [hj]; simp [hst]
    · simp [Function.update_of_ne hj]
  · funext q
    by_cases hq : q = OP
    · rw [hq]; simp [Function.update_apply, Ne.symm hK, hOP]
    · by_cases hqK : q = K
      · rw [hqK]; simp [Function.update_apply, hK]
      · simp [Function.update_of_ne hq, Function.update_of_ne hqK]
  · simp

/-- The fill with the count copied from `v` (through the temporary `t`). -/
def flFillC (OP K t v : Fin nr) (bs : List Bool) (e : Bool) : WM ns nr :=
  .seq (Hash4.wcopyR v K t) (flFill o OP K bs e)

theorem flFillC_spec (OP K t v : Fin nr) (hK : K ≠ OP) (hvK : v ≠ K) (hvt : v ≠ t) (hKt : K ≠ t)
    (bs : List Bool) (e : Bool) (σ : WState ns nr) (hK0 : σ.val K = 0) (ht0 : σ.val t = 0)
    (hst : σ.st o = []) (hsh : σ.sh o = 0) (hOP : σ.val OP = 0)
    (hc : σ.val v * bs.length + 1 ≤ cap) (hn : σ.val v ≤ cap) :
    WExec cap (flFillC o OP K t v bs e) σ (σ.sets o ((List.replicate (σ.val v) bs).flatten ++ [e]))
      (18 * σ.val v + 3 + 1 + flCost (σ.val v) bs.length) := by
  have e1 := Hash4.wcopyR_spec cap v K t hvK hvt hKt σ hK0 ht0 hn
  have hOP' : (σ.setv K (σ.val v)).val OP = 0 := by simp [Function.update_apply, Ne.symm hK, hOP]
  have e2 := flFill_spec cap o OP K hK bs e (σ.val v) (σ.setv K (σ.val v)) (by simp) (by simpa using hst)
    (by simpa using hsh) hOP' hc hn
  rw [wsetv_setv, ← hK0, wsetv_same] at e2
  exact WExec.seq e1 e2

/-- One framed bit crossed: the head moves `2`, `K += 1`, `C += 2`. -/
def flStep (s : Fin (ns + 1)) (K C : Fin nr) : WM ns nr :=
  .seq (.fwd s) (.seq (.fwd s) (.seq (.inc K) (.seq (.inc C) (.inc C))))

theorem flStep_spec (s : Fin (ns + 1)) (K C : Fin nr) (hKC : K ≠ C) (σ : WState ns nr)
    (hK : σ.val K < cap) (hC : σ.val C + 2 ≤ cap) :
    WExec cap (flStep s K C) σ (((σ.setv K (σ.val K + 1)).setv C (σ.val C + 2)).seth s (σ.sh s + 2)) 15 := by
  obtain ⟨σ1, h1⟩ : ∃ y : WState ns nr, y = σ.seth s (σ.sh s + 1) := ⟨_, rfl⟩
  have e1 := WExec.fwd (cap := cap) s σ
  rw [← h1] at e1
  obtain ⟨σ2, h2⟩ : ∃ y : WState ns nr, y = σ1.seth s (σ1.sh s + 1) := ⟨_, rfl⟩
  have e2 := WExec.fwd (cap := cap) s σ1
  rw [← h2] at e2
  have v2 : σ2.val = σ.val := by rw [h2, h1]; rfl
  have e3 := WExec.inc (cap := cap) K σ2 (by rw [v2]; exact hK)
  obtain ⟨σ3, h3⟩ : ∃ y : WState ns nr, y = σ2.setv K (σ2.val K + 1) := ⟨_, rfl⟩
  rw [← h3] at e3
  have v3 : σ3.val C = σ.val C := by rw [h3, WState.setv_val, Function.update_of_ne (Ne.symm hKC), v2]
  have e4 := WExec.inc (cap := cap) C σ3 (by rw [v3]; omega)
  obtain ⟨σ4, h4⟩ : ∃ y : WState ns nr, y = σ3.setv C (σ3.val C + 1) := ⟨_, rfl⟩
  rw [← h4] at e4
  have v4 : σ4.val C = σ.val C + 1 := by rw [h4, WState.setv_val, Function.update_self, v3]
  have e5 := WExec.inc (cap := cap) C σ4 (by rw [v4]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by omega)
  rw [v4, h4, v3, h3, h2, h1]
  wgen_eq [hKC, Ne.symm hKC]

/-- **Across a framed word**: `K += |w|`, `C += 2|w|`, the head past its bits. -/
def flMeas (s : Fin (ns + 1)) (K C : Fin nr) : WM ns nr := .whs s (flStep s K C)

theorem flMeas_spec (s : Fin (ns + 1)) (K C : Fin nr) (hKC : K ≠ C) :
    ∀ (w rest : List Bool) (σ : WState ns nr) (p : ℕ),
      (σ.st s).drop p = frameP w ++ false :: rest → σ.sh s = p → σ.val K + w.length ≤ cap →
      σ.val C + 2 * w.length ≤ cap →
      WExec cap (flMeas s K C) σ
        (((σ.setv K (σ.val K + w.length)).setv C (σ.val C + 2 * w.length)).seth s (p + 2 * w.length))
        (18 * w.length + 1)
  | [], rest, σ, p, hd, hp, _, _ => by
    have hb : wbit σ s = false := by
      unfold wbit; rw [hp]; exact flRead _ p false rest (by simpa using hd)
    have e : ((σ.setv K (σ.val K + 0)).setv C (σ.val C + 2 * 0)).seth s (p + 2 * 0) = σ := by
      simp only [Nat.add_zero, Nat.mul_zero]
      rw [wsetv_same, wsetv_same, ← hp]
      exact WState.eq (by simp) rfl rfl rfl
    simp only [List.length_nil]
    rw [e]
    exact WExec.whsF hb
  | b :: w, rest, σ, p, hd, hp, hK, hC => by
    simp only [List.length_cons] at hK hC ⊢
    have hd' : (σ.st s).drop p = true :: b :: (frameP w ++ false :: rest) := by
      rw [hd]; simp [frameP]
    have hb : wbit σ s = true := by unfold wbit; rw [hp]; exact flRead _ p true _ hd'
    have e1 := flStep_spec cap s K C hKC σ (by omega) (by omega)
    obtain ⟨σ1, h1⟩ : ∃ y : WState ns nr,
        y = ((σ.setv K (σ.val K + 1)).setv C (σ.val C + 2)).seth s (σ.sh s + 2) := ⟨_, rfl⟩
    rw [← h1] at e1
    have k1 : σ1.val K = σ.val K + 1 := by rw [h1]; simp [Function.update_apply, hKC]
    have c1 : σ1.val C = σ.val C + 2 := by rw [h1]; simp
    have s1 : σ1.st s = σ.st s := by rw [h1]; simp
    have p1 : σ1.sh s = p + 2 := by rw [h1]; simp [hp]
    have hdd : (σ.st s).drop (p + 2) = ((σ.st s).drop p).drop 2 := by
      simp [List.drop_drop, Nat.add_comm]
    have ih := flMeas_spec s K C hKC w rest σ1 (p + 2) (by rw [s1, hdd, hd']; rfl) p1 (by rw [k1]; omega)
      (by rw [c1]; omega)
    refine WExec.cast cap (WExec.whsT hb e1 ih) ?_ (by omega)
    rw [k1, c1, h1]
    wgen_eq [hKC, Ne.symm hKC]

end Fill

end NearCubicWires.WireExponent3_5.FinalPass.Sd
