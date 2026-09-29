import Proof.Wire_3_5.Primitive.SeedFix.CarWM
import Proof.Wire_3_5.Primitive.Writers.SparseNum

/-! # SWt, part 1: counted skips and copies

The top-table writer reads each filled slot's scan word `natWord x ++ (frame y ++ tabSeg)` and must leave every head
at `0`; the moves are counted so the rewinds are exact:

* **`cntW`** (`cnt_loop`): the leading `1`s counted; **`fwdNW`** (`fwdN_spec`): `m` steps forward, the counter
  consumed; **`skipCW`** (`skipC_spec`): a `natWord x` skipped, `natBitLength x` kept in a register;
* **`copyCW`** (`copyCLoop_spec`, `copyC_spec`): CarWM's frame copy with its cells counted.

Paper quantity of the main types: the framed top tables `frame (ofFn C.top)` of the SYM call's circuits
(`symWords`, kind `1`; P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.SWt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.PrimT.CarWM NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm

theorem rd_ones (pre rest : List Bool) (x i : ℕ) (hi : i < natBitLength x) :
    readTapeBit (pre ++ (natWord x ++ rest)) (pre.length + i) = true := by
  have hnw : natWord x = List.replicate (natBitLength x) true ++
      false :: WilliamsPublishedForm.fixedWidthNatBits (natBitLength x) x := rfl
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega), show pre.length + i - pre.length = i by omega, hnw,
    List.append_assoc, List.getD_append _ _ _ _ (by simp; omega)]
  simp [hi]

theorem rd_zero (pre rest : List Bool) (x : ℕ) :
    readTapeBit (pre ++ (natWord x ++ rest)) (pre.length + natBitLength x) = false := by
  have hnw : natWord x = List.replicate (natBitLength x) true ++
      false :: WilliamsPublishedForm.fixedWidthNatBits (natBitLength x) x := rfl
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega), show pre.length + natBitLength x - pre.length = natBitLength x by omega,
    hnw, List.append_assoc, List.getD_append_right _ _ _ _ (by simp)]
  simp

section Kit
variable {ns nr : ℕ} (cap : ℕ)

/-- Count the leading `1`s of `S` into `d`. -/
def cntW (S : Fin (ns + 1)) (d : Fin nr) : WM ns nr := .whs S (.seq (.fwd S) (.inc d))

theorem cnt_loop (S : Fin (ns + 1)) (d : Fin nr) : ∀ (m : ℕ) (σ : WState ns nr),
    (∀ i < m, readTapeBit (σ.st S) (σ.sh S + i) = true) → readTapeBit (σ.st S) (σ.sh S + m) = false →
    σ.val d + m ≤ cap →
    WExec cap (cntW S d) σ ((σ.seth S (σ.sh S + m)).setv d (σ.val d + m)) (8 * m + 1)
  | 0, σ, _, hf, _ => by
    have e : (σ.seth S (σ.sh S + 0)).setv d (σ.val d + 0) = σ := WState.eq (by simp) rfl (by simp) rfl
    rw [e]
    exact WExec.whsF (by unfold wbit; simpa using hf)
  | m + 1, σ, ht, hf, hc => by
    have hb : wbit σ S = true := by unfold wbit; simpa using ht 0 (by omega)
    have h1 := WExec.fwd (cap := cap) S σ
    have h2 := WExec.inc (cap := cap) d (σ.seth S (σ.sh S + 1)) (by simp; omega)
    have h3 := cnt_loop S d m ((σ.seth S (σ.sh S + 1)).setv d ((σ.seth S (σ.sh S + 1)).val d + 1))
      (fun i hi => by
        simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [show σ.sh S + 1 + i = σ.sh S + (i + 1) by omega]; exact ht (i + 1) (by omega))
      (by
        simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [show σ.sh S + 1 + m = σ.sh S + (m + 1) by omega]; exact hf)
      (by simp; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) h3) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hj : j = S
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]
    · rfl
    · funext q
      by_cases hq : q = d
      · subst hq; simp; omega
      · simp [Function.update_of_ne hq]
    · rfl

/-- `m` steps forward on `S`, the counter `e` consumed. -/
def fwdNW (S : Fin (ns + 1)) (e : Fin nr) : WM ns nr := .whr e (.seq (.dec e) (.fwd S))

theorem fwdN_spec (S : Fin (ns + 1)) (e : Fin nr) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val e = m → σ.val e ≤ cap →
      WExec cap (fwdNW S e) σ ((σ.setv e 0).seth S (σ.sh S + m)) (5 * m + 1)
  | 0, σ, h0, _ => by
    have e0 : (σ.setv e 0).seth S (σ.sh S + 0) = σ := WState.eq (by simp) rfl (by rw [← h0]; simp) rfl
    rw [e0]
    exact WExec.whrF h0
  | m + 1, σ, hm, hc => by
    have h1 := WExec.dec (cap := cap) e σ hc
    have h2 := WExec.fwd (cap := cap) S (σ.setv e (σ.val e - 1))
    have h3 := fwdN_spec S e m ((σ.setv e (σ.val e - 1)).seth S ((σ.setv e (σ.val e - 1)).sh S + 1))
      (by simp; omega) (by simp; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) h3) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hj : j = S
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]
    · rfl
    · funext q
      by_cases hq : q = e
      · subst hq; simp
      · simp [Function.update_of_ne hq]
    · rfl

/-- **Skip a `natWord`**, its bit length kept in `d`. -/
def skipCW (S : Fin (ns + 1)) (d e t : Fin nr) : WM ns nr :=
  .seq (cntW S d) (.seq (.fwd S) (.seq (FinalPass.Hash4.wcopyR d e t) (fwdNW S e)))

theorem skipC_spec (S : Fin (ns + 1)) (d e t : Fin nr) (hde : d ≠ e) (hdt : d ≠ t) (het : e ≠ t) (x : ℕ)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st S = pre ++ (natWord x ++ rest))
    (hsh : σ.sh S = pre.length) (zd : σ.val d = 0) (ze : σ.val e = 0) (zt : σ.val t = 0)
    (hcap : natBitLength x + 1 ≤ cap) :
    ∃ c, WExec cap (skipCW S d e t) σ ((σ.seth S (pre.length + (natWord x).length)).setv d (natBitLength x)) c ∧
      c ≤ 20 * (natBitLength x + 1) + 2 * UnaryPow.sq cap := by
  obtain ⟨L, hL⟩ : ∃ L, L = natBitLength x := ⟨_, rfl⟩
  have hnw : natWord x = List.replicate L true ++ false :: WilliamsPublishedForm.fixedWidthNatBits L x := by
    rw [hL]; rfl
  have hfl : (WilliamsPublishedForm.fixedWidthNatBits L x).length = L := by
    simp [WilliamsPublishedForm.fixedWidthNatBits]
  have hlen : (natWord x).length = 2 * L + 1 := by rw [hnw]; simp [hfl]; omega
  rw [← hL] at hcap ⊢
  have e1 := cnt_loop cap S d L σ
    (fun i hi => by rw [hst, hsh]; exact rd_ones pre rest x i (by omega))
    (by rw [hst, hsh, hL]; exact rd_zero pre rest x)
    (by rw [zd]; omega)
  rw [zd, Nat.zero_add, hsh] at e1
  have e2 := WExec.fwd (cap := cap) S ((σ.seth S (pre.length + L)).setv d L)
  have e3 := SparseNum.copy1 cap d e t hde hdt het L
    (((σ.seth S (pre.length + L)).setv d L).seth S (((σ.seth S (pre.length + L)).setv d L).sh S + 1))
    (by simp) (by simp [Function.update_of_ne (Ne.symm hde), ze]) (by simp [Function.update_of_ne (Ne.symm hdt), zt])
    (by omega)
  have e4 := fwdN_spec cap S e L
    ((((σ.seth S (pre.length + L)).setv d L).seth S (((σ.seth S (pre.length + L)).setv d L).sh S + 1)).setv e L)
    (by simp) (by simp; omega)
  have hsq := UnaryPow.lin_le_sq cap
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl, by omega⟩
  apply WState.eq
  · funext j
    by_cases hj : j = S
    · subst hj; simp; omega
    · simp [Function.update_of_ne hj]
  · rfl
  · funext q
    by_cases hq : q = e
    · subst hq; simp [Function.update_of_ne (Ne.symm hde), ze]
    · by_cases hq' : q = d
      · subst hq'; simp [Function.update_of_ne hde]
      · simp [Function.update_of_ne hq, Function.update_of_ne hq']
  · rfl

/-- **Copy one framed word**, its cells counted in `c`. -/
def copyCW (N O : Fin (ns + 1)) (c : Fin nr) : WM ns nr :=
  .seq (.whs N (.seq (copyBodyW N O) (.inc c))) (emitW O false)

theorem copyCLoop_spec (N O : Fin (ns + 1)) (c : Fin nr) (hNO : N ≠ O) (rest : List Bool) :
    ∀ (y pre : List Bool) (σ : WState ns nr), σ.st N = pre ++ (frame y ++ rest) → σ.sh N = pre.length →
      σ.sh O = (σ.st O).length → σ.val c + y.length ≤ cap →
      ∃ τ, WExec cap (.whs N (.seq (copyBodyW N O) (.inc c))) σ τ (20 * y.length + 1) ∧
        τ.st O = σ.st O ++ frameP y ∧ τ.sh O = (τ.st O).length ∧ τ.st N = σ.st N ∧
        τ.sh N = pre.length + 2 * y.length ∧ (∀ j, j ≠ N → j ≠ O → Same σ τ j) ∧
        τ.val = Function.update σ.val c (σ.val c + y.length) ∧ τ.cell = σ.cell
  | [], pre, σ, hN, hNh, hO, _ => by
    have hz : wbit σ N = false := by simp only [wbit, hN, hNh, rd_at]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp [frameP], hO, rfl, by simp [hNh],
      fun _ _ _ => ⟨rfl, rfl⟩, by simp, rfl⟩
  | b :: bs, pre, σ, hN, hNh, hO, hc => by
    have hON : O ≠ N := fun e => hNO e.symm
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts cap N σ
    have O1 := o1 O hON
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap O true σ1 (by rw [O1.1, O1.2, hO])
    have N2 := o2 N hNO
    have hb : wbit σ2 N = b := by
      simp only [wbit, N2.1, N2.2, n1, n1h, hN, hNh, rd_at1]; rfl
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap O b σ2 e2h
    have s3' : WExec cap (.ifs N (emitW O true) (emitW O false)) σ2 σ3 4 := by
      cases b
      · exact WExec.ifsF hb s3
      · exact WExec.ifsT hb s3
    have N3 := o3 N hNO
    obtain ⟨σ4, s4, n4, n4h, o4, v4, c4⟩ := fwd_facts cap N σ3
    have O4 := o4 O hON
    have hv4 : σ4.val = σ.val := by rw [v4, v3, v2, v1]
    have hcl : σ.val c + (bs.length + 1) ≤ cap := by simpa using hc
    have s5 := WExec.inc (cap := cap) c σ4 (by rw [hv4]; omega)
    obtain ⟨τ, s6, eO, eOh, eN, eNh, oth, v6, c6⟩ := copyCLoop_spec N O c hNO rest bs (pre ++ [true, b])
      (σ4.setv c (σ4.val c + 1))
      (by simp only [WState.setv_st]; rw [n4, N3.1, N2.1, n1, hN]; simp [frame])
      (by simp only [WState.setv_sh]; rw [n4h, N3.2, N2.2, n1h, hNh]; simp)
      (by simp only [WState.setv_sh, WState.setv_st]; rw [O4.1, O4.2, e3h])
      (by simp only [WState.setv_val, Function.update_self]; rw [hv4]; omega)
    have hw : wbit σ N = true := by simp only [wbit, hN, hNh, rd_at]; rfl
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq (WExec.seq s1 (WExec.seq s2 (WExec.seq s3' s4))) s5) s6)
      (by simp; omega), ?_, eOh, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eO]; simp only [WState.setv_st]; rw [O4.1, e3, e2, O1.1]; simp [frameP]
    · rw [eN]; simp only [WState.setv_st]; rw [n4, N3.1, N2.1, n1]
    · rw [eNh]; simp; omega
    · intro j h1 h2
      have hS5 : Same σ4 (σ4.setv c (σ4.val c + 1)) j := ⟨rfl, rfl⟩
      exact (((((o1 j h1).trans' (o2 j h2)).trans' (o3 j h2)).trans' (o4 j h1)).trans' hS5).trans' (oth j h1 h2)
    · rw [v6]
      funext q
      simp only [WState.setv_val, Function.update_apply, hv4]
      by_cases hq : q = c
      · subst hq; simp; omega
      · simp [hq]
    · rw [c6]; simp only [WState.setv_cell]; rw [c4, c3, c2, c1]

/-- **One framed word copied** to the end of `O`, its cells counted in `c`. -/
theorem copyC_spec (N O : Fin (ns + 1)) (c : Fin nr) (hNO : N ≠ O) (pre y rest : List Bool) (σ : WState ns nr)
    (hN : σ.st N = pre ++ (frame y ++ rest)) (hNh : σ.sh N = pre.length) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val c + y.length ≤ cap) :
    ∃ τ, WExec cap (copyCW N O c) σ τ (20 * y.length + 5) ∧ τ.st O = σ.st O ++ frame y ∧
      τ.sh O = (τ.st O).length ∧ τ.st N = σ.st N ∧ τ.sh N = pre.length + 2 * y.length ∧
      (∀ j, j ≠ N → j ≠ O → Same σ τ j) ∧ τ.val = Function.update σ.val c (σ.val c + y.length) ∧
      τ.cell = σ.cell := by
  obtain ⟨τ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := copyCLoop_spec cap N O c hNO rest y pre σ hN hNh hO hc
  obtain ⟨τ, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap O false τ1 e1h
  have N2 := o2 N hNO
  refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by omega), by rw [e2, e1, frame_eq_frameP]; simp, e2h,
    by rw [N2.1, n1], by rw [N2.2, n1h], fun j h1 h2 => (o1 j h1 h2).trans' (o2 j h2), by rw [v2, v1],
    by rw [c2, c1]⟩

end Kit

end NearCubicWires.WireExponent3_5.PrimT.SWt
