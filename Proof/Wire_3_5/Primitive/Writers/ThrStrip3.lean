import Proof.Wire_3_5.Primitive.Writers.ThrStrip2

/-! # c4 THR block, the request's strip, part 3: copying the prefix's pairs

* `cpyW i o a` copies `k = val a` marked pairs from stream `i` (from its head) to the end of stream `o`;
  **`cpyW_spec`**.

Paper quantity of the main type: none (the copy loop's run). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {ns nr : ℕ} (cap : ℕ)

/-- Copy `val a` marked pairs from stream `i` to the end of stream `o`. -/
def cpyW (i o : Fin (ns + 1)) (a : Fin nr) : WM ns nr :=
  .whr a (.seq (.dec a) (.seq (.wr o true) (.seq (.fwd o) (.seq (.fwd i) (.seq (.ifs i (.wr o true) (.wr o false))
    (.seq (.fwd o) (.fwd i)))))))

/-- The state after `k` copied pairs. -/
def cpyS (i o : Fin (ns + 1)) (a : Fin nr) (σ : WState ns nr) (pre acc u : List Bool) (k : ℕ) : WState ns nr :=
  (((σ.sets o (acc ++ marks (u.take k))).seth o (acc.length + 2 * k)).seth i (pre.length + 2 * k)).setv a (u.length - k)

theorem marks_append (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by simp [marks]

theorem marks_take_succ (u : List Bool) (k : ℕ) (hk : k < u.length) :
    marks (u.take (k + 1)) = marks (u.take k) ++ [true, u[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, marks_append]
  simp [marks]

theorem rd_pair (pre rest u : List Bool) (k : ℕ) (hk : k < u.length) :
    readTapeBit (pre ++ marks u ++ rest) (pre.length + 2 * k + 1) = u[k] := by
  have hu : u = u.take k ++ u.drop k := (List.take_append_drop k u).symm
  have hd : u.drop k = u[k] :: u.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk]
  have e : pre ++ marks u ++ rest = (pre ++ marks (u.take k) ++ [true]) ++ u[k] :: (marks (u.drop (k + 1)) ++ rest) := by
    conv_lhs => rw [hu, marks_append, hd, marks_cons]
    simp [List.append_assoc]
  rw [e]
  have hl : (pre ++ marks (u.take k) ++ [true]).length = pre.length + 2 * k + 1 := by
    simp only [List.length_append, marks_len, List.length_take, Nat.min_eq_left hk.le, List.length_singleton]
  rw [← hl]
  exact rd_at _ _ _

theorem cpy_step (i o : Fin (ns + 1)) (a : Fin nr) (hio : i ≠ o) (σ : WState ns nr) (pre acc u rest : List Bool)
    (hst : σ.st i = pre ++ marks u ++ rest) (hcap : u.length ≤ cap) (k : ℕ) (hk : k < u.length) :
    WExec cap (.seq (.dec a) (.seq (.wr o true) (.seq (.fwd o) (.seq (.fwd i) (.seq (.ifs i (.wr o true) (.wr o false))
      (.seq (.fwd o) (.fwd i)))))))
      (cpyS i o a σ pre acc u k) (cpyS i o a σ pre acc u (k + 1)) 14 := by
  set T := cpyS i o a σ pre acc u k with hT
  have hTo : T.st o = acc ++ marks (u.take k) := by rw [hT]; simp [cpyS]
  have hTi : T.st i = pre ++ marks u ++ rest := by rw [hT]; simp [cpyS, hio, hst]
  have hTsho : T.sh o = acc.length + 2 * k := by rw [hT]; simp [cpyS, Ne.symm hio]
  have hTshi : T.sh i = pre.length + 2 * k := by rw [hT]; simp [cpyS]
  have hTa : T.val a = u.length - k := by rw [hT]; simp [cpyS]
  have hlen : (acc ++ marks (u.take k)).length = acc.length + 2 * k := by
    simp [marks_len, List.length_take, Nat.min_eq_left hk.le]
  have e1 := WExec.dec (cap := cap) a T (by rw [hTa]; omega)
  set T1 := T.setv a (T.val a - 1) with hT1
  have e2 := WExec.wr (cap := cap) o true T1
  set T2 := T1.sets o (writeTapeBit (T1.st o) (T1.sh o) true) with hT2
  have w2 : writeTapeBit (T1.st o) (T1.sh o) true = acc ++ marks (u.take k) ++ [true] := by
    rw [hT1]; simp only [WState.setv_st, WState.setv_sh]; rw [hTo, hTsho, ← hlen, PrimT.C4Pipe.write_end]
  have e3 := WExec.fwd (cap := cap) o T2
  set T3 := T2.seth o (T2.sh o + 1) with hT3
  have e4 := WExec.fwd (cap := cap) i T3
  set T4 := T3.seth i (T3.sh i + 1) with hT4
  have hb : wbit T4 i = u[k] := by
    simp only [wbit, hT4, hT3, hT2, hT1, WState.seth_st, WState.sets_st, WState.setv_st, WState.seth_sh,
      WState.sets_sh, WState.setv_sh, Function.update_apply, if_neg hio, if_pos rfl, hTi, hTshi]
    exact rd_pair pre rest u k hk
  have sh4o : T4.sh o = acc.length + 2 * k + 1 := by
    simp [hT4, hT3, hT2, hT1, Function.update_apply, Ne.symm hio, hTsho]
  have st4o : T4.st o = acc ++ marks (u.take k) ++ [true] := by
    simp only [hT4, hT3, hT2, WState.seth_st, WState.sets_st, Function.update_self]; rw [w2]
  have len4 : (acc ++ marks (u.take k) ++ [true]).length = acc.length + 2 * k + 1 := by
    rw [List.length_append, hlen]; simp
  -- the data bit
  have key : ∀ (bb : Bool), bb = u[k] →
      ∃ T5 : WState ns nr, WExec cap (.ifs i (.wr o true) (.wr o false)) T4 T5 2 ∧
        T5 = T4.sets o (acc ++ marks (u.take k) ++ [true] ++ [bb]) := by
    intro bb hbb
    cases bb with
    | true =>
      refine ⟨_, WExec.ifsT (by rw [hb, ← hbb]) (WExec.wr (cap := cap) o true T4), ?_⟩
      rw [st4o, sh4o, ← len4, PrimT.C4Pipe.write_end]
    | false =>
      refine ⟨_, WExec.ifsF (by rw [hb, ← hbb]) (WExec.wr (cap := cap) o false T4), ?_⟩
      rw [st4o, sh4o, ← len4, PrimT.C4Pipe.write_end]
  obtain ⟨T5, e5, hT5⟩ := key u[k] rfl
  have e6 := WExec.fwd (cap := cap) o T5
  have e7 := WExec.fwd (cap := cap) i (T5.seth o (T5.sh o + 1))
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_ (by omega)
  rw [hT5]
  apply WState.eq
  · funext j
    by_cases hj1 : j = i
    · subst hj1
      simp [hT4, hT3, hT2, hT1, hT, cpyS, Function.update_apply, hio]; omega
    · by_cases hj2 : j = o
      · subst hj2
        simp [hT4, hT3, hT2, hT1, hT, cpyS, Function.update_apply, Ne.symm hio]; omega
      · simp [hT4, hT3, hT2, hT1, hT, cpyS, Function.update_apply, hj1, hj2]
  · funext j
    by_cases hj2 : j = o
    · subst hj2
      simp [hT4, hT3, hT2, hT1, hT, cpyS, Function.update_apply, marks_take_succ u k hk]
    · simp [hT4, hT3, hT2, hT1, hT, cpyS, Function.update_apply, hj2]
  · funext r
    by_cases hr : r = a
    · subst hr; simp [hT4, hT3, hT2, hT1, hT, cpyS, Function.update_apply]; omega
    · simp [hT4, hT3, hT2, hT1, hT, cpyS, Function.update_apply, hr]
  · simp [hT4, hT3, hT2, hT1, hT, cpyS]

/-- **The copy loop's run**: `|u|` marked pairs from stream `i` to the end of stream `o`. -/
theorem cpyW_spec (i o : Fin (ns + 1)) (a : Fin nr) (hio : i ≠ o) (σ : WState ns nr) (pre acc u rest : List Bool)
    (hst : σ.st i = pre ++ marks u ++ rest) (hsh : σ.sh i = pre.length) (hso : σ.st o = acc)
    (hsho : σ.sh o = acc.length) (ha : σ.val a = u.length) (hcap : u.length ≤ cap) :
    WExec cap (cpyW i o a) σ (cpyS i o a σ pre acc u u.length) (u.length * 16 + 1) := by
  have l := UnaryPow.flagLoop cap a _ 14 u.length (cpyS i o a σ pre acc u)
    (fun k hk => by simp [cpyS]; omega) (by simp [cpyS])
    (fun k hk => cpy_step cap i o a hio σ pre acc u rest hst hcap k hk)
  have e0 : cpyS i o a σ pre acc u 0 = σ := by
    apply WState.eq
    · funext j
      by_cases hj1 : j = i
      · subst hj1; simp [cpyS, Function.update_apply, hsh]
      · by_cases hj2 : j = o
        · subst hj2; simp [cpyS, Function.update_apply, hj1, hsho]
        · simp [cpyS, Function.update_apply, hj1, hj2]
    · funext j
      by_cases hj2 : j = o
      · subst hj2; simp [cpyS, marks, hso]
      · simp [cpyS, Function.update_apply, hj2]
    · funext r
      by_cases hr : r = a
      · subst hr; simp [cpyS, ha]
      · simp [cpyS, Function.update_apply, hr]
    · simp [cpyS]
  rw [e0] at l
  exact WExec.mono l (by nlinarith)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
