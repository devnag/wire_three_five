import Proof.Wire_3_5.Primitive.SeedFix.HbPops

/-! # C4.Hb, machine part 6: the HASH factor of a cell's term (P3:2285-2290)

"At prefix `p` print `V_p(z) = Δ₀Σ_yΣ_e F_aux(e,x(y,z))·E_h[H_h(x(y,z)) | p]`" (P3:2285-2287): a cell's term carries
the aux FILTER row `F_{q,e}` of its star row `q` and aux seed `e`. PA's HASH tape holds these rows as single-row
entries at `q·nE + e`. This module skips `k` entries (`skipEntriesC`, C6's `wloop`) and writes the factor record
`T polyWord F` of entry `q·nE + e` on the output (**`factorF_spec`**; the index computed by PA's `mulAddW`).

Registers: `0` the output length; `12` `e`, `13` `q`, `14` `nE`; `22`, `26`, `27` scratch.

Paper quantity of the main type: the factor `F_{q,e}` (`polyWord (Fs[q·nE+e])`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord)
open NearCubicWires.WireExponent3_5.SeedFix (blockWord entryRec)

/-- The HASH tape of the rows `Fs`: one single-row FILTER entry per row. -/
def htWord (Fs : List (List (List ℕ))) : List Bool := blockWord (Fs.map fun P => [[((1 : ℤ), [P])]])

/-- The prefix of the first `k` entries. -/
def htPre (Fs : List (List (List ℕ))) (k : ℕ) : List Bool := (Fs.take k).flatMap fun P => entryRec [[((1 : ℤ), [P])]]

theorem htWord_eq (Fs : List (List (List ℕ))) :
    htWord Fs = Fs.flatMap (fun P => entryRec [[((1 : ℤ), [P])]]) ++ [false] := by
  simp [htWord, blockWord, List.flatMap_map]

theorem ht_split (Fs : List (List (List ℕ))) (k : ℕ) (hk : k < Fs.length) :
    htWord Fs = htPre Fs k ++ (entryRec [[((1 : ℤ), [Fs[k]])]] ++
      ((Fs.drop (k + 1)).flatMap (fun P => entryRec [[((1 : ℤ), [P])]]) ++ [false])) := by
  rw [htWord_eq]
  unfold htPre
  have h1 : Fs.flatMap (fun P => entryRec [[((1 : ℤ), [P])]]) =
      (Fs.take k).flatMap (fun P => entryRec [[((1 : ℤ), [P])]]) ++
        (Fs.drop k).flatMap (fun P => entryRec [[((1 : ℤ), [P])]]) := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [h1, List.drop_eq_getElem_cons hk, List.flatMap_cons]
  simp only [List.append_assoc]

theorem htPre_succ (Fs : List (List (List ℕ))) (k : ℕ) (hk : k < Fs.length) :
    htPre Fs (k + 1) = htPre Fs k ++ entryRec [[((1 : ℤ), [Fs[k]])]] := by
  unfold htPre
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
  simp

section Entries
variable {ns nr : ℕ} (cap : ℕ)

/-- Skip `K` HASH entries. -/
def skipEntriesC (S : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (skipEntryW S))

theorem skipEntriesC_spec (S : Fin (ns + 1)) (K : Fin nr) (Fs : List (List (List ℕ))) (n : ℕ) (hn : n ≤ Fs.length)
    (σ : WState ns nr) (hS : σ.st S = htWord Fs) (hh : σ.sh S = 0) (hK : σ.val K = n) (hnc : n ≤ cap) :
    WExec cap (skipEntriesC S K) σ ((σ.seth S (htPre Fs n).length).setv K 0)
      (n * (2 * 9 + 1 + (4 * (htWord Fs).length + 3 + 1 + 2 * 3) + 4) + 1) := by
  let T : ℕ → WState ns nr := fun k => (σ.seth S (htPre Fs k).length).setv K (n - k)
  have hT0 : T 0 = σ := by
    have e1 : σ.seth S 0 = σ := by conv_lhs => rw [← hh]
                                   exact wseth_same σ S
    simp only [T, htPre, List.take_zero, List.flatMap_nil, List.length_nil, Nat.sub_zero, e1]
    rw [← hK, wsetv_same]
  have hloop := UnionMachine.Round.wloop cap K (skipEntryW S) (2 * 9 + 1 + (4 * (htWord Fs).length + 3 + 1 + 2 * 3))
    n T (fun k _ => by simp [T]) hnc
    (fun k hk => by
      have hkl : k < Fs.length := by omega
      have hpl : (polyWord Fs[k]).length ≤ (htWord Fs).length := by
        rw [ht_split Fs k hkl, entry_single]; simp only [List.length_append]; omega
      have s := skipEntry_spec cap S Fs[k] (htPre Fs k)
        ((Fs.drop (k + 1)).flatMap (fun P => entryRec [[((1 : ℤ), [P])]]) ++ [false]) ((T k).setv K (n - k - 1))
        (by simp [T, hS, ht_split Fs k hkl]) (by simp [T])
      refine WExec.cast cap s ?_ (by omega)
      simp only [T, htPre_succ Fs k hkl, List.length_append]
      wst
      all_goals omega)
  rw [hT0] at hloop
  refine WExec.cast cap hloop ?_ (by omega)
  simp [T]

end Entries

section Factor
variable (cap : ℕ)

/-- `mulAddW`'s registers for the entry index: `a = 13` (`q`), `b = 14` (`nE`), `c = 26`, `t = 22`, `w = 27`. -/
def fR : Fin 5 ↪ Fin 40 := ⟨![13, 14, 26, 22, 27], by decide⟩

/-- **The HASH factor record** `T polyWord F_{q,e}` of entry `q·nE + e`. -/
def factorFW : HW :=
  .seq (emitC sOUT 0 true) (.seq (PrimAsm.ParseNat.addTo 12 26 22) (.seq (PrimAsm.UnaryArith.mulAddW fR)
    (.seq (skipEntriesC sHT 26) (.seq (fwdsW sHT 9) (copyPolyC sHT sOUT 0)))))

/-- The factor record's cost. -/
def factorCost (e q nE idx htl pl : ℕ) : ℕ :=
  7 + 1 + ((18 * e + 3) + 1 + ((nE * (18 * q + 8) + 18 * nE + 10) + 1 +
    ((idx * (2 * 9 + 1 + (4 * htl + 3 + 1 + 2 * 3) + 4) + 1) + 1 + (2 * 9 + 1 + (12 * pl + 10)))))

theorem factorFW_spec (Fs : List (List (List ℕ))) (e q nE idx : ℕ) (hi : e + q * nE = idx) (hidx : idx < Fs.length)
    (σ : HS) (h12 : σ.val 12 = e) (h13 : σ.val 13 = q) (h14 : σ.val 14 = nE) (h22 : σ.val 22 = 0)
    (h26 : σ.val 26 = 0) (h27 : σ.val 27 = 0) (hO : σ.sh sOUT = (σ.st sOUT).length) (hS : σ.st sHT = htWord Fs)
    (hh : σ.sh sHT = 0) (hcap : σ.val 0 + 1 + (htWord Fs).length + e + q * nE + nE + q ≤ cap) :
    ∃ x, WExec cap factorFW σ (appendO (σ.seth sHT x) sOUT 0 ([true] ++ polyWord Fs[idx]))
      (factorCost e q nE idx (htWord Fs).length (polyWord Fs[idx]).length) := by
  have hpl : (htPre Fs idx).length + 9 + (polyWord Fs[idx]).length + 3 ≤ (htWord Fs).length := by
    rw [ht_split Fs idx hidx, entry_single]; simp only [List.length_append]; simp; omega
  have s1 := emitC_app cap sOUT 0 true σ hO (by omega)
  have s2 := PrimAsm.ParseNat.addTo_spec cap 12 26 22 (by decide) (by decide) (by decide) (appendO σ sOUT 0 [true])
    (by simp [h22]) (by simp [h12]; omega) (by simp [h12, h26]; omega)
  have v2 : (appendO σ sOUT 0 [true]).val 26 + (appendO σ sOUT 0 [true]).val 12 = e := by simp [h12, h26]
  have v2' : (appendO σ sOUT 0 [true]).val 12 = e := by simp [h12]
  rw [v2, v2'] at s2
  have va : ((appendO σ sOUT 0 [true]).setv 26 e).val (fR 0) = q := by simp [fR, h13]
  have vb : ((appendO σ sOUT 0 [true]).setv 26 e).val (fR 1) = nE := by simp [fR, h14]
  have vc : ((appendO σ sOUT 0 [true]).setv 26 e).val (fR 2) = e := by simp [fR]
  have s3 := PrimAsm.UnaryArith.mulAddW_spec cap fR ((appendO σ sOUT 0 [true]).setv 26 e) (by simp [fR, h22])
    (by simp [fR, h27]) (by rw [vb]; omega) (by rw [vc, va, vb]; omega) (by rw [va]; omega)
  rw [va, vb, vc, hi] at s3
  have hf2 : (fR 2 : Fin 40) = 26 := rfl
  rw [hf2, wsetv_setv] at s3
  have s4 := skipEntriesC_spec cap sHT 26 Fs idx hidx.le (((appendO σ sOUT 0 [true]).setv 26 idx))
    (by simp [hS]) (by simp [hh]) (by simp) (by omega)
  have s5 := fwdsW_spec cap sHT 9 (((appendO σ sOUT 0 [true]).setv 26 idx).seth sHT (htPre Fs idx).length |>.setv 26 0)
  have s6 := copyPolyC_spec cap sHT sOUT (by decide) 0 Fs[idx]
    (htPre Fs idx ++ [true, true, true, true, false, true, true, false, true])
    ([false, false, false] ++ ((Fs.drop (idx + 1)).flatMap (fun P => entryRec [[((1 : ℤ), [P])]]) ++ [false]))
    ((((appendO σ sOUT 0 [true]).setv 26 idx).seth sHT (htPre Fs idx).length |>.setv 26 0).seth sHT
      ((htPre Fs idx).length + 9))
    (by simp [hS, ht_split Fs idx hidx, entry_single])
    (by simp)
    (by simp [hO])
    (by simp; omega)
  refine ⟨(htPre Fs idx ++ [true, true, true, true, false, true, true, false, true]).length + (polyWord Fs[idx]).length,
    WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_
    (by unfold factorCost; omega)⟩
  wst
  all_goals (try simp_all) <;> omega

end Factor

/-! ## The coefficient word -/

/-- The cleared weights' stream: one framed word per level. -/
def wtWord (Ws : List (List Bool)) : List Bool := Ws.flatMap frame

section Coef
variable {ns nr : ℕ} (cap : ℕ)

/-- The prefix of the first `k` framed words. -/
def wtPre (Ws : List (List Bool)) (k : ℕ) : List Bool := (Ws.take k).flatMap frame

theorem wtPre_succ (Ws : List (List Bool)) (k : ℕ) (hk : k < Ws.length) :
    wtPre Ws (k + 1) = wtPre Ws k ++ frame Ws[k] := by
  unfold wtPre
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
  simp

theorem wt_split (Ws : List (List Bool)) (k : ℕ) (hk : k < Ws.length) :
    wtWord Ws = wtPre Ws k ++ (frame Ws[k] ++ (Ws.drop (k + 1)).flatMap frame) := by
  unfold wtWord wtPre
  have h1 : Ws.flatMap frame = (Ws.take k).flatMap frame ++ (Ws.drop k).flatMap frame := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [h1, List.drop_eq_getElem_cons hk, List.flatMap_cons]

/-- Skip `K` framed words. -/
def skipFramesK (S : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (PrimT.skipFrameW S))

theorem skipFramesK_spec (S : Fin (ns + 1)) (K : Fin nr) (Ws : List (List Bool)) (n : ℕ) (hn : n ≤ Ws.length)
    (σ : WState ns nr) (hS : σ.st S = wtWord Ws) (hh : σ.sh S = 0) (hK : σ.val K = n) (hnc : n ≤ cap) :
    WExec cap (skipFramesK S K) σ ((σ.seth S (wtPre Ws n).length).setv K 0)
      (n * (5 * (wtWord Ws).length + 3 + 4) + 1) := by
  let T : ℕ → WState ns nr := fun k => (σ.seth S (wtPre Ws k).length).setv K (n - k)
  have hT0 : T 0 = σ := by
    have e1 : σ.seth S 0 = σ := by conv_lhs => rw [← hh]
                                   exact wseth_same σ S
    simp only [T, wtPre, List.take_zero, List.flatMap_nil, List.length_nil, Nat.sub_zero, e1]
    rw [← hK, wsetv_same]
  have hloop := UnionMachine.Round.wloop cap K (PrimT.skipFrameW S) (5 * (wtWord Ws).length + 3) n T
    (fun k _ => by simp [T]) hnc
    (fun k hk => by
      have hkl : k < Ws.length := by omega
      have hwl : Ws[k].length ≤ (wtWord Ws).length := by
        rw [wt_split Ws k hkl]; simp only [List.length_append, frame_length]; omega
      have s := PrimT.skipFrame_spec cap S (wtPre Ws k) ((Ws.drop (k + 1)).flatMap frame) Ws[k]
        ((T k).setv K (n - k - 1)) (by simp [T, hS, wt_split Ws k hkl]) (by simp [T])
      refine WExec.cast cap s ?_ (by omega)
      simp only [T, wtPre_succ Ws k hkl, List.length_append]
      wst
      all_goals omega)
  rw [hT0] at hloop
  refine WExec.cast cap hloop ?_ (by omega)
  simp [T]

theorem reps_succ' (n : ℕ) (u : List Bool) : PrimAsm.FiltRec.reps (n + 1) u = u ++ PrimAsm.FiltRec.reps n u := by
  unfold PrimAsm.FiltRec.reps; rw [List.replicate_succ, List.flatten_cons]

/-- The count exponent's pairs: one `T F` per `1` of `X`. -/
def expPairsW (X O : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .whs X (.seq (emitC O OP true) (.seq (emitC O OP false) (.fwd X)))

theorem expPairs_spec (X O : Fin (ns + 1)) (hXO : X ≠ O) (OP : Fin nr) (xs : List Bool) :
    ∀ (e : ℕ) (pre : List Bool) (σ : WState ns nr), σ.st X = pre ++ (List.replicate e true ++ false :: xs) →
      σ.sh X = pre.length → σ.sh O = (σ.st O).length → σ.val OP + 2 * e ≤ cap →
      WExec cap (expPairsW X O OP) σ (appendO (σ.seth X (pre.length + e)) O OP (PrimAsm.FiltRec.reps e [true, false]))
        (19 * e + 1)
  | 0, pre, σ, hX, hh, _, _ => by
    have hz : wbit σ X = false := by simp [wbit, hX, hh, rd_app0]
    have e : appendO (σ.seth X (pre.length + 0)) O OP (PrimAsm.FiltRec.reps 0 [true, false]) = σ := by
      simp only [Nat.add_zero, ← hh, wseth_same, PrimAsm.FiltRec.reps_zero, appendO_nil]
    rw [e]; exact WExec.whsF hz
  | e + 1, pre, σ, hX, hh, hO, hc => by
    have hOX : O ≠ X := fun h => hXO h.symm
    have hw : wbit σ X = true := by simp [wbit, hX, hh, rd_app0, List.replicate_succ]
    have s1 := emitC_app cap O OP true σ hO (by omega)
    have s2 := emitC_app cap O OP false (appendO σ O OP [true]) (by simp [hO]) (by simp; omega)
    have s3 := WExec.fwd (cap := cap) X (appendO (appendO σ O OP [true]) O OP [false])
    have ih := expPairs_spec X O hXO OP xs e (pre ++ [true])
      ((appendO (appendO σ O OP [true]) O OP [false]).seth X ((appendO (appendO σ O OP [true]) O OP [false]).sh X + 1))
      (by simp [Function.update_of_ne hXO, hX, List.replicate_succ])
      (by simp [Function.update_of_ne hXO, hh])
      (by simp [Function.update_of_ne hOX, hO]; try omega)
      (by simp; omega)
    refine WExec.cast cap (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) ih) ?_ (by omega)
    rw [wseth_seth, appendO_seth_comm _ O X hXO, appendO_seth_comm _ O X hXO, appendO_append, appendO_append,
      reps_succ']
    congr 1
    simp; omega

end Coef

section CoefW
variable (cap : ℕ)

/-- **The coefficient word** `[T, sign] ++ (TF)^e ++ frame(bits W_λ)`: the sign from register `23`, the count's exponent
`e` from `XE`, the cleared weight of level `λ` (register `9`) from `WT`. -/
def coefW : HW :=
  .seq (emitC sOUT 0 true) (.seq (.ifr 23 (emitC sOUT 0 true) (emitC sOUT 0 false)) (.seq (expPairsW sXE sOUT 0)
    (.seq (FinalPass.Hash4.wcopyR 9 18 22) (.seq (skipFramesK sWT 18) (copyFrameC sWT sOUT 0)))))

/-- The coefficient word's cost. -/
def coefCost (e lam wtl fl : ℕ) : ℕ :=
  7 + 1 + (8 + 1 + ((19 * e + 1) + 1 + ((18 * lam + 3) + 1 + ((lam * (5 * wtl + 3 + 4) + 1) + 1 + 11 * fl))))

theorem coefW_spec (s : Bool) (e lam : ℕ) (xs : List Bool) (Ws : List (List Bool)) (hlam : lam < Ws.length) (σ : HS)
    (h23 : σ.val 23 = if s then 1 else 0) (h9 : σ.val 9 = lam) (h18 : σ.val 18 = 0) (h22 : σ.val 22 = 0)
    (hX : σ.st sXE = List.replicate e true ++ false :: xs) (hXh : σ.sh sXE = 0)
    (hW : σ.st sWT = wtWord Ws) (hWh : σ.sh sWT = 0) (hO : σ.sh sOUT = (σ.st sOUT).length)
    (hcap : σ.val 0 + 2 + 2 * e + (wtWord Ws).length + lam + 1 ≤ cap) :
    ∃ hx hw, WExec cap coefW σ
      (appendO ((σ.seth sXE hx).seth sWT hw) sOUT 0 ([true, s] ++ PrimAsm.FiltRec.reps e [true, false] ++ frame Ws[lam]))
      (coefCost e lam (wtWord Ws).length (frame Ws[lam]).length) := by
  have hfl : (frame Ws[lam]).length + (wtPre Ws lam).length ≤ (wtWord Ws).length := by
    rw [wt_split Ws lam hlam]; simp only [List.length_append]; omega
  have s1 := emitC_app cap sOUT 0 true σ hO (by omega)
  have s2 : WExec cap (.ifr 23 (emitC sOUT 0 true) (emitC sOUT 0 false)) (appendO σ sOUT 0 [true])
      (appendO (appendO σ sOUT 0 [true]) sOUT 0 [s]) 8 := by
    have ho : (appendO σ sOUT 0 [true]).sh sOUT = ((appendO σ sOUT 0 [true]).st sOUT).length := by simp [hO]
    have hc : (appendO σ sOUT 0 [true]).val 0 < cap := by simp; omega
    cases s
    · exact WExec.ifrF (by simp [h23]) (emitC_app cap sOUT 0 false _ ho hc)
    · exact WExec.ifrT (by simp [h23]) (emitC_app cap sOUT 0 true _ ho hc)
  have s3 := expPairs_spec cap sXE sOUT (by decide) 0 xs e [] (appendO (appendO σ sOUT 0 [true]) sOUT 0 [s])
    (by simp [hX]) (by simp [hXh]) (by simp [hO]) (by simp; omega)
  simp only [List.length_nil, Nat.zero_add] at s3
  set σ3 := appendO ((appendO (appendO σ sOUT 0 [true]) sOUT 0 [s]).seth sXE e) sOUT 0
    (PrimAsm.FiltRec.reps e [true, false]) with hσ3
  have s4 := FinalPass.Hash4.wcopyR_spec cap 9 18 22 (by decide) (by decide) (by decide) σ3
    (by simp [σ3, h18]) (by simp [σ3, h22]) (by simp [σ3, h9]; omega)
  have v4 : σ3.val 9 = lam := by simp [σ3, h9]
  rw [v4] at s4
  have s5 := skipFramesK_spec cap sWT 18 Ws lam hlam.le (σ3.setv 18 lam) (by simp [σ3, hW]) (by simp [σ3, hWh])
    (by simp) (by omega)
  have s6 := copyFrameC_spec cap sWT sOUT (by decide) 0 (wtPre Ws lam) Ws[lam] ((Ws.drop (lam + 1)).flatMap frame)
    (((σ3.setv 18 lam).seth sWT (wtPre Ws lam).length).setv 18 0)
    (by simp [σ3, hW, wt_split Ws lam hlam]) (by simp [σ3]) (by simp [σ3, hO]; try omega)
    (by have hfl2 : (frame Ws[lam]).length = 2 * Ws[lam].length + 1 := frame_length _
        simp only [hσ3, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
        simp [PrimT.HbM.reps_length]; omega)
  refine ⟨e, (wtPre Ws lam).length + (frame Ws[lam]).length,
    WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_
      (by unfold coefCost; omega)⟩
  rw [hσ3]
  wst
  all_goals (try simp_all [PrimT.HbM.reps_length]) <;> omega

end CoefW

end NearCubicWires.WireExponent3_5.PrimT.HbM
