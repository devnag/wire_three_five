import Proof.Wire_3_5.UnionMachine.FrontTWKit

/-! # C6 front, U5: the table writer's layout and its field moves

The table writer is one register program (C5's `WM`) over eleven streams: the table it writes (`sOut`, scratch), the
PCPP output word (`sPO`, read once per pass), the witness (`sW`: the guess's grid entries, raw), the framed item
lists it copies from (`sHd` the fixed head `natWord q ++ [mode] ++ natWord 4` of every request word, `sTl` the fixed
tail `natListWord translation`, `sCC` the constant's code, `sPC` the parities' codes, `sCR` the carriers' codes) and
three flag strings (`sDF`, `sPF`, `sEF`: the description envelope of each grid atom and parity, the carrier envelope
of each variable). Every source head rests at `0` between moves (**`ts`**: the writer's state, its output and
registers; the output position register is the output's length).

Moves (each from `ts` to `ts`): `emitRawT` (one raw bit), **`copyItemT`** (the `k`-th framed item's `marks`),
**`copyEntT`** (the `e`-th grid entry's code field, as `marks`), **`bitAtT`** (a flag bit into a register),
`okAndT` (conjoin a flag into `OK`).

Paper quantity of the main statements: the fields of each call's word, copied into the table. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)

/-! ## The layout -/

/-- The register count. -/
abbrev NR : ℕ := 56

/-- The writer's state. -/
abbrev TS := WState 10 NR

abbrev sOut : Fin 11 := 0
abbrev sPO : Fin 11 := 1
abbrev sW : Fin 11 := 2
abbrev sHd : Fin 11 := 3
abbrev sTl : Fin 11 := 4
abbrev sCC : Fin 11 := 5
abbrev sPC : Fin 11 := 6
abbrev sCR : Fin 11 := 7
abbrev sDF : Fin 11 := 8
abbrev sPF : Fin 11 := 9
abbrev sEF : Fin 11 := 10

abbrev rOP : Fin NR := 0
abbrev rBIG : Fin NR := 1
abbrev rT : Fin NR := 2
abbrev rF : Fin NR := 3
abbrev rC : Fin NR := 4
abbrev rP : Fin NR := 5
abbrev rTT : Fin NR := 6
abbrev rSS : Fin NR := 7
abbrev rLAM : Fin NR := 8
abbrev rSYS : Fin NR := 9
abbrev rCDF : Fin NR := 11
abbrev rOK : Fin NR := 12
abbrev rX : Fin NR := 13
abbrev rY : Fin NR := 14
abbrev rXS : Fin NR := 15
abbrev rYS : Fin NR := 16
abbrev rN0 : Fin NR := 17
abbrev rN1 : Fin NR := 18
abbrev rCL : Fin NR := 19
abbrev rL0 : Fin NR := 20
abbrev rL1 : Fin NR := 21
abbrev rMAG : Fin NR := 22
abbrev rNEG : Fin NR := 23
abbrev rZ : Fin NR := 36
abbrev rFL : Fin NR := 37
abbrev rNZ : Fin NR := 38
abbrev rSYSX : Fin NR := 39

/-- Digit `k`'s entry index, sign bit and loop counter. -/
def rE (k : Fin 4) : Fin NR := ⟨24 + k.val, by have := k.isLt; show 24 + k.val < 56; omega⟩
def rNB (k : Fin 4) : Fin NR := ⟨28 + k.val, by have := k.isLt; show 28 + k.val < 56; omega⟩
def rA (k : Fin 4) : Fin NR := ⟨32 + k.val, by have := k.isLt; show 32 + k.val < 56; omega⟩

/-- **The writer's state**: the sources `src` (every head at `0` except the PCPP cursor `h`), the output `o` (head at
its end, its length in `OP`), the registers `v` and the cell. -/
def ts (src : Fin 11 → List Bool) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) : TS :=
  ⟨fun i => if i = sOut then o.length else if i = sPO then h else 0, fun i => if i = sOut then o else src i,
    Function.update v rOP o.length, c⟩

variable (cap : ℕ) (src : Fin 11 → List Bool)

@[simp] theorem ts_st (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (s : Fin 11) (hs : s ≠ sOut) :
    (ts src h o v c).st s = src s := by simp +decide [ts, hs]

@[simp] theorem ts_st_out (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) : (ts src h o v c).st sOut = o := by
  simp +decide [ts]

@[simp] theorem ts_sh_out (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) :
    (ts src h o v c).sh sOut = o.length := by simp +decide [ts]

@[simp] theorem ts_sh_PO (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) : (ts src h o v c).sh sPO = h := by
  simp +decide [ts]

theorem ts_sh_src (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (s : Fin 11) (h1 : s ≠ sOut) (h2 : s ≠ sPO) :
    (ts src h o v c).sh s = 0 := by simp +decide [ts, h1, h2]

theorem ts_val (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (r : Fin NR) (hr : r ≠ rOP) :
    (ts src h o v c).val r = v r := by simp +decide [ts, Function.update_of_ne hr]

@[simp] theorem ts_val_OP (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) : (ts src h o v c).val rOP = o.length := by
  simp +decide [ts]

@[simp] theorem ts_cell (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) : (ts src h o v c).cell = c := rfl

theorem ts_setv (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (r : Fin NR) (hr : r ≠ rOP) (x : ℕ) :
    (ts src h o v c).setv r x = ts src h o (Function.update v r x) c := by
  apply WState.eq <;> try rfl
  simp only [ts, WState.setv_val]
  exact (Function.update_comm hr _ _ _).symm

theorem appendO_ts (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (u : List Bool) :
    appendO (ts src h o v c) sOut rOP u = ts src h (o ++ u) v c := by
  apply WState.eq
  · funext i; by_cases hi : i = sOut
    · subst hi; simp +decide [ts]
    · simp +decide [ts, hi]
  · funext i; by_cases hi : i = sOut
    · subst hi; simp +decide [ts]
    · simp +decide [ts, hi]
  · simp +decide [ts]
  · rfl

theorem ts_seth_zero (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (s : Fin 11) (h1 : s ≠ sOut) (h2 : s ≠ sPO)
    (p : ℕ) : ((ts src h o v c).seth s p).seth s 0 = ts src h o v c := by
  apply WState.eq <;> try rfl
  funext i; by_cases hi : i = s
  · subst hi; simp +decide [ts, h1, h2]
  · simp +decide [Function.update_of_ne hi]

theorem ts_seth_PO (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (p : ℕ) :
    (ts src h o v c).seth sPO p = ts src p o v c := by
  apply WState.eq <;> try rfl
  funext i; by_cases hi : i = sPO
  · subst hi; simp +decide [ts]
  · by_cases ho : i = sOut
    · subst ho; simp +decide [ts]
    · simp +decide [ts, Function.update_of_ne hi, hi, ho]

/-! ## One raw bit -/

theorem emitRawT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c b : Bool) (hc : o.length < cap) :
    WExec cap (emitC sOut rOP b) (ts src h o v c) (ts src h (o ++ [b]) v c) 7 := by
  have e := emitC_spec cap sOut rOP b (ts src h o v c) (by simp +decide) (by simpa using hc)
  refine WExec.cast cap e ?_ le_rfl
  have : (((ts src h o v c).sets sOut ((ts src h o v c).st sOut ++ [b])).seth sOut
      ((ts src h o v c).sh sOut + 1)).setv rOP ((ts src h o v c).val rOP + 1) = appendO (ts src h o v c) sOut rOP [b] := by
    simp +decide [appendO]
  rw [this, appendO_ts]

/-! ## Rewinding a source -/

theorem rewT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (s : Fin 11) (h1 : s ≠ sOut) (h2 : s ≠ sPO) (p : ℕ)
    (hT : v rT = 0) (hp : p ≤ v rBIG) (hcap : v rBIG ≤ cap) :
    WExec cap (rewB s rBIG rT) ((ts src h o v c).seth s p) (ts src h o v c) (16 * v rBIG + 3) := by
  have vT : ((ts src h o v c).seth s p).val rT = 0 := by
    rw [WState.seth_val, ts_val _ _ _ _ _ rT (by decide)]; exact hT
  have vB : ((ts src h o v c).seth s p).val rBIG = v rBIG := by
    rw [WState.seth_val, ts_val _ _ _ _ _ rBIG (by decide)]
  have hsh : ((ts src h o v c).seth s p).sh s = p := by simp
  have e := rewB_spec cap s rBIG rT (by decide) ((ts src h o v c).seth s p) vT (by rw [hsh, vB]; exact hp)
    (by rw [vB]; exact hcap)
  rw [ts_seth_zero src h o v c s h1 h2, vB] at e
  exact WExec.mono e (by omega)

/-! ## Copying a framed item -/

/-- Copy item `K` of the framed list on `s`, then rewind `s`. -/
def copyItem (s : Fin 11) (K : Fin NR) : WM 10 NR := .seq (skipFrK s K rT) (.seq (copyFr s sOut rOP) (rewB s rBIG rT))

/-- **Copying item `K`**: `marks` of the item is appended; every register is as before. -/
theorem copyItemT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (s : Fin 11) (h1 : s ≠ sOut) (h2 : s ≠ sPO)
    (K : Fin NR) (hK1 : K ≠ rT) (hK2 : K ≠ rOP) (ws : List (List Bool)) (rest : List Bool)
    (hsrc : src s = frItems ws ++ rest) (hk : v K < ws.length) (hT : v rT = 0)
    (hBIG : (frItems ws).length ≤ v rBIG) (hcapB : v rBIG ≤ cap) (hcapK : v K ≤ cap)
    (hcapO : o.length + 2 * (frItems ws).length ≤ cap) :
    WExec cap (copyItem s K) (ts src h o v c) (ts src h (o ++ marks (ws.getD (v K) [])) v c)
      (v K * (5 * (frItems ws).length + 3 + 8) + 1 + 1 + (7 * v K + 1) + 1 + (22 * (frItems ws).length + 3) + 1 +
        (16 * v rBIG + 3)) := by
  have hsplit := frItems_split ws (v K) hk
  have hwl : (ws.getD (v K) []).length ≤ (frItems ws).length := by
    rw [hsplit]; simp +decide [FrontTWKit.frame_length]; omega
  have s1 := skipFrK_spec cap s K rT hK1 ws rest (ts src h o v c) (by simp +decide [h1, hsrc])
    (ts_sh_src src h o v c s h1 h2) (by rw [ts_val _ _ _ _ _ rT (by decide)]; exact hT)
    (by rw [ts_val _ _ _ _ _ K hK2]; omega) (by rw [ts_val _ _ _ _ _ K hK2]; exact hcapK)
  rw [ts_val _ _ _ _ _ K hK2] at s1
  set σ1 := (ts src h o v c).seth s (frItems (ws.take (v K))).length with hσ1
  have s2 := copyFr_spec cap s sOut h1 rOP (frItems (ws.take (v K))) (ws.getD (v K) [])
    (frItems (ws.drop (v K + 1)) ++ rest) σ1 (by simp +decide [σ1, h1, hsrc, hsplit, List.append_assoc]) (by simp +decide [σ1])
    (by simp +decide [σ1, Function.update_of_ne (Ne.symm h1)]) (by simp only [σ1, WState.seth_val, ts_val_OP]; omega)
  have e2 : (appendO σ1 sOut rOP (marks (ws.getD (v K) []))).seth s
      ((frItems (ws.take (v K))).length + (frame (ws.getD (v K) [])).length) =
      (ts src h (o ++ marks (ws.getD (v K) [])) v c).seth s
        ((frItems (ws.take (v K))).length + (frame (ws.getD (v K) [])).length) := by
    simp only [σ1]
    have : appendO ((ts src h o v c).seth s (frItems (ws.take (v K))).length) sOut rOP (marks (ws.getD (v K) [])) =
        (appendO (ts src h o v c) sOut rOP (marks (ws.getD (v K) []))).seth s (frItems (ws.take (v K))).length := by
      apply WState.eq <;> try rfl
      · funext i; by_cases hi : i = sOut
        · subst hi; simp +decide [Function.update_of_ne (Ne.symm h1)]
        · by_cases his : i = s
          · subst his; simp +decide [hi]
          · simp +decide [Function.update_of_ne hi, Function.update_of_ne his]
    rw [this, appendO_ts, wseth_seth]
  rw [e2] at s2
  have hpos : (frItems (ws.take (v K))).length + (frame (ws.getD (v K) [])).length ≤ v rBIG := by
    have := congrArg List.length hsplit
    simp only [List.length_append] at this
    omega
  have s3 := rewT cap src h (o ++ marks (ws.getD (v K) [])) v c s h1 h2 _ hT hpos hcapB
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega)

/-! ## Copying a grid entry's code -/

/-- A grid entry: its sign word `b 1 0 x`, then its atom's code. -/
def entW (e : Bool × Bool × ℕ) : List Bool := [e.1, true, false, e.2.1] ++ natWord e.2.2

/-- The entries' word. -/
def entsW (es : List (Bool × Bool × ℕ)) : List Bool := (es.map entW).flatten

/-- Skip one grid entry. -/
def skipEnt : WM 10 NR := .seq (.fwd sW) (.seq (.fwd sW) (.seq (.fwd sW) (.seq (.fwd sW) (skipNatM false sW rF rC))))

theorem entsW_split (es : List (Bool × Bool × ℕ)) (k : ℕ) (hk : k < es.length) :
    entsW es = entsW (es.take k) ++ entW (es.getD k (false, false, 0)) ++ entsW (es.drop (k + 1)) := by
  unfold entsW
  conv_lhs => rw [← List.take_append_drop k es, List.drop_eq_getElem_cons hk]
  rw [List.getD_eq_getElem _ _ hk]
  simp only [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons, List.append_assoc]

theorem skipEnt_spec (σ : TS) (es : List (Bool × Bool × ℕ)) (rest : List Bool) (k : ℕ) (hk : k < es.length)
    (hst : σ.st sW = entsW es ++ rest) (hsh : σ.sh sW = (entsW (es.take k)).length) (hF : σ.val rF = 0)
    (hC : σ.val rC = 0) (hcap : natBitLength (es.getD k (false, false, 0)).2.2 + 1 ≤ cap) :
    WExec cap skipEnt σ (σ.seth sW (entsW (es.take (k + 1))).length)
      (20 * natBitLength (es.getD k (false, false, 0)).2.2 + 20 + 8) := by
  set e := es.getD k (false, false, 0) with he
  have hsplit := entsW_split es k hk
  have f1 := WExec.fwd (cap := cap) sW σ
  have f2 := WExec.fwd (cap := cap) sW (σ.seth sW (σ.sh sW + 1))
  have f3 := WExec.fwd (cap := cap) sW ((σ.seth sW (σ.sh sW + 1)).seth sW ((σ.seth sW (σ.sh sW + 1)).sh sW + 1))
  simp only [wseth_seth, WState.seth_sh, Function.update_self] at f2 f3
  have f4 := WExec.fwd (cap := cap) sW (σ.seth sW (σ.sh sW + 1 + 1 + 1))
  simp only [wseth_seth, WState.seth_sh, Function.update_self] at f4
  have s5 := skipNatM_spec cap false sW rF rC (by decide) e.2.2 (entsW (es.take k) ++ [e.1, true, false, e.2.1])
    (entsW (es.drop (k + 1)) ++ rest) (σ.seth sW (σ.sh sW + 1 + 1 + 1 + 1))
    (by simp +decide [hst, hsplit, entW, PrimAsm.ParseNat.enc, List.append_assoc, he]) (by simp +decide [hsh]) (by simpa using hF) (by simpa using hC) hcap
  rw [wseth_seth] at s5
  have hlen : (entsW (es.take (k + 1))).length = (entsW (es.take k) ++ [e.1, true, false, e.2.1]).length +
      stp false * (natWord e.2.2).length := by
    have : es.take (k + 1) = es.take k ++ [e] := by
      rw [he, List.getD_eq_getElem _ _ hk]; exact List.take_succ_eq_append_getElem hk
    rw [this]; simp +decide [entsW, entW, stp]; ring
  rw [← hlen] at s5
  exact WExec.mono (WExec.seq f1 (WExec.seq f2 (WExec.seq f3 (WExec.seq f4 s5)))) (by omega)

/-- Skip `K` grid entries, restoring `K`. -/
def skipEntK (K : Fin NR) : WM 10 NR := cloop K rT skipEnt

/-- The largest code among the entries (for the capacity). -/
def codeMax (es : List (Bool × Bool × ℕ)) : ℕ := (es.map fun e => natBitLength e.2.2).foldr max 0

theorem le_codeMax (es : List (Bool × Bool × ℕ)) (k : ℕ) (hk : k < es.length) :
    natBitLength (es.getD k (false, false, 0)).2.2 ≤ codeMax es := by
  unfold codeMax
  have hmem : natBitLength (es.getD k (false, false, 0)).2.2 ∈ es.map fun e => natBitLength e.2.2 := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.mem_map.2 ⟨_, List.getElem_mem hk, rfl⟩
  have key : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
    intro l x hx
    induction l with
    | nil => simp +decide at hx
    | cons a l ih =>
      rcases List.mem_cons.1 hx with h | h
      · subst h; exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)
  exact key _ _ hmem

theorem skipEntK_spec (σ : TS) (K : Fin NR) (hK1 : K ≠ rT) (hK2 : K ≠ rF) (hK3 : K ≠ rC)
    (es : List (Bool × Bool × ℕ)) (rest : List Bool)
    (hst : σ.st sW = entsW es ++ rest) (hsh : σ.sh sW = 0) (hF : σ.val rF = 0) (hC : σ.val rC = 0)
    (hT : σ.val rT = 0) (hk : σ.val K ≤ es.length) (hcapK : σ.val K ≤ cap) (hcap : codeMax es + 1 ≤ cap) :
    WExec cap (skipEntK K) σ (σ.seth sW (entsW (es.take (σ.val K))).length)
      (σ.val K * (20 * codeMax es + 28 + 8) + 1 + 1 + (7 * σ.val K + 1)) := by
  set n := σ.val K with hn
  have h := cloop_spec cap K rT hK1 skipEnt n (20 * codeMax es + 28)
    (fun j => σ.seth sW (entsW (es.take j)).length) hcapK (by
      intro j hj
      have hj' : j < es.length := by omega
      have hs := skipEnt_spec cap (((σ.seth sW (entsW (es.take j)).length).setv K (n - j - 1)).setv rT (j + 1)) es rest
        j hj' (by simp +decide [hst]) (by simp +decide) (by simp +decide [Function.update_of_ne (Ne.symm hK2), hF])
        (by simp +decide [Function.update_of_ne (Ne.symm hK3), hC]) (by have := le_codeMax es j hj'; omega)
      have hle := le_codeMax es j hj'
      refine WExec.mono (WExec.cast cap hs ?_ le_rfl) (by omega)
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = sW
      · subst hi; simp
      · simp +decide [Function.update_of_ne hi])
  have e0 : ((σ.seth sW (entsW (es.take 0)).length).setv K n).setv rT 0 = σ := by
    apply WState.eq <;> try rfl
    · funext i; by_cases hi : i = sW
      · subst hi; simp +decide [hsh, entsW]
      · simp +decide [Function.update_of_ne hi]
    · funext i; by_cases hi : i = rT
      · subst hi; simp +decide [hT]
      · by_cases hi' : i = K
        · subst hi'; simp +decide [Function.update_of_ne hi, hn]
        · simp +decide [Function.update_of_ne hi, Function.update_of_ne hi']
  have e1 : ((σ.seth sW (entsW (es.take n)).length).setv K n).setv rT 0 = σ.seth sW (entsW (es.take n)).length := by
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = rT
    · subst hi; simp +decide [hT]
    · by_cases hi' : i = K
      · subst hi'; simp +decide [Function.update_of_ne hi, hn]
      · simp +decide [Function.update_of_ne hi, Function.update_of_ne hi']
  rw [e0, e1] at h
  exact h

/-- Copy grid entry `E`'s code field (as `marks`), then rewind the witness. -/
def copyEnt (E : Fin NR) : WM 10 NR :=
  .seq (skipEntK E) (.seq (.fwd sW) (.seq (.fwd sW) (.seq (.fwd sW) (.seq (.fwd sW)
    (.seq (copyNatM false sW sOut rF rC rOP) (rewB sW rBIG rT))))))

/-- **Copying grid entry `E`'s code**: `marks (natWord c)` is appended; every register is as before. -/
theorem copyEntT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (E : Fin NR) (hE1 : E ≠ rT) (hE2 : E ≠ rF)
    (hE3 : E ≠ rC) (hE4 : E ≠ rOP) (es : List (Bool × Bool × ℕ)) (rest : List Bool) (hsrc : src sW = entsW es ++ rest)
    (hk : v E < es.length) (hF : v rF = 0) (hC : v rC = 0) (hT : v rT = 0) (hBIG : (entsW es).length ≤ v rBIG)
    (hcapB : v rBIG ≤ cap) (hcapE : v E ≤ cap) (hcapM : codeMax es + 1 ≤ cap)
    (hcapO : o.length + 2 * (entsW es).length + 2 ≤ cap) :
    WExec cap (copyEnt E) (ts src h o v c) (ts src h (o ++ marks (natWord (es.getD (v E) (false, false, 0)).2.2)) v c)
      (v E * (20 * codeMax es + 28 + 8) + 1 + 1 + (7 * v E + 1) + 1 + 8 + (60 * (entsW es).length + 60) + 1 +
        (16 * v rBIG + 3)) := by
  set e := es.getD (v E) (false, false, 0) with he
  have hsplit := entsW_split es (v E) hk
  have s1 := skipEntK_spec cap (ts src h o v c) E hE1 hE2 hE3 es rest (by simp +decide [hsrc]) (by simp +decide [ts])
    (by rw [ts_val _ _ _ _ _ rF (by decide)]; exact hF) (by rw [ts_val _ _ _ _ _ rC (by decide)]; exact hC)
    (by rw [ts_val _ _ _ _ _ rT (by decide)]; exact hT) (by rw [ts_val _ _ _ _ _ E hE4]; omega)
    (by rw [ts_val _ _ _ _ _ E hE4]; exact hcapE) hcapM
  rw [ts_val _ _ _ _ _ E hE4] at s1
  set p0 := (entsW (es.take (v E))).length with hp0
  have f1 := WExec.fwd (cap := cap) sW ((ts src h o v c).seth sW p0)
  have f2 := WExec.fwd (cap := cap) sW (((ts src h o v c).seth sW p0).seth sW
    (((ts src h o v c).seth sW p0).sh sW + 1))
  simp only [wseth_seth, WState.seth_sh, Function.update_self] at f1 f2
  have f3 := WExec.fwd (cap := cap) sW ((ts src h o v c).seth sW (p0 + 1 + 1))
  simp only [wseth_seth, WState.seth_sh, Function.update_self] at f3
  have f4 := WExec.fwd (cap := cap) sW ((ts src h o v c).seth sW (p0 + 1 + 1 + 1))
  simp only [wseth_seth, WState.seth_sh, Function.update_self] at f4
  set σ5 := (ts src h o v c).seth sW (p0 + 1 + 1 + 1 + 1) with hσ5
  have hlenE : (natWord e.2.2).length ≤ (entsW es).length := by
    rw [hsplit, ← he]; simp only [List.length_append, entW, List.length_cons, List.length_nil]; omega
  have s6 := copyNatM_spec cap false sW sOut (by decide) rF rC rOP (by decide) (by decide) (by decide) e.2.2
    (entsW (es.take (v E)) ++ [e.1, true, false, e.2.1]) (entsW (es.drop (v E + 1)) ++ rest) σ5
    (by simp +decide [σ5, hsrc, hsplit, entW, PrimAsm.ParseNat.enc, List.append_assoc, he]) (by simp +decide [σ5, hp0])
    (by simp +decide [σ5]) (by simp +decide [σ5, ts_val _ _ _ _ _ rF (by decide), hF])
    (by simp +decide [σ5, ts_val _ _ _ _ _ rC (by decide), hC]) (by simp only [σ5, WState.seth_val, ts_val_OP]; omega)
  have e6 : (appendO σ5 sOut rOP (marks (natWord e.2.2))).seth sW
      ((entsW (es.take (v E)) ++ [e.1, true, false, e.2.1]).length + stp false * (natWord e.2.2).length) =
      (ts src h (o ++ marks (natWord e.2.2)) v c).seth sW
        ((entsW (es.take (v E)) ++ [e.1, true, false, e.2.1]).length + stp false * (natWord e.2.2).length) := by
    have : appendO σ5 sOut rOP (marks (natWord e.2.2)) =
        (appendO (ts src h o v c) sOut rOP (marks (natWord e.2.2))).seth sW (p0 + 1 + 1 + 1 + 1) := by
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = sOut
      · subst hi; simp +decide [σ5]
      · by_cases his : i = sW
        · subst his; simp +decide [σ5]
        · simp +decide [σ5, Function.update_of_ne hi, Function.update_of_ne his]
    rw [this, appendO_ts, wseth_seth]
  rw [e6] at s6
  have hpos : (entsW (es.take (v E)) ++ [e.1, true, false, e.2.1]).length + stp false * (natWord e.2.2).length ≤
      v rBIG := by
    have := congrArg List.length hsplit
    simp only [List.length_append, entW, List.length_cons, List.length_nil] at this
    rw [← he] at this
    simp only [List.length_append, List.length_cons, List.length_nil, stp, Bool.false_eq_true, if_false, one_mul]; omega
  have s7 := rewT cap src h (o ++ marks (natWord e.2.2)) v c sW (by decide) (by decide) _ hT hpos hcapB
  have hcm := le_codeMax es (v E) hk
  exact WExec.mono (WExec.seq s1 (WExec.seq f1 (WExec.seq f2 (WExec.seq f3 (WExec.seq f4 (WExec.seq s6 s7))))))
    (by omega)


end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
