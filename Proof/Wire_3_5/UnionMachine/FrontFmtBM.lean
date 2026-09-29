import Proof.Wire_3_5.UnionMachine.FrontFmtHd
import Proof.Wire_3_5.UnionMachine.FrontFoldBuild

/-! # C6 front, U5, the source formats (d): the supports' bitmaps for the parity writers

"The encoding parity of a variable, constructed from the PCPP output" (P3:3672): the PCPP output word holds the
header `natListWord [sys, aux, cb]`, then the systematic supports' bitmaps (`sys` rows of `q` bits), then the
clauses. The fold's parity writers read one framed bitmap per variable (`FrontFoldLoop.FoldIn.ys`: the systematic
supports, then the empty support of every auxiliary variable). **`bmW`** writes them: it counts `q`, `sys`, `aux`
into registers, skips the header's four fields, copies `sys` rows (`FrontFold.rowP`, flag on) and writes `aux` zero
rows (flag off) (**`bmW_spec`**, **`bmStage`**).

Paper quantity of the main type: the supports of the PCPP variables (the parity atoms' supports). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtBM
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (wm_step wenc_H_zero)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_append appendO_setv)
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Gen
variable {ns nr : ℕ} (cap : ℕ)

/-- Count a unary stream `S` into register `r`. -/
def ld (S : Fin (ns + 1)) (r : Fin nr) : WM ns nr := .whs S (.seq (.inc r) (.fwd S))

theorem ld_spec (S : Fin (ns + 1)) (r : Fin nr) (m : ℕ) (hm : m ≤ cap) (n : ℕ) : ∀ (σ : WState ns nr), n ≤ m →
    σ.st S = List.replicate m true → σ.sh S = m - n → σ.val r = m - n →
    WExec cap (ld S r) σ ((σ.seth S m).setv r m) (7 * n + 1) := by
  induction n with
  | zero =>
    intro σ _ h0 hh hv
    have hz : wbit σ S = false := by
      simp only [wbit, h0, hh, Nat.sub_zero]; exact FrontFmtHd.rd_rep_end m
    have e : (σ.seth S m).setv r m = σ := by
      apply WState.eq
      · funext j; by_cases hj : j = S
        · subst hj; simp [hh]
        · simp [hj]
      · simp
      · funext j; by_cases hj : j = r
        · subst hj; simp [hv]
        · simp [hj]
      · simp
    rw [e]; exact WExec.mono (WExec.whsF hz) (by omega)
  | succ n ih =>
    intro σ hn h0 hh hv
    have hw : wbit σ S = true := by
      simp only [wbit, h0, hh]; exact FrontFmtHd.rd_rep m _ (by omega)
    have hlt : σ.val r < cap := by rw [hv]; omega
    have s1 := WExec.inc (cap := cap) r σ hlt
    have s2 := WExec.fwd (cap := cap) S (σ.setv r (σ.val r + 1))
    have ih' := ih ((σ.setv r (σ.val r + 1)).seth S ((σ.setv r (σ.val r + 1)).sh S + 1)) (by omega)
      (by simp [h0]) (by simp [hh]; omega) (by simp [hv]; omega)
    have e : ((((σ.setv r (σ.val r + 1)).seth S ((σ.setv r (σ.val r + 1)).sh S + 1)).seth S m).setv r m) =
        (σ.seth S m).setv r m := by
      apply WState.eq
      · funext j; by_cases hj : j = S
        · subst hj; simp
        · simp [hj]
      · simp
      · funext j; by_cases hj : j = r
        · subst hj; simp
        · simp [hj]
      · simp
    rw [e] at ih'
    exact WExec.mono (WExec.whsT hw (WExec.seq s1 s2) ih') (by omega)

theorem appendO_seth (σ : WState ns nr) (i o : Fin (ns + 1)) (hio : i ≠ o) (OP : Fin nr) (x : ℕ) (u : List Bool) :
    appendO (σ.seth i x) o OP u = (appendO σ o OP u).seth i x := by
  apply WState.eq
  · funext j; by_cases hj : j = i
    · subst hj; simp [Function.update_apply, hio]
    · by_cases hjo : j = o
      · subst hjo; simp [Function.update_apply, hj]
      · simp [Function.update_apply, hj, hjo]
  · simp
  · simp
  · simp

end Gen

/-! ## The rows -/

/-- Row `i` of the supports' bits. -/
def chunk (q : ℕ) (sb : List Bool) (i : ℕ) : List Bool := (sb.drop (i * q)).take q

theorem chunk_split (q : ℕ) (sb : List Bool) (i : ℕ) :
    sb.drop (i * q) = chunk q sb i ++ sb.drop ((i + 1) * q) := by
  unfold chunk
  rw [show (i + 1) * q = i * q + q by ring, ← List.drop_drop, List.take_append_drop]

theorem chunk_len (q : ℕ) (sb : List Bool) (sys i : ℕ) (hsb : sb.length = sys * q) (hi : i < sys) :
    (chunk q sb i).length = q := by
  unfold chunk; rw [List.length_take, List.length_drop, hsb]
  have : i * q + q ≤ sys * q := by nlinarith
  rw [min_eq_left (by omega)]

/-- The rows of the first `j` systematic variables. -/
def rows (q : ℕ) (sb : List Bool) (j : ℕ) : List (List Bool) := (List.range j).map (chunk q sb)

theorem rows_succ (q : ℕ) (sb : List Bool) (j : ℕ) : rows q sb (j + 1) = rows q sb j ++ [chunk q sb j] := by
  unfold rows; rw [List.range_succ, List.map_append]; rfl

/-! ## The program -/

/-- **The bitmaps' program** (streams `0` the PCPP output, `1` `1^q`, `2` `1^sys`, `3` `1^aux`, `4` the output;
registers `0` `q`, `1` `sys`, `2` `aux`, `3`, `4` the loops' counters, `5` the flag, `6` the row counter, `7` the output
count, `8`, `9` the field skipper's). -/
def bmW : WM 4 10 :=
  .seq (ld 1 0) (.seq (ld 2 1) (.seq (ld 3 2)
  (.seq (PrimAsm.ParseNat.skipNatM false 0 8 9) (.seq (PrimAsm.ParseNat.skipNatM false 0 8 9)
  (.seq (PrimAsm.ParseNat.skipNatM false 0 8 9) (.seq (PrimAsm.ParseNat.skipNatM false 0 8 9)
  (.seq (.inc 5) (.seq (FrontTWKit.cloop 1 3 (FrontFold.rowP 0 4 5 0 6 7))
    (.seq (.dec 5) (FrontTWKit.cloop 2 4 (FrontFold.rowP 0 4 5 0 6 7)))))))))))

/-- The rows' family during the systematic loop. -/
def Gs (σ : WState 4 10) (hl q : ℕ) (sb : List Bool) (j : ℕ) : WState 4 10 :=
  (appendO σ 4 7 ((rows q sb j).flatMap frame)).seth 0 (hl + j * q)

/-- The rows' family during the auxiliary loop. -/
def Ga (σ : WState 4 10) (q : ℕ) (j : ℕ) : WState 4 10 :=
  appendO σ 4 7 ((List.replicate j (List.replicate q false)).flatMap frame)

theorem flat_frame_le (L : ℕ) : ∀ ws : List (List Bool), (∀ w ∈ ws, w.length ≤ L) →
    (ws.flatMap frame).length ≤ ws.length * (2 * L + 1)
  | [], _ => by simp
  | w :: ws, h => by
    rw [List.flatMap_cons, List.length_append, FrontTWKit.frame_length, List.length_cons]
    have h1 := h w (by simp)
    have h2 := flat_frame_le L ws (fun z hz => h z (by simp [hz]))
    rw [Nat.add_mul, one_mul]; omega

theorem rowCost_eq (q : ℕ) : q * (19 + 8) + 1 + 1 + (7 * q + 1) + 1 + 7 = 34 * q + 11 := by ring

section Rows
variable (cap : ℕ)

theorem take_len (sb : List Bool) (q sys j : ℕ) (hsb : sb.length = sys * q) (hj : j < sys) :
    (sb.take (j * q)).length = j * q := by
  rw [List.length_take, hsb]; exact min_eq_left (by nlinarith)

/-- **One systematic row.** -/
theorem sysRow (q sys : ℕ) (hdr sb rest : List Bool) (hsb : sb.length = sys * q) (σ : WState 4 10)
    (h0 : σ.st 0 = hdr ++ sb ++ rest) (h4 : σ.sh 4 = (σ.st 4).length) (hF : σ.val 5 = 1) (hK : σ.val 0 = q)
    (hT : σ.val 6 = 0) (hOP : σ.val 7 = 0) (j : ℕ) (hj : j < sys)
    (hcap : sys * (2 * q + 1) + 2 * q + 1 ≤ cap) (hq : q ≤ cap) :
    WExec cap (FrontFold.rowP 0 4 5 0 6 7) (((Gs σ hdr.length q sb j).setv 1 (sys - j - 1)).setv 3 (j + 1))
      (((Gs σ hdr.length q sb (j + 1)).setv 1 (sys - j - 1)).setv 3 (j + 1)) (34 * q + 11) := by
  have hc := chunk_len q sb sys j hsb hj
  have ht := take_len sb q sys j hsb hj
  have hsplit : sb = sb.take (j * q) ++ (chunk q sb j ++ sb.drop ((j + 1) * q)) := by
    rw [← chunk_split, List.take_append_drop]
  have hrows : ((rows q sb j).flatMap frame).length ≤ j * (2 * q + 1) := by
    have := flat_frame_le q (rows q sb j) (by
      intro w hw; unfold rows at hw; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      rw [chunk_len q sb sys i hsb (by have := List.mem_range.mp hi; omega)])
    simpa [rows] using this
  have hjq : j * (2 * q + 1) + 2 * q + 1 ≤ cap := by
    have : j * (2 * q + 1) ≤ sys * (2 * q + 1) := Nat.mul_le_mul_right _ hj.le
    omega
  have hop : (((Gs σ hdr.length q sb j).setv 1 (sys - j - 1)).setv 3 (j + 1)).val 7 =
      ((rows q sb j).flatMap frame).length := by simp [Gs, hOP]
  have e := FrontFold.rowP_spec cap 0 4 (by decide) 5 0 6 7 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) true (hdr ++ sb.take (j * q)) (chunk q sb j) (sb.drop ((j + 1) * q) ++ rest) q
    (fun _ => hc) (((Gs σ hdr.length q sb j).setv 1 (sys - j - 1)).setv 3 (j + 1))
    (fun _ => by
      simp only [Gs, WState.setv_st, WState.seth_st, appendO_st]
      rw [Function.update_of_ne (by decide), h0]
      conv_lhs => rw [hsplit]
      simp)
    (fun _ => by simp [Gs, ht])
    (by simp [Gs, h4])
    (by simp [Gs, hF])
    (by simp [Gs, hK])
    (by simp [Gs, hT])
    (by rw [hop]; omega) hq
  refine WExec.cast cap e ?_ (by rw [rowCost_eq])
  simp only [FrontFold.rowOf, if_true]
  apply WState.eq
  · funext x; by_cases hx : x = 0
    · subst hx; simp [Gs]; ring
    · by_cases hx4 : x = 4
      · subst hx4; simp [Gs, rows_succ, List.flatMap_append, FrontFmtHd.frame_marks, FrontFmtHd.marks_len]; ring
      · simp [Gs, hx, hx4]
  · funext x; by_cases hx4 : x = 4
    · subst hx4; simp [Gs, rows_succ, List.flatMap_append, FrontFmtHd.frame_marks]
    · simp [Gs, hx4]
  · funext x; by_cases hx : x = 7
    · subst hx; simp [Gs, rows_succ, List.flatMap_append, FrontFmtHd.frame_marks, FrontFmtHd.marks_len]; ring
    · simp [Gs, Function.update_apply, hx]
  · simp [Gs]

/-- **One auxiliary (empty-support) row.** -/
theorem auxRow (q aux : ℕ) (σ : WState 4 10) (h4 : σ.sh 4 = (σ.st 4).length) (hF : σ.val 5 = 0) (hK : σ.val 0 = q)
    (hT : σ.val 6 = 0) (j : ℕ) (hj : j < aux) (hcap : σ.val 7 + aux * (2 * q + 1) + 2 * q + 1 ≤ cap) (hq : q ≤ cap) :
    WExec cap (FrontFold.rowP 0 4 5 0 6 7) (((Ga σ q j).setv 2 (aux - j - 1)).setv 4 (j + 1))
      (((Ga σ q (j + 1)).setv 2 (aux - j - 1)).setv 4 (j + 1)) (34 * q + 11) := by
  have hrows : ((List.replicate j (List.replicate q false)).flatMap frame).length ≤ j * (2 * q + 1) := by
    have := flat_frame_le q (List.replicate j (List.replicate q false)) (by
      intro w hw; rw [(List.mem_replicate.mp hw).2]; simp)
    simpa using this
  have hop : (((Ga σ q j).setv 2 (aux - j - 1)).setv 4 (j + 1)).val 7 =
      σ.val 7 + ((List.replicate j (List.replicate q false)).flatMap frame).length := by simp [Ga]
  have hja : j * (2 * q + 1) ≤ aux * (2 * q + 1) := Nat.mul_le_mul_right _ hj.le
  have e := FrontFold.rowP_spec cap 0 4 (by decide) 5 0 6 7 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) false [] [] [] q (fun h => absurd h (by decide))
    (((Ga σ q j).setv 2 (aux - j - 1)).setv 4 (j + 1)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (by simp [Ga, h4]) (by simp [Ga, hF]) (by simp [Ga, hK]) (by simp [Ga, hT])
    (by rw [hop]; omega) hq
  refine WExec.cast cap e ?_ (by rw [rowCost_eq])
  simp only [FrontFold.rowOf, Bool.false_eq_true, if_false, Nat.add_zero]
  apply WState.eq
  · funext x; by_cases hx : x = 0
    · subst hx; simp [Ga]
    · by_cases hx4 : x = 4
      · subst hx4; simp [Ga, List.replicate_succ', List.flatMap_append, FrontFmtHd.frame_marks,
          FrontFmtHd.marks_len]; ring
      · simp [Ga, hx, hx4]
  · funext x; by_cases hx4 : x = 4
    · subst hx4; simp [Ga, List.replicate_succ', List.flatMap_append, FrontFmtHd.frame_marks]
    · simp [Ga, hx4]
  · funext x; by_cases hx : x = 7
    · subst hx; simp [Ga, List.replicate_succ', List.flatMap_append, FrontFmtHd.frame_marks, FrontFmtHd.marks_len]
      ring
    · simp [Ga, Function.update_apply, hx]
  · simp [Ga]

end Rows

/-! ## The whole program -/

/-- The PCPP output word's header `natListWord [sys, aux, cb]`. -/
def hdrOf (sys aux cb : ℕ) : List Bool := natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb

/-- The bitmaps' fuel. -/
def bmCost (q sys aux cb : ℕ) : ℕ :=
  (7 * q + 1) + 1 + ((7 * sys + 1) + 1 + ((7 * aux + 1) + 1 + ((20 * natBitLength 3 + 20) + 1 +
    ((20 * natBitLength sys + 20) + 1 + ((20 * natBitLength aux + 20) + 1 + ((20 * natBitLength cb + 20) + 1 +
    (3 + 1 + ((sys * (34 * q + 11 + 8) + 1 + 1 + (7 * sys + 1)) + 1 + (1 + 1 +
    (aux * (34 * q + 11 + 8) + 1 + 1 + (7 * aux + 1)))))))))))

theorem skip_norm {ns nr : ℕ} (σ : WState ns nr) (a b : ℕ) :
    (σ.seth 0 a).seth 0 (a + PrimAsm.ParseNat.stp false * b) = σ.seth 0 (a + b) := by
  rw [wseth_seth]; simp [PrimAsm.ParseNat.stp]

section Spec
variable (cap : ℕ)

/-- **The bitmaps' program**: the systematic supports' rows (copied from the PCPP output), then `aux` empty rows,
each framed. -/
theorem bmW_spec (q sys aux cb : ℕ) (sb rest : List Bool) (hsb : sb.length = sys * q)
    (hc1 : (sys + aux + 1) * (2 * q + 1) + q + sys + aux + 1 ≤ cap)
    (hc2 : natBitLength 3 + natBitLength sys + natBitLength aux + natBitLength cb + 1 ≤ cap)
    (σ : WState 4 10) (h0 : σ.st 0 = hdrOf sys aux cb ++ sb ++ rest) (h1 : σ.st 1 = List.replicate q true)
    (h2 : σ.st 2 = List.replicate sys true) (h3 : σ.st 3 = List.replicate aux true) (h4 : σ.st 4 = [])
    (hsh : ∀ j, σ.sh j = 0) (hv : ∀ r, σ.val r = 0) :
    ∃ τ, WExec cap bmW σ τ (bmCost q sys aux cb) ∧
      τ.st 4 = (rows q sb sys ++ List.replicate aux (List.replicate q false)).flatMap frame ∧
      τ.st 0 = σ.st 0 ∧ τ.st 1 = σ.st 1 ∧ τ.st 2 = σ.st 2 ∧ τ.st 3 = σ.st 3 ∧ τ.cell = σ.cell := by
  have hq : q ≤ cap := by nlinarith
  -- 1-3: the counts
  have s1 := ld_spec cap (1 : Fin 5) (0 : Fin 10) q hq q σ le_rfl h1 (by rw [hsh]; omega) (by rw [hv]; omega)
  set σ1 := (σ.seth 1 q).setv 0 q with hσ1
  have s2 := ld_spec cap (2 : Fin 5) (1 : Fin 10) sys (by nlinarith) sys σ1 le_rfl (by simp [σ1, h2])
    (by simp [σ1, hsh]) (by simp [σ1, hv])
  set σ2 := (σ1.seth 2 sys).setv 1 sys with hσ2
  have s3 := ld_spec cap (3 : Fin 5) (2 : Fin 10) aux (by nlinarith) aux σ2 le_rfl (by simp [σ2, σ1, h3])
    (by simp [σ2, σ1, hsh]) (by simp [σ2, σ1, hv])
  set σ3 := (σ2.seth 3 aux).setv 2 aux with hσ3
  have g3 : σ3.st 0 = hdrOf sys aux cb ++ sb ++ rest := by simp [σ3, σ2, σ1, h0]
  have g3h : σ3.sh 0 = 0 := by simp [σ3, σ2, σ1, hsh]
  have g3v : ∀ r : Fin 10, r ≠ 0 → r ≠ 1 → r ≠ 2 → σ3.val r = 0 := fun r a b c => by
    simp [σ3, σ2, σ1, Function.update_apply, a, b, c, hv]
  -- 4: the header's four fields
  have k1 := PrimAsm.ParseNat.skipNatM_spec cap false (0 : Fin 5) (8 : Fin 10) (9 : Fin 10) (by decide) 3 []
    (natWord sys ++ natWord aux ++ natWord cb ++ sb ++ rest) σ3
    (by rw [g3]; simp [hdrOf, PrimAsm.ParseNat.enc]) (by rw [g3h]; rfl) (g3v 8 (by decide) (by decide) (by decide))
    (g3v 9 (by decide) (by decide) (by decide)) (by omega)
  simp only [List.length_nil, Nat.zero_add] at k1
  have k1' : σ3.seth 0 (PrimAsm.ParseNat.stp false * (natWord 3).length) = σ3.seth 0 (natWord 3).length := by
    simp [PrimAsm.ParseNat.stp]
  rw [k1'] at k1
  have k2 := PrimAsm.ParseNat.skipNatM_spec cap false (0 : Fin 5) (8 : Fin 10) (9 : Fin 10) (by decide) sys
    (natWord 3) (natWord aux ++ natWord cb ++ sb ++ rest) (σ3.seth 0 (natWord 3).length)
    (by simp [g3, hdrOf, PrimAsm.ParseNat.enc]) (by simp)
    (by simp [g3v 8 (by decide) (by decide) (by decide)]) (by simp [g3v 9 (by decide) (by decide) (by decide)])
    (by omega)
  rw [skip_norm] at k2
  have k3 := PrimAsm.ParseNat.skipNatM_spec cap false (0 : Fin 5) (8 : Fin 10) (9 : Fin 10) (by decide) aux
    (natWord 3 ++ natWord sys) (natWord cb ++ sb ++ rest) (σ3.seth 0 ((natWord 3).length + (natWord sys).length))
    (by simp [g3, hdrOf, PrimAsm.ParseNat.enc]) (by simp)
    (by simp [g3v 8 (by decide) (by decide) (by decide)]) (by simp [g3v 9 (by decide) (by decide) (by decide)])
    (by omega)
  rw [show (natWord 3 ++ natWord sys).length = (natWord 3).length + (natWord sys).length by simp, skip_norm] at k3
  have k4 := PrimAsm.ParseNat.skipNatM_spec cap false (0 : Fin 5) (8 : Fin 10) (9 : Fin 10) (by decide) cb
    (natWord 3 ++ natWord sys ++ natWord aux) (sb ++ rest)
    (σ3.seth 0 ((natWord 3).length + (natWord sys).length + (natWord aux).length))
    (by simp [g3, hdrOf, PrimAsm.ParseNat.enc]) (by simp; ring)
    (by simp [g3v 8 (by decide) (by decide) (by decide)]) (by simp [g3v 9 (by decide) (by decide) (by decide)])
    (by omega)
  rw [show (natWord 3 ++ natWord sys ++ natWord aux).length =
    (natWord 3).length + (natWord sys).length + (natWord aux).length by simp; ring, skip_norm] at k4
  set σ7 := σ3.seth 0 ((natWord 3).length + (natWord sys).length + (natWord aux).length + (natWord cb).length)
    with hσ7
  have hL : (hdrOf sys aux cb).length =
      (natWord 3).length + (natWord sys).length + (natWord aux).length + (natWord cb).length := by
    simp [hdrOf]; ring
  -- 5: the flag on
  have s8 := WExec.inc (cap := cap) (5 : Fin 10) σ7 (by simp [σ7, g3v 5 (by decide) (by decide) (by decide)]; omega)
  set σ8 := σ7.setv 5 (σ7.val 5 + 1) with hσ8
  have f8 : σ8.val 5 = 1 := by simp [σ8, σ7, g3v 5 (by decide) (by decide) (by decide)]
  -- 6: the systematic rows
  have hsys := FrontTWKit.cloop_spec cap (1 : Fin 10) (3 : Fin 10) (by decide) (FrontFold.rowP 0 4 5 0 6 7) sys
    (34 * q + 11) (Gs σ8 (hdrOf sys aux cb).length q sb) (by nlinarith) (fun j hj => sysRow cap q sys
      (hdrOf sys aux cb) sb rest hsb σ8 (by simp [σ8, σ7, g3]) (by simp [σ8, σ7, σ3, σ2, σ1, hsh, h4]) f8
      (by simp [σ8, σ7, σ3, σ2, σ1]) (by simp [σ8, σ7, g3v 6 (by decide) (by decide) (by decide)])
      (by simp [σ8, σ7, g3v 7 (by decide) (by decide) (by decide)]) j hj (by nlinarith) hq)
  have e0 : ((Gs σ8 (hdrOf sys aux cb).length q sb 0).setv 1 sys).setv 3 0 = σ8 := by
    apply WState.eq
    · funext x; by_cases hx : x = 0
      · subst hx; simp [Gs, rows, σ8, σ7, hL]
      · simp [Gs, rows, hx]
    · simp [Gs, rows]
    · funext x; by_cases hx1 : x = 1
      · subst hx1; simp [Gs, rows, σ8, σ7, σ3, σ2]
      · by_cases hx3 : x = 3
        · subst hx3; simp [Gs, rows, σ8, σ7, g3v 3 (by decide) (by decide) (by decide)]
        · simp [Gs, rows, Function.update_apply, hx1, hx3]; intro h; subst h; rfl
    · simp [Gs]
  rw [e0] at hsys
  set σ9 := ((Gs σ8 (hdrOf sys aux cb).length q sb sys).setv 1 sys).setv 3 0 with hσ9
  -- 7: the flag off
  have s10 := WExec.dec (cap := cap) (5 : Fin 10) σ9 (by simp [σ9, Gs, f8]; omega)
  set σ10 := σ9.setv 5 (σ9.val 5 - 1) with hσ10
  -- 8: the auxiliary rows
  have hrows : ((rows q sb sys).flatMap frame).length ≤ sys * (2 * q + 1) := by
    have := flat_frame_le q (rows q sb sys) (by
      intro w hw; unfold rows at hw; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      rw [chunk_len q sb sys i hsb (List.mem_range.mp hi)])
    simpa [rows] using this
  have v10 : σ10.val 7 = ((rows q sb sys).flatMap frame).length := by
    simp [σ10, σ9, Gs, σ8, σ7, g3v 7 (by decide) (by decide) (by decide)]
  have haux := FrontTWKit.cloop_spec cap (2 : Fin 10) (4 : Fin 10) (by decide) (FrontFold.rowP 0 4 5 0 6 7) aux
    (34 * q + 11) (Ga σ10 q) (by nlinarith) (fun j hj => auxRow cap q aux σ10
      (by simp [σ10, σ9, Gs, σ8, σ7, σ3, σ2, σ1, hsh, h4]) (by simp [σ10, σ9, Gs, f8])
      (by simp [σ10, σ9, Gs, σ8, σ7, σ3, σ2, σ1])
      (by simp [σ10, σ9, Gs, σ8, σ7, g3v 6 (by decide) (by decide) (by decide)]) j hj
      (by rw [v10]; nlinarith) hq)
  have e1 : ((Ga σ10 q 0).setv 2 aux).setv 4 0 = σ10 := by
    apply WState.eq
    · simp [Ga]
    · simp [Ga]
    · funext x; by_cases hx2 : x = 2
      · subst hx2; simp [Ga, σ10, σ9, Gs, σ8, σ7, σ3]
      · by_cases hx4 : x = 4
        · subst hx4; simp [Ga, σ10, σ9, Gs, σ8, σ7, g3v 4 (by decide) (by decide) (by decide)]
        · simp [Ga, Function.update_apply, hx2, hx4]; intro h; subst h; rfl
    · simp [Ga]
  rw [e1] at haux
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq k1 (WExec.seq k2 (WExec.seq k3
    (WExec.seq k4 (WExec.seq s8 (WExec.seq hsys (WExec.seq s10 haux)))))))))) (by unfold bmCost; exact le_refl _),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Ga, σ10, σ9, Gs, σ8, σ7, σ3, σ2, σ1, h4, List.flatMap_append]
  · simp [Ga, σ10, σ9, Gs, σ8, σ7, σ3, σ2, σ1]
  · simp [Ga, σ10, σ9, Gs, σ8, σ7, σ3, σ2, σ1, h1]
  · simp [Ga, σ10, σ9, Gs, σ8, σ7, σ3, σ2, σ1, h2]
  · simp [Ga, σ10, σ9, Gs, σ8, σ7, σ3, σ2, σ1, h3]
  · simp [Ga, σ10, σ9, Gs, σ8, σ7, σ3, σ2, σ1]

end Spec

/-! ## As a Step -/

def σB (PO Q SY AX : List Bool) : WState 4 10 := ⟨fun _ => 0, ![PO, Q, SY, AX, []], fun _ => 0, false⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtBM
