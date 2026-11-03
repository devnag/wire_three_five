import W3.Recovery3.Case2Block
import Proof.Wire_3_5.Recovery.CaseTwoFold

/-!
# One round of the uniform Case-2 XOR fold over a Case-2 source block

Paper v2, §H.5 Case 2 ("Lemma H.1 makes `f^{⊕t(q)}` correlation hard") and §H.6 ("Each honest proof bit is then
computed by the deterministic PCPP algorithm"): the number of copies `t(q) + 1` grows with `q`, so one fixed machine
evaluates every copy on ONE reused bank, with the block index as data (a unary offset `1^{i·w}` on a port).

One round, on a bank holding the source block's two words (`w0`, `frame d`), the accumulator, the framed address
`frame x`, the offset `1^{i·w}` and the block width `1^w`:
* crop block `i` of the address, `frame (x[i·w, (i+1)·w))`, onto the block's address tape (base `SliceFrame`);
* run the source block's whole block at block `0` with its heads reset and XOR its honest bit into the accumulator
  (`S.programs D 0`, base `XorBody`).
The block is any `SBlock` (the near-cubic-wires Case-2 source block interface, `W3 Recovery3/Case2Block`); its request
is `S.req i`. This is the earlier padded-source fold round of this proof with the padded block replaced by `S` (the
padded block also needed `1^q` on a tape; `S` does not).

Paper quantity of the main type (`round_run`): the unsigned honest proof bit of `S.req i` at block `i`,
`paddedUnsigned (a.output (S.req i)) hcb (field x (i·w) w)`, XORed into the accumulator.
-/

set_option autoImplicit false

namespace Stage35.Fold

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open W3.NearCubicWires.RepairSource.Outer3.Case2
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold (block_word split_at)
open NearCubicWires.WireExponent3_5.Transfer (ready_pad)

noncomputable section
variable {a : PointwisePCPPAlgorithm} (S : SBlock a) (D : ℕ)

theorem wtapes_ge : 3 ≤ S.wtapes D := by
  have := S.three; unfold SBlock.wtapes; omega

/-- The accumulator block's tape count (`S.xtapes D = wtapes + 2`). -/
abbrev xt : ℕ := S.xtapes D
/-- The round's tape count: the accumulator block, then nine tapes (four ports, five scratch). -/
abbrev tw : ℕ := xt S D + 9

/-- The accumulator block's tapes, first in the round. -/
def xe (i : Fin (xt S D)) : Fin (tw S D) := i.castAdd 9
/-- The nine extra tapes: `0` address, `1` offset, `2` block width, `3` width `1^q` (kept for the bank's owner),
`4`–`8` scratch. -/
def ee (j : Fin 9) : Fin (tw S D) := j.natAdd (xt S D)

theorem xe_injective : Function.Injective (xe S D) := by
  intro i j h; exact Fin.ext (by simpa [xe] using congrArg Fin.val h)

theorem xe_val (i : Fin (xt S D)) : (xe S D i).val = i.val := rfl
theorem ee_val (j : Fin 9) : (ee S D j).val = xt S D + j.val := rfl

/-- The block's address tape (the source block's tape `2`). -/
def xa : Fin (xt S D) := ⟨2, by have := wtapes_ge S D; show 2 < S.wtapes D + 1 + 1; omega⟩
/-- The accumulator. -/
def xacc : Fin (xt S D) := S.accumulator D

/-- The crop's slots: address port, raw field (scratch), offset port, width port, two scratch, the block's address
tape, one scratch. -/
def sliceSlots : Fin 8 → Fin (tw S D) :=
  ![ee S D 0, ee S D 4, ee S D 1, ee S D 2, ee S D 5, ee S D 6, xe S D (xa S D), ee S D 7]

theorem sliceSlots_val (i : Fin 8) : (sliceSlots S D i).val =
    if i.val = 6 then 2 else xt S D + (![0, 4, 1, 2, 5, 6, 0, 7] : Fin 8 → ℕ) i := by
  fin_cases i <;> rfl

theorem sliceSlots_injective : Function.Injective (sliceSlots S D) := by
  have hw := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  intro i j h
  have hv := congrArg Fin.val h
  rw [sliceSlots_val, sliceSlots_val] at hv
  apply Fin.ext
  revert hv
  fin_cases i <;> fin_cases j <;> simp <;> omega

/-- **The round's worker**: crop the block, then the accumulator block (`S.programs D 0`). -/
def worker :=
  Composition.machine (RecoveryFocus.machine (sliceSlots S D) SliceFrame.machine)
    (RecoveryFocus.machine (xe S D) (S.programs D 0))

/-- The round's tapes by position value. -/
def bankN (w0 desc : List Bool) (parity : Bool) (addr off width qw : List Bool) (v : ℕ) : List Bool :=
  if v = 0 then w0 else if v = 1 then desc
  else if v = S.wtapes D + 1 then [parity]
  else if v = xt S D then addr else if v = xt S D + 1 then off
  else if v = xt S D + 2 then width else if v = xt S D + 3 then qw else []

/-- **The round's tapes**, by position: the block's word `w0`, its framed descriptor, the accumulator `[parity]`, the
address frame, the offset, the block width, `1^q`; all other tapes empty. -/
def bank (w0 desc : List Bool) (parity : Bool) (addr off width qw : List Bool) : Fin (tw S D) → List Bool :=
  fun t => bankN S D w0 desc parity addr off width qw t.val

section BankValues
variable (w0 desc : List Bool) (parity : Bool) (addr off width qw : List Bool)

theorem bankN_w0 : bankN S D w0 desc parity addr off width qw 0 = w0 := by simp [bankN]
theorem bankN_desc : bankN S D w0 desc parity addr off width qw 1 = desc := by simp [bankN]
theorem bankN_acc : bankN S D w0 desc parity addr off width qw (S.wtapes D + 1) = [parity] := by
  have := wtapes_ge S D
  unfold bankN; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem bankN_addr : bankN S D w0 desc parity addr off width qw (xt S D) = addr := by
  have := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  unfold bankN; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem bankN_off : bankN S D w0 desc parity addr off width qw (xt S D + 1) = off := by
  have := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  unfold bankN; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem bankN_width : bankN S D w0 desc parity addr off width qw (xt S D + 2) = width := by
  have := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  unfold bankN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem bankN_q : bankN S D w0 desc parity addr off width qw (xt S D + 3) = qw := by
  have := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  unfold bankN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]
theorem bankN_other (v : ℕ) (h0 : v ≠ 0) (h1 : v ≠ 1) (h2 : v ≠ S.wtapes D + 1)
    (h3 : v ≠ xt S D) (h4 : v ≠ xt S D + 1) (h5 : v ≠ xt S D + 2) (h6 : v ≠ xt S D + 3) :
    bankN S D w0 desc parity addr off width qw v = [] := by
  unfold bankN
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]

end BankValues

theorem slice_xe (i : Fin 8) (j : Fin (xt S D)) (hj : j.val ≠ 2) : sliceSlots S D i ≠ xe S D j := by
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  have hjl := j.isLt
  intro h
  have hv := congrArg Fin.val h
  rw [sliceSlots_val, xe_val] at hv
  revert hv
  fin_cases i <;> simp <;> omega

theorem xe_ee (i : Fin (xt S D)) (j : Fin 9) : xe S D i ≠ ee S D j := by
  intro h
  have hv := congrArg Fin.val h
  rw [xe_val, ee_val] at hv
  have := i.isLt
  omega

/-- The accumulator block's input, by position. -/
theorem xinput_val (i : S.ι) (addr : List Bool) (parity : Bool) (j : Fin (xt S D)) :
    XorBody.input (S.wresetInput D i addr) parity j =
      if j.val = 0 then S.w0 i else if j.val = 1 then RepairOrdinary.frame (S.d i)
      else if j.val = 2 then RepairOrdinary.frame addr
      else if j.val = S.wtapes D + 1 then [parity] else [] := by
  have hw := wtapes_ge S D
  rw [S.body_input]
  unfold FixedFold.bodyInput
  have hacc : (S.accumulator D).val = S.wtapes D + 1 := rfl
  rw [hacc]
  by_cases h0 : j.val = 0
  · rw [dif_pos (by omega), if_pos h0]; simp only [SBlock.words, h0]; rfl
  by_cases h1 : j.val = 1
  · rw [dif_pos (by omega), if_neg h0, if_pos h1]; simp only [SBlock.words, h1]; rfl
  by_cases h2 : j.val = 2
  · rw [dif_pos (by omega), if_neg h0, if_neg h1, if_pos h2]; simp only [SBlock.words, h2]; rfl
  rw [dif_neg (by omega), if_neg h0, if_neg h1, if_neg h2]

/-! ## One round -/

section Round
variable (i : S.ι)

/-- The request's clause cap `⌈D log₂(arity+2)⌉`. -/
abbrev capOf : ℕ := CloseoutLanguage.clauseWidth D (S.req i).arity
/-- The block width `arity + cap + 1`. -/
abbrev widthOf : ℕ := (S.req i).arity + capOf S D i + 1

/-- **The cost of round `blk`**: the crop at offset `blk·w`, and the accumulator block on that block. -/
def roundCost {N : ℕ} (point : BitInput N) (blk : ℕ) : ℕ :=
  SliceFrame.budget (blk * widthOf S D i) (widthOf S D i) + 1 +
    (2 * S.wbudget i D 0
      (AddressWindow.field point (blk * widthOf S D i) (S.req i).arity)
      (AddressWindow.field point (blk * widthOf S D i + (S.req i).arity) (a.output (S.req i)).clauseBits)
      (AddressWindow.read point (blk * widthOf S D i + (S.req i).arity + capOf S D i))
      (capOf S D i - (a.output (S.req i)).clauseBits) + 2 + 2)

/-- The round's input tapes at block `blk` with accumulator `parity` and bank capacity `total`. -/
def roundIn {N : ℕ} (point : BitInput N) (blk total : ℕ) (parity : Bool) : Fin (tw S D) → List Bool :=
  bank S D (S.w0 i) (RepairOrdinary.frame (S.d i)) parity (RepairOrdinary.frame (List.ofFn point))
    (ZeroPadding.pad total (List.replicate (blk * widthOf S D i) true))
    (ZeroPadding.pad total (List.replicate (widthOf S D i) true)) (List.replicate (S.req i).arity true)

section RoundIn
variable {N : ℕ} (point : BitInput N) (blk total : ℕ) (parity : Bool)

theorem roundIn_val (t : Fin (tw S D)) : roundIn S D i point blk total parity t =
    bankN S D (S.w0 i) (RepairOrdinary.frame (S.d i)) parity (RepairOrdinary.frame (List.ofFn point))
      (ZeroPadding.pad total (List.replicate (blk * widthOf S D i) true))
      (ZeroPadding.pad total (List.replicate (widthOf S D i) true)) (List.replicate (S.req i).arity true) t.val := rfl
theorem roundIn_e0 : roundIn S D i point blk total parity (ee S D 0) = RepairOrdinary.frame (List.ofFn point) := by
  rw [roundIn_val]; exact bankN_addr S D _ _ _ _ _ _ _
theorem roundIn_e1 : roundIn S D i point blk total parity (ee S D 1) =
    ZeroPadding.pad total (List.replicate (blk * widthOf S D i) true) := by
  rw [roundIn_val]; exact bankN_off S D _ _ _ _ _ _ _
theorem roundIn_e2 : roundIn S D i point blk total parity (ee S D 2) =
    ZeroPadding.pad total (List.replicate (widthOf S D i) true) := by
  rw [roundIn_val]; exact bankN_width S D _ _ _ _ _ _ _
theorem roundIn_e3 : roundIn S D i point blk total parity (ee S D 3) = List.replicate (S.req i).arity true := by
  rw [roundIn_val]; exact bankN_q S D _ _ _ _ _ _ _
theorem roundIn_other (t : Fin (tw S D)) (h0 : t.val ≠ 0) (h1 : t.val ≠ 1)
    (h2 : t.val ≠ S.wtapes D + 1) (h3 : t.val ≠ xt S D) (h4 : t.val ≠ xt S D + 1) (h5 : t.val ≠ xt S D + 2)
    (h6 : t.val ≠ xt S D + 3) : roundIn S D i point blk total parity t = [] := by
  rw [roundIn_val]; exact bankN_other S D _ _ _ _ _ _ _ t.val h0 h1 h2 h3 h4 h5 h6

end RoundIn

/-- **One round is ready**: block `blk`'s honest bit of `S.req i` is XORed into the accumulator; the address, offset,
width, word and descriptor ports are kept. -/
theorem round_run (hD : 1 ≤ D) {N : ℕ} (point : BitInput N)
    (hcb : (a.output (S.req i)).clauseBits ≤ capOf S D i)
    (blk total : ℕ) (parity : Bool) (hfit : (blk + 1) * widthOf S D i ≤ N) :
    ∃ out, ClockJoin.ReadyRun (worker S D) (roundCost S D i point blk) (roundIn S D i point blk total parity) out ∧
      out (xe S D (xacc S D)) =
        [xor parity (CloseoutLanguage.paddedUnsigned (a.output (S.req i)) hcb
          (AddressWindow.field point (blk * widthOf S D i) (widthOf S D i)))] ∧
      (∀ j : Fin 4, out (ee S D (j.castAdd 5)) = roundIn S D i point blk total parity (ee S D (j.castAdd 5))) ∧
      (∀ j : Fin (xt S D), j.val < 2 → out (xe S D j) = roundIn S D i point blk total parity (xe S D j)) := by
  have hw3 := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  set req := S.req i with hreq
  set cap := capOf S D i with hcap
  set width := widthOf S D i with hwidth
  set off := blk * width with hoff
  have b_e0 := roundIn_e0 S D i point blk total parity
  have b_e1 := roundIn_e1 S D i point blk total parity
  have b_e2 := roundIn_e2 S D i point blk total parity
  have b_e3 := roundIn_e3 S D i point blk total parity
  have b_other : ∀ (t : Fin (tw S D)) (v : ℕ), t.val = v → v ≠ 0 → v ≠ 1 → v ≠ S.wtapes D + 1 →
      v ≠ xt S D → v ≠ xt S D + 1 → v ≠ xt S D + 2 → v ≠ xt S D + 3 → roundIn S D i point blk total parity t = [] := by
    intro t v hv h0 h1 h2 h3 h4 h5 h6
    subst hv
    exact roundIn_other S D i point blk total parity t h0 h1 h2 h3 h4 h5 h6
  have hoffw : off + width ≤ N := by
    have : off + width = (blk + 1) * width := by rw [hoff]; ring
    omega
  set B1 := roundIn S D i point blk total parity with hB1
  -- the crop of block `blk`
  set pre := List.ofFn (AddressWindow.field point 0 off) with hpre
  set fld := List.ofFn (AddressWindow.field point off width) with hfld
  set tl := AddressWindow.tail point off width with htl
  have hsplit : List.ofFn point = pre ++ fld ++ tl := split_at point off width hoffw
  have hpre_len : pre.length = off := List.length_ofFn
  have hfld_len : fld.length = width := List.length_ofFn
  obtain ⟨s2, hs2, s26, _, s20, s22, s23⟩ := SliceFrame.slice_run pre fld tl
  set cap2 : Fin 8 → ℕ := ![0, 0, total, total, 0, 0, 0, 0] with hcap2
  have p2 := ready_pad SliceFrame.machine _ _ _ cap2 hs2
  have f2 := p2.focus (sliceSlots S D) (sliceSlots_injective S D) B1 (by
    intro j
    fin_cases j
    · show B1 (ee S D 0) = ZeroPadding.pad 0 (RepairOrdinary.frame (pre ++ fld ++ tl))
      rw [b_e0, ZeroPadding.pad_zero, hsplit]
    · exact b_other _ (xt S D + 4) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · show B1 (ee S D 1) = ZeroPadding.pad total (List.replicate pre.length true)
      rw [b_e1, hpre_len]
    · show B1 (ee S D 2) = ZeroPadding.pad total (List.replicate fld.length true)
      rw [b_e2, hfld_len]
    · exact b_other _ (xt S D + 5) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact b_other _ (xt S D + 6) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact b_other _ 2 rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact b_other _ (xt S D + 7) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  set o2 : Fin 8 → List Bool := fun j => ZeroPadding.pad (cap2 j) (s2 j) with ho2
  set B2 := install (sliceSlots S D) B1 o2 with hB2
  -- the accumulator block on block `blk`
  set u := AddressWindow.field point off req.arity with hu
  set clause := AddressWindow.field point (off + req.arity) (a.output req).clauseBits with hclause
  set padw := AddressWindow.padding point off req.arity (a.output req).clauseBits cap with hpadw
  set position := AddressWindow.read point (off + req.arity + cap) with hposition
  have hpadw_len : padw.length = cap - (a.output req).clauseBits := List.length_ofFn
  have hcapw : (a.output req).clauseBits + padw.length = CloseoutLanguage.clauseWidth D req.arity := by
    rw [hpadw_len]; show _ = cap; omega
  have hpre0 : ([] : List Bool).length = 0 * (req.arity + CloseoutLanguage.clauseWidth D req.arity + 1) := by simp
  obtain ⟨wout, hw, hbit, hret⟩ := S.wreset_run i D 0 hD u clause padw [] [] position hcapw hpre0
  have haddr : [] ++ AddressFields.word u clause padw position ++ [] = fld := by
    rw [List.nil_append, List.append_nil, hfld]
    exact (block_word point off req.arity (a.output req).clauseBits cap hcb).symm
  obtain ⟨xres, hx, hxacc, hxold⟩ := XorBody.ready (S.wresetMachine D 0) ((S.woutputSlot D).castAdd 1) _ _ wout
    parity _ hw hbit
  have hB2x : ∀ j : Fin (xt S D), j.val ≠ 2 → B2 (xe S D j) = B1 (xe S D j) :=
    fun j hj => install_other _ _ _ _ (fun i => slice_xe S D i j hj)
  have f3 := hx.focus (xe S D) (xe_injective S D) B2 (by
    intro j
    rw [xinput_val]
    have hjl := j.isLt
    by_cases h2 : j.val = 2
    · have hj : xe S D j = sliceSlots S D 6 := Fin.ext (by simp [xe, sliceSlots, xa, h2])
      rw [hj, hB2, install_slot _ (sliceSlots_injective S D), if_neg (by omega), if_neg (by omega), if_pos h2,
        haddr]
      show ZeroPadding.pad 0 (s2 6) = _
      rw [ZeroPadding.pad_zero, s26]
    rw [hB2x j h2, if_neg h2]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, hB1, roundIn_val, show (xe S D j).val = 0 from h0, bankN_w0]
    by_cases h1 : j.val = 1
    · rw [if_neg h0, if_pos h1, hB1, roundIn_val, show (xe S D j).val = 1 from h1, bankN_desc]
    rw [if_neg h0, if_neg h1]
    by_cases hacc : j.val = S.wtapes D + 1
    · rw [if_pos hacc, hB1, roundIn_val, show (xe S D j).val = S.wtapes D + 1 from hacc, bankN_acc]
    rw [if_neg hacc]
    exact b_other _ j.val rfl h0 h1 hacc (by omega) (by omega) (by omega) (by omega))
  -- the round
  have j23 := ClockJoin.join _ _ _ _ _ _ _ f2 f3
  refine ⟨_, ClockJoin.enlarge _ _ _ _ _ j23 (le_of_eq ?_), ?_, ?_, ?_⟩
  · unfold roundCost
    rw [hpre_len, hfld_len, hpadw_len]
  · erw [install_slot _ (xe_injective S D)]
    show xres (Fin.last _) = _
    rw [hxacc]
    congr 2
    show _ = CloseoutLanguage.paddedUnsigned (a.output req) hcb (AddressWindow.field point off (req.arity + cap + 1))
    rw [AddressWindow.padded_value]
    rfl
  · intro j
    erw [install_other _ _ _ _ (fun i => xe_ee S D i _)]
    fin_cases j
    · show B2 (sliceSlots S D 0) = _
      rw [hB2, install_slot _ (sliceSlots_injective S D)]
      show ZeroPadding.pad 0 (s2 0) = B1 (ee S D 0)
      rw [ZeroPadding.pad_zero, s20, b_e0, hsplit]
    · show B2 (sliceSlots S D 2) = _
      rw [hB2, install_slot _ (sliceSlots_injective S D)]
      show ZeroPadding.pad total (s2 2) = B1 (ee S D 1)
      rw [s22, b_e1, hpre_len]
    · show B2 (sliceSlots S D 3) = _
      rw [hB2, install_slot _ (sliceSlots_injective S D)]
      show ZeroPadding.pad total (s2 3) = B1 (ee S D 2)
      rw [s23, b_e2, hfld_len]
    · show B2 (ee S D 3) = B1 (ee S D 3)
      exact install_other _ _ _ _ (fun j => by
        intro h; have hv := congrArg Fin.val h; rw [sliceSlots_val] at hv
        simp only [ee_val] at hv; revert hv; fin_cases j <;> simp)
  · intro j hj
    erw [install_slot _ (xe_injective S D)]
    have hjv : j.val = 0 ∨ j.val = 1 := by omega
    rcases hjv with h0 | h1
    · have he : j = XorBody.old ((S.wold D (S.lo 0)).castAdd 1) := Fin.ext (by simp [XorBody.old, SBlock.wold, SBlock.lo, h0])
      rw [hB1, roundIn_val, show (xe S D j).val = 0 from h0, bankN_w0, he, hxold, hret 0]
      rfl
    · have he : j = XorBody.old ((S.wold D (S.lo 1)).castAdd 1) := Fin.ext (by simp [XorBody.old, SBlock.wold, SBlock.lo, h1])
      rw [hB1, roundIn_val, show (xe S D j).val = 1 from h1, bankN_desc, he, hxold, hret 1]
      rfl

end Round

end

end Stage35.Fold
