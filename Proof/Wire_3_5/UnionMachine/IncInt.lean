import Proof.Wire_3_5.UnionMachine.IncMath
import Proof.Wire_3_5.UnionMachine.BitLoop
import Proof.Wire_3_5.UnionMachine.BinW

/-! # C6 front, the C1 dock: the integer increment `intWord z ↦ intWord (z+1)`

C1's request word carries each gate's threshold `θ` as `intWord θ` (`Plan.selWord`); base's native gate word carries
`intWord (θ − 1)` (`TabRef.tabGW_eq`). This word program reads `enc ε (intWord z)` on stream `0` and appends
`marks (intWord (z+1))` to stream `1`, bit-serially (the threshold is never read into a unary register). Layout
`WState 1 16`: registers `0` flag, `1` length `ℓ`, `2` counter, `3` copy temp, `4` prescan flag, `5` carry/borrow,
`6` output count.
* `z ≥ 0` (**`pos_spec`**): read `ℓ`; prescan (all ones?) and rewind; write `0`, `1^{ℓ+[all ones]} 0`, the carry
  bits (`IncMath.natWord_succ`).

Paper quantity: the gate threshold `θ` of C1's request (P3:1326-1330). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.IncInt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.UnionMachine.IncMath
open NearCubicWires.WilliamsPublishedForm
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR)
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable (cap : ℕ)

/-- Prescan: all ones. -/
def gAll : BitLoop.Mealy := fun b c => (c && b, [])
/-- The carry. -/
def gInc : BitLoop.Mealy := fun b c => (c && b, [xor b c])

theorem run_gAll : ∀ (c : Bool) (l : List Bool), BitLoop.run gAll c l = (c && l.all id, [])
  | c, [] => by simp [BitLoop.run]
  | c, b :: t => by
    have ih := run_gAll (c && b) t
    simp only [BitLoop.run, gAll] at ih ⊢
    rw [ih]; simp [Bool.and_assoc]

theorem run_gInc : ∀ (c : Bool) (l : List Bool), BitLoop.run gInc c l = ((incC c l).2, (incC c l).1)
  | c, [] => by simp [BitLoop.run, incC]
  | c, b :: t => by
    have ih := run_gInc (c && b) t
    simp only [BitLoop.run, gInc, incC] at ih ⊢
    rw [ih]; simp

theorem incC_all : ∀ (l : List Bool), (incC true l).2 = l.all id
  | [] => rfl
  | b :: t => by
    cases b
    · simp only [incC, Bool.true_and]
      have : ∀ l' : List Bool, (incC false l').2 = false := by
        intro l'; induction l' with
        | nil => rfl
        | cons a t' ih => simp [incC, ih]
      simp [this]
    · simp [incC, incC_all t]

/-- Read the unary length into register `1`. -/
def posA (ε : Bool) : WM 1 16 := .seq (.inc 0) (.whr 0 (unaryBody ε 0 0 1))
/-- Prescan (all ones?) into register `4`, then rewind. -/
def posB (ε : Bool) : WM 1 16 :=
  .seq (.seq (.seq (.seq (.inc 4) (dupR 1 2 3)) (BitLoop.loop gAll ε 0 1 2 4 6)) (dupR 1 2 3)) (BitLoop.rew ε 0 2)
/-- Write the sign `0` and the unary length `1^{ℓ+[all ones]} 0`. -/
def posC : WM 1 16 :=
  .seq (.seq (.seq (.seq (emitPair 1 6 false) (dupR 1 2 3)) (BitLoop.ones 1 2 6)) (.ifr 4 (emitPair 1 6 true) .skip))
    (emitPair 1 6 false)
/-- Write the carry bits, the carry's last bit, clear the scratch. -/
def posD (ε : Bool) : WM 1 16 :=
  .seq (.seq (.seq (.seq (.seq (.inc 5) (dupR 1 2 3)) (BitLoop.loop gInc ε 0 1 2 5 6))
    (.ifr 5 (.seq (emitPair 1 6 true) (.dec 5)) .skip)) (.ifr 4 (.dec 4) .skip)) (WM.clear 1)

/-- **The increment of a nonnegative integer word** (from its unary prefix). -/
def posP (ε : Bool) : WM 1 16 := .seq (.seq (.seq (posA ε) (posB ε)) posC) (posD ε)

theorem readI (ε : Bool) (σ : WState 1 16) (pre rest : List Bool) (z : ℤ)
    (hst : σ.st 0 = pre ++ enc ε (intWord z) ++ rest) (j : ℕ) (hj : j < (intWord z).length) :
    readTapeBit (σ.st 0) (pre.length + stp ε * j + off ε) = (intWord z).getD j false := by
  rw [hst, List.append_assoc, Nat.add_assoc, read_pre]
  exact read_enc_bit ε rest _ j hj

theorem condEmit_spec (b : Bool) (σ : WState 1 16) (hb : σ.val 4 = b.toNat) (ho : σ.sh 1 = (σ.st 1).length)
    (hc : σ.val 6 + 2 ≤ cap) :
    WExec cap (.ifr 4 (emitPair 1 6 true) .skip) σ (appendO σ 1 6 (if b then [true, true] else [])) 16 := by
  cases b
  · have e : appendO σ 1 6 (if false = true then [true, true] else []) = σ := by simp [appendO_nil]
    rw [e]; exact WExec.mono (WExec.ifrF (by simp [hb]) (WExec.skip σ)) (by omega)
  · simp only [if_true]
    exact WExec.mono (WExec.ifrT (by simp [hb]) (emitPair_spec cap 1 6 true σ ho hc)) (by omega)

theorem condEmitDec_spec (b : Bool) (σ : WState 1 16) (hb : σ.val 5 = b.toNat) (ho : σ.sh 1 = (σ.st 1).length)
    (hc : σ.val 6 + 2 ≤ cap) :
    WExec cap (.ifr 5 (.seq (emitPair 1 6 true) (.dec 5)) .skip) σ
      ((appendO σ 1 6 (if b then [true, true] else [])).setv 5 0) 20 := by
  cases b
  · have e : (appendO σ 1 6 (if false = true then [true, true] else [])).setv 5 0 = σ := by
      rw [show (if false = true then [true, true] else []) = ([] : List Bool) from rfl, appendO_nil,
        show (0 : ℕ) = σ.val 5 by simp [hb], wsetv_same]
    rw [e]; exact WExec.mono (WExec.ifrF (by simp [hb]) (WExec.skip σ)) (by omega)
  · simp only [if_true]
    have h1 := emitPair_spec cap 1 6 true σ ho hc
    have h2 := WExec.dec (cap := cap) 5 (appendO σ 1 6 [true, true]) (by simp [Function.update_apply, hb]; omega)
    refine WExec.mono (WExec.ifrT (by simp [hb]) (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl)) (by omega)
    apply WState.eq <;> simp [Function.update_apply, hb]

theorem condDec_spec (b : Bool) (σ : WState 1 16) (hb : σ.val 4 = b.toNat) (hcap : 1 ≤ cap) :
    WExec cap (.ifr 4 (.dec 4) .skip) σ (σ.setv 4 0) 2 := by
  cases b
  · rw [show (0 : ℕ) = σ.val 4 by simp [hb], wsetv_same]
    exact WExec.mono (WExec.ifrF (by simp [hb]) (WExec.skip σ)) (by omega)
  · have h := WExec.dec (cap := cap) 4 σ (by simp [hb]; omega)
    refine WExec.mono (WExec.ifrT (by simp [hb]) (WExec.cast cap h ?_ le_rfl)) (by omega)
    simp [hb]

/-- Phase A: the unary length `ℓ` into register `1`, the head past the prefix and its `0`. -/
theorem posA_spec (ε : Bool) (ℓ : ℕ) (σ : WState 1 16) (hf : σ.val 0 = 0) (hL : σ.val 1 = 0)
    (hones : ∀ k, k < ℓ → readTapeBit (σ.st 0) (σ.sh 0 + stp ε * k + off ε) = true)
    (hzero : readTapeBit (σ.st 0) (σ.sh 0 + stp ε * ℓ + off ε) = false) (hcap : ℓ + 1 ≤ cap) :
    WExec cap (posA ε) σ ((σ.seth 0 (σ.sh 0 + stp ε * ℓ + stp ε)).setv 1 ℓ) (10 * ℓ + 13) := by
  have c1 := WExec.inc (cap := cap) 0 σ (by rw [hf]; omega)
  have c2 := unary_loop cap ε (0 : Fin 2) (0 : Fin 16) 1 (by decide) (by omega) ℓ (σ.setv 0 (σ.val 0 + 1))
    (by simp [hf]) (fun k hk => by simpa using hones k hk) (by simpa using hzero) (by simp [hL]; omega)
  refine WExec.cast cap (WExec.seq c1 c2) ?_ (by omega)
  apply WState.eq
  · simp
  · simp
  · funext r; by_cases h0 : r = 0
    · subst h0; simp [hf]
    · by_cases h1 : r = 1
      · subst h1; simp [hL]
      · simp [Function.update_apply, h0, h1]
  · simp

theorem gAll_len : ∀ b c, (gAll b c).2.length ≤ 1 := fun _ _ => by simp [gAll]
theorem gInc_len : ∀ b c, (gInc b c).2.length ≤ 1 := fun _ _ => by simp [gInc]

/-- Phase B: the all-ones flag of the next `|bs|` bits into register `4`, the head back. -/
theorem posB_spec (ε : Bool) (bs : List Bool) (σ : WState 1 16) (hL : σ.val 1 = bs.length) (hT : σ.val 2 = 0)
    (hU : σ.val 3 = 0) (hF : σ.val 4 = 0) (ho : σ.sh 1 = (σ.st 1).length)
    (hread : ∀ k, k < bs.length → readTapeBit (σ.st 0) (σ.sh 0 + stp ε * k + off ε) = bs.getD k false)
    (hcap : σ.val 6 + 3 * bs.length + 4 ≤ cap) :
    WExec cap (posB ε) σ (σ.setv 4 (bs.all id).toNat) (100 * (bs.length + 1)) := by
  have hs := stp_eq ε
  have hoff := off_le ε
  have c1 := WExec.inc (cap := cap) 4 σ (by rw [hF]; omega)
  have c2 := WExec.seq c1 (BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) _ bs.length
    (by simp [hL]) (by simp [hT]) (by simp [hU]) (by omega))
  have c3 := WExec.seq c2 (BitLoop.loop_spec cap gAll ε 0 1 2 4 6 gAll_len (by decide) (by decide) (by decide)
    (by decide) _ true bs (fun k hk => by simpa using hread k hk) (by simp) (by simp [hF]) (by simpa using ho)
    (by simp; omega))
  have c4 := WExec.seq c3 (BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) _ bs.length
    (by simp [BitLoop.st, hL]) (by simp [BitLoop.st]) (by simp [BitLoop.st, hU]) (by omega))
  have c5 := WExec.seq c4 (BitLoop.rew_spec cap ε 0 2 bs.length _ (by simp [BitLoop.st])
    (by simp [BitLoop.st]) (by simp [BitLoop.st]; omega))
  refine WExec.cast cap c5 ?_ (by nlinarith)
  apply WState.eq
  · funext j; fin_cases j <;> simp [BitLoop.st, run_gAll, BitLoop.marks_nil, appendO_nil]
  · funext j; fin_cases j <;> simp [BitLoop.st, run_gAll, BitLoop.marks_nil, appendO_nil]
  · funext r
    by_cases h4 : r = 4
    · subst h4; simp [BitLoop.st, run_gAll]
    · by_cases h2 : r = 2
      · subst h2; simp [BitLoop.st, hT]
      · by_cases h6 : r = 6
        · subst h6; simp [BitLoop.st, run_gAll, BitLoop.marks_nil]
        · simp [BitLoop.st, Function.update_apply, h4, h2, h6]
  · simp [BitLoop.st]

/-- Phase C: the sign `0`, then `1^{ℓ+[b]} 0`, framed. -/
theorem posC_spec (ℓ : ℕ) (b : Bool) (σ : WState 1 16) (hL : σ.val 1 = ℓ) (hT : σ.val 2 = 0) (hU : σ.val 3 = 0)
    (hF : σ.val 4 = b.toNat) (ho : σ.sh 1 = (σ.st 1).length) (hcap : σ.val 6 + 3 * ℓ + 10 ≤ cap) :
    WExec cap posC σ (appendO σ 1 6 ([true, false] ++ marks (List.replicate ℓ true) ++
      (if b then [true, true] else []) ++ [true, false])) (100 * (ℓ + 1)) := by
  have c1 := emitPair_spec cap 1 6 false σ ho (by omega)
  have c2 := WExec.seq c1 (BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) _ ℓ
    (by simp [hL]) (by simp [hT]) (by simp [hU]) (by omega))
  have c3 := WExec.seq c2 (BitLoop.ones_spec cap 1 2 6 (by decide) ℓ _ (by simp) (by simp [ho]) (by simp; omega))
  have c4 := WExec.seq c3 (condEmit_spec cap b _ (by simp [hF]) (by simp [ho]; omega) (by simp; omega))
  have c5 := WExec.seq c4 (emitPair_spec cap 1 6 false _ (by simp [ho]; cases b <;> simp <;> omega)
    (by simp; cases b <;> simp <;> omega))
  refine WExec.cast cap c5 ?_ (by omega)
  apply WState.eq
  · funext j; fin_cases j <;> simp <;> cases b <;> simp <;> ring
  · funext j; fin_cases j <;> simp <;> cases b <;> simp
  · funext r
    by_cases h2 : r = 2
    · subst h2; simp [hT]
    · by_cases h6 : r = 6
      · subst h6; simp; cases b <;> simp <;> ring
      · simp [Function.update_apply, h2, h6]
  · simp

/-- Phase D: the carry bits of the next `|bs|` bits and the carry's last bit, framed; the scratch cleared. -/
theorem posD_spec (ε : Bool) (bs : List Bool) (b : Bool) (σ : WState 1 16) (hL : σ.val 1 = bs.length)
    (hT : σ.val 2 = 0) (hU : σ.val 3 = 0) (hF : σ.val 4 = b.toNat) (hC : σ.val 5 = 0)
    (ho : σ.sh 1 = (σ.st 1).length)
    (hread : ∀ k, k < bs.length → readTapeBit (σ.st 0) (σ.sh 0 + stp ε * k + off ε) = bs.getD k false)
    (hcap : σ.val 6 + 3 * bs.length + 10 ≤ cap) :
    WExec cap (posD ε) σ ((((appendO σ 1 6 (marks (incC true bs).1 ++
      (if (incC true bs).2 then [true, true] else []))).seth 0 (σ.sh 0 + stp ε * bs.length)).setv 4 0).setv 1 0)
      (100 * (bs.length + 1)) := by
  have hs := stp_eq ε
  have hoff := off_le ε
  have c1 := WExec.inc (cap := cap) 5 σ (by rw [hC]; omega)
  have c2 := WExec.seq c1 (BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) _ bs.length
    (by simp [hL]) (by simp [hT]) (by simp [hU]) (by omega))
  have c3 := WExec.seq c2 (BitLoop.loop_spec cap gInc ε 0 1 2 5 6 gInc_len (by decide) (by decide) (by decide)
    (by decide) _ true bs (fun k hk => by simpa using hread k hk) (by simp) (by simp [hC]) (by simpa using ho)
    (by simp; omega))
  have hle := incC_length true bs
  have c4 := WExec.seq c3 (condEmitDec_spec cap (incC true bs).2 _ (by simp [BitLoop.st, run_gInc])
    (by simp [BitLoop.st, ho]) (by simp [BitLoop.st, run_gInc, hle]; omega))
  have c5 := WExec.seq c4 (condDec_spec cap b _ (by simp [BitLoop.st, hF]) (by omega))
  have c6 := WExec.seq c5 (wclear_spec cap 1 bs.length _ (by simp [BitLoop.st, hL]) (by simp [BitLoop.st]; omega))
  refine WExec.cast cap c6 ?_ (by nlinarith)
  apply WState.eq
  · funext j; fin_cases j <;> simp [BitLoop.st, run_gInc] <;> cases (incC true bs).2 <;> simp [hle] <;> omega
  · funext j; fin_cases j <;> simp [BitLoop.st, run_gInc]
  · funext r
    by_cases h1 : r = 1
    · subst h1; simp [BitLoop.st]
    · by_cases h2 : r = 2
      · subst h2; simp [BitLoop.st, hT]
      · by_cases h4 : r = 4
        · subst h4; simp [BitLoop.st]
        · by_cases h5 : r = 5
          · subst h5; simp [BitLoop.st, hC]
          · by_cases h6 : r = 6
            · subst h6; simp [BitLoop.st, run_gInc, hle]; cases (incC true bs).2 <;> simp <;> ring
            · simp [BitLoop.st, Function.update_apply, h1, h2, h4, h5, h6]
  · simp [BitLoop.st]

theorem intWord_len (z : ℤ) : (intWord z).length = 2 * natBitLength z.natAbs + 2 := by
  rw [intWord_eq, List.length_cons, natWord_length]

theorem marks_rep_succ (k : ℕ) : marks (List.replicate (k + 1) true) = marks (List.replicate k true) ++ [true, true] := by
  rw [List.replicate_succ', Streaming.marks_append]; rfl

/-- The emitted words of the nonnegative increment are `intWord (z+1)`'s marks. -/
theorem pos_emitted (z : ℤ) (hz : 0 ≤ z) :
    marks (intWord (z + 1)) = [true, false] ++ marks (List.replicate (natBitLength z.natAbs) true) ++
      (if (incC true (fixedWidthNatBits (natBitLength z.natAbs) z.natAbs)).2 then [true, true] else []) ++
      [true, false] ++ (marks (incC true (fixedWidthNatBits (natBitLength z.natAbs) z.natAbs)).1 ++
      (if (incC true (fixedWidthNatBits (natBitLength z.natAbs) z.natAbs)).2 then [true, true] else [])) := by
  rw [intWord_succ_nonneg z hz, natWord_succ]
  cases (incC true (fixedWidthNatBits (natBitLength z.natAbs) z.natAbs)).2
  · simp [Streaming.marks_append, BitLoop.marks_cons, BitLoop.marks_nil]
  · simp [Streaming.marks_append, BitLoop.marks_cons, BitLoop.marks_nil, marks_rep_succ]

/-- **`z ≥ 0`**: from the unary prefix of `enc ε (intWord z)` (the sign already read), the program appends
`marks (intWord (z+1))` and moves the source past the word; every scratch register back at `0`. -/
theorem pos_spec (ε : Bool) (σ : WState 1 16) (pre rest : List Bool) (z : ℤ) (hz : 0 ≤ z)
    (hst : σ.st 0 = pre ++ enc ε (intWord z) ++ rest) (hsh : σ.sh 0 = pre.length + stp ε)
    (ho : σ.sh 1 = (σ.st 1).length) (hf : σ.val 0 = 0) (hL : σ.val 1 = 0) (hT : σ.val 2 = 0) (hU : σ.val 3 = 0)
    (hF : σ.val 4 = 0) (hC : σ.val 5 = 0) (hcap : σ.val 6 + 10 * (natBitLength z.natAbs + 2) ≤ cap) :
    WExec cap (posP ε) σ (appendO (σ.seth 0 (pre.length + stp ε * (intWord z).length)) 1 6 (marks (intWord (z + 1))))
      (400 * (natBitLength z.natAbs + 2)) := by
  have hemit := pos_emitted z hz
  obtain ⟨m, hm⟩ : ∃ m, m = z.natAbs := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = natBitLength m := ⟨_, rfl⟩
  obtain ⟨bs, hbs⟩ : ∃ bs, bs = fixedWidthNatBits ℓ m := ⟨_, rfl⟩
  rw [← hm, ← hℓ, ← hbs] at hemit
  rw [← hm, ← hℓ] at hcap ⊢
  have hs := stp_eq ε
  have hoff := off_le ε
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; exact nbl_pos m
  have hbl : bs.length = ℓ := by rw [hbs]; exact fwb_length ℓ m
  have hIw : intWord z = false :: (List.replicate ℓ true ++ false :: bs) := by
    rw [intWord_eq, show decide (z < 0) = false by simp; omega, ← hm, natWord_eq', ← hℓ, ← hbs]
  have hIl : (intWord z).length = 2 * ℓ + 2 := by rw [hIw]; simp [hbl]; ring
  have hrd := readI ε σ pre rest z hst
  have hget1 : ∀ k, k < ℓ → (intWord z).getD (k + 1) false = true := by
    intro k hk
    rw [hIw, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using hk)]
    simp [List.getD_eq_getElem?_getD, hk]
  have hget0 : (intWord z).getD (ℓ + 1) false = false := by
    rw [hIw, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hgetb : ∀ k, k < ℓ → (intWord z).getD (ℓ + 2 + k) false = bs.getD k false := by
    intro k hk
    rw [hIw, show ℓ + 2 + k = (ℓ + (k + 1)) + 1 by omega, List.getD_cons_succ,
      List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hall : bs.all id = (incC true bs).2 := (incC_all bs).symm
  have cA := posA_spec cap ε ℓ σ hf hL
    (fun k hk => by
      rw [hsh, show pre.length + stp ε + stp ε * k + off ε = pre.length + stp ε * (k + 1) + off ε by ring,
        hrd (k + 1) (by omega), hget1 k hk])
    (by rw [hsh, show pre.length + stp ε + stp ε * ℓ + off ε = pre.length + stp ε * (ℓ + 1) + off ε by ring,
        hrd (ℓ + 1) (by omega), hget0])
    (by omega)
  have hbread : ∀ k, k < bs.length →
      readTapeBit (((σ.seth 0 (σ.sh 0 + stp ε * ℓ + stp ε)).setv 1 ℓ).st 0)
        (((σ.seth 0 (σ.sh 0 + stp ε * ℓ + stp ε)).setv 1 ℓ).sh 0 + stp ε * k + off ε) = bs.getD k false := by
    intro k hk
    simp only [WState.setv_st, WState.setv_sh, WState.seth_st, WState.seth_sh, Function.update_self, hsh]
    rw [show pre.length + stp ε + stp ε * ℓ + stp ε + stp ε * k + off ε =
      pre.length + stp ε * (ℓ + 2 + k) + off ε by ring, hrd (ℓ + 2 + k) (by omega), hgetb k (by omega)]
  have cB := WExec.seq cA (posB_spec cap ε bs _ (by simp [hbl]) (by simp [hT]) (by simp [hU]) (by simp [hF])
    (by simp [ho]) hbread (by simp; omega))
  have cC := WExec.seq cB (posC_spec cap ℓ (bs.all id) _ (by simp) (by simp [hT]) (by simp [hU]) (by simp)
    (by simp [ho]) (by simp; omega))
  have cD := WExec.seq cC (posD_spec cap ε bs (bs.all id) _ (by simp [hbl]) (by simp [hT]) (by simp [hU])
    (by simp) (by simp [hC]) (by cases hb : bs.all id <;> simp [ho, hb] <;> omega)
    (fun k hk => by simpa using hbread k hk) (by cases hb : bs.all id <;> simp [hb] <;> omega))
  refine WExec.cast cap cD ?_ (by nlinarith)
  rw [hall] at *
  apply WState.eq
  · funext j; fin_cases j
    · simp [hsh, hIl, hbl]; ring
    · simp [ho, hemit]
      cases (incC true bs).2 <;> simp [incC_length] <;> ring
  · funext j; fin_cases j
    · simp
    · simp [hemit, List.append_assoc]
  · funext r
    by_cases h1 : r = 1
    · subst h1; simp [hL]
    · by_cases h4 : r = 4
      · subst h4; simp [hF]
      · by_cases h6 : r = 6
        · subst h6; simp [hemit]; cases (incC true bs).2 <;> simp [incC_length] <;> ring
        · simp [Function.update_apply, h1, h4, h6]
  · simp

/-! ## `z < 0`: the borrow -/

/-- Prescan: all zeros. -/
def gZero : BitLoop.Mealy := fun b c => (c && !b, [])
/-- The borrow. -/
def gDec : BitLoop.Mealy := fun b c => (c && !b, [xor b c])

theorem gZero_len : ∀ b c, (gZero b c).2.length ≤ 1 := fun _ _ => by simp [gZero]
theorem gDec_len : ∀ b c, (gDec b c).2.length ≤ 1 := fun _ _ => by simp [gDec]

theorem run_gZero : ∀ (c : Bool) (l : List Bool), BitLoop.run gZero c l = (c && l.all (fun b => !b), [])
  | c, [] => by simp [BitLoop.run]
  | c, b :: t => by
    have ih := run_gZero (c && !b) t
    simp only [BitLoop.run, gZero] at ih ⊢
    rw [ih]; simp [Bool.and_assoc]

theorem run_gDec : ∀ (c : Bool) (l : List Bool), BitLoop.run gDec c l = ((decC c l).2, (decC c l).1)
  | c, [] => by simp [BitLoop.run, decC]
  | c, b :: t => by
    have ih := run_gDec (c && !b) t
    simp only [BitLoop.run, gDec, decC] at ih ⊢
    rw [ih]; simp

theorem decC_take : ∀ (c : Bool) (l : List Bool) (k : ℕ), (decC c (l.take k)).1 = (decC c l).1.take k
  | c, [], k => by simp [decC]
  | c, b :: t, 0 => by simp [decC]
  | c, b :: t, k + 1 => by
    simp only [List.take_succ_cons, decC]
    rw [decC_take (c && !b) t k]

theorem allNot_iff : ∀ (l : List Bool), l.all (fun b => !b) = true ↔ bv l = 0
  | [] => by simp [bv]
  | b :: t => by
    have ih := allNot_iff t
    cases b <;> simp [bv, ih]

/-- The drop flag the prescan computes is `dropP m`. -/
theorem drop_eq (m : ℕ) :
    (decide (2 ≤ natBitLength m) && ((fixedWidthNatBits (natBitLength m) m).take (natBitLength m - 1)).all
      (fun b => !b)) = dropP m := by
  unfold dropP
  rw [fwb_take _ _ _ (by omega)]
  by_cases h2 : 2 ≤ natBitLength m
  · have e : ((fixedWidthNatBits (natBitLength m - 1) m).all fun b => !b) =
        decide (m % 2 ^ (natBitLength m - 1) = 0) := by
      rw [Bool.eq_iff_iff, allNot_iff, bv_fwb]; simp
    simp [h2, e]
  · simp [h2]

theorem two_le_iff (m : ℕ) (hm : 1 ≤ m) : 2 ≤ m ↔ 2 ≤ natBitLength m := by
  constructor
  · intro h
    have h1 : 1 ≤ Nat.log 2 m := Nat.log_pos (by norm_num) h
    unfold natBitLength; omega
  · intro h
    have := pow_nbl_le m hm
    have h4 : 2 ≤ 2 ^ (natBitLength m - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (natBitLength m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem condDecR_spec (r : Fin 16) (b : Bool) (σ : WState 1 16) (hb : σ.val r = b.toNat) (hcap : 1 ≤ cap) :
    WExec cap (.ifr r (.dec r) .skip) σ (σ.setv r 0) 2 := by
  cases b
  · rw [show (0 : ℕ) = σ.val r by simp [hb], wsetv_same]
    exact WExec.mono (WExec.ifrF (by simp [hb]) (WExec.skip σ)) (by omega)
  · have h := WExec.dec (cap := cap) r σ (by simp [hb]; omega)
    refine WExec.mono (WExec.ifrT (by simp [hb]) (WExec.cast cap h ?_ le_rfl)) (by omega)
    simp [hb]

/-- Phase B1: the all-zeros flag of the low `ℓ−1` bits into register `4`, the head back. -/
def negB1 (ε : Bool) : WM 1 16 :=
  .seq (.seq (.seq (.seq (.seq (.seq (.inc 4) (dupR 1 2 3)) (.dec 2)) (BitLoop.loop gZero ε 0 1 2 4 6)) (dupR 1 2 3))
    (.dec 2)) (BitLoop.rew ε 0 2)

theorem negB1_spec (ε : Bool) (bs : List Bool) (σ : WState 1 16) (hbl : 1 ≤ bs.length) (hL : σ.val 1 = bs.length)
    (hT : σ.val 2 = 0) (hU : σ.val 3 = 0) (hF : σ.val 4 = 0) (ho : σ.sh 1 = (σ.st 1).length)
    (hread : ∀ k, k < bs.length → readTapeBit (σ.st 0) (σ.sh 0 + stp ε * k + off ε) = bs.getD k false)
    (hcap : σ.val 6 + 3 * bs.length + 4 ≤ cap) :
    WExec cap (negB1 ε) σ (σ.setv 4 ((bs.take (bs.length - 1)).all (fun b => !b)).toNat) (200 * (bs.length + 1)) := by
  have hs := stp_eq ε
  have hoff := off_le ε
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = bs.take (bs.length - 1) := ⟨_, rfl⟩
  rw [← hlo]
  have hlol : lo.length = bs.length - 1 := by rw [hlo, List.length_take]; omega
  have c1 := WExec.inc (cap := cap) 4 σ (by rw [hF]; omega)
  have c2 := WExec.seq c1 (BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) _ bs.length
    (by simp [hL]) (by simp [hT]) (by simp [hU]) (by omega))
  have c3 := WExec.seq c2 (WExec.dec (cap := cap) 2 _ (by simp; omega))
  have c4 := WExec.seq c3 (BitLoop.loop_spec cap gZero ε 0 1 2 4 6 gZero_len (by decide) (by decide) (by decide)
    (by decide) _ true lo (fun k hk => by
      simp only [WState.setv_st, WState.setv_sh]
      rw [hread k (by omega), hlo, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
      simp [show k < bs.length - 1 from by omega]) (by simp [hlol]) (by simp [hF]) (by simpa using ho)
    (by simp; omega))
  have c5 := WExec.seq c4 (BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) _ bs.length
    (by simp [BitLoop.st, hL]) (by simp [BitLoop.st]) (by simp [BitLoop.st, hU]) (by omega))
  have c6 := WExec.seq c5 (WExec.dec (cap := cap) 2 _ (by simp; omega))
  have c7 := WExec.seq c6 (BitLoop.rew_spec cap ε 0 2 (bs.length - 1) _ (by simp) (by simp [BitLoop.st, hlol])
    (by simp; omega))
  refine WExec.cast cap c7 ?_ (by omega)
  apply WState.eq
  · funext j; fin_cases j <;> simp [BitLoop.st, run_gZero, BitLoop.marks_nil, appendO_nil, hlol]
  · funext j; fin_cases j <;> simp [BitLoop.st, run_gZero, BitLoop.marks_nil, appendO_nil]
  · funext r
    by_cases h4 : r = 4
    · subst h4; simp [BitLoop.st, run_gZero, List.take_length]
    · by_cases h2 : r = 2
      · subst h2; simp [BitLoop.st, hT]
      · by_cases h6 : r = 6
        · subst h6; simp [BitLoop.st, run_gZero, BitLoop.marks_nil]
        · simp [BitLoop.st, Function.update_apply, h4, h2, h6]
  · simp [BitLoop.st]

/-- Phase B2: clear the flag at `ℓ = 1` (no drop there). -/
def negB2 : WM 1 16 := .seq (.seq (.seq (dupR 1 7 3) (.dec 7)) (.ifr 7 .skip (.ifr 4 (.dec 4) .skip))) (WM.clear 7)

theorem negB2_spec (ℓ : ℕ) (f : Bool) (σ : WState 1 16) (hℓ : 1 ≤ ℓ) (hL : σ.val 1 = ℓ) (hU : σ.val 3 = 0)
    (hF : σ.val 4 = f.toNat) (hW : σ.val 7 = 0) (hcap : ℓ + 2 ≤ cap) :
    WExec cap negB2 σ (σ.setv 4 (decide (2 ≤ ℓ) && f).toNat) (30 * (ℓ + 1)) := by
  have c1 := BinW.dupR_spec cap 1 7 3 (by decide) (by decide) (by decide) σ ℓ hL hW hU (by omega)
  have c2 := WExec.seq c1 (WExec.dec (cap := cap) 7 _ (by simp; omega))
  by_cases h2 : 2 ≤ ℓ
  · have c3 := WExec.seq c2 (WExec.ifrT (r := 7) (Q := .ifr 4 (.dec 4) .skip)
      (by simp only [WState.setv_val, Function.update_self]; omega)
      (WExec.skip ((σ.setv 7 ℓ).setv 7 ((σ.setv 7 ℓ).val 7 - 1))))
    have c4 := WExec.seq c3 (wclear_spec cap 7 (ℓ - 1) _ (by simp) (by simp; omega))
    refine WExec.cast cap c4 ?_ (by omega)
    apply WState.eq
    · simp
    · simp
    · funext r; by_cases h7 : r = 7
      · subst h7; simp [hW]
      · by_cases h4 : r = 4
        · subst h4; simp [hF, h2]
        · simp [Function.update_apply, h7, h4]
    · simp
  · have hℓ1 : ℓ = 1 := by omega
    have c3 := WExec.seq c2 (WExec.ifrF (r := 7) (P := .skip)
      (by simp only [WState.setv_val, Function.update_self]; omega)
      (condDecR_spec cap 4 f ((σ.setv 7 ℓ).setv 7 ((σ.setv 7 ℓ).val 7 - 1)) (by simp [hF]) (by omega)))
    have c4 := WExec.seq c3 (wclear_spec cap 7 0 _ (by simp; omega) (by simp; omega))
    refine WExec.cast cap c4 ?_ (by omega)
    apply WState.eq
    · simp
    · simp
    · funext r; by_cases h7 : r = 7
      · subst h7; simp [hW]
      · by_cases h4 : r = 4
        · subst h4; simp [h2]
        · simp [Function.update_apply, h7, h4]
    · simp

theorem condDecOther_spec (d : Bool) (σ : WState 1 16) (hd : σ.val 4 = d.toNat) (h2 : d.toNat ≤ σ.val 2)
    (hcap : σ.val 2 ≤ cap) :
    WExec cap (.ifr 4 (.dec 2) .skip) σ (σ.setv 2 (σ.val 2 - d.toNat)) 2 := by
  cases d
  · rw [show σ.val 2 - false.toNat = σ.val 2 by simp, wsetv_same]
    exact WExec.mono (WExec.ifrF (by simp [hd]) (WExec.skip σ)) (by omega)
  · exact WExec.mono (WExec.ifrT (by simp [hd]) (WExec.cast cap (WExec.dec (cap := cap) 2 σ hcap) (by simp) le_rfl))
      (by omega)

theorem condSkip_spec (ε : Bool) (d : Bool) (σ : WState 1 16) (hd : σ.val 4 = d.toNat) :
    WExec cap (.ifr 4 (.seq (preE ε 0) (.fwd 0)) .skip) σ (σ.seth 0 (σ.sh 0 + stp ε * d.toNat)) (off ε + 3) := by
  have hs := stp_eq ε
  cases d
  · have e : σ.seth 0 (σ.sh 0 + stp ε * false.toNat) = σ := WState.eq (by simp) rfl rfl rfl
    rw [e]; exact WExec.mono (WExec.ifrF (by simp [hd]) (WExec.skip σ)) (by omega)
  · have h1 := preE_spec cap ε 0 σ
    have h2 := WExec.fwd (cap := cap) 0 (σ.seth 0 (σ.sh 0 + off ε))
    refine WExec.mono (WExec.ifrT (by simp [hd]) (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl)) (by omega)
    apply WState.eq
    · funext j; fin_cases j <;> simp; omega
    · rfl
    · rfl
    · rfl

/-- Phase C (negative): the sign `[ℓ ≥ 2]` and `1^{ℓ−d} 0`, framed. -/
def negC : WM 1 16 :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (dupR 1 2 3) (.dec 2)) (PrimAsm.CopyNat.writeBitM 1 6 2)) (WM.clear 2))
    (dupR 1 2 3)) (.ifr 4 (.dec 2) .skip)) (BitLoop.ones 1 2 6)) (emitPair 1 6 false)

theorem negC_spec (ℓ : ℕ) (d : Bool) (σ : WState 1 16) (hℓ : 1 ≤ ℓ) (hdℓ : d.toNat ≤ ℓ) (hL : σ.val 1 = ℓ)
    (hT : σ.val 2 = 0) (hU : σ.val 3 = 0) (hF : σ.val 4 = d.toNat) (ho : σ.sh 1 = (σ.st 1).length)
    (hcap : σ.val 6 + 3 * ℓ + 10 ≤ cap) :
    WExec cap negC σ (appendO σ 1 6 ([true, decide (2 ≤ ℓ)] ++ marks (List.replicate (ℓ - d.toNat) true) ++
      [true, false])) (100 * (ℓ + 1)) := by
  have c1 := BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) σ ℓ hL hT hU (by omega)
  have c2 := WExec.seq c1 (WExec.dec (cap := cap) 2 _ (by simp; omega))
  have c3 := WExec.seq c2 (PrimAsm.CopyNat.writeBitM_spec cap 1 6 2 _ (by simp [ho]) (by simp; omega))
  have c4 := WExec.seq c3 (wclear_spec cap 2 (ℓ - 1) _ (by simp) (by simp; omega))
  have c5 := WExec.seq c4 (BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) _ ℓ
    (by simp [hL]) (by simp) (by simp [hU]) (by omega))
  have c6 := WExec.seq c5 (condDecOther_spec cap d _ (by simp [hF]) (by simp; omega) (by simp; omega))
  have c7 := WExec.seq c6 (BitLoop.ones_spec cap 1 2 6 (by decide) (ℓ - d.toNat) _ (by simp) (by simp [ho])
    (by simp; omega))
  have c8 := WExec.seq c7 (emitPair_spec cap 1 6 false _ (by simp [ho]; omega) (by simp; omega))
  have hsg : decide (((σ.setv 2 ℓ).setv 2 ((σ.setv 2 ℓ).val 2 - 1)).val 2 ≠ 0) = decide (2 ≤ ℓ) := by
    simp only [WState.setv_val, Function.update_self]
    exact decide_eq_decide.mpr (by omega)
  rw [hsg] at c8
  refine WExec.cast cap c8 ?_ (by omega)
  apply WState.eq
  · funext j; fin_cases j <;> simp <;> omega
  · funext j; fin_cases j <;> simp
  · funext r
    by_cases h2 : r = 2
    · subst h2; simp [hT]
    · by_cases h6 : r = 6
      · subst h6; simp; omega
      · simp [Function.update_apply, h2, h6]
  · simp

/-- Phase D (negative): the borrow bits of the low `ℓ−d` bits; the dropped top bit skipped; the scratch cleared. -/
def negD (ε : Bool) : WM 1 16 :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.inc 5) (dupR 1 2 3)) (.ifr 4 (.dec 2) .skip))
    (BitLoop.loop gDec ε 0 1 2 5 6)) (.ifr 4 (.seq (preE ε 0) (.fwd 0)) .skip)) (.ifr 5 (.dec 5) .skip))
    (.ifr 4 (.dec 4) .skip)) (WM.clear 1)

theorem negD_spec (ε : Bool) (bs : List Bool) (d : Bool) (σ : WState 1 16) (hdl : d.toNat ≤ bs.length)
    (hL : σ.val 1 = bs.length) (hT : σ.val 2 = 0) (hU : σ.val 3 = 0) (hF : σ.val 4 = d.toNat) (hC : σ.val 5 = 0)
    (ho : σ.sh 1 = (σ.st 1).length)
    (hread : ∀ k, k < bs.length → readTapeBit (σ.st 0) (σ.sh 0 + stp ε * k + off ε) = bs.getD k false)
    (hcap : σ.val 6 + 3 * bs.length + 10 ≤ cap) :
    WExec cap (negD ε) σ ((((appendO σ 1 6 (marks (decC true (bs.take (bs.length - d.toNat))).1)).seth 0
      (σ.sh 0 + stp ε * bs.length)).setv 4 0).setv 1 0) (200 * (bs.length + 1)) := by
  have hs := stp_eq ε
  have hoff := off_le ε
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = bs.take (bs.length - d.toNat) := ⟨_, rfl⟩
  rw [← hlo]
  have hlol : lo.length = bs.length - d.toNat := by rw [hlo, List.length_take]; omega
  have hle := decC_length true lo
  have c1 := WExec.inc (cap := cap) 5 σ (by rw [hC]; omega)
  have c2 := WExec.seq c1 (BinW.dupR_spec cap 1 2 3 (by decide) (by decide) (by decide) _ bs.length
    (by simp [hL]) (by simp [hT]) (by simp [hU]) (by omega))
  have c3 := WExec.seq c2 (condDecOther_spec cap d _ (by simp [hF]) (by simp; omega) (by simp; omega))
  have c4 := WExec.seq c3 (BitLoop.loop_spec cap gDec ε 0 1 2 5 6 gDec_len (by decide) (by decide) (by decide)
    (by decide) _ true lo (fun k hk => by
      simp only [WState.setv_st, WState.setv_sh]
      rw [hread k (by omega), hlo, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
      simp [show k < bs.length - d.toNat from by omega]) (by simp [hlol]) (by simp [hC]) (by simpa using ho)
    (by simp; omega))
  have c5 := WExec.seq c4 (condSkip_spec cap ε d _ (by simp [BitLoop.st, hF]))
  have c6 := WExec.seq c5 (condDecR_spec cap 5 (BitLoop.run gDec true (lo.take lo.length)).1 _
    (by simp [BitLoop.st]) (by omega))
  have c7 := WExec.seq c6 (condDecR_spec cap 4 d _ (by simp [BitLoop.st, hF]) (by omega))
  have c8 := WExec.seq c7 (wclear_spec cap 1 bs.length _ (by simp [BitLoop.st, hL]) (by simp [BitLoop.st]; omega))
  refine WExec.cast cap c8 ?_ (by omega)
  apply WState.eq
  · funext j; fin_cases j
    · have hm1 : ∀ n : ℕ, 1 ≤ n → stp ε * (n - 1) + stp ε = stp ε * n := fun n hn => by
        rw [← Nat.mul_succ]; congr 1; omega
      cases d
      · simp [BitLoop.st, hlol]
      · simp at hdl
        have := hm1 bs.length hdl
        simp [BitLoop.st, hlol]; omega
    · simp [BitLoop.st, run_gDec, hle]
  · funext j; fin_cases j <;> simp [BitLoop.st, run_gDec]
  · funext r
    by_cases h1 : r = 1
    · subst h1; simp [BitLoop.st]
    · by_cases h2 : r = 2
      · subst h2; simp [BitLoop.st, hT]
      · by_cases h4 : r = 4
        · subst h4; simp [BitLoop.st]
        · by_cases h5 : r = 5
          · subst h5; simp [BitLoop.st, hC]
          · by_cases h6 : r = 6
            · subst h6; simp [BitLoop.st, run_gDec, hle]
            · simp [BitLoop.st, Function.update_apply, h1, h2, h4, h5, h6]
  · simp [BitLoop.st]

/-- The emitted words of the negative increment are `intWord (z+1)`'s marks. -/
theorem neg_emitted (z : ℤ) (hz : z < 0) :
    marks (intWord (z + 1)) = [true, decide (2 ≤ natBitLength z.natAbs)] ++
      marks (List.replicate (natBitLength z.natAbs - (dropP z.natAbs).toNat) true) ++ [true, false] ++
      marks (decC true ((fixedWidthNatBits (natBitLength z.natAbs) z.natAbs).take
        (natBitLength z.natAbs - (dropP z.natAbs).toNat))).1 := by
  have hm : 1 ≤ z.natAbs := by omega
  rw [intWord_succ_neg z hz, natWord_pred z.natAbs hm, decC_take,
    show decide (2 ≤ z.natAbs) = decide (2 ≤ natBitLength z.natAbs) from decide_eq_decide.mpr (two_le_iff _ hm)]
  simp [Streaming.marks_append, BitLoop.marks_cons]

/-- **The increment of a negative integer word** (from its unary prefix). -/
def negP (ε : Bool) : WM 1 16 := .seq (.seq (.seq (.seq (posA ε) (negB1 ε)) negB2) negC) (negD ε)

/-- **`z < 0`**: from the unary prefix of `enc ε (intWord z)` (the sign already read), the program appends
`marks (intWord (z+1))` and moves the source past the word; every scratch register back at `0`. -/
theorem neg_spec (ε : Bool) (σ : WState 1 16) (pre rest : List Bool) (z : ℤ) (hz : z < 0)
    (hst : σ.st 0 = pre ++ enc ε (intWord z) ++ rest) (hsh : σ.sh 0 = pre.length + stp ε)
    (ho : σ.sh 1 = (σ.st 1).length) (hf : σ.val 0 = 0) (hL : σ.val 1 = 0) (hT : σ.val 2 = 0) (hU : σ.val 3 = 0)
    (hF : σ.val 4 = 0) (hC : σ.val 5 = 0) (hW : σ.val 7 = 0)
    (hcap : σ.val 6 + 10 * (natBitLength z.natAbs + 2) ≤ cap) :
    WExec cap (negP ε) σ (appendO (σ.seth 0 (pre.length + stp ε * (intWord z).length)) 1 6 (marks (intWord (z + 1))))
      (600 * (natBitLength z.natAbs + 2)) := by
  have hemit := neg_emitted z hz
  have hm1 : 1 ≤ z.natAbs := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = z.natAbs := ⟨_, rfl⟩
  rw [← hm] at hemit hm1
  have hdrop := drop_eq m
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = natBitLength m := ⟨_, rfl⟩
  obtain ⟨bs, hbs⟩ : ∃ bs, bs = fixedWidthNatBits ℓ m := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = dropP m := ⟨_, rfl⟩
  rw [← hℓ, ← hbs, ← hd] at hemit
  rw [← hℓ, ← hbs, ← hd] at hdrop
  rw [← hm, ← hℓ] at hcap ⊢
  have hs := stp_eq ε
  have hoff := off_le ε
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; exact nbl_pos m
  have hbl : bs.length = ℓ := by rw [hbs]; exact fwb_length ℓ m
  have hdℓ : d.toNat ≤ ℓ := by cases d <;> simp <;> omega
  have hIw : intWord z = true :: (List.replicate ℓ true ++ false :: bs) := by
    rw [intWord_eq, show decide (z < 0) = true by simp; omega, ← hm, natWord_eq', ← hℓ, ← hbs]
  have hIl : (intWord z).length = 2 * ℓ + 2 := by rw [hIw]; simp [hbl]; ring
  have hrd := readI ε σ pre rest z hst
  have hget1 : ∀ k, k < ℓ → (intWord z).getD (k + 1) false = true := by
    intro k hk
    rw [hIw, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using hk)]
    simp [List.getD_eq_getElem?_getD, hk]
  have hget0 : (intWord z).getD (ℓ + 1) false = false := by
    rw [hIw, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hgetb : ∀ k, k < ℓ → (intWord z).getD (ℓ + 2 + k) false = bs.getD k false := by
    intro k hk
    rw [hIw, show ℓ + 2 + k = (ℓ + (k + 1)) + 1 by omega, List.getD_cons_succ,
      List.getD_append_right _ _ _ _ (by simp)]
    simp
  have cA := posA_spec cap ε ℓ σ hf hL
    (fun k hk => by
      rw [hsh, show pre.length + stp ε + stp ε * k + off ε = pre.length + stp ε * (k + 1) + off ε by ring,
        hrd (k + 1) (by omega), hget1 k hk])
    (by rw [hsh, show pre.length + stp ε + stp ε * ℓ + off ε = pre.length + stp ε * (ℓ + 1) + off ε by ring,
        hrd (ℓ + 1) (by omega), hget0])
    (by omega)
  have hbread : ∀ k, k < bs.length →
      readTapeBit (((σ.seth 0 (σ.sh 0 + stp ε * ℓ + stp ε)).setv 1 ℓ).st 0)
        (((σ.seth 0 (σ.sh 0 + stp ε * ℓ + stp ε)).setv 1 ℓ).sh 0 + stp ε * k + off ε) = bs.getD k false := by
    intro k hk
    simp only [WState.setv_st, WState.setv_sh, WState.seth_st, WState.seth_sh, Function.update_self, hsh]
    rw [show pre.length + stp ε + stp ε * ℓ + stp ε + stp ε * k + off ε =
      pre.length + stp ε * (ℓ + 2 + k) + off ε by ring, hrd (ℓ + 2 + k) (by omega), hgetb k (by omega)]
  have cB1 := WExec.seq cA (negB1_spec cap ε bs _ (by omega) (by simp [hbl]) (by simp [hT]) (by simp [hU])
    (by simp [hF]) (by simp [ho]) hbread (by simp; omega))
  have cB2 := WExec.seq cB1 (negB2_spec cap ℓ ((bs.take (bs.length - 1)).all fun b => !b) _ hℓ1 (by simp)
    (by simp [hU]) (by simp) (by simp [hW]) (by omega))
  rw [hbl, hdrop] at cB2
  have cC := WExec.seq cB2 (negC_spec cap ℓ d _ hℓ1 hdℓ (by simp) (by simp [hT]) (by simp [hU]) (by simp)
    (by simp [ho]) (by simp; omega))
  have cD := WExec.seq cC (negD_spec cap ε bs d _ (by omega) (by simp [hbl]) (by simp [hT]) (by simp [hU])
    (by simp) (by simp [hC]) (by simp [ho] <;> omega) (fun k hk => by simpa using hbread k hk) (by simp; omega))
  refine WExec.cast cap cD ?_ (by omega)
  apply WState.eq
  · funext j; fin_cases j
    · simp [hsh, hIl, hbl]; ring
    · simp [ho, hemit, hbl, decC_length]; omega
  · funext j; fin_cases j
    · simp
    · simp [hemit, hbl, List.append_assoc]
  · funext r
    by_cases h1 : r = 1
    · subst h1; simp [hL]
    · by_cases h4 : r = 4
      · subst h4; simp [hF]
      · by_cases h6 : r = 6
        · subst h6; simp [hemit, hbl, decC_length]; omega
        · simp [Function.update_apply, h1, h4, h6]
  · simp

/-- **The integer increment**: read the sign, then the nonnegative or the negative branch. -/
def incIntM (ε : Bool) : WM 1 16 := .seq (preE ε 0) (.ifs 0 (.seq (.fwd 0) (negP ε)) (.seq (.fwd 0) (posP ε)))

/-- **The integer increment's spec**: from `enc ε (intWord z)` at the head of stream `0`, it appends
`marks (intWord (z+1))` to stream `1` and moves stream `0` past the word; every scratch register back at `0`. -/
theorem incInt_spec (ε : Bool) (σ : WState 1 16) (pre rest : List Bool) (z : ℤ)
    (hst : σ.st 0 = pre ++ enc ε (intWord z) ++ rest) (hsh : σ.sh 0 = pre.length)
    (ho : σ.sh 1 = (σ.st 1).length) (hf : σ.val 0 = 0) (hL : σ.val 1 = 0) (hT : σ.val 2 = 0) (hU : σ.val 3 = 0)
    (hF : σ.val 4 = 0) (hC : σ.val 5 = 0) (hW : σ.val 7 = 0)
    (hcap : σ.val 6 + 10 * (natBitLength z.natAbs + 2) ≤ cap) :
    WExec cap (incIntM ε) σ (appendO (σ.seth 0 (pre.length + stp ε * (intWord z).length)) 1 6
      (marks (intWord (z + 1)))) (700 * (natBitLength z.natAbs + 2)) := by
  have hs := stp_eq ε
  have hoff := off_le ε
  have h1 := preE_spec cap ε 0 σ
  set σ1 := σ.seth 0 (σ.sh 0 + off ε) with hσ1
  have hbit : wbit σ1 0 = decide (z < 0) := by
    simp only [wbit, σ1, WState.seth_st, WState.seth_sh, Function.update_self]
    have := readI ε σ pre rest z hst 0 (by rw [intWord_len]; omega)
    rw [hsh, show pre.length + off ε = pre.length + stp ε * 0 + off ε by ring, this, intWord_eq]
    rfl
  have h2 := WExec.fwd (cap := cap) 0 σ1
  set σ2 := σ1.seth 0 (σ1.sh 0 + 1) with hσ2
  have e2 : σ2 = σ.seth 0 (pre.length + stp ε) := by
    apply WState.eq
    · funext j; fin_cases j <;> simp [σ2, σ1, hsh]; omega
    · rfl
    · rfl
    · rfl
  by_cases hz : z < 0
  · have hn := neg_spec cap ε σ2 pre rest z hz (by simp [σ2, σ1, hst]) (by rw [e2]; simp)
      (by simp [σ2, σ1, ho]) (by simp [σ2, σ1, hf]) (by simp [σ2, σ1, hL]) (by simp [σ2, σ1, hT])
      (by simp [σ2, σ1, hU]) (by simp [σ2, σ1, hF]) (by simp [σ2, σ1, hC]) (by simp [σ2, σ1, hW])
      (by simp [σ2, σ1]; omega)
    have hb : wbit σ1 0 = true := by rw [hbit]; simp [hz]
    refine WExec.cast cap (WExec.seq h1 (WExec.ifsT hb (WExec.seq h2 hn))) ?_ (by omega)
    rw [e2]
    apply WState.eq
    · funext j; fin_cases j <;> simp
    · funext j; fin_cases j <;> simp
    · rfl
    · rfl
  · have hp := pos_spec cap ε σ2 pre rest z (by omega) (by simp [σ2, σ1, hst]) (by rw [e2]; simp)
      (by simp [σ2, σ1, ho]) (by simp [σ2, σ1, hf]) (by simp [σ2, σ1, hL]) (by simp [σ2, σ1, hT])
      (by simp [σ2, σ1, hU]) (by simp [σ2, σ1, hF]) (by simp [σ2, σ1, hC]) (by simp [σ2, σ1]; omega)
    have hb : wbit σ1 0 = false := by rw [hbit]; simp [hz]
    refine WExec.cast cap (WExec.seq h1 (WExec.ifsF hb (WExec.seq h2 hp))) ?_ (by omega)
    rw [e2]
    apply WState.eq
    · funext j; fin_cases j <;> simp
    · funext j; fin_cases j <;> simp
    · rfl
    · rfl

end NearCubicWires.WireExponent3_5.UnionMachine.IncInt
