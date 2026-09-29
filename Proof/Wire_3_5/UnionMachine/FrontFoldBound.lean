import Proof.Wire_3_5.UnionMachine.FrontFoldSem

/-! # C6 front, U5, the writers' fold (b): its fuel and widths are polynomial

The union front runs within a fixed polynomial of its input (the plan's `FrontAtW` costs). This module bounds the
fold's round fuel (`FrontFoldLoop.rcost`) and every kept tape by powers of `B ≥ 2`, for any class-mode writers
(`K`, `d` symbolic, `K ≤ B^K`):
* the toolkit (`bpos`, `ble`, `bK`, `badd`, `bmul`, `bpw`, `bconst`);
* a writer's output length from its ready run (`out_len`);
* the envelope stage: the atoms of a code (`atoms_le`, `frames_le`), its fold fuel (`foldCwE_le`) and its fuel
  (`envCost_le`).

Paper quantity: none (the front's time, a fixed polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm (frameP frame_eq_frameP)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (inBank)
open NearCubicWires.WireExponent3_5.UnionMachine.CWIface (outBankJ outBankJ_out ParityWriterJ CarrierWriterJ)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (bitmap codesWord carrierOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode (envCodeCost atomsOf atoms_len atoms_width)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvRound (foldCwE fB)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvChk (cntChkCost)

/-! ## Powers of `B ≥ 2` -/

section Toolkit
variable {B : ℕ}

theorem bpos (hB : 2 ≤ B) (e : ℕ) : 1 ≤ B ^ e := Nat.one_le_pow _ _ (by omega)

theorem ble (hB : 2 ≤ B) {x a b : ℕ} (hab : a ≤ b) (hx : x ≤ B ^ a) : x ≤ B ^ b :=
  hx.trans (Nat.pow_le_pow_right (by omega) hab)

theorem bconst (hB : 2 ≤ B) (c k : ℕ) (hc : c ≤ 2 ^ k) : c ≤ B ^ k := hc.trans (Nat.pow_le_pow_left hB k)

theorem bK (hB : 2 ≤ B) (K : ℕ) : K ≤ B ^ K := bconst hB K K (Nat.lt_two_pow_self).le

theorem bmul {x y a b : ℕ} (hx : x ≤ B ^ a) (hy : y ≤ B ^ b) : x * y ≤ B ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem bpw {x a : ℕ} (k : ℕ) (hx : x ≤ B ^ a) : x ^ k ≤ B ^ (a * k) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left hx k

theorem badd (hB : 2 ≤ B) {x y e : ℕ} (hx : x ≤ B ^ e) (hy : y ≤ B ^ e) : x + y ≤ B ^ (e + 1) := by
  rw [pow_succ]; nlinarith

/-- A constant multiple: `c ≤ 2^k`. -/
theorem bcm (hB : 2 ≤ B) {x e : ℕ} (c k : ℕ) (hc : c ≤ 2 ^ k) (hx : x ≤ c * B ^ e) : x ≤ B ^ (e + k) := by
  have h := Nat.mul_le_mul_right (B ^ e) (bconst hB c k hc)
  rw [pow_add, mul_comm (B ^ e)]; exact hx.trans h

end Toolkit

/-! ## A writer's output -/

theorem frame_length (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  rw [frame_eq_frameP]; simp [frameP]; omega

/-- **A writer's output is shorter than its fuel plus its input.** -/
theorem out_len {t s : ℕ} (M : Machine t s) (inS outS : Fin t) (hio : inS ≠ outS) (u v : List Bool)
    (J : Fin t → List Bool) (c : ℕ) (hr : ClockJoin.ReadyRun M c (inBank inS u) (outBankJ inS outS u v J)) :
    v.length ≤ c + u.length + 1 := by
  have h := NearCubicWires.WireExponent3_5.Transfer.ready_lengths hr (2 * u.length + 1) (by
    intro i; unfold inBank; split_ifs
    · rw [frame_length]
    · simp) outS
  rw [outBankJ_out inS outS hio, frame_length] at h
  rcases le_max_iff.mp (le_refl (max (2 * u.length + 1) (c + 1))) with hm | hm <;> omega

/-! ## The envelope stage -/

theorem atoms_le (x : ℕ) : (atomsOf x).length ≤ natBitLength x := by
  rw [atoms_len]
  exact (CloseoutWitness.Reencode.atoms_length _).trans (PCPPNativeCanonicalTree.tree_nodes x)

theorem flat_frame_len (W : ℕ) : ∀ ys : List (List Bool), (∀ y ∈ ys, y.length = W) →
    (ys.flatMap frame).length = ys.length * (2 * W + 1)
  | [], _ => by simp
  | y :: ys, h => by
    rw [List.flatMap_cons, List.length_append, frame_length, h y (by simp),
      flat_frame_len W ys (fun z hz => h z (by simp [hz])), List.length_cons]
    ring

theorem frames_le (x : ℕ) : ((atomsOf x).flatMap frame).length ≤ natBitLength x * (2 * natBitLength x + 1) := by
  rw [flat_frame_len _ _ (atoms_width x)]
  exact Nat.mul_le_mul_right _ (atoms_le x)

/-- **The envelope loop's round fuel**, within `B^(26w + 91)` when `W + 2 ≤ B^w`. -/
theorem foldCwE_le {B : ℕ} (hB : 2 ≤ B) (W c w : ℕ) (hc : c ≤ W) (hW : W + 2 ≤ B ^ w) :
    foldCwE W c ≤ B ^ (26 * w + 91) := by
  have hP : (W + 2) ^ 26 ≤ B ^ (w * 26) := bpw 26 hW
  have hq : c * (5 * W + 8) ≤ 5 * (W + 2) ^ 26 := by
    have h1 : c * (5 * W + 8) ≤ (W + 2) * (5 * (W + 2)) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (W + 2) * (5 * (W + 2)) = 5 * (W + 2) ^ 2 := by ring
    have h3 : (W + 2) ^ 2 ≤ (W + 2) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have hW26 : W + 2 ≤ (W + 2) ^ 26 := Nat.le_self_pow (by norm_num) _
  have hE : 2 ^ 91 * B ^ (w * 26) ≤ B ^ (26 * w + 91) := by
    rw [show 26 * w + 91 = w * 26 + 91 by ring, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 91)
  unfold foldCwE fB
  generalize (W + 2) ^ 26 = P at *
  generalize c * (5 * W + 8) = cq at *
  generalize B ^ (w * 26) = Q at *
  generalize B ^ (26 * w + 91) = R at *
  omega

/-- **The envelope stage's fuel**, within `B^(27w + t + 156)` when `natBitLength x + 2 ≤ B^w`, `T ≤ B^t`. -/
theorem envCost_le {B : ℕ} (hB : 2 ≤ B) (x T w t : ℕ) (hW : natBitLength x + 2 ≤ B ^ w) (hT : T ≤ B ^ t) :
    envCodeCost x T ≤ B ^ (27 * w + t + 156) := by
  have hc := atoms_le x
  have hF := foldCwE_le hB (natBitLength x) (atomsOf x).length w hc hW
  set E := B ^ (27 * w + 91 + t) with hEd
  have hwE : B ^ w ≤ E := Nat.pow_le_pow_right (by omega) (by omega)
  have htE : B ^ t ≤ E := Nat.pow_le_pow_right (by omega) (by omega)
  have hE1 := bpos hB (27 * w + 91 + t)
  have hin : foldCwE (natBitLength x) (atomsOf x).length + 1 + (2 * T + 4 + 1 + 0) + 2 ≤
      11 * B ^ (26 * w + 91 + t) := by
    have a1 : B ^ (26 * w + 91) ≤ B ^ (26 * w + 91 + t) := Nat.pow_le_pow_right (by omega) (by omega)
    have a2 : B ^ t ≤ B ^ (26 * w + 91 + t) := Nat.pow_le_pow_right (by omega) (by omega)
    have a3 := bpos hB (26 * w + 91 + t)
    omega
  have hprod : (atomsOf x).length * (foldCwE (natBitLength x) (atomsOf x).length + 1 + (2 * T + 4 + 1 + 0) + 2) ≤
      11 * E := by
    have h1 : (atomsOf x).length ≤ B ^ w := by omega
    have h2 := Nat.mul_le_mul h1 hin
    have h3 : B ^ w * (11 * B ^ (26 * w + 91 + t)) = 11 * E := by
      rw [hEd, show 27 * w + 91 + t = w + (26 * w + 91 + t) by ring, pow_add]; ring
    omega
  have hpoly : 16 * (1000000000000000000 * (natBitLength x + 1) ^ 24) ≤ 2 ^ 64 * E := by
    have h1 : (natBitLength x + 1) ^ 24 ≤ B ^ (w * 24) := bpw 24 (by omega)
    have h2 : B ^ (w * 24) ≤ E := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hfin : 2 ^ 65 * E ≤ B ^ (27 * w + t + 156) := by
    have h1 : 2 ^ 65 * E ≤ B ^ 65 * E := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB 65)
    have h2 : B ^ 65 * E = B ^ (27 * w + t + 156) := by rw [hEd, ← pow_add]; congr 1; ring
    omega
  unfold envCodeCost CloseoutWitness.CanonicalTest.budget CloseoutWitness.Reencode.polynomialBudget cntChkCost
  rw [CWWords.pay_length]
  omega

/-! ## The per-variable widths -/

section Widths
variable {m : Mode} {q : ℕ}

/-- The parity writer's fuel exponent. -/
def eP (Pw : ParityWriterJ m) : ℕ := Pw.K + 2 * Pw.d
/-- The parity code's width exponent. -/
def lp (Pw : ParityWriterJ m) : ℕ := eP Pw + 2
/-- The carrier input's width exponent. -/
def lw (Pw : ParityWriterJ m) : ℕ := lp Pw + 1
/-- The carrier writer's fuel exponent. -/
def eC (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) : ℕ := Cw.K + (lw Pw + 1) * Cw.d
/-- The carrier code's width exponent. -/
def lc (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) : ℕ := eC Pw Cw + lw Pw + 2

variable (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (F : FoldIn m q) (s : ℕ)

theorem cP_le (hq : q ≤ s) (X : ℕ) :
    Pw.K * ((bitmap (F.supp X)).length + q + 1) ^ Pw.d ≤ (s + 2) ^ eP Pw := by
  have hB : 2 ≤ s + 2 := by omega
  rw [bitmap_len]
  have h1 : q + q + 1 ≤ (s + 2) ^ 2 := by nlinarith
  have h2 := bmul (bK hB Pw.K) (bpw Pw.d h1)
  unfold eP; rw [show Pw.K + 2 * Pw.d = Pw.K + 2 * Pw.d from rfl]
  exact h2.trans (le_of_eq (by rw [mul_comm 2]))

theorem pw_len (hq : q ≤ s) (X : ℕ) : (F.pw X).length ≤ (s + 2) ^ lp Pw := by
  have hB : 2 ≤ s + 2 := by omega
  obtain ⟨J, -, hr⟩ := Pw.parity_ready q (F.supp X)
  have h := out_len Pw.M Pw.inS Pw.outS Pw.hio _ _ J _ hr
  have hc := cP_le Pw F s hq X
  rw [bitmap_len] at h hc
  have h3 : q + 1 ≤ (s + 2) ^ (eP Pw + 1) :=
    (show q + 1 ≤ s + 2 by omega).trans (Nat.le_self_pow (by omega) _)
  have h4 := badd hB (ble hB (Nat.le_succ _) hc) h3
  have h5 := ble hB (show eP Pw + 1 + 1 ≤ lp Pw by unfold lp; omega) h4
  show (natWord (m.code (Transfer.unionParityAtom m q (F.supp X)))).length ≤ _
  omega

theorem w_len (hq : q ≤ s) (X : ℕ) (hA : (codesWord m (F.atoms X)).length ≤ s) :
    (codesWord m (F.cs X)).length ≤ (s + 2) ^ lw Pw := by
  have hB : 2 ≤ s + 2 := by omega
  have hp := pw_len Pw F s hq X
  have hs : s ≤ (s + 2) ^ lp Pw := (show s ≤ s + 2 by omega).trans (Nat.le_self_pow (by unfold lp; omega) _)
  have h := badd hB hs hp
  rw [cs_word' F X, List.length_append]
  unfold lw
  split_ifs
  · omega
  · simp; omega

theorem cC_le (hq : q ≤ s) (X : ℕ) (hA : (codesWord m (F.atoms X)).length ≤ s) :
    Cw.K * ((codesWord m (F.cs X)).length + q + 1) ^ Cw.d ≤ (s + 2) ^ eC Pw Cw := by
  have hB : 2 ≤ s + 2 := by omega
  have hw := w_len Pw F s hq X hA
  have hq1 : q + 1 ≤ (s + 2) ^ lw Pw := (show q + 1 ≤ s + 2 by omega).trans (Nat.le_self_pow (by unfold lw; omega) _)
  have h1 : (codesWord m (F.cs X)).length + q + 1 ≤ (s + 2) ^ (lw Pw + 1) := by
    have := badd hB hw hq1; omega
  exact bmul (bK hB Cw.K) (bpw Cw.d h1)

theorem cw_len (hq : q ≤ s) (X : ℕ) (hA : (codesWord m (F.atoms X)).length ≤ s) :
    (F.cw X).length ≤ (s + 2) ^ lc Pw Cw := by
  have hB : 2 ≤ s + 2 := by omega
  obtain ⟨J, -, hr⟩ := Cw.carrier_ready q (F.cs X)
  have h := out_len Cw.M Cw.inS Cw.outS Cw.hio _ _ J _ hr
  have hc := cC_le Pw Cw F s hq X hA
  have hw := w_len Pw F s hq X hA
  have a1 : (s + 2) ^ eC Pw Cw ≤ (s + 2) ^ (eC Pw Cw + lw Pw) := Nat.pow_le_pow_right (by omega) (by omega)
  have a2 : (s + 2) ^ lw Pw ≤ (s + 2) ^ (eC Pw Cw + lw Pw) := Nat.pow_le_pow_right (by omega) (by omega)
  have a3 := bpos hB (eC Pw Cw + lw Pw)
  have h3 : (F.cw X).length ≤ 3 * (s + 2) ^ (eC Pw Cw + lw Pw) := by
    show (natWord (Stars.Carrier.code (carrierOf m (F.cs X)))).length ≤ _
    omega
  exact bcm hB 3 2 (by norm_num) h3

theorem Wc_le (hq : q ≤ s) (X : ℕ) (hA : (codesWord m (F.atoms X)).length ≤ s) :
    natBitLength (Stars.Carrier.code (F.car X)) + 2 ≤ (s + 2) ^ (lc Pw Cw + 2) := by
  have hB : 2 ≤ s + 2 := by omega
  have hc := cw_len Pw Cw F s hq X hA
  have hn := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length (Stars.Carrier.code (F.car X))
  have hp := bpos hB (lc Pw Cw)
  have h : natBitLength (Stars.Carrier.code (F.car X)) + 2 ≤ 3 * (s + 2) ^ lc Pw Cw := by
    have : (F.cw X).length = (natWord (Stars.Carrier.code (F.car X))).length := rfl
    omega
  exact bcm hB 3 2 (by norm_num) h

end Widths

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound
