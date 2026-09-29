import Proof.Wire_3_5.Selection.PointBlock

/-! # C1.4: writing the join keys (P3:1345-1356)

Paper: "For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities [...] dominance
counting needs only `O(U log^{O(1)} U)` comparisons" (P3:1345-1350). Every count is a `<`-join of tagged keys (C1.1,
C1.3); this module writes one point's tagged keys to the key stream, from the point's two key words (`lo`, `hi`),
bit by bit on C1.3's writer state `rst` (a source head, and the output `overlay out L` with its head at `out.length`):
* `emitPairsN`, `copyPairsN`, `skipPairsN`: counted loops (C6's `cloop`) that emit a fixed pair, copy pairs from a
  source, or skip pairs;
* **`EY`**: the key `2v + t` of a word `v` (a `Y`-join key: `t = 1` for an inner key, `0` for a query).
Paper quantity: the tagged join keys of one point. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.UnionMachine.Round (binary_succ)

variable {ns nr : ℕ}

/-! ## Counted pair loops -/

/-- Emit `N` pairs `(1, b)`. -/
def emitPairsN (K : Fin (ns + 1)) (CK N T : Fin nr) (b : Bool) : WM ns nr :=
  cloop N T (.seq (emitB K CK true) (emitB K CK b))

/-- Copy `N` pairs from `A`. -/
def copyPairsN (A K : Fin (ns + 1)) (CA CK N T : Fin nr) : WM ns nr := cloop N T (copyPair A K CA CK)

/-- Skip `N` pairs of `A`. -/
def skipPairsN (A : Fin (ns + 1)) (CA N T : Fin nr) : WM ns nr := cloop N T (.seq (WM.fwdC A CA) (WM.fwdC A CA))

/-- The writer state with no source moved: `K` holds `overlay out L`, its head and `CK` at `out.length`. -/
def kst (σ : WState ns nr) (K : Fin (ns + 1)) (CK : Fin nr) (L out : List Bool) : WState ns nr :=
  ((σ.sets K (overlay out L)).seth K out.length).setv CK out.length

theorem frameP_replicate_succ (n : ℕ) (b : Bool) :
    frameP (List.replicate (n + 1) b) = frameP (List.replicate n b) ++ [true, b] := by
  rw [List.replicate_succ', frameP_append]; rfl

theorem frameP_take_succ (bits : List Bool) (j : ℕ) (hj : j < bits.length) :
    frameP (bits.take (j + 1)) = frameP (bits.take j) ++ [true, bits.getD j false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, frameP_append, List.getD_eq_getElem _ _ hj]; rfl

theorem rd_pairs_bit (pre bits rest : List Bool) (j : ℕ) (hj : j < bits.length) :
    readTapeBit (pre ++ frameP bits ++ rest) (pre.length + 2 * j + 1) = bits.getD j false := by
  unfold readTapeBit
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), show pre.length + 2 * j + 1 - pre.length = 2 * j + 1
    by omega, List.getD_append _ _ _ _ (by simp; omega), frameP_getD_odd]

section Writer
variable (cap : ℕ) (σ0 : WState ns nr) {A K : Fin (ns + 1)} {CA CK : Fin nr} (L : List Bool)
variable (hAK : A ≠ K) (hC : CA ≠ CK)
include hAK hC

theorem rst_setv (r : Fin nr) (v : ℕ) (hr1 : r ≠ CA) (hr2 : r ≠ CK) (pA : ℕ) (out : List Bool) :
    (rst σ0 A K CA CK L pA out).setv r v = rst (σ0.setv r v) A K CA CK L pA out := by
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [rst, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

theorem rst_setv2 (r r' : Fin nr) (v w : ℕ) (hr1 : r ≠ CA) (hr2 : r ≠ CK) (hr1' : r' ≠ CA) (hr2' : r' ≠ CK)
    (pA : ℕ) (out : List Bool) :
    ((rst σ0 A K CA CK L pA out).setv r v).setv r' w = rst ((σ0.setv r v).setv r' w) A K CA CK L pA out := by
  rw [rst_setv σ0 L hAK hC r v hr1 hr2, rst_setv (σ0.setv r v) L hAK hC r' w hr1' hr2']

/-- **Emit `n` pairs `(1, b)`.** -/
theorem emitPairs_rst (N T : Fin nr) (hNT : N ≠ T) (hN1 : N ≠ CA) (hN2 : N ≠ CK) (hT1 : T ≠ CA) (hT2 : T ≠ CK)
    (b : Bool) (n pA : ℕ) (out : List Bool) (hN : σ0.val N = n) (hT : σ0.val T = 0) (hn : n ≤ cap)
    (hq : out.length + 2 * n ≤ cap) :
    WExec cap (emitPairsN K CK N T b) (rst σ0 A K CA CK L pA out)
      (rst σ0 A K CA CK L pA (out ++ frameP (List.replicate n b))) (n * (15 + 8) + 1 + 1 + (7 * n + 1)) := by
  unfold emitPairsN
  let M : WState ns nr → ℕ → WState ns nr := fun σ j => rst σ A K CA CK L pA (out ++ frameP (List.replicate j b))
  have hl := cloopM cap N T hNT _ M (fun σ j v w => rst_setv2 σ L hAK hC N T v w hN1 hN2 hT1 hT2 _ _) σ0 n 15 hN hT
    hn (by
      intro j hj v w
      have e1 := emitB_rst cap ((σ0.setv N v).setv T w) L hAK hC pA (out ++ frameP (List.replicate j b)) true
        (by simp; omega)
      have e2 := emitB_rst cap ((σ0.setv N v).setv T w) L hAK hC pA (out ++ frameP (List.replicate j b) ++ [true]) b
        (by simp; omega)
      refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
      simp only [M, frameP_replicate_succ, List.append_assoc]; rfl)
  simpa [M] using hl

/-- **Copy the `n` pairs `frameP bits` of `A`.** -/
theorem copyPairs_rst (N T : Fin nr) (hNT : N ≠ T) (hN1 : N ≠ CA) (hN2 : N ≠ CK) (hT1 : T ≠ CA) (hT2 : T ≠ CK)
    (pre bits rest out : List Bool) (hA : σ0.st A = pre ++ frameP bits ++ rest) (hN : σ0.val N = bits.length)
    (hT : σ0.val T = 0) (hp : pre.length + 2 * bits.length ≤ cap) (hq : out.length + 2 * bits.length ≤ cap) :
    WExec cap (copyPairsN A K CA CK N T) (rst σ0 A K CA CK L pre.length out)
      (rst σ0 A K CA CK L (pre.length + 2 * bits.length) (out ++ frameP bits))
      (bits.length * (28 + 8) + 1 + 1 + (7 * bits.length + 1)) := by
  unfold copyPairsN
  let M : WState ns nr → ℕ → WState ns nr := fun σ j =>
    rst σ A K CA CK L (pre.length + 2 * j) (out ++ frameP (bits.take j))
  have hl := cloopM cap N T hNT _ M (fun σ j v w => rst_setv2 σ L hAK hC N T v w hN1 hN2 hT1 hT2 _ _) σ0
    bits.length 28 hN hT (by omega) (by
      intro j hj v w
      have hb : readTapeBit (((σ0.setv N v).setv T w).st A) (pre.length + 2 * j + 1) = bits.getD j false := by
        simp only [WState.setv_st, hA]; exact rd_pairs_bit pre bits rest j hj
      have ht : (bits.take j).length = j := by simp; omega
      have h := copyPair_rst cap ((σ0.setv N v).setv T w) L hAK hC (pre.length + 2 * j) (out ++ frameP (bits.take j))
        (bits.getD j false) hb (by omega) (by simp [ht]; omega)
      refine WExec.cast cap h ?_ le_rfl
      simp only [M, frameP_take_succ bits j hj, List.append_assoc]
      congr 1)
  simpa [M] using hl

/-- **Skip `n` pairs of `A`.** -/
theorem skipPairs_rst (N T : Fin nr) (hNT : N ≠ T) (hN1 : N ≠ CA) (hN2 : N ≠ CK) (hT1 : T ≠ CA) (hT2 : T ≠ CK)
    (n pA : ℕ) (out : List Bool) (hN : σ0.val N = n) (hT : σ0.val T = 0) (hp : pA + 2 * n ≤ cap) :
    WExec cap (skipPairsN A CA N T) (rst σ0 A K CA CK L pA out) (rst σ0 A K CA CK L (pA + 2 * n) out)
      (n * (11 + 8) + 1 + 1 + (7 * n + 1)) := by
  unfold skipPairsN
  let M : WState ns nr → ℕ → WState ns nr := fun σ j => rst σ A K CA CK L (pA + 2 * j) out
  have hl := cloopM cap N T hNT _ M (fun σ j v w => rst_setv2 σ L hAK hC N T v w hN1 hN2 hT1 hT2 _ _) σ0 n 11 hN hT
    (by omega) (by
      intro j hj v w
      have f1 := fwdA_rst cap ((σ0.setv N v).setv T w) L hAK hC (pA + 2 * j) out (by omega)
      have f2 := fwdA_rst cap ((σ0.setv N v).setv T w) L hAK hC (pA + 2 * j + 1) out (by omega)
      refine WExec.cast cap (WExec.seq f1 f2) ?_ (by omega)
      simp only [M]; congr 1)
  simpa [M] using hl

/-- Return the source's head. -/
theorem rewA_rst (pA : ℕ) (out : List Bool) (hp : pA ≤ cap) :
    WExec cap (WM.rewind A CA) (rst σ0 A K CA CK L pA out) (rst σ0 A K CA CK L 0 out) (5 * pA + 1) := by
  have h := wrewind_spec cap A CA pA (rst σ0 A K CA CK L pA out) (by simp [rst, hC]) (by simp [rst, hC]; exact hp)
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · funext j; simp only [rst, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl
  · funext j; simp only [rst, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

theorem rst_kst (hA : σ0.sh A = 0) (hCA : σ0.val CA = 0) (out : List Bool) :
    rst σ0 A K CA CK L 0 out = kst σ0 K CK L out := by
  apply WState.eq
  · funext j; simp only [rst, kst, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext j; simp only [rst, kst, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
  · funext j; simp only [rst, kst, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

end Writer

/-! ## A `Y`-join key -/

/-- **The key `2v + t`** of the word `v` on `A`: the tag pair, the first `W − 1` pairs of `v`, the end mark. -/
def EY (t : Bool) (A K : Fin (ns + 1)) (CA CK N T : Fin nr) : WM ns nr :=
  .seq (emitB K CK true) (.seq (emitB K CK t) (.seq (copyPairsN A K CA CK N T) (.seq (emitB K CK false)
    (WM.rewind A CA))))

theorem frame_tag (W v : ℕ) (t : Bool) :
    frame (binary (W + 1) (2 * v + t.toNat)) = [true, t] ++ frameP (binary W v) ++ [false] := by
  rw [binary_succ, frame_eq_frameP, frameP_cons]
  have e1 : ((2 * v + t.toNat) % 2 == 1) = t := by cases t <;> simp [Nat.add_mod]
  have e2 : (2 * v + t.toNat) / 2 = v := by cases t <;> simp <;> omega
  rw [e1, e2]; rfl

section EY
variable (cap : ℕ) (σ0 : WState ns nr) {A K : Fin (ns + 1)} {CA CK N T : Fin nr} (L : List Bool)
variable (hAK : A ≠ K) (hC : CA ≠ CK) (hNT : N ≠ T) (hN1 : N ≠ CA) (hN2 : N ≠ CK) (hT1 : T ≠ CA) (hT2 : T ≠ CK)
include hAK hC hNT hN1 hN2 hT1 hT2

/-- **A `Y`-join key**: `K` gains the framed width-`(W+1)` word of `2v + t`. -/
theorem EY_spec (t : Bool) (W v : ℕ) (out : List Bool) (hA : σ0.st A = frame (binary (W + 1) v))
    (hAh : σ0.sh A = 0) (hCA : σ0.val CA = 0) (hN : σ0.val N = W) (hT : σ0.val T = 0)
    (hcap : out.length + 2 * W + 3 ≤ cap) (hcapA : 2 * W + 1 ≤ cap) :
    WExec cap (EY t A K CA CK N T) (kst σ0 K CK L out)
      (kst σ0 K CK L (out ++ frame (binary (W + 1) (2 * v + t.toNat)))) (60 * W + 30) := by
  rw [← rst_kst σ0 L hAK hC hAh hCA]
  have e1 := emitB_rst cap σ0 L hAK hC 0 out true (by omega)
  have e2 := emitB_rst cap σ0 L hAK hC 0 (out ++ [true]) t (by simp; omega)
  have hsplit : σ0.st A = [] ++ frameP (binary W v) ++ ([true, v / 2 ^ W % 2 == 1] ++ [false]) := by
    rw [hA, frame_eq_frameP, binary_add W 1 v]
    simp [frameP_append, binary]
  have c1 := copyPairs_rst cap σ0 L hAK hC N T hNT hN1 hN2 hT1 hT2 [] (binary W v) _ (out ++ [true] ++ [t]) hsplit
    (by simp [hN]) hT (by simp; omega) (by simp; omega)
  simp only [List.length_nil, binary_length, Nat.zero_add] at c1
  have e3 := emitB_rst cap σ0 L hAK hC (2 * W) (out ++ [true] ++ [t] ++ frameP (binary W v)) false (by simp; omega)
  have r := rewA_rst cap σ0 L hAK hC (2 * W) (out ++ [true] ++ [t] ++ frameP (binary W v) ++ [false]) (by omega)
  rw [rst_kst σ0 L hAK hC hAh hCA] at r
  have hall := WExec.seq e1 (WExec.seq e2 (WExec.seq c1 (WExec.seq e3 r)))
  unfold EY
  refine WExec.cast cap hall ?_ (by omega)
  rw [frame_tag]; simp

end EY

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
