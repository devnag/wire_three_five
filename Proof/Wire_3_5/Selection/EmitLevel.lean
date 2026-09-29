import Proof.Wire_3_5.Selection.Emit

/-! # C1.4: writing the level keys (P3:1345-1356)

Paper: "dominance counting needs only `O(U log^{O(1)} U)` comparisons for two lists of length `U`" (P3:1349-1350).
C1.1's R6 splits the 2-d count by the most significant differing bit `ℓ` of the upper ends into 1-d `<`-joins on the
level keys `lvlK1`, `lvlK2`, `lvlK3`. This module writes one point's level-`ℓ` key, tagged, from its two key words
`lo`, `hi` (the level `ℓ` in register `LV`): it skips `ℓ` pairs of `hi`, reads `hi`'s bit `ℓ`, and either copies `V + 1`
pairs of `lo` and `W − V − 2` pairs of `hi` (from bit `ℓ + 1`) or writes a fixed key (the null query `0`, or the
sentinel `2^(2V+2) − 1`). The two sources' heads live in `est` (C1.3's `rst` with a second source).
Main declarations: `est`, `est_swap`, `lvlE`, **`lvlE_spec`** (and its value lemmas `frame_lvl`, `frame_fix`).
Paper quantity: the tagged level keys of one point. -/

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

/-! ## Two sources -/

/-- The writer state with two sources: `lo` at `plo` (counted in `Clo`), `hi` at `phi` (in `Chi`). -/
def est (σ0 : WState ns nr) (lo hi K : Fin (ns + 1)) (Clo Chi CK : Fin nr) (L : List Bool) (plo phi : ℕ)
    (out : List Bool) : WState ns nr :=
  rst ((σ0.seth hi phi).setv Chi phi) lo K Clo CK L plo out

section Two
variable (σ0 : WState ns nr) {lo hi K : Fin (ns + 1)} {Clo Chi CK : Fin nr} (L : List Bool)
variable (h1 : lo ≠ hi) (h2 : lo ≠ K) (h3 : hi ≠ K) (c1 : Clo ≠ Chi) (c2 : Clo ≠ CK) (c3 : Chi ≠ CK)
include h1 h2 h3 c1 c2 c3

theorem est_swap (plo phi : ℕ) (out : List Bool) :
    est σ0 lo hi K Clo Chi CK L plo phi out = rst ((σ0.seth lo plo).setv Clo plo) hi K Chi CK L phi out := by
  apply WState.eq
  · funext j; simp only [est, rst, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl
  · funext j; simp only [est, rst, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

theorem est_kst (hlo : σ0.sh lo = 0) (hhi : σ0.sh hi = 0) (hClo : σ0.val Clo = 0) (hChi : σ0.val Chi = 0)
    (out : List Bool) : est σ0 lo hi K Clo Chi CK L 0 0 out = kst σ0 K CK L out := by
  apply WState.eq
  · funext j; simp only [est, rst, kst, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext j; simp only [est, rst, kst, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
  · funext j; simp only [est, rst, kst, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

end Two

/-! ## The level emitter -/

/-- The copying branch: the tag pair `(1, t)`, `N1` pairs of `lo`, `N2` pairs of `hi`, the end mark. -/
def cpB (t : Bool) (lo hi K : Fin (ns + 1)) (Clo Chi CK N1 N2 T : Fin nr) : WM ns nr :=
  .seq (WM.fwdC hi Chi) (.seq (emitB K CK true) (.seq (emitB K CK t) (.seq (copyPairsN lo K Clo CK N1 T)
    (.seq (copyPairsN hi K Chi CK N2 T) (emitB K CK false)))))

/-- The fixed branch: `N1` pairs `(1, 1)`, `N2` pairs `(1, 0)`, the end mark. -/
def fxB (hi K : Fin (ns + 1)) (Chi CK N1 N2 T : Fin nr) : WM ns nr :=
  .seq (WM.fwdC hi Chi) (.seq (emitPairsN K CK N1 T true) (.seq (emitPairsN K CK N2 T false) (emitB K CK false)))

/-- **The level emitter**: skip `LV` pairs of `hi`, branch on `hi`'s bit there, return both heads. -/
def lvlE (lo hi : Fin (ns + 1)) (Clo Chi LV T : Fin nr) (Bset Bclr : WM ns nr) : WM ns nr :=
  .seq (skipPairsN hi Chi LV T) (.seq (WM.fwdC hi Chi) (.seq (.ifs hi Bset Bclr)
    (.seq (WM.rewind lo Clo) (WM.rewind hi Chi))))

section Lvl
variable (cap : ℕ) (σ0 : WState ns nr) {lo hi K : Fin (ns + 1)} {Clo Chi CK LV T : Fin nr} (L : List Bool)
variable (h1 : lo ≠ hi) (h2 : lo ≠ K) (h3 : hi ≠ K) (c1 : Clo ≠ Chi) (c2 : Clo ≠ CK) (c3 : Chi ≠ CK)
variable (hT : T ≠ Clo ∧ T ≠ Chi ∧ T ≠ CK)
include h1 h2 h3 c1 c2 c3 hT

/-- **The copying branch.** -/
theorem cpB_spec (t : Bool) (N1 N2 : Fin nr) (hN1 : N1 ≠ Clo ∧ N1 ≠ Chi ∧ N1 ≠ CK ∧ N1 ≠ T)
    (hN2 : N2 ≠ Clo ∧ N2 ≠ Chi ∧ N2 ≠ CK ∧ N2 ≠ T) (bl bh preh resth restl : List Bool) (out : List Bool)
    (hlo : σ0.st lo = frameP bl ++ restl) (hhi : σ0.st hi = preh ++ frameP bh ++ resth)
    (hn1 : σ0.val N1 = bl.length) (hn2 : σ0.val N2 = bh.length) (hT0 : σ0.val T = 0)
    (hcap : out.length + 2 * bl.length + 2 * bh.length + 3 ≤ cap) (hcl : 2 * bl.length ≤ cap)
    (hch : preh.length + 2 * bh.length ≤ cap) (hp : 1 ≤ preh.length) :
    WExec cap (cpB t lo hi K Clo Chi CK N1 N2 T) (est σ0 lo hi K Clo Chi CK L 0 (preh.length - 1) out)
      (est σ0 lo hi K Clo Chi CK L (2 * bl.length) (preh.length + 2 * bh.length)
        (out ++ [true, t] ++ frameP bl ++ frameP bh ++ [false]))
      (50 * bl.length + 50 * bh.length + 40) := by
  have hsw := est_swap σ0 L h1 h2 h3 c1 c2 c3
  -- step hi to the first copied pair
  have f1 := fwdA_rst cap ((σ0.seth lo 0).setv Clo 0) L h3 c3 (preh.length - 1) out (by omega)
  rw [show preh.length - 1 + 1 = preh.length by omega] at f1
  rw [← hsw, ← hsw] at f1
  -- the tag pair
  have e1 := emitB_rst cap ((σ0.seth hi preh.length).setv Chi preh.length) L h2 c2 0 out true (by omega)
  have e2 := emitB_rst cap ((σ0.seth hi preh.length).setv Chi preh.length) L h2 c2 0 (out ++ [true]) t
    (by simp; omega)
  -- the pairs of lo
  have k1 := copyPairs_rst cap ((σ0.seth hi preh.length).setv Chi preh.length) L h2 c2 N1 T hN1.2.2.2 hN1.1 hN1.2.2.1
    hT.1 hT.2.2 [] bl restl (out ++ [true] ++ [t]) (by simp [hlo]) (by simp [Function.update_apply, hN1.2.1, hn1])
    (by simp [Function.update_apply, hT.2.1, hT0]) (by simp; omega) (by simp; omega)
  simp only [List.length_nil, Nat.zero_add] at k1
  -- the pairs of hi
  have k2 := copyPairs_rst cap ((σ0.seth lo (2 * bl.length)).setv Clo (2 * bl.length)) L h3 c3 N2 T hN2.2.2.2 hN2.2.1
    hN2.2.2.1 hT.2.1 hT.2.2 preh bh resth (out ++ [true] ++ [t] ++ frameP bl) (by simp [hhi, Ne.symm h1])
    (by simp [Function.update_apply, hN2.1, hn2]) (by simp [Function.update_apply, hT.1, hT0]) hch
    (by simp; omega)
  rw [← hsw, ← hsw] at k2
  have e3 := emitB_rst cap ((σ0.seth hi (preh.length + 2 * bh.length)).setv Chi (preh.length + 2 * bh.length)) L h2 c2
    (2 * bl.length) (out ++ [true] ++ [t] ++ frameP bl ++ frameP bh) false (by simp; omega)
  have hall := WExec.seq f1 (WExec.seq e1 (WExec.seq e2 (WExec.seq k1 (WExec.seq k2 e3))))
  unfold cpB
  refine WExec.cast cap hall ?_ (by omega)
  simp [est, List.append_assoc]

/-- **The fixed branch.** -/
theorem fxB_spec (N1 N2 : Fin nr) (hN1 : N1 ≠ Clo ∧ N1 ≠ Chi ∧ N1 ≠ CK ∧ N1 ≠ T)
    (hN2 : N2 ≠ Clo ∧ N2 ≠ Chi ∧ N2 ≠ CK ∧ N2 ≠ T) (n1 n2 phi : ℕ) (out : List Bool)
    (hn1 : σ0.val N1 = n1) (hn2 : σ0.val N2 = n2) (hT0 : σ0.val T = 0)
    (hcap : out.length + 2 * n1 + 2 * n2 + 1 ≤ cap) (hc1 : n1 ≤ cap) (hc2 : n2 ≤ cap) (hph : phi < cap) :
    WExec cap (fxB hi K Chi CK N1 N2 T) (est σ0 lo hi K Clo Chi CK L 0 phi out)
      (est σ0 lo hi K Clo Chi CK L 0 (phi + 1)
        (out ++ frameP (List.replicate n1 true) ++ frameP (List.replicate n2 false) ++ [false]))
      (40 * n1 + 40 * n2 + 30) := by
  have hsw := est_swap σ0 L h1 h2 h3 c1 c2 c3
  have f1 := fwdA_rst cap ((σ0.seth lo 0).setv Clo 0) L h3 c3 phi out hph
  rw [← hsw, ← hsw] at f1
  have p1 := emitPairs_rst cap ((σ0.seth hi (phi + 1)).setv Chi (phi + 1)) L h2 c2 N1 T hN1.2.2.2 hN1.1 hN1.2.2.1
    hT.1 hT.2.2 true n1 0 out (by simp [Function.update_apply, hN1.2.1, hn1])
    (by simp [Function.update_apply, hT.2.1, hT0]) hc1 (by omega)
  have p2 := emitPairs_rst cap ((σ0.seth hi (phi + 1)).setv Chi (phi + 1)) L h2 c2 N2 T hN2.2.2.2 hN2.1 hN2.2.2.1
    hT.1 hT.2.2 false n2 0 (out ++ frameP (List.replicate n1 true)) (by simp [Function.update_apply, hN2.2.1, hn2])
    (by simp [Function.update_apply, hT.2.1, hT0]) hc2 (by simp; omega)
  have e3 := emitB_rst cap ((σ0.seth hi (phi + 1)).setv Chi (phi + 1)) L h2 c2 0
    (out ++ frameP (List.replicate n1 true) ++ frameP (List.replicate n2 false)) false (by simp; omega)
  have hall := WExec.seq f1 (WExec.seq p1 (WExec.seq p2 e3))
  unfold fxB
  refine WExec.cast cap hall rfl (by omega)

end Lvl

section LvlE
variable (cap : ℕ) (σ0 : WState ns nr) {lo hi K : Fin (ns + 1)} {Clo Chi CK LV T : Fin nr} (L : List Bool)
variable (h1 : lo ≠ hi) (h2 : lo ≠ K) (h3 : hi ≠ K) (c1 : Clo ≠ Chi) (c2 : Clo ≠ CK) (c3 : Chi ≠ CK)
variable (hT : T ≠ Clo ∧ T ≠ Chi ∧ T ≠ CK) (hLV : LV ≠ Clo ∧ LV ≠ Chi ∧ LV ≠ CK ∧ LV ≠ T)
include h1 h2 h3 c1 c2 c3 hT hLV

/-- **The level emitter**, from its branch: `hi`'s head skips `ℓ` pairs to the bit cell of pair `ℓ`, the branch
writes `bits` and leaves the heads at `p1`, `p2`, and both heads return. -/
theorem lvlE_spec (Bset Bclr : WM ns nr) (ℓ p1 p2 cB : ℕ) (out bits : List Bool)
    (hlo : σ0.sh lo = 0) (hhi : σ0.sh hi = 0) (hClo : σ0.val Clo = 0) (hChi : σ0.val Chi = 0)
    (hℓ : σ0.val LV = ℓ) (hT0 : σ0.val T = 0) (hcap : 2 * ℓ + 1 < cap) (hp1 : p1 ≤ cap) (hp2 : p2 ≤ cap)
    (hbr : WExec cap (.ifs hi Bset Bclr) (est σ0 lo hi K Clo Chi CK L 0 (2 * ℓ + 1) out)
      (est σ0 lo hi K Clo Chi CK L p1 p2 (out ++ bits)) cB) :
    WExec cap (lvlE lo hi Clo Chi LV T Bset Bclr) (kst σ0 K CK L out) (kst σ0 K CK L (out ++ bits))
      (ℓ * 19 + 3 + 7 * ℓ + 5 + cB + 5 * p1 + 5 * p2 + 6) := by
  have hsw := est_swap σ0 L h1 h2 h3 c1 c2 c3
  rw [← est_kst σ0 L h1 h2 h3 c1 c2 c3 hlo hhi hClo hChi, ← est_kst σ0 L h1 h2 h3 c1 c2 c3 hlo hhi hClo hChi,
    hsw 0 0 out, hsw 0 0 (out ++ bits)]
  have k1 := skipPairs_rst cap ((σ0.seth lo 0).setv Clo 0) L h3 c3 LV T hLV.2.2.2 hLV.2.1 hLV.2.2.1 hT.2.1 hT.2.2
    ℓ 0 out (by simp [Function.update_apply, hLV.1, hℓ]) (by simp [Function.update_apply, hT.1, hT0]) (by omega)
  have f1 := fwdA_rst cap ((σ0.seth lo 0).setv Clo 0) L h3 c3 (0 + 2 * ℓ) out (by omega)
  rw [show 0 + 2 * ℓ + 1 = 2 * ℓ + 1 by omega] at f1
  have f1' := WExec.cast cap f1 (hsw 0 (2 * ℓ + 1) out).symm le_rfl
  have r1 := rewA_rst cap ((σ0.seth hi p2).setv Chi p2) L h2 c2 p1 (out ++ bits) hp1
  have r1' := WExec.cast cap r1 (hsw 0 p2 (out ++ bits)) le_rfl
  have r2 := rewA_rst cap ((σ0.seth lo 0).setv Clo 0) L h3 c3 p2 (out ++ bits) hp2
  have hall := WExec.seq k1 (WExec.seq f1' (WExec.seq hbr (WExec.seq r1' r2)))
  unfold lvlE
  refine WExec.cast cap hall rfl (by omega)

end LvlE

/-! ## The level keys' words -/

theorem binary_zero_rep : ∀ w : ℕ, binary w 0 = List.replicate w false
  | 0 => rfl
  | w + 1 => by rw [binary_succ, binary_zero_rep w]; rfl

theorem binary_ones : ∀ k w : ℕ, k ≤ w → binary w (2 ^ k - 1) = List.replicate k true ++ List.replicate (w - k) false
  | 0, w, _ => by simp [binary_zero_rep]
  | k + 1, w + 1, h => by
    have e1 : (2 ^ (k + 1) - 1) % 2 = 1 := by
      have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega
    have e2 : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by
      have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega
    rw [binary_succ, e1, e2, binary_ones k w (by omega)]
    simp [List.replicate_succ]
  | k + 1, 0, h => absurd h (by omega)

/-- A copied level key: the tag, `V + 1` bits of the low word, `W − V − 2` bits of the high part. -/
theorem frame_lvl (W V q vlo : ℕ) (t : Bool) (hW : V + 2 ≤ W) (hlo : vlo < 2 ^ (V + 1)) :
    frame (binary W (2 * (q * 2 ^ (V + 1) + vlo) + t.toNat)) =
      [true, t] ++ frameP (binary (V + 1) vlo) ++ frameP (binary (W - V - 2) q) ++ [false] := by
  obtain ⟨c, rfl⟩ : ∃ c, W = V + 2 + c := ⟨W - V - 2, by omega⟩
  rw [show V + 2 + c - V - 2 = c by omega, show V + 2 + c = (V + 1 + c) + 1 by ring, frame_tag, binary_add,
    ← binary_mod (V + 1) (q * 2 ^ (V + 1) + vlo)]
  have e1 : (q * 2 ^ (V + 1) + vlo) % 2 ^ (V + 1) = vlo := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo]
  have e2 : (q * 2 ^ (V + 1) + vlo) / 2 ^ (V + 1) = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [e1, e2, frameP_append]
  simp only [List.append_assoc]

/-- A fixed level key: `n1` ones, then zeros. -/
theorem frame_fix (W k : ℕ) (hk : k ≤ W) :
    frame (binary W (2 ^ k - 1)) = frameP (List.replicate k true) ++ frameP (List.replicate (W - k) false) ++ [false] := by
  rw [frame_eq_frameP, binary_ones k W hk, frameP_append]

/-- The low word's first `V + 1` pairs. -/
theorem frame_low (W V v : ℕ) (hW : V + 1 ≤ W) :
    frame (binary W v) = frameP (binary (V + 1) v) ++ (frameP (binary (W - (V + 1)) (v / 2 ^ (V + 1))) ++ [false]) := by
  obtain ⟨c, rfl⟩ : ∃ c, W = V + 1 + c := ⟨W - (V + 1), by omega⟩
  rw [show V + 1 + c - (V + 1) = c by omega, frame_eq_frameP, binary_add, frameP_append]
  simp only [List.append_assoc]

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
