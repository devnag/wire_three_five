import Proof.Wire_3_5.Primitive.SeedFix.C4KWd
import Proof.Wire_3_5.UnionMachine.BinW

/-! # C4KW, part 13: stage B2's kit (products by repeated addition, `Nat.bits` emission, erasure)

Stage B2 writes `wtWord (wsOf MP)`: for every level `λ ≤ J` the framed `Nat.bits` of the cleared weight
`Π_{j ≠ λ} W_j^{2t}` (P3:2280-2281). The products are exponential in `t`, so they live on width-`W` binary words
(C1's `NumOn`, C1.2's in-place `RegRat` passes); a factor `w` (a unary register) multiplies by `w` additions:
* **`addL_spec`** (`C += n·P`), **`mulU_spec`** (`P := p·w`, `C := p·w`), **`powU_spec`** (`P := p·w^e`);
* **`bits_add_pow`** (`Nat.bits (m + 2^i)` for `m < 2^i`), **`emitB_spec`**: from `frame (binary W p)`, append
  `frame (Nat.bits p)` to the output (the trailing zeros held back in a register), the word kept, heads back;
* **`eraseF_spec`**: a framed word overwritten by falses.

Paper quantity of the main type: the cleared weights `W_λ` of the Hb printer's static stream (P3:2280-2281). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (addB zeroB copyB addB_spec zeroB_spec copyB_spec)
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## State algebra -/

theorem sets_same (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) (h : σ.st i = l) : σ.sets i l = σ :=
  WState.eq rfl (by funext j; by_cases hj : j = i <;> simp [WState.sets, Function.update_apply, hj, h]) rfl rfl

theorem sets_sets (σ : WState ns nr) (i : Fin (ns + 1)) (a b : List Bool) : (σ.sets i a).sets i b = σ.sets i b :=
  WState.eq rfl (by funext j; by_cases hj : j = i <;> simp [WState.sets, Function.update_apply, hj]) rfl rfl

theorem sets_setv (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) (r : Fin nr) (x : ℕ) :
    (σ.sets i l).setv r x = (σ.setv r x).sets i l := rfl

theorem numOn_sets (σ : WState ns nr) (i : Fin (ns + 1)) (W v : ℕ) (h0 : σ.sh i = 0) :
    NumOn (σ.sets i (frame (binary W v))) i W v := ⟨by simp [WState.sets], by simpa [WState.sets] using h0⟩

theorem numOn_sets_ne {σ : WState ns nr} {i j : Fin (ns + 1)} {W v : ℕ} (l : List Bool) (h : NumOn σ i W v)
    (hij : i ≠ j) : NumOn (σ.sets j l) i W v :=
  ⟨by simp [WState.sets, Function.update_of_ne hij, h.1], by simpa [WState.sets] using h.2⟩

/-! ## `C += n·P` -/

/-- `n` additions `C += P` (counter `c`). -/
def addL (C P : Fin (ns + 1)) (F R c : Fin nr) : WM ns nr := .whr c (.seq (.dec c) (addB C P F R))

theorem addL_spec (W : ℕ) {C P : Fin (ns + 1)} {F R c : Fin nr} (hCP : C ≠ P) (hFR : F ≠ R) (hcF : c ≠ F)
    (hcR : c ≠ R) (p : ℕ) :
    ∀ (n a : ℕ) (σ : WState ns nr), NumOn σ C W a → NumOn σ P W p → σ.val F = 0 → σ.val R = 0 → σ.val c = n →
      a + n * p < 2 ^ W → 2 * W + 1 ≤ cap → n ≤ cap →
      WExec cap (addL C P F R c) σ ((σ.sets C (frame (binary W (a + n * p)))).setv c 0) (n * (41 * W + 8) + 1)
  | 0, a, σ, hC, _, _, _, hc, _, _, _ => by
    rw [Nat.zero_mul, Nat.add_zero, sets_same σ C _ hC.1, ← hc, wsetv_same]
    exact WExec.mono (WExec.whrF hc) (by omega)
  | n + 1, a, σ, hC, hP, hF, hR, hc, hlt, hW, hn => by
    have t1 := WExec.dec (cap := cap) c σ (by omega)
    rw [hc] at t1
    have hC1 : NumOn (σ.setv c (n + 1 - 1)) C W a := hC
    have hP1 : NumOn (σ.setv c (n + 1 - 1)) P W p := hP
    have t2 := addB_spec cap W hCP hFR (σ.setv c (n + 1 - 1)) a p hC1 hP1 (by simp [Ne.symm hcF, hF])
      (by simp [Ne.symm hcR, hR]) (by nlinarith) hW
    have ih := addL_spec W hCP hFR hcF hcR p n (a + p) ((σ.setv c (n + 1 - 1)).sets C (frame (binary W (a + p))))
      (numOn_sets _ C W _ (by simpa using hC.2)) (numOn_sets_ne _ hP1 (Ne.symm hCP)) (by simp [Ne.symm hcF, hF])
      (by simp [Ne.symm hcR, hR]) (by simp) (by nlinarith) hW (by omega)
    have e : (((σ.setv c (n + 1 - 1)).sets C (frame (binary W (a + p)))).sets C
        (frame (binary W (a + p + n * p)))).setv c 0 = (σ.sets C (frame (binary W (a + (n + 1) * p)))).setv c 0 := by
      rw [sets_sets, sets_setv, sets_setv, wsetv_setv]
      congr 3; ring
    rw [e] at ih
    refine WExec.mono (WExec.whrT (by omega) (WExec.seq t1 t2) ih) ?_
    rw [Nat.add_mul, Nat.one_mul]; omega

/-! ## `P := p·w` -/

/-- `P := P·w` (`C` scratch, counter `c`, temporary `T`). -/
def mulU (P C : Fin (ns + 1)) (F R w c T : Fin nr) : WM ns nr :=
  .seq (zeroB C P F R) (.seq (UnionMachine.BinW.dupR w c T) (.seq (addL C P F R c) (copyB P C F R)))

def mulUCost (W v : ℕ) : ℕ := (v + 3) * (41 * W + 30) + 18 * v

theorem mulU_spec (W : ℕ) {P C : Fin (ns + 1)} {F R w c T : Fin nr} (hPC : P ≠ C) (hFR : F ≠ R) (hcF : c ≠ F)
    (hcR : c ≠ R) (hwc : w ≠ c) (hwT : w ≠ T) (hcT : c ≠ T) (hTF : T ≠ F) (hTR : T ≠ R) (hwF : w ≠ F)
    (hwR : w ≠ R) (σ : WState ns nr) (p v q : ℕ) (hP : NumOn σ P W p) (hC : NumOn σ C W q) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hw : σ.val w = v) (hc : σ.val c = 0) (hT : σ.val T = 0) (hpv : p * v < 2 ^ W)
    (hW : 2 * W + 1 ≤ cap) (hv : v ≤ cap) :
    WExec cap (mulU P C F R w c T) σ ((σ.sets C (frame (binary W (p * v)))).sets P (frame (binary W (p * v))))
      (mulUCost W v) := by
  have t1 := zeroB_spec cap W (Ne.symm hPC) hFR σ q p hC hP hF hR hW
  set σ1 := σ.sets C (frame (binary W 0)) with hσ1
  have t2 := UnionMachine.BinW.dupR_spec cap w c T hwc hwT hcT σ1 v hw hc hT hv
  set σ2 := σ1.setv c v with hσ2
  have hC2 : NumOn σ2 C W 0 := numOn_sets σ C W 0 hC.2
  have hP2 : NumOn σ2 P W p := numOn_sets_ne _ hP hPC
  have t3 := addL_spec cap W (Ne.symm hPC) hFR hcF hcR p v 0 σ2 hC2 hP2 (by simp [hσ2, hσ1, Ne.symm hcF, hF])
    (by simp [hσ2, hσ1, Ne.symm hcR, hR]) (by simp [hσ2]) (by rw [Nat.zero_add, Nat.mul_comm]; exact hpv) hW hv
  set σ3 := (σ2.sets C (frame (binary W (0 + v * p)))).setv c 0 with hσ3
  have hP3 : NumOn σ3 P W p := numOn_sets_ne _ hP2 hPC
  have hC3 : NumOn σ3 C W (0 + v * p) := numOn_sets σ2 C W _ hC2.2
  have t4 := copyB_spec cap W hPC hFR σ3 p (0 + v * p) hP3 hC3 (by simp [hσ3, hσ2, hσ1, Ne.symm hcF, hF])
    (by simp [hσ3, hσ2, hσ1, Ne.symm hcR, hR]) hW
  refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4))) ?_ ?_
  · rw [hσ3, hσ2, hσ1]
    refine WState.eq rfl ?_ ?_ rfl
    · funext j
      simp only [WState.sets, WState.setv, Function.update_apply]
      split_ifs <;> simp_all [Nat.mul_comm]
    · funext r
      simp only [WState.sets, WState.setv, Function.update_apply]
      split_ifs <;> simp_all
  · unfold mulUCost
    have : v * (41 * W + 8) ≤ v * (41 * W + 30) := Nat.mul_le_mul_left _ (by omega)
    nlinarith

/-! ## `P := p·w^e` -/

/-- `e` rounds of `mulU` (counter `k`, from the register `m`). -/
def powU (P C : Fin (ns + 1)) (F R w c T k m : Fin nr) : WM ns nr :=
  .seq (UnionMachine.BinW.dupR m k T) (.whr k (.seq (.dec k) (mulU P C F R w c T)))

theorem powL (W : ℕ) {P C : Fin (ns + 1)} {F R w c T k : Fin nr} (hPC : P ≠ C) (hFR : F ≠ R) (hcF : c ≠ F)
    (hcR : c ≠ R) (hwc : w ≠ c) (hwT : w ≠ T) (hcT : c ≠ T) (hTF : T ≠ F) (hTR : T ≠ R) (hwF : w ≠ F)
    (hwR : w ≠ R) (hkF : k ≠ F) (hkR : k ≠ R) (hkw : k ≠ w) (hkc : k ≠ c) (hkT : k ≠ T) (v : ℕ) (hv1 : 1 ≤ v)
    (hW : 2 * W + 1 ≤ cap) (hv : v ≤ cap) :
    ∀ (i p : ℕ) (σ : WState ns nr), NumOn σ P W p → NumOn σ C W p → σ.val F = 0 → σ.val R = 0 → σ.val w = v →
      σ.val c = 0 → σ.val T = 0 → σ.val k = i → p * v ^ i < 2 ^ W → i ≤ cap →
      WExec cap (.whr k (.seq (.dec k) (mulU P C F R w c T))) σ
        (((σ.sets C (frame (binary W (p * v ^ i)))).sets P (frame (binary W (p * v ^ i)))).setv k 0)
        (i * (mulUCost W v + 4) + 1)
  | 0, p, σ, hP, hC, _, _, _, _, _, hk, _, _ => by
    rw [pow_zero, Nat.mul_one, sets_same σ C _ hC.1, sets_same σ P _ hP.1, ← hk, wsetv_same]
    exact WExec.mono (WExec.whrF hk) (by omega)
  | i + 1, p, σ, hP, hC, hF, hR, hw, hc, hT, hk, hlt, hi => by
    have t1 := WExec.dec (cap := cap) k σ (by omega)
    rw [hk] at t1
    have hpv : p * v < 2 ^ W := by
      have : p * v ≤ p * v ^ (i + 1) := Nat.mul_le_mul_left _ (by
        calc v = v ^ 1 := (pow_one v).symm
          _ ≤ v ^ (i + 1) := Nat.pow_le_pow_right hv1 (by omega))
      omega
    have t2 := mulU_spec cap W hPC hFR hcF hcR hwc hwT hcT hTF hTR hwF hwR (σ.setv k (i + 1 - 1)) p v p hP hC
      (by simp [Ne.symm hkF, hF]) (by simp [Ne.symm hkR, hR]) (by simp [Ne.symm hkw, hw])
      (by simp [Ne.symm hkc, hc]) (by simp [Ne.symm hkT, hT]) hpv hW hv
    set σ1 := ((σ.setv k (i + 1 - 1)).sets C (frame (binary W (p * v)))).sets P (frame (binary W (p * v))) with hσ1
    have ih := powL W hPC hFR hcF hcR hwc hwT hcT hTF hTR hwF hwR hkF hkR hkw hkc hkT v hv1 hW hv i (p * v) σ1
      (numOn_sets _ P W _ (by simpa [hσ1] using hP.2))
      (numOn_sets_ne _ (numOn_sets _ C W _ (by simpa using hC.2)) (Ne.symm hPC))
      (by simp [hσ1, Ne.symm hkF, hF]) (by simp [hσ1, Ne.symm hkR, hR]) (by simp [hσ1, Ne.symm hkw, hw])
      (by simp [hσ1, Ne.symm hkc, hc]) (by simp [hσ1, Ne.symm hkT, hT]) (by simp [hσ1])
      (by rw [Nat.mul_assoc, ← pow_succ']; exact hlt) (by omega)
    have e : ((σ1.sets C (frame (binary W (p * v * v ^ i)))).sets P (frame (binary W (p * v * v ^ i)))).setv k 0 =
        ((σ.sets C (frame (binary W (p * v ^ (i + 1))))).sets P (frame (binary W (p * v ^ (i + 1))))).setv k 0 := by
      rw [hσ1, show p * v * v ^ i = p * v ^ (i + 1) by ring]
      refine WState.eq rfl ?_ ?_ rfl
      · funext j
        simp only [WState.sets, WState.setv, Function.update_apply]
        split_ifs <;> simp_all
      · funext r
        simp only [WState.sets, WState.setv, Function.update_apply]
        split_ifs <;> simp_all
    rw [e] at ih
    refine WExec.mono (WExec.whrT (by omega) (WExec.seq t1 t2) ih) ?_
    rw [Nat.add_mul, Nat.one_mul]; omega

def powUCost (W v e : ℕ) : ℕ := 18 * e + 3 + 1 + (e * (mulUCost W v + 4) + 1)

theorem powU_spec (W : ℕ) {P C : Fin (ns + 1)} {F R w c T k m : Fin nr} (hPC : P ≠ C) (hFR : F ≠ R) (hcF : c ≠ F)
    (hcR : c ≠ R) (hwc : w ≠ c) (hwT : w ≠ T) (hcT : c ≠ T) (hTF : T ≠ F) (hTR : T ≠ R) (hwF : w ≠ F)
    (hwR : w ≠ R) (hkF : k ≠ F) (hkR : k ≠ R) (hkw : k ≠ w) (hkc : k ≠ c) (hkT : k ≠ T) (hmk : m ≠ k) (hmT : m ≠ T)
    (σ : WState ns nr) (p v e : ℕ) (hv1 : 1 ≤ v) (hP : NumOn σ P W p) (hC : NumOn σ C W p) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hw : σ.val w = v) (hc : σ.val c = 0) (hT : σ.val T = 0) (hk : σ.val k = 0)
    (hm : σ.val m = e) (hlt : p * v ^ e < 2 ^ W) (hW : 2 * W + 1 ≤ cap) (hv : v ≤ cap) (he : e ≤ cap) :
    WExec cap (powU P C F R w c T k m) σ
      ((σ.sets C (frame (binary W (p * v ^ e)))).sets P (frame (binary W (p * v ^ e)))) (powUCost W v e) := by
  have t1 := UnionMachine.BinW.dupR_spec cap m k T hmk hmT hkT σ e hm hk hT he
  have t2 := powL cap W hPC hFR hcF hcR hwc hwT hcT hTF hTR hwF hwR hkF hkR hkw hkc hkT v hv1 hW hv e p (σ.setv k e)
    hP hC (by simp [Ne.symm hkF, hF]) (by simp [Ne.symm hkR, hR]) (by simp [Ne.symm hkw, hw])
    (by simp [Ne.symm hkc, hc]) (by simp [Ne.symm hkT, hT]) (by simp) hlt he
  refine WExec.cast cap (WExec.seq t1 t2) ?_ le_rfl
  rw [sets_setv, sets_setv, wsetv_setv, show σ.setv k 0 = σ from by rw [← hk]; exact wsetv_same σ k]

/-! ## `Nat.bits` -/

theorem bits_length_le (m i : ℕ) (h : m < 2 ^ i) : (Nat.bits m).length ≤ i := by
  rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr h

theorem bits_add_pow : ∀ (i m : ℕ), m < 2 ^ i →
    Nat.bits (m + 2 ^ i) = Nat.bits m ++ List.replicate (i - (Nat.bits m).length) false ++ [true]
  | 0, m, h => by
    have : m = 0 := by simpa using h
    subst this; simp [Nat.zero_bits]
  | i + 1, m, h => by
    have h2 : m / 2 < 2 ^ i := by rw [pow_succ] at h; omega
    have ih := bits_add_pow i (m / 2) h2
    have e1 : m + 2 ^ (i + 1) = Nat.bit (m % 2 == 1) (m / 2 + 2 ^ i) := by
      rw [Nat.bit_val, pow_succ]; rcases Nat.mod_two_eq_zero_or_one m with h0 | h0 <;> simp [h0] <;> omega
    rw [e1, Nat.bits_append_bit _ _ (by intro hz; have := Nat.two_pow_pos i; omega), ih]
    by_cases hm : m = 0
    · subst hm; simp [Nat.zero_bits, List.replicate_succ]
    · have e2 : m = Nat.bit (m % 2 == 1) (m / 2) := by
        rw [Nat.bit_val]; rcases Nat.mod_two_eq_zero_or_one m with h0 | h0 <;> simp [h0] <;> omega
      have hb : Nat.bits m = (m % 2 == 1) :: Nat.bits (m / 2) := by
        conv_lhs => rw [e2]
        rw [Nat.bits_append_bit _ _ (by intro hz; rcases Nat.mod_two_eq_zero_or_one m with h0 | h0 <;> simp [h0] <;> omega)]
      rw [hb, List.length_cons,
        show i + 1 - ((Nat.bits (m / 2)).length + 1) = i - (Nat.bits (m / 2)).length by omega]
      rfl

theorem bits_mod_succ (p i : ℕ) :
    Nat.bits (p % 2 ^ (i + 1)) = if p / 2 ^ i % 2 = 1 then
      Nat.bits (p % 2 ^ i) ++ List.replicate (i - (Nat.bits (p % 2 ^ i)).length) false ++ [true]
    else Nat.bits (p % 2 ^ i) := by
  rw [Nat.mod_pow_succ]
  rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ i) with h0 | h0
  · rw [h0]; simp
  · rw [h0, if_pos rfl, Nat.mul_one]
    exact bits_add_pow i _ (Nat.mod_lt _ (Nat.two_pow_pos i))

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
