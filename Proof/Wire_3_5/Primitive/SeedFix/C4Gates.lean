import Proof.Wire_3_5.Primitive.SeedFix.TabConv
import Proof.Wire_3_5.Primitive.Writers.WriteNat
import Proof.Wire_3_5.Primitive.Writers.Emit

/-! # G1, the gate converter, part 1: a table number's length pass (P3:1645-1650, 1655-1664)

C3a reads the pool's gates as one native stream (`C4Geo.gateField G`: `natWord |G|`, the framed arity, then each
gate's framed native word `tabGW g = natWord n ++ (weights).flatMap intWord ++ intWord (θ − 1)`), while the data stage
leaves each slot's gates as the table `gatesW h G` (per gate a marker, the P/N pair of `−θ`, the P/N pairs of the
weights, in `h`-bit framed words). "Evaluating at most `n` coordinate functions and adding polynomial-bit integers
takes polynomial time" (P3:1648-1650): the converter reads each `h`-bit framed word twice. This part is the first
read: through a 1-bit carry map (copy, increment, decrement: TabRef's `cmap`), it computes the position after the
last `1` of the mapped word (`accLZ`), which is its `natBitLength` (**`accLZ_binary`**), and counts the word's cells
for the rewind.

Paper quantity of the main type (`lenLoop_spec`, `accLZ_binary`): the bit length `natBitLength v` of a table number,
the length field of its native word `natWord v`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Gates
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

/-! ## The length accumulator -/

/-- Scanning bits left to right: `L` is the position after the last `1`, `Z` the zeros since. -/
def accLZ : List Bool → ℕ × ℕ → ℕ × ℕ
  | [], s => s
  | b :: bs, s => accLZ bs (if b then (s.1 + s.2 + 1, 0) else (s.1, s.2 + 1))

theorem accLZ_sum : ∀ (bs : List Bool) (l z : ℕ), (accLZ bs (l, z)).1 + (accLZ bs (l, z)).2 = l + z + bs.length
  | [], l, z => rfl
  | b :: bs, l, z => by
    cases b
    · simp only [accLZ, Bool.false_eq_true, if_false]
      rw [accLZ_sum bs l (z + 1)]; simp; omega
    · simp only [accLZ, if_true]
      rw [accLZ_sum bs (l + z + 1) 0]; simp; omega

theorem accLZ_fst_ge : ∀ (bs : List Bool) (l z : ℕ), l ≤ (accLZ bs (l, z)).1
  | [], _, _ => le_rfl
  | b :: bs, l, z => by
    cases b
    · exact accLZ_fst_ge bs l (z + 1)
    · exact le_trans (by omega) (accLZ_fst_ge bs (l + z + 1) 0)

theorem accLZ_le (bs : List Bool) (l z : ℕ) : (accLZ bs (l, z)).2 ≤ z + bs.length := by
  have h := accLZ_sum bs l z
  have h2 := accLZ_fst_ge bs l z
  omega

theorem accLZ_zeros : ∀ (bs : List Bool) (k l z : ℕ),
    (accLZ (bs ++ List.replicate k false) (l, z)).1 = (accLZ bs (l, z)).1
  | [], k, l, z => by
    simp only [List.nil_append, accLZ]
    induction k generalizing z with
    | zero => rfl
    | succ k ih => simp only [List.replicate_succ, accLZ, Bool.false_eq_true, if_false]; exact ih (z + 1)
  | b :: bs, k, l, z => by
    simp only [List.cons_append, accLZ]
    exact accLZ_zeros bs k _ _

theorem accLZ_true (bs : List Bool) : (accLZ (bs ++ [true]) (0, 0)).1 = bs.length + 1 := by
  have key : ∀ (bs : List Bool) (l z : ℕ), (accLZ (bs ++ [true]) (l, z)).1 = l + z + bs.length + 1 := by
    intro bs
    induction bs with
    | nil => intro l z; simp [accLZ]
    | cons b bs ih =>
      intro l z
      cases b
      · simp only [List.cons_append, accLZ, Bool.false_eq_true, if_false]; rw [ih]; simp; omega
      · simp only [List.cons_append, accLZ, if_true]; rw [ih]; simp; omega
  rw [key]; omega

theorem binary_top (v : ℕ) (hv : 1 ≤ v) :
    binary (natBitLength v) v = binary (natBitLength v - 1) v ++ [true] := by
  have hL : 1 ≤ natBitLength v := by unfold natBitLength; omega
  have e := CompilerMachine.Pool.binary_append' (natBitLength v - 1) 1 v
  rw [Nat.sub_add_cancel hL] at e
  rw [e]
  congr 1
  have hlt := CompilerMachine.Pool.lt_pow_natBitLength v
  have hge : 2 ^ (natBitLength v - 1) ≤ v := by
    unfold natBitLength
    simp only [Nat.add_sub_cancel]
    exact Nat.pow_log_le_self 2 (by omega)
  have hq : v / 2 ^ (natBitLength v - 1) = 1 := by
    have h2 : v < 2 * 2 ^ (natBitLength v - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hL]; exact hlt
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [SignedSortKey.binary, hq]

/-- **The pass computes the bit length**: over the `h`-bit word of `v`, the position after the last `1` is
`natBitLength v` (or `0` for `v = 0`). -/
theorem accLZ_binary (h v : ℕ) (hh : 1 ≤ h) (hv : v < 2 ^ h) :
    (accLZ (binary h v) (0, 0)).1 = if v = 0 then 0 else natBitLength v := by
  rw [CompilerMachine.Pool.binary_pad v h hh hv, accLZ_zeros]
  split_ifs with h0
  · subst h0
    have e : binary (natBitLength 0) 0 = List.replicate (natBitLength 0) false := by
      simp [natBitLength, SignedSortKey.binary]
    rw [e]
    have : ∀ k z, (accLZ (List.replicate k false) (0, z)).1 = 0 := by
      intro k
      induction k with
      | zero => intro z; rfl
      | succ k ih => intro z; simp only [List.replicate_succ, accLZ, Bool.false_eq_true, if_false]; exact ih _
    exact this _ 0
  · rw [binary_top v (by omega), accLZ_true, binary_length]
    have : 1 ≤ natBitLength v := by unfold natBitLength; omega
    omega

/-! ## The pass's state -/

section Pass1
variable {ns nr : ℕ} (cap : ℕ) (I : Fin (ns + 1)) (L Z F H2 : Fin nr)

/-- The pass's state: the input head at `p`, `L, Z, F, H2` at `l, z, f, h`. -/
def u1 (σ : WState ns nr) (p l z f h : ℕ) : WState ns nr :=
  ((((σ.seth I p).setv L l).setv Z z).setv F f).setv H2 h

variable {L Z F H2}
variable (hLZ : L ≠ Z) (hLF : L ≠ F) (hLH : L ≠ H2) (hZF : Z ≠ F) (hZH : Z ≠ H2) (hFH : F ≠ H2)
include hLZ hLF hLH hZF hZH hFH

theorem u1_u1 (σ : WState ns nr) (p l z f h p' l' z' f' h' : ℕ) :
    u1 I L Z F H2 (u1 I L Z F H2 σ p l z f h) p' l' z' f' h' = u1 I L Z F H2 σ p' l' z' f' h' := by
  apply WState.eq
  · funext j; simp only [u1, WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> rfl
  · rfl
  · funext r; simp only [u1, WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs <;> rfl
  · rfl

theorem u1_val_L (σ : WState ns nr) (p l z f h : ℕ) : (u1 I L Z F H2 σ p l z f h).val L = l := by
  simp [u1, Function.update_apply, hLZ, hLF, hLH]
theorem u1_val_Z (σ : WState ns nr) (p l z f h : ℕ) : (u1 I L Z F H2 σ p l z f h).val Z = z := by
  simp [u1, Function.update_apply, hZF, hZH]
theorem u1_val_F (σ : WState ns nr) (p l z f h : ℕ) : (u1 I L Z F H2 σ p l z f h).val F = f := by
  simp [u1, Function.update_apply, hFH]
theorem u1_val_H (σ : WState ns nr) (p l z f h : ℕ) : (u1 I L Z F H2 σ p l z f h).val H2 = h := by
  simp [u1, Function.update_apply]

end Pass1

/-! ## The length pass -/

section Pass1Prog
variable {ns nr : ℕ} (cap : ℕ) (I : Fin (ns + 1)) (L Z F H2 : Fin nr) (out nxt : Bool → Bool → Bool)

/-- One mapped bit's update of `L, Z`. -/
def luStep (o : Bool) : WM ns nr := if o then .seq (WM.move Z L) (.inc L) else .inc Z

/-- One leaf: the bit `b` and the carry `c` are known. -/
def lf (b c : Bool) : WM ns nr := .seq (luStep L Z (out b c)) (setFlag F (nxt b c))

/-- Branch on the bit and the carry. -/
def bitL : WM ns nr :=
  .ifs I (.ifr F (lf L Z F out nxt true true) (lf L Z F out nxt true false))
    (.ifr F (lf L Z F out nxt false true) (lf L Z F out nxt false false))

/-- One framed cell pair: the marker, the bit. -/
def lenBody : WM ns nr := .seq (.fwd I) (.seq (bitL I L Z F out nxt) (.seq (.inc H2) (.seq (.inc H2) (.fwd I))))

/-- **The length pass** over one framed word: `L, Z` over the mapped bits, `F` the carry, `H2` the word's cells. -/
def lenPass : WM ns nr := .seq (.whs I (lenBody I L Z F H2 out nxt)) (.seq (.fwd I) (.inc H2))

/-- The step of the accumulator. -/
def stepLZ (o : Bool) (s : ℕ × ℕ) : ℕ × ℕ := if o then (s.1 + s.2 + 1, 0) else (s.1, s.2 + 1)

variable {L Z F H2}
variable (hLZ : L ≠ Z) (hLF : L ≠ F) (hLH : L ≠ H2) (hZF : Z ≠ F) (hZH : Z ≠ H2) (hFH : F ≠ H2)

include hLZ in
theorem luStep_spec (o : Bool) (σ : WState ns nr) (l z : ℕ) (hl : σ.val L = l) (hz : σ.val Z = z)
    (hc : l + z + 1 ≤ cap) :
    WExec cap (luStep L Z o) σ ((σ.setv L (stepLZ o (l, z)).1).setv Z (stepLZ o (l, z)).2) (7 * z + 5) := by
  cases o
  · have h := WExec.inc (cap := cap) Z σ (by omega)
    simp only [luStep, Bool.false_eq_true, if_false, stepLZ]
    refine WExec.cast cap h ?_ (by omega)
    rw [hz, ← hl, wsetv_same]
  · have h1 := wmove_spec cap Z L (Ne.symm hLZ) z σ hz (by omega) (by omega)
    have h2 := WExec.inc (cap := cap) L ((σ.setv Z 0).setv L (σ.val L + σ.val Z)) (by simp; omega)
    simp only [luStep, if_true, stepLZ]
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext r
      simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all <;> omega
    · rfl

include hLZ hLF hZF in
theorem lf_spec (b c : Bool) (σ : WState ns nr) (l z : ℕ) (hl : σ.val L = l) (hz : σ.val Z = z)
    (hF : σ.val F = c.toNat) (hc : l + z + 1 ≤ cap) :
    WExec cap (lf L Z F out nxt b c) σ
      (((σ.setv L (stepLZ (out b c) (l, z)).1).setv Z (stepLZ (out b c) (l, z)).2).setv F (nxt b c).toNat)
      (7 * z + 10) := by
  have h1 := luStep_spec cap hLZ (out b c) σ l z hl hz hc
  have h2 := setFlag_spec cap F (nxt b c) c ((σ.setv L (stepLZ (out b c) (l, z)).1).setv Z (stepLZ (out b c) (l, z)).2)
    (by simp [Function.update_apply, Ne.symm hLF, Ne.symm hZF, hF]) (by omega)
  exact WExec.mono (WExec.seq h1 h2) (by omega)

include hLZ hLF hZF in
theorem bitL_spec (b c : Bool) (σ : WState ns nr) (l z : ℕ) (hb : wbit σ I = b) (hl : σ.val L = l)
    (hz : σ.val Z = z) (hF : σ.val F = c.toNat) (hc : l + z + 1 ≤ cap) :
    WExec cap (bitL I L Z F out nxt) σ
      (((σ.setv L (stepLZ (out b c) (l, z)).1).setv Z (stepLZ (out b c) (l, z)).2).setv F (nxt b c).toNat)
      (7 * z + 12) := by
  have h := lf_spec cap out nxt hLZ hLF hZF b c σ l z hl hz hF hc
  have hF0 : c = false → σ.val F = 0 := fun e => by rw [hF, e]; rfl
  have hF1 : c = true → σ.val F ≠ 0 := fun e => by rw [hF, e]; simp
  cases b <;> cases c
  · exact WExec.mono (WExec.ifsF hb (WExec.ifrF (hF0 rfl) h)) (by omega)
  · exact WExec.mono (WExec.ifsF hb (WExec.ifrT (hF1 rfl) h)) (by omega)
  · exact WExec.mono (WExec.ifsT hb (WExec.ifrF (hF0 rfl) h)) (by omega)
  · exact WExec.mono (WExec.ifsT hb (WExec.ifrT (hF1 rfl) h)) (by omega)

include hLZ hLF hLH hZF hZH hFH in
theorem lenBody_spec (b c : Bool) (σ : WState ns nr) (p l z h : ℕ) (hp : σ.sh I = p)
    (hb : readTapeBit (σ.st I) (p + 1) = b) (hl : σ.val L = l) (hz : σ.val Z = z) (hF : σ.val F = c.toNat)
    (hh : σ.val H2 = h) (hc : l + z + 1 ≤ cap) (hch : h + 2 < cap) :
    WExec cap (lenBody I L Z F H2 out nxt) σ
      (u1 I L Z F H2 σ (p + 2) (stepLZ (out b c) (l, z)).1 (stepLZ (out b c) (l, z)).2 (nxt b c).toNat (h + 2))
      (7 * z + 30) := by
  have s1 := WExec.fwd (cap := cap) I σ
  set σ1 := σ.seth I (σ.sh I + 1) with hσ1
  have s2 := bitL_spec cap I out nxt hLZ hLF hZF b c σ1 l z (by simp [wbit, σ1, hp, hb]) (by simp [σ1, hl])
    (by simp [σ1, hz]) (by simp [σ1, hF]) hc
  set σ2 := ((σ1.setv L (stepLZ (out b c) (l, z)).1).setv Z (stepLZ (out b c) (l, z)).2).setv F (nxt b c).toNat
    with hσ2
  have e2 : σ2.val H2 = h := by simp [σ2, σ1, Function.update_apply, Ne.symm hLH, Ne.symm hZH, Ne.symm hFH, hh]
  have s3 := WExec.inc (cap := cap) H2 σ2 (by omega)
  have s4 := WExec.inc (cap := cap) H2 (σ2.setv H2 (σ2.val H2 + 1)) (by simp; omega)
  have s5 := WExec.fwd (cap := cap) I ((σ2.setv H2 (σ2.val H2 + 1)).setv H2 ((σ2.setv H2 (σ2.val H2 + 1)).val H2 + 1))
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (by omega)
  apply WState.eq
  · funext j; simp only [u1, σ2, σ1, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · funext r; simp only [u1, σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

include hLZ hLF hLH hZF hZH hFH in
theorem u1_self (σ : WState ns nr) : u1 I L Z F H2 σ (σ.sh I) (σ.val L) (σ.val Z) (σ.val F) (σ.val H2) = σ := by
  apply WState.eq
  · funext j; simp only [u1, WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> simp_all
  · rfl
  · funext r; simp only [u1, WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs <;> simp_all
  · rfl

include hLZ hLF hLH hZF hZH hFH in
/-- **The length loop** over the framed bits `sfx`: `L, Z` accumulate over the mapped bits, the carry and `H2`
advance, the head reaches the terminator. -/
theorem lenLoop_spec (hcap : 1 ≤ cap) : ∀ (sfx pre rest : List Bool) (σ : WState ns nr) (c : Bool) (l z h B : ℕ),
    σ.st I = pre ++ (frameP sfx ++ false :: rest) → σ.sh I = pre.length →
    σ.val L = l → σ.val Z = z → σ.val F = c.toNat → σ.val H2 = h →
    l + z + sfx.length ≤ cap → h + 2 * sfx.length + 1 ≤ cap → z + sfx.length ≤ B →
    WExec cap (.whs I (lenBody I L Z F H2 out nxt)) σ
      (u1 I L Z F H2 σ (pre.length + 2 * sfx.length) (accLZ (cmap out nxt sfx c) (l, z)).1
        (accLZ (cmap out nxt sfx c) (l, z)).2 (cfin nxt sfx c).toNat (h + 2 * sfx.length))
      (sfx.length * (7 * B + 40) + 1)
  | [], pre, rest, σ, c, l, z, h, B, hst, hsh, hl, hz, hF, hh, _, _, _ => by
    have hr : wbit σ I = false := by
      simp only [wbit, hst, hsh]
      have := rd_shift pre (frameP [] ++ false :: rest) 0
      simp only [Nat.add_zero] at this
      rw [this]; rfl
    have e : u1 I L Z F H2 σ (pre.length + 2 * ([] : List Bool).length) (accLZ (cmap out nxt [] c) (l, z)).1
        (accLZ (cmap out nxt [] c) (l, z)).2 (cfin nxt [] c).toNat (h + 2 * ([] : List Bool).length) = σ := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, cmap, accLZ, cfin]
      rw [← hsh, ← hl, ← hz, ← hF, ← hh]
      exact u1_self I hLZ hLF hLH hZF hZH hFH σ
    rw [e]
    exact WExec.mono (WExec.whsF hr) (by omega)
  | b :: sfx, pre, rest, σ, c, l, z, h, B, hst, hsh, hl, hz, hF, hh, hc1, hc2, hB => by
    have hm : wbit σ I = true := by
      simp only [wbit, hst, hsh]
      have := rd_marker pre (b :: sfx) (false :: rest) 0 (by simp)
      simpa using this
    have hbit : readTapeBit (σ.st I) (pre.length + 1) = b := by
      rw [hst]
      have := rd_bit pre (b :: sfx) (false :: rest) 0 (by simp)
      simpa using this
    simp only [List.length_cons] at hc1 hc2 hB
    have s1 := lenBody_spec cap I out nxt hLZ hLF hLH hZF hZH hFH b c σ pre.length l z h hsh hbit hl hz hF hh
      (by omega) (by omega)
    set σ' := u1 I L Z F H2 σ (pre.length + 2) (stepLZ (out b c) (l, z)).1 (stepLZ (out b c) (l, z)).2
      (nxt b c).toNat (h + 2) with hσ'
    have hsz : (stepLZ (out b c) (l, z)).1 + (stepLZ (out b c) (l, z)).2 = l + z + 1 := by
      unfold stepLZ; split_ifs <;> simp <;> omega
    have hz2 : (stepLZ (out b c) (l, z)).2 ≤ z + 1 := by unfold stepLZ; split_ifs <;> simp
    have s2 := lenLoop_spec hcap sfx (pre ++ [true, b]) rest σ' (nxt b c) (stepLZ (out b c) (l, z)).1
      (stepLZ (out b c) (l, z)).2 (h + 2) B
      (by rw [hσ']; simp only [u1, WState.setv_st, WState.seth_st]; rw [hst]; simp [frameP])
      (by rw [hσ']; simp [u1] <;> omega)
      (u1_val_L I hLZ hLF hLH hZF hZH hFH σ _ _ _ _ _)
      (u1_val_Z I hLZ hLF hLH hZF hZH hFH σ _ _ _ _ _)
      (u1_val_F I hLZ hLF hLH hZF hZH hFH σ _ _ _ _ _)
      (u1_val_H I hLZ hLF hLH hZF hZH hFH σ _ _ _ _ _)
      (by omega) (by omega) (by omega)
    rw [hσ', u1_u1 I hLZ hLF hLH hZF hZH hFH] at s2
    have hlen : (pre ++ [true, b]).length + 2 * sfx.length = pre.length + 2 * (sfx.length + 1) := by simp; omega
    rw [hlen, show h + 2 + 2 * sfx.length = h + 2 * (sfx.length + 1) by omega] at s2
    refine WExec.mono (WExec.whsT hm s1 s2) ?_
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end Pass1Prog

section Pass1Wrap
variable {ns nr : ℕ} (cap : ℕ) (I : Fin (ns + 1)) {L Z F H2 : Fin nr} (out nxt : Bool → Bool → Bool)
variable (hLZ : L ≠ Z) (hLF : L ≠ F) (hLH : L ≠ H2) (hZF : Z ≠ F) (hZH : Z ≠ H2) (hFH : F ≠ H2)

include hLZ hLF hLH hZF hZH hFH in
/-- **The length pass** from cleared registers: the head past the word, `L, Z` over the mapped bits, `F` the final
carry, `H2 = 2|bs| + 1` (the word's cells). -/
theorem lenPass_spec (hcap : 1 ≤ cap) (bs pre rest : List Bool) (σ : WState ns nr) (c : Bool) (B : ℕ)
    (hst : σ.st I = pre ++ (frameP bs ++ false :: rest)) (hsh : σ.sh I = pre.length)
    (hl : σ.val L = 0) (hz : σ.val Z = 0) (hF : σ.val F = c.toNat) (hh : σ.val H2 = 0)
    (hc2 : 2 * bs.length + 2 ≤ cap) (hB : bs.length ≤ B) :
    WExec cap (lenPass I L Z F H2 out nxt) σ
      (u1 I L Z F H2 σ (pre.length + 2 * bs.length + 1) (accLZ (cmap out nxt bs c) (0, 0)).1
        (accLZ (cmap out nxt bs c) (0, 0)).2 (cfin nxt bs c).toNat (2 * bs.length + 1))
      (bs.length * (7 * B + 40) + 7) := by
  have s1 := lenLoop_spec cap I out nxt hLZ hLF hLH hZF hZH hFH hcap bs pre rest σ c 0 0 0 B hst hsh hl hz hF hh
    (by omega) (by omega) (by omega)
  set τ := u1 I L Z F H2 σ (pre.length + 2 * bs.length) (accLZ (cmap out nxt bs c) (0, 0)).1
    (accLZ (cmap out nxt bs c) (0, 0)).2 (cfin nxt bs c).toNat (0 + 2 * bs.length) with hτ
  have s2 := WExec.fwd (cap := cap) I τ
  have hτH : (τ.seth I (τ.sh I + 1)).val H2 = 2 * bs.length := by
    simp only [WState.seth_val, hτ]; rw [u1_val_H I hLZ hLF hLH hZF hZH hFH]; omega
  have s3 := WExec.inc (cap := cap) H2 (τ.seth I (τ.sh I + 1)) (by rw [hτH]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by omega)
  rw [hτH]
  apply WState.eq
  · funext j; simp only [hτ, u1, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · funext r; simp only [hτ, u1, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

end Pass1Wrap

/-! ## The emitting pass -/

section Pass2Prog
variable {ns nr : ℕ} (cap : ℕ) (I O : Fin (ns + 1)) (OP L2 F : Fin nr) (out nxt : Bool → Bool → Bool)

/-- One emitted bit: its two-framed cells `T T T o`, the carry updated. -/
def lfE (b c : Bool) : WM ns nr :=
  .seq (PrimAsm.Emit.emitW O OP [true, true, true, out b c]) (setFlag F (nxt b c))

def bitE : WM ns nr :=
  .ifs I (.ifr F (lfE O OP F out nxt true true) (lfE O OP F out nxt true false))
    (.ifr F (lfE O OP F out nxt false true) (lfE O OP F out nxt false false))

def emitBody : WM ns nr := .seq (.dec L2) (.seq (.fwd I) (.seq (bitE I O OP F out nxt) (.fwd I)))

/-- Skip the remaining framed cells and the terminator. -/
def skipRest : WM ns nr := .seq (.whs I (.seq (.fwd I) (.fwd I))) (.fwd I)

/-- **The emitting pass**: `L2` mapped bits emitted two-framed, then the rest of the word skipped. -/
def bitsPass : WM ns nr := .seq (.whr L2 (emitBody I O OP L2 F out nxt)) (skipRest I)

/-- The emitting pass's state: `w` appended to `O`, the head at `p`, `L2, F` at `k, f`. -/
def u2 (σ : WState ns nr) (p k f : ℕ) (w : List Bool) : WState ns nr :=
  (((PrimAsm.WriteNat.appendO σ O OP w).seth I p).setv L2 k).setv F f

variable {OP L2 F}
variable (hIO : I ≠ O) (hOL : OP ≠ L2) (hOF : OP ≠ F) (hLF : L2 ≠ F)

theorem appendO_seth (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) (u : List Bool) (hi : i ≠ O) :
    PrimAsm.WriteNat.appendO (σ.seth i x) O OP u = (PrimAsm.WriteNat.appendO σ O OP u).seth i x := by
  apply WState.eq
  · funext j; simp only [PrimAsm.WriteNat.appendO_sh, WState.seth_sh, Function.update_apply]
    split_ifs with h1 h2 <;> simp_all
  · simp
  · simp
  · simp

include hIO hOL hOF hLF in
theorem u2_u2 (σ : WState ns nr) (p k f p' k' f' : ℕ) (w w' : List Bool) :
    u2 I O OP L2 F (u2 I O OP L2 F σ p k f w) p' k' f' w' = u2 I O OP L2 F σ p' k' f' (w ++ w') := by
  unfold u2
  rw [PrimAsm.WriteNat.appendO_setv _ O OP F (Ne.symm hOF), PrimAsm.WriteNat.appendO_setv _ O OP L2 (Ne.symm hOL),
    appendO_seth O _ I p w' hIO, PrimAsm.WriteNat.appendO_append]
  apply WState.eq
  · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> rfl
  · rfl
  · funext r; simp only [WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs <;> rfl
  · rfl

include hIO hOL hOF hLF in
theorem u2_self (σ : WState ns nr) : u2 I O OP L2 F σ (σ.sh I) (σ.val L2) (σ.val F) [] = σ := by
  unfold u2
  rw [PrimAsm.WriteNat.appendO_nil]
  apply WState.eq
  · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> simp_all
  · rfl
  · funext r; simp only [WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs <;> simp_all
  · rfl

include hOF in
theorem lfE_spec (b c : Bool) (σ : WState ns nr) (hF : σ.val F = c.toNat) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val OP + 4 ≤ cap) (hcap : 1 ≤ cap) :
    WExec cap (lfE O OP F out nxt b c) σ
      ((PrimAsm.WriteNat.appendO σ O OP [true, true, true, out b c]).setv F (nxt b c).toNat) 37 := by
  have h1 := PrimAsm.Emit.emitW_spec cap O OP [true, true, true, out b c] σ hO (by simpa using hc)
  have h2 := setFlag_spec cap F (nxt b c) c (PrimAsm.WriteNat.appendO σ O OP [true, true, true, out b c])
    (by simp [Function.update_apply, Ne.symm hOF, hF]) hcap
  exact WExec.mono (WExec.seq h1 h2) (by simp)

include hOF in
theorem bitE_spec (b c : Bool) (σ : WState ns nr) (hb : wbit σ I = b) (hF : σ.val F = c.toNat)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + 4 ≤ cap) (hcap : 1 ≤ cap) :
    WExec cap (bitE I O OP F out nxt) σ
      ((PrimAsm.WriteNat.appendO σ O OP [true, true, true, out b c]).setv F (nxt b c).toNat) 39 := by
  have h := lfE_spec cap O out nxt hOF b c σ hF hO hc hcap
  have hF0 : c = false → σ.val F = 0 := fun e => by rw [hF, e]; rfl
  have hF1 : c = true → σ.val F ≠ 0 := fun e => by rw [hF, e]; simp
  cases b <;> cases c
  · exact WExec.mono (WExec.ifsF hb (WExec.ifrF (hF0 rfl) h)) (by omega)
  · exact WExec.mono (WExec.ifsF hb (WExec.ifrT (hF1 rfl) h)) (by omega)
  · exact WExec.mono (WExec.ifsT hb (WExec.ifrF (hF0 rfl) h)) (by omega)
  · exact WExec.mono (WExec.ifsT hb (WExec.ifrT (hF1 rfl) h)) (by omega)

include hIO hOL hOF hLF in
theorem emitBody_spec (b c : Bool) (σ : WState ns nr) (p k : ℕ) (hp : σ.sh I = p)
    (hb : readTapeBit (σ.st I) (p + 1) = b) (hk : σ.val L2 = k + 1) (hF : σ.val F = c.toNat)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + 4 ≤ cap) (hcap : 1 ≤ cap) (hkc : k + 1 ≤ cap) :
    WExec cap (emitBody I O OP L2 F out nxt) σ
      (u2 I O OP L2 F σ (p + 2) k (nxt b c).toNat [true, true, true, out b c]) 45 := by
  have s1 := WExec.dec (cap := cap) L2 σ (by omega)
  have s2 := WExec.fwd (cap := cap) I (σ.setv L2 (σ.val L2 - 1))
  set σ2 := (σ.setv L2 (σ.val L2 - 1)).seth I ((σ.setv L2 (σ.val L2 - 1)).sh I + 1) with hσ2
  have s3 := bitE_spec cap I O out nxt hOF b c σ2 (by simp [wbit, σ2, hp, hb]) (by simp [σ2, Function.update_apply,
    Ne.symm hLF, hF]) (by simp [σ2, Function.update_apply, hIO.symm, hO]) (by simp [σ2, Function.update_apply, hOL, hc])
    hcap
  have s4 := WExec.fwd (cap := cap) I ((PrimAsm.WriteNat.appendO σ2 O OP [true, true, true, out b c]).setv F
    (nxt b c).toNat)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (by omega)
  simp only [hσ2, u2]
  rw [appendO_seth O _ I _ _ hIO, PrimAsm.WriteNat.appendO_setv _ O OP L2 (Ne.symm hOL)]
  apply WState.eq
  · funext j; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · funext r; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

end Pass2Prog

/-- Each bit as its two-framed cells `T T T b`. -/
def quad (x : List Bool) : List Bool := x.flatMap fun b => [true, true, true, b]

theorem quad_cons (b : Bool) (x : List Bool) : quad (b :: x) = [true, true, true, b] ++ quad x := rfl
theorem quad_nil : quad [] = [] := rfl
theorem quad_append (x y : List Bool) : quad (x ++ y) = quad x ++ quad y := by simp [quad]

@[simp] theorem quad_length (x : List Bool) : (quad x).length = 4 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => rw [quad_cons, List.length_append, ih]; simp; omega

section Pass2Loop
variable {ns nr : ℕ} (cap : ℕ) (I O : Fin (ns + 1)) {OP L2 F : Fin nr} (out nxt : Bool → Bool → Bool)
variable (hIO : I ≠ O) (hOL : OP ≠ L2) (hOF : OP ≠ F) (hLF : L2 ≠ F)

include hIO hOL hOF hLF in
/-- **The emitting loop**: `k` mapped bits of the word emitted two-framed. -/
theorem emitLoop_spec (hcap : 1 ≤ cap) : ∀ (k : ℕ) (sfx pre rest : List Bool) (σ : WState ns nr) (c : Bool),
    σ.st I = pre ++ (frameP sfx ++ false :: rest) → σ.sh I = pre.length → k ≤ sfx.length →
    σ.val L2 = k → σ.val F = c.toNat → σ.sh O = (σ.st O).length → σ.val OP + 4 * k ≤ cap → k ≤ cap →
    WExec cap (.whr L2 (emitBody I O OP L2 F out nxt)) σ
      (u2 I O OP L2 F σ (pre.length + 2 * k) 0 (cfin nxt (sfx.take k) c).toNat
        (quad ((cmap out nxt sfx c).take k)))
      (k * 47 + 1)
  | 0, sfx, pre, rest, σ, c, _, hsh, _, hk, hF, _, _, _ => by
    have e := u2_self I O hIO hOL hOF hLF σ
    rw [hsh, hk, hF] at e
    simp only [List.take_zero, cfin, quad_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    rw [e]
    exact WExec.whrF hk
  | k + 1, [], _, _, _, _, _, _, hks, _, _, _, _, _ => by simp at hks
  | k + 1, b :: sfx, pre, rest, σ, c, hst, hsh, hks, hk, hF, hO, hc, hkc => by
    have hbit : readTapeBit (σ.st I) (pre.length + 1) = b := by
      rw [hst]
      have := rd_bit pre (b :: sfx) (false :: rest) 0 (by simp)
      simpa using this
    have s1 := emitBody_spec cap I O out nxt hIO hOL hOF hLF b c σ pre.length k hsh hbit hk hF hO (by omega) hcap
      (by omega)
    set σ' := u2 I O OP L2 F σ (pre.length + 2) k (nxt b c).toNat [true, true, true, out b c] with hσ'
    have hv : ∀ r, r ≠ OP → r ≠ L2 → r ≠ F → σ'.val r = σ.val r := fun r h1 h2 h3 => by
      simp [hσ', u2, Function.update_apply, h1, h2, h3]
    have s2 := emitLoop_spec hcap k sfx (pre ++ [true, b]) rest σ' (nxt b c)
      (by simp only [hσ', u2, WState.setv_st, WState.seth_st, PrimAsm.WriteNat.appendO_st, Function.update_apply,
        if_neg hIO]; rw [hst]; simp [frameP])
      (by simp [hσ', u2, Function.update_apply, hIO] <;> omega)
      (by simp at hks; omega)
      (by simp [hσ', u2, Function.update_apply, hLF])
      (by simp [hσ', u2, Function.update_apply])
      (by simp [hσ', u2, Function.update_apply, hO, Ne.symm hIO])
      (by simp [hσ', u2, Function.update_apply, hOL, hOF]; omega)
      (by omega)
    rw [hσ', u2_u2 I O hIO hOL hOF hLF] at s2
    have hlen : (pre ++ [true, b]).length + 2 * k = pre.length + 2 * (k + 1) := by simp; omega
    rw [hlen] at s2
    refine WExec.cast cap (WExec.whrT (by omega) s1 s2) ?_ (by rw [Nat.add_mul, Nat.one_mul]; omega)
    rfl

end Pass2Loop

section Skip
variable {ns nr : ℕ} (cap : ℕ) (I : Fin (ns + 1))

/-- **Skip the rest of a framed word**, from a marker of its remaining bits to past the terminator. -/
theorem skipLoop_spec : ∀ (sfx pre rest : List Bool) (σ : WState ns nr),
    σ.st I = pre ++ (frameP sfx ++ false :: rest) → σ.sh I = pre.length →
    WExec cap (.whs I (.seq (.fwd I) (.fwd I))) σ (σ.seth I (pre.length + 2 * sfx.length)) (5 * sfx.length + 1)
  | [], pre, rest, σ, hst, hsh => by
    have hr : wbit σ I = false := by
      simp only [wbit, hst, hsh]
      have := rd_shift pre (frameP [] ++ false :: rest) 0
      simp only [Nat.add_zero] at this
      rw [this]; rfl
    have e : σ.seth I (pre.length + 2 * ([] : List Bool).length) = σ := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]; rw [← hsh]; exact wseth_same σ I
    rw [e]
    exact WExec.whsF hr
  | b :: sfx, pre, rest, σ, hst, hsh => by
    have hm : wbit σ I = true := by
      simp only [wbit, hst, hsh]
      have := rd_marker pre (b :: sfx) (false :: rest) 0 (by simp)
      simpa using this
    have s1 := WExec.seq (WExec.fwd (cap := cap) I σ) (WExec.fwd (cap := cap) I (σ.seth I (σ.sh I + 1)))
    have s2 := skipLoop_spec sfx (pre ++ [true, b]) rest ((σ.seth I (σ.sh I + 1)).seth I
      ((σ.seth I (σ.sh I + 1)).sh I + 1)) (by simp only [WState.seth_st]; rw [hst]; simp [frameP])
      (by simp [hsh] <;> omega)
    have hlen : (pre ++ [true, b]).length + 2 * sfx.length = pre.length + 2 * (b :: sfx).length := by
      simp; omega
    refine WExec.cast cap (WExec.whsT hm s1 s2) ?_ ?_
    · rw [wseth_seth, wseth_seth, hlen]
    · simp only [List.length_cons]; omega

theorem skipRest_spec (sfx pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st I = pre ++ (frameP sfx ++ false :: rest)) (hsh : σ.sh I = pre.length) :
    WExec cap (skipRest I) σ (σ.seth I (pre.length + 2 * sfx.length + 1)) (5 * sfx.length + 3) := by
  have s1 := skipLoop_spec cap I sfx pre rest σ hst hsh
  have s2 := WExec.fwd (cap := cap) I (σ.seth I (pre.length + 2 * sfx.length))
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  rw [wseth_seth]; simp

end Skip

theorem frameP_take_drop (bs : List Bool) (k : ℕ) : frameP bs = frameP (bs.take k) ++ frameP (bs.drop k) := by
  unfold frameP
  rw [← List.flatMap_append, List.take_append_drop]

theorem frameP_length' (bs : List Bool) : (frameP bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [frameP] at ih ⊢; omega

section Pass2Wrap
variable {ns nr : ℕ} (cap : ℕ) (I O : Fin (ns + 1)) {OP L2 F : Fin nr} (out nxt : Bool → Bool → Bool)
variable (hIO : I ≠ O) (hOL : OP ≠ L2) (hOF : OP ≠ F) (hLF : L2 ≠ F)

theorem u2_seth (σ : WState ns nr) (p k f p' : ℕ) (w : List Bool) :
    (u2 I O OP L2 F σ p k f w).seth I p' = u2 I O OP L2 F σ p' k f w := by
  apply WState.eq
  · funext j; simp only [u2, WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> rfl
  · rfl
  · rfl
  · rfl

include hIO hOL hOF hLF in
/-- **The emitting pass**: `k` mapped bits emitted two-framed, the head past the word. -/
theorem bitsPass_spec (hcap : 1 ≤ cap) (k : ℕ) (bs pre rest : List Bool) (σ : WState ns nr) (c : Bool)
    (hst : σ.st I = pre ++ (frameP bs ++ false :: rest)) (hsh : σ.sh I = pre.length) (hk : k ≤ bs.length)
    (hL : σ.val L2 = k) (hF : σ.val F = c.toNat) (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + 4 * k ≤ cap)
    (hkc : k ≤ cap) :
    WExec cap (bitsPass I O OP L2 F out nxt) σ
      (u2 I O OP L2 F σ (pre.length + 2 * bs.length + 1) 0 (cfin nxt (bs.take k) c).toNat
        (quad ((cmap out nxt bs c).take k)))
      (k * 47 + 5 * bs.length + 5) := by
  have s1 := emitLoop_spec cap I O out nxt hIO hOL hOF hLF hcap k bs pre rest σ c hst hsh hk hL hF hO hc hkc
  set τ := u2 I O OP L2 F σ (pre.length + 2 * k) 0 (cfin nxt (bs.take k) c).toNat (quad ((cmap out nxt bs c).take k))
    with hτ
  have hτst : τ.st I = (pre ++ frameP (bs.take k)) ++ (frameP (bs.drop k) ++ false :: rest) := by
    simp only [hτ, u2, WState.setv_st, WState.seth_st, PrimAsm.WriteNat.appendO_st, Function.update_apply,
      if_neg hIO]
    rw [hst, frameP_take_drop bs k]; simp
  have hτsh : τ.sh I = (pre ++ frameP (bs.take k)).length := by
    simp [hτ, u2, Function.update_apply, frameP_length', List.length_take, Nat.min_eq_left hk]
  have s2 := skipRest_spec cap I (bs.drop k) (pre ++ frameP (bs.take k)) rest τ hτst hτsh
  refine WExec.cast cap (WExec.seq s1 s2) ?_ ?_
  · rw [hτ, u2_seth]
    congr 1
    simp [frameP_length', List.length_take, Nat.min_eq_left hk]
    omega
  · simp only [List.length_drop]
    have : 5 * (bs.length - k) ≤ 5 * bs.length := by omega
    omega

end Pass2Wrap

/-! ## The natWord's length field and the rewind -/

section Head
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) {OP L L2 : Fin nr}
variable (hOL : OP ≠ L) (hOL2 : OP ≠ L2) (hLL : L ≠ L2)

/-- Emit the length field `1^L 0` two-framed, moving `L` into `L2`. -/
def headW (O : Fin (ns + 1)) (OP L L2 : Fin nr) : WM ns nr :=
  .seq (.whr L (.seq (.dec L) (.seq (.inc L2) (PrimAsm.Emit.emitW O OP [true, true, true, true]))))
    (PrimAsm.Emit.emitW O OP [true, true, true, false])

include hOL hOL2 hLL in
theorem headLoop_spec : ∀ (l m : ℕ) (σ : WState ns nr), σ.val L = l → σ.val L2 = m →
    σ.sh O = (σ.st O).length → σ.val OP + 4 * l ≤ cap → l + m ≤ cap →
    WExec cap (.whr L (.seq (.dec L) (.seq (.inc L2) (PrimAsm.Emit.emitW O OP [true, true, true, true])))) σ
      (((PrimAsm.WriteNat.appendO σ O OP (quad (List.replicate l true))).setv L 0).setv L2 (m + l)) (40 * l + 1)
  | 0, m, σ, hl, hm, _, _, _ => by
    have e : ((PrimAsm.WriteNat.appendO σ O OP (quad (List.replicate 0 true))).setv L 0).setv L2 (m + 0) = σ := by
      simp only [List.replicate_zero, quad_nil, PrimAsm.WriteNat.appendO_nil, Nat.add_zero]
      apply WState.eq
      · rfl
      · rfl
      · funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
      · rfl
    rw [e]; exact WExec.whrF hl
  | l + 1, m, σ, hl, hm, hO, hc, hlm => by
    have s1 := WExec.dec (cap := cap) L σ (by omega)
    have s2 := WExec.inc (cap := cap) L2 (σ.setv L (σ.val L - 1)) (by simp [Function.update_apply, hLL.symm]; omega)
    set σ2 := (σ.setv L (σ.val L - 1)).setv L2 ((σ.setv L (σ.val L - 1)).val L2 + 1) with hσ2
    have s3 := PrimAsm.Emit.emitW_spec cap O OP [true, true, true, true] σ2 (by simp [σ2, hO])
      (by simp [σ2, Function.update_apply, hOL, hOL2]; omega)
    set σ3 := PrimAsm.WriteNat.appendO σ2 O OP [true, true, true, true] with hσ3
    have hv3 : σ3.val OP = σ.val OP + 4 := by
      simp only [σ3, σ2, PrimAsm.WriteNat.appendO_val, WState.setv_val, Function.update_apply, if_pos rfl,
        if_neg hOL, if_neg hOL2]
      rfl
    have s4 := headLoop_spec l (m + 1) σ3
      (by simp [σ3, σ2, Function.update_apply, hOL.symm, hLL] <;> omega)
      (by simp [σ3, σ2, Function.update_apply, hOL2.symm, hLL.symm, hm])
      (by simp [σ3, σ2, hO]) (by rw [hv3]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2 s3)) s4) ?_
      (by simp only [List.length_cons, List.length_nil]; omega)
    have eq : quad (List.replicate (l + 1) true) = [true, true, true, true] ++ quad (List.replicate l true) := by
      rw [List.replicate_succ, quad_cons]
    rw [hσ3, hσ2, PrimAsm.WriteNat.appendO_append, PrimAsm.WriteNat.appendO_setv _ O OP L2 hOL2.symm,
      PrimAsm.WriteNat.appendO_setv _ O OP L hOL.symm, ← eq]
    apply WState.eq
    · rfl
    · rfl
    · funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> simp_all <;> omega
    · rfl

include hOL hOL2 hLL in
theorem headW_spec (l : ℕ) (σ : WState ns nr) (hl : σ.val L = l) (hm : σ.val L2 = 0)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + 4 * l + 4 ≤ cap) (hlc : l ≤ cap) :
    WExec cap (headW O OP L L2) σ
      (((PrimAsm.WriteNat.appendO σ O OP (quad (List.replicate l true ++ [false]))).setv L 0).setv L2 l)
      (40 * l + 34) := by
  have s1 := headLoop_spec cap O hOL hOL2 hLL l 0 σ hl hm hO (by omega) (by omega)
  set τ := ((PrimAsm.WriteNat.appendO σ O OP (quad (List.replicate l true))).setv L 0).setv L2 (0 + l) with hτ
  have hvτ : τ.val OP = σ.val OP + 4 * l := by
    simp only [τ, PrimAsm.WriteNat.appendO_val, WState.setv_val, Function.update_apply, if_pos rfl, if_neg hOL,
      if_neg hOL2, quad_length, List.length_replicate, ite_true]
  have s2 := PrimAsm.Emit.emitW_spec cap O OP [true, true, true, false] τ (by simp [τ, hO])
    (by rw [hvτ]; simp; omega)
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by simp)
  rw [hτ, PrimAsm.WriteNat.appendO_setv _ O OP L2 hOL2.symm, PrimAsm.WriteNat.appendO_setv _ O OP L hOL.symm,
    PrimAsm.WriteNat.appendO_append, quad_append, Nat.zero_add]
  rfl

end Head

section Rewind
variable {ns nr : ℕ} (cap : ℕ) (I : Fin (ns + 1)) (H2 : Fin nr)

/-- Move the head back by `H2` cells. -/
def rewW : WM ns nr := .whr H2 (.seq (.dec H2) (.bwd I))

theorem rewW_spec : ∀ (m : ℕ) (σ : WState ns nr), σ.val H2 = m → m ≤ σ.sh I → m ≤ cap →
    WExec cap (rewW I H2) σ ((σ.seth I (σ.sh I - m)).setv H2 0) (5 * m + 1)
  | 0, σ, hm, _, _ => by
    have e : (σ.seth I (σ.sh I - 0)).setv H2 0 = σ := by rw [Nat.sub_zero, wseth_same, ← hm, wsetv_same]
    rw [e]; exact WExec.whrF hm
  | m + 1, σ, hm, hle, hc => by
    have s1 := WExec.dec (cap := cap) H2 σ (by omega)
    have s2 := WExec.bwd (cap := cap) I (σ.setv H2 (σ.val H2 - 1))
    have s3 := rewW_spec m ((σ.setv H2 (σ.val H2 - 1)).seth I ((σ.setv H2 (σ.val H2 - 1)).sh I - 1))
      (by simp; omega) (by simp; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 s2) s3) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> simp_all <;> omega
    · rfl
    · funext r; simp only [WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs <;> simp_all
    · rfl

end Rewind

/-! ## One table number to its native word -/

/-- **The emitted word is the native word**: the length field `1^L 0` and the first `L` bits of the `h`-bit word
of `v'`, `L = natBitLength v'`, two-framed, are `quad (natWord v')`. -/
theorem quad_natWord (h v' : ℕ) (hh : 1 ≤ h) (hv : v' < 2 ^ h) :
    quad (List.replicate (natBitLength v') true ++ [false]) ++ quad ((binary h v').take (natBitLength v')) =
      quad (natWord v') := by
  rw [CompilerMachine.Pool.natWord_eq, CompilerMachine.Pool.binary_pad v' h hh hv,
    List.take_left' (binary_length _ _)]
  rw [← quad_append]
  simp

theorem lmax_eq (h v' : ℕ) (hh : 1 ≤ h) (hv : v' < 2 ^ h) :
    (if (accLZ (binary h v') (0, 0)).1 = 0 then 1 else (accLZ (binary h v') (0, 0)).1) = natBitLength v' := by
  rw [accLZ_binary h v' hh hv]
  by_cases h0 : v' = 0
  · subst h0; simp [natBitLength]
  · have : 1 ≤ natBitLength v' := by unfold natBitLength; omega
    simp [h0]; omega

section Conv
variable {ns nr : ℕ} (cap : ℕ) (I O : Fin (ns + 1)) (OP L L2 Z F H2 : Fin nr) (out nxt : Bool → Bool → Bool)

/-- Measure the mapped word: `L := natBitLength`, the head back at the word's start. -/
def measW (c0 : Bool) : WM ns nr :=
  .seq (setFlag F c0) (.seq (lenPass I L Z F H2 out nxt) (.seq (WM.clear Z) (.seq (.ifr L .skip (.inc L))
    (rewW I H2))))

/-- Emit the native word of the mapped value, the head past the word. -/
def emitNatW (c0 : Bool) : WM ns nr :=
  .seq (headW O OP L L2) (.seq (WM.clear F) (.seq (setFlag F c0) (.seq (bitsPass I O OP L2 F out nxt) (WM.clear F))))

/-- **One table number to its native word** (through the carry map with initial carry `c0`). -/
def convWord (c0 : Bool) : WM ns nr := .seq (measW I L Z F H2 out nxt c0) (emitNatW I O OP L L2 F out nxt c0)

variable {OP L L2 Z F H2}
variable (hIO : I ≠ O) (hLZ : L ≠ Z) (hLF : L ≠ F) (hLH : L ≠ H2) (hZF : Z ≠ F) (hZH : Z ≠ H2) (hFH : F ≠ H2)
  (hOL : OP ≠ L) (hOL2 : OP ≠ L2) (hOF : OP ≠ F) (hLL : L ≠ L2) (hL2F : L2 ≠ F) (hOZ : OP ≠ Z) (hOH : OP ≠ H2)
  (hL2Z : L2 ≠ Z) (hL2H : L2 ≠ H2)

include hLZ hLF hLH hZF hZH hFH in
/-- **The measuring half**: `L := natBitLength v'` (`v'` the mapped value), `F` the final carry, the head back. -/
theorem measW_spec (hcap : 1 ≤ cap) (c0 : Bool) (bs pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st I = pre ++ (frameP bs ++ false :: rest)) (hsh : σ.sh I = pre.length)
    (hL : σ.val L = 0) (hZ : σ.val Z = 0) (hF : σ.val F = 0) (hH : σ.val H2 = 0) (hc2 : 2 * bs.length + 2 ≤ cap) :
    WExec cap (measW I L Z F H2 out nxt c0) σ
      ((σ.setv L (if (accLZ (cmap out nxt bs c0) (0, 0)).1 = 0 then 1 else (accLZ (cmap out nxt bs c0) (0, 0)).1)).setv
        F (cfin nxt bs c0).toNat)
      (bs.length * (7 * bs.length + 40) + 23 * bs.length + 30) := by
  have s1 := setFlag_spec cap F c0 false σ (by simpa using hF) hcap
  set σ1 := σ.setv F c0.toNat with hσ1
  have s2 := lenPass_spec cap I out nxt hLZ hLF hLH hZF hZH hFH hcap bs pre rest σ1 c0 bs.length
    (by simpa [σ1] using hst) (by simpa [σ1] using hsh) (by simp [σ1, Function.update_apply, hLF, hL])
    (by simp [σ1, Function.update_apply, hZF, hZ]) (by simp [σ1]) (by simp [σ1, Function.update_apply, hFH.symm, hH])
    hc2 le_rfl
  set la := (accLZ (cmap out nxt bs c0) (0, 0)).1 with hla
  set za := (accLZ (cmap out nxt bs c0) (0, 0)).2 with hza
  have hzab : za ≤ bs.length := by
    have := accLZ_le (cmap out nxt bs c0) 0 0; rw [cmap_length] at this; omega
  have hlab : la ≤ bs.length := by
    have := accLZ_sum (cmap out nxt bs c0) 0 0; rw [cmap_length] at this; omega
  set σ2 := u1 I L Z F H2 σ1 (pre.length + 2 * bs.length + 1) la za (cfin nxt bs c0).toNat (2 * bs.length + 1)
    with hσ2
  have s3 := wclear_spec cap Z za σ2 (u1_val_Z I hLZ hLF hLH hZF hZH hFH σ1 _ _ _ _ _) (by
    rw [u1_val_Z I hLZ hLF hLH hZF hZH hFH]; omega)
  set σ3 := σ2.setv Z 0 with hσ3
  have hσ3L : σ3.val L = la := by simp [σ3, Function.update_apply, hLZ]; exact u1_val_L I hLZ hLF hLH hZF hZH hFH σ1 _ _ _ _ _
  set lm := if la = 0 then 1 else la with hlm
  have s4 : WExec cap (.ifr L .skip (.inc L)) σ3 (σ3.setv L lm) 4 := by
    by_cases h0 : la = 0
    · have hi := WExec.inc (cap := cap) L σ3 (by omega)
      rw [hσ3L, h0] at hi
      have e : lm = 1 := by simp [hlm, h0]
      rw [e]
      exact WExec.mono (WExec.ifrF (by rw [hσ3L, h0]) hi) (by omega)
    · have e : σ3.setv L lm = σ3 := by rw [show lm = la by simp [hlm, h0], ← hσ3L, wsetv_same]
      rw [e]
      exact WExec.mono (WExec.ifrT (by rw [hσ3L]; exact h0) (WExec.skip σ3)) (by omega)
  set σ4 := σ3.setv L lm with hσ4
  have hσ4H : σ4.val H2 = 2 * bs.length + 1 := by
    simp [σ4, σ3, Function.update_apply, hLH.symm, hZH.symm]; exact u1_val_H I hLZ hLF hLH hZF hZH hFH σ1 _ _ _ _ _
  have hσ4sh : σ4.sh I = pre.length + 2 * bs.length + 1 := by simp [σ4, σ3, σ2, u1]
  have s5 := rewW_spec cap I H2 (2 * bs.length + 1) σ4 hσ4H (by rw [hσ4sh]; omega) (by omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · rw [hσ4sh, show pre.length + 2 * bs.length + 1 - (2 * bs.length + 1) = pre.length by omega]
    apply WState.eq
    · funext j; simp only [σ4, σ3, σ2, σ1, u1, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · funext r; simp only [σ4, σ3, σ2, σ1, u1, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  · have : 3 * za ≤ 3 * bs.length := by omega
    omega

include hIO hOL hOL2 hOF hLL hL2F hLF in
/-- **The emitting half**: `1^L 0` and the first `L` mapped bits, two-framed; the head past the word. -/
theorem emitNatW_spec (hcap : 1 ≤ cap) (c0 : Bool) (bs pre rest : List Bool) (σ : WState ns nr) (lm : ℕ)
    (hst : σ.st I = pre ++ (frameP bs ++ false :: rest)) (hsh : σ.sh I = pre.length)
    (hL : σ.val L = lm) (hL2 : σ.val L2 = 0) (hF : σ.val F ≤ 1) (hlm : lm ≤ bs.length)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + 8 * lm + 4 ≤ cap) (hc2 : lm ≤ cap) :
    WExec cap (emitNatW I O OP L L2 F out nxt c0) σ
      ((((PrimAsm.WriteNat.appendO σ O OP (quad (List.replicate lm true ++ [false]) ++
        quad ((cmap out nxt bs c0).take lm))).setv L 0).setv F 0).seth I (pre.length + 2 * bs.length + 1))
      (87 * lm + 5 * bs.length + 60) := by
  have s1 := headW_spec cap O hOL hOL2 hLL lm σ hL hL2 hO (by omega) hc2
  set σ1 := ((PrimAsm.WriteNat.appendO σ O OP (quad (List.replicate lm true ++ [false]))).setv L 0).setv L2 lm
    with hσ1
  have hF1 : σ1.val F ≤ 1 := by
    simp only [σ1, WState.setv_val, PrimAsm.WriteNat.appendO_val, Function.update_apply, if_neg hLF.symm,
      if_neg hL2F.symm, if_neg hOF.symm]; exact hF
  have s2 := wclear_spec cap F (σ1.val F) σ1 rfl (by omega)
  have s3 := setFlag_spec cap F c0 false (σ1.setv F 0) (by simp) hcap
  set σ3 := (σ1.setv F 0).setv F c0.toNat with hσ3
  have s4 := bitsPass_spec cap I O out nxt hIO hOL2 hOF hL2F hcap lm bs pre rest σ3 c0
    (by simp [σ3, σ1, Function.update_apply, hIO, hst]) (by simp [σ3, σ1, Function.update_apply, hIO, hsh])
    hlm (by simp [σ3, σ1, Function.update_apply, hL2F]) (by simp [σ3])
    (by simp [σ3, σ1, hO]) (by simp [σ3, σ1, Function.update_apply, hOF, hOL, hOL2]; omega) hc2
  set σ4 := u2 I O OP L2 F σ3 (pre.length + 2 * bs.length + 1) 0 (cfin nxt (bs.take lm) c0).toNat
    (quad ((cmap out nxt bs c0).take lm)) with hσ4
  have hF4 : σ4.val F ≤ 1 := by simp [σ4, u2]; cases (cfin nxt (bs.take lm) c0) <;> simp
  have s5 := wclear_spec cap F (σ4.val F) σ4 rfl (by omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · simp only [hσ4, u2, hσ3, hσ1]
    rw [PrimAsm.WriteNat.appendO_setv _ O OP F hOF.symm, PrimAsm.WriteNat.appendO_setv _ O OP F hOF.symm,
      PrimAsm.WriteNat.appendO_setv _ O OP L2 hOL2.symm, PrimAsm.WriteNat.appendO_setv _ O OP L hOL.symm,
      PrimAsm.WriteNat.appendO_append]
    apply WState.eq
    · funext j; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
      all_goals (try split_ifs) <;> simp_all
    · funext j; simp only [WState.setv_st, WState.seth_st, PrimAsm.WriteNat.appendO_st, Function.update_apply]
    · funext r; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
      all_goals (try split_ifs) <;> simp_all
    · rfl
  · have : σ1.val F ≤ 1 := hF1
    have : σ4.val F ≤ 1 := hF4
    omega

include hIO hLZ hLF hLH hZF hZH hFH hOL hOL2 hOF hLL hL2F hOZ hOH hL2Z hL2H in
/-- **One table number to its native word**: the framed `h`-bit word of `v`, read through the carry map to the
`h`-bit word of `v'`, becomes `quad (natWord v')` on the output; the head is past the word; every scratch register
is `0` again. -/
theorem convWord_spec (hcap : 1 ≤ cap) (c0 : Bool) (h v v' : ℕ) (pre rest : List Bool) (σ : WState ns nr)
    (hh : 1 ≤ h) (hv' : v' < 2 ^ h) (hmap : cmap out nxt (binary h v) c0 = binary h v')
    (hst : σ.st I = pre ++ (frameP (binary h v) ++ false :: rest)) (hsh : σ.sh I = pre.length)
    (hL : σ.val L = 0) (hL2 : σ.val L2 = 0) (hZ : σ.val Z = 0) (hF : σ.val F = 0) (hH : σ.val H2 = 0)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + 8 * h + 4 ≤ cap) (hc2 : 2 * h + 2 ≤ cap) :
    WExec cap (convWord I O OP L L2 Z F H2 out nxt c0) σ
      ((PrimAsm.WriteNat.appendO σ O OP (quad (natWord v'))).seth I (pre.length + 2 * h + 1))
      (7 * h * h + 200 * h + 200) := by
  have hb : (binary h v).length = h := binary_length h v
  have s1 := measW_spec cap I out nxt (hLZ := hLZ) (hLF := hLF) (hLH := hLH) (hZF := hZF) (hZH := hZH) (hFH := hFH)
    hcap c0 (binary h v) pre rest σ hst hsh hL hZ hF hH
    (by rw [hb]; omega)
  rw [hmap, lmax_eq h v' hh hv'] at s1
  set σA := (σ.setv L (natBitLength v')).setv F (cfin nxt (binary h v) c0).toNat with hσA
  have hnl := CompilerMachine.Pool.natBitLength_le v' h hh hv'
  have s2 := emitNatW_spec cap I O out nxt (hIO := hIO) (hOL := hOL) (hOL2 := hOL2) (hOF := hOF) (hLL := hLL)
    (hL2F := hL2F) (hLF := hLF) hcap c0 (binary h v) pre rest σA
    (natBitLength v') (by simp [σA, hst]) (by simp [σA, hsh])
    (by simp [σA, Function.update_apply, hLF])
    (by simp [σA, Function.update_apply, hLL.symm, hL2F, hL2]) (by simp [σA]; cases (cfin nxt (binary h v) c0) <;> simp)
    (by rw [hb]; exact hnl) (by simp [σA, hO])
    (by simp [σA, Function.update_apply, hOL, hOF]; omega) (by omega)
  rw [hmap, quad_natWord h v' hh hv', hb] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ ?_
  · simp only [hσA]
    rw [PrimAsm.WriteNat.appendO_setv _ O OP F hOF.symm, PrimAsm.WriteNat.appendO_setv _ O OP L hOL.symm]
    apply WState.eq
    · funext j; simp only [WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
    · rfl
    · funext r; simp only [WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
      all_goals (try split_ifs) <;> simp_all
    · rfl
  · have : 87 * natBitLength v' ≤ 87 * h := by omega
    nlinarith

end Conv

end NearCubicWires.WireExponent3_5.PrimT.C4Gates
