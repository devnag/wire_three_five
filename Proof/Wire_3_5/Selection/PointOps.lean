import Proof.Wire_3_5.Selection.ScanW
import Proof.Wire_3_5.UnionMachine.RegRatOps
import Proof.Wire_3_5.UnionMachine.RegRatRead

/-! # C1.4: the point routine's word operations (P3:1339-1344)

Paper: "For each gate and row, the four threshold predicates have integer scores of the form `a_j(z_L) + b_j(z_R)`"
(P3:1341-1342). The point routine computes, for each half, two signed weighted sums and the blocks' syndromes; these
are its word operations, each a C5 `mapPass` (or C6's C1.2 ops) with an exact final state:
* `eqAtF`: a flag `G := [the word on A equals the segment of B at B's head]` (the error code's flip position, the
  syndrome against the coset's code);
* `xorB`: `A := A xor B` (the syndrome accumulation), with `binary_xor`;
* `accW`: `A := A ± w` for the magnitude word `WV` and the sign flag `SG` (C6's `addB`/`subB`);
* `rdW`: read one weight record `sign :: frame (binary W |w|)` of a table (the sign into `SG`, the magnitude into
  `WV`), the table's head advancing past the record, counted;
* `emitW`: append a word to a table at its head (overwriting or extending), counted.
Paper quantity: a half's integer scores. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Round (binary_succ mapS_keepA)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-! ## The passes' values -/

/-- The equality carry: stays `true` while the bits agree. -/
def eqN (a b c : Bool) : Bool := c && (a == b)

theorem mapS_eq : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    (mapS keepA eqN as bs c).2 = (c && decide (as = bs))
  | [], [], c, _ => by simp [mapS]
  | a :: as, b :: bs, c, h => by
    simp only [mapS, eqN]
    rw [mapS_eq as bs _ (by simpa using h)]
    cases a <;> cases b <;> cases c <;> simp
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- The exclusive-or output. -/
def xorO (a b _ : Bool) : Bool := xor a b

theorem mapS_xor : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    mapS xorO keepS as bs c = (List.zipWith xor as bs, c)
  | [], [], c, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, xorO, keepS]
    rw [mapS_xor as bs c (by simpa using h)]
    rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem binary_xor : ∀ (w a b : ℕ), List.zipWith xor (binary w a) (binary w b) = binary w (a ^^^ b)
  | 0, _, _ => rfl
  | w + 1, a, b => by
    rw [binary_succ, binary_succ, binary_succ, List.zipWith_cons_cons, binary_xor w (a / 2) (b / 2)]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        simp [ha, hb, Nat.xor_mod_two_eq] <;> omega
    · congr 1
      rw [Nat.xor_div_two]

theorem binary_inj (w a b : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) : binary w a = binary w b ↔ a = b := by
  constructor
  · intro h
    rw [← binary_value w a ha, ← binary_value w b hb, h]
  · intro h; rw [h]

/-! ## Flags -/

/-- Move a `0/1` flag from `F` to `G`. -/
def mvF (F G : Fin nr) : WM ns nr := .ifr F (.seq (.dec F) (.inc G)) .skip

theorem mvF_spec (cap : ℕ) {F G : Fin nr} (hFG : F ≠ G) (σ : WState ns nr) (bf : Bool) (hF : σ.val F = bf.toNat)
    (hG : σ.val G = 0) (hcap : 1 ≤ cap) :
    WExec cap (mvF F G) σ ((σ.setv F 0).setv G bf.toNat) 6 := by
  unfold mvF
  cases bf
  · have e : (σ.setv F 0).setv G (false.toNat) = σ := by
      refine WState.eq ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · funext x; simp only [WState.setv_val, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
    rw [e]
    exact WExec.mono (WExec.ifrF (by simpa using hF) (WExec.skip σ)) (by omega)
  · have h1 := WExec.dec (cap := cap) F σ (by simp at hF; omega)
    have h2 := WExec.inc (cap := cap) G (σ.setv F (σ.val F - 1)) (by simp [Ne.symm hFG, hG]; omega)
    refine WExec.cast cap (WExec.ifrT (by simp at hF; omega) (WExec.seq h1 h2)) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext x; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl

/-! ## Comparing a word with a segment -/

/-- `G := [the word on A equals the segment of B at B's head]` (the pass's carry starts at `1`). -/
def eqAtF (A B : Fin (ns + 1)) (F R G : Fin nr) : WM ns nr :=
  .seq (.inc F) (.seq (mapPass keepA eqN A B F R) (mvF F G))

theorem eqAtF_spec (cap : ℕ) {A B : Fin (ns + 1)} {F R G : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (hFG : F ≠ G)
    (σ : WState ns nr) (as bs preB restB : List Bool) (hl : as.length = bs.length)
    (hA : σ.st A = frameP as ++ [false]) (hAh : σ.sh A = 0) (hB : σ.st B = preB ++ frameP bs ++ restB)
    (hBh : σ.sh B = preB.length) (hF : σ.val F = 0) (hR : σ.val R = 0) (hG : σ.val G = 0)
    (hcap : 2 * as.length + 1 ≤ cap) :
    WExec cap (eqAtF A B F R G) σ (σ.setv G (decide (as = bs)).toNat) (as.length * 41 + 14) := by
  have h1 := WExec.inc (cap := cap) F σ (by omega)
  set σ1 := σ.setv F (σ.val F + 1) with hσ1
  have h2 := mapPassAt_spec cap keepA eqN A B F R hAB hFR (by omega) as bs [] preB [] restB true σ1 hl
    (by simp [hσ1, hA]) (by simp [hσ1, hAh]) (by simp [hσ1, hB]) (by simp [hσ1, hBh]) (by simp [hσ1, hF])
    (by simp [hσ1, Ne.symm hFR, hR]) (by omega)
  rw [mapS_keepA eqN as bs true hl, mapS_eq as bs true hl] at h2
  set σ2 := (σ1.sets A ([] ++ frameP as ++ false :: [])).setv F ((true && decide (as = bs)).toNat) with hσ2
  have h3 := mvF_spec cap hFG σ2 (true && decide (as = bs)) (by simp [hσ2]) (by simp [hσ2, hσ1, Ne.symm hFG, hG])
    (by omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  refine WState.eq ?_ ?_ ?_ ?_
  · rfl
  · funext x; simp only [hσ2, hσ1, WState.setv_st, WState.sets_st, Function.update_apply]
    split_ifs with h
    · subst h; simp [hA]
    · rfl
  · funext x; simp only [hσ2, hσ1, WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

/-! ## Exclusive-or of two words -/

/-- `A := A xor B`. -/
def xorB (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass xorO keepS A B F R

theorem xorB_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (xorB A B F R) σ (σ.sets A (frame (binary W (a ^^^ b)))) (41 * W + 3) := by
  have h := mapPass_spec cap xorO keepS A B F R hAB hFR (by omega) (binary W a) (binary W b) [] [false] false σ
    (by simp) (by simp [hA.1, frame_eq_frameP]) hA.2 (by simp [hB.1, frame_eq_frameP]) hB.2 (by simp [hF]) hR
    (by simp; omega)
  rw [mapS_xor _ _ _ (by simp), binary_xor] at h
  refine WExec.cast cap h ?_ (by simp; omega)
  refine WState.eq ?_ ?_ ?_ ?_
  · rfl
  · funext x; simp only [WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP]
  · funext x; simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

/-! ## Signed accumulation -/

/-- `A := A + w` for `w = ±|w|`: subtract when the sign flag is set. -/
def accW (A V : Fin (ns + 1)) (SG F R : Fin nr) : WM ns nr := .ifr SG (subB A V F R) (addB A V F R)

/-- The signed value of a weight record `(sign, magnitude)`. -/
def sv (sgn : Bool) (m : ℕ) : ℤ := if sgn then -(m : ℤ) else (m : ℤ)

/-- **Signed accumulation of a record**: `A := a + sv sgn m` for `m` on `V` and `SG = sgn` (a set sign with a zero
magnitude subtracts `0`). -/
theorem accR_spec (cap W : ℕ) {A V : Fin (ns + 1)} {SG F R : Fin nr} (hAV : A ≠ V) (hFR : F ≠ R) (σ : WState ns nr)
    (a m : ℕ) (sgn : Bool) (hA : NumOn σ A W a) (hV : NumOn σ V W m) (hSG : σ.val SG = sgn.toNat)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (h0 : 0 ≤ (a : ℤ) + sv sgn m) (hW : (a : ℤ) + sv sgn m < 2 ^ W)
    (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (accW A V SG F R) σ (σ.sets A (frame (binary W ((a : ℤ) + sv sgn m).toNat))) (41 * W + 10) := by
  unfold accW
  cases sgn
  · have hs : σ.val SG = 0 := by rw [hSG]; rfl
    simp only [sv, Bool.false_eq_true, if_false] at h0 hW ⊢
    have hlt : a + m < 2 ^ W := by exact_mod_cast hW
    have h := addB_spec cap W hAV hFR σ a m hA hV hF hR hlt hcap
    have e : ((a : ℤ) + (m : ℤ)).toNat = a + m := by omega
    rw [e]
    exact WExec.mono (WExec.ifrF hs h) (by omega)
  · have hs : σ.val SG ≠ 0 := by rw [hSG]; decide
    simp only [sv, if_true] at h0 hW ⊢
    have hle : m ≤ a := by omega
    have h := subB_spec cap W hAV hFR σ a m hA hV hF hR hle ha hcap
    have e : ((a : ℤ) + -(m : ℤ)).toNat = a - m := by omega
    rw [e]
    exact WExec.mono (WExec.ifrT hs h) (by omega)

/-! ## Reading a weight record, writing a word -/

/-- Skip one framed word, counting the moves. -/
def skipC (I : Fin (ns + 1)) (C : Fin nr) : WM ns nr :=
  .seq (.whs I (.seq (WM.fwdC I C) (WM.fwdC I C))) (WM.fwdC I C)

theorem skipC_spec (cap : ℕ) (I : Fin (ns + 1)) (C : Fin nr) (bits pre post : List Bool) (σ : WState ns nr)
    (hI : σ.st I = pre ++ frameP bits ++ false :: post) (hIh : σ.sh I = pre.length) (hC : σ.val C = pre.length)
    (hcap : pre.length + 2 * bits.length + 1 ≤ cap) :
    WExec cap (skipC I C) σ ((σ.seth I (pre.length + 2 * bits.length + 1)).setv C (pre.length + 2 * bits.length + 1))
      (13 * bits.length + 7) := by
  have h1 := skipGen cap I C bits pre post σ hI hIh hC (by omega)
  have h2 := wfwdC_spec cap I C ((σ.seth I (pre.length + 2 * bits.length)).setv C (pre.length + 2 * bits.length))
    (by simp; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  refine WState.eq ?_ ?_ ?_ ?_
  · funext x; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · funext x; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

/-- Copy the word at `I`'s head into `A`, `I`'s head moving past it, counted in `C`. -/
def copyAtC (A I : Fin (ns + 1)) (C F R : Fin nr) : WM ns nr := .seq (mapPass copyOut keepS A I F R) (skipC I C)

theorem copyAtC_spec (cap W : ℕ) {A I : Fin (ns + 1)} {C F R : Fin nr} (hAI : A ≠ I) (hFR : F ≠ R) (hCF : C ≠ F)
    (σ : WState ns nr) (a v : ℕ) (pre post : List Bool) (hA : NumOn σ A W a)
    (hI : σ.st I = pre ++ frame (binary W v) ++ post) (hIh : σ.sh I = pre.length) (hC : σ.val C = pre.length)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : pre.length + 2 * W + 1 ≤ cap) (hcap2 : 2 * W + 1 ≤ cap) :
    WExec cap (copyAtC A I C F R) σ
      (((σ.sets A (frame (binary W v))).seth I (pre.length + 2 * W + 1)).setv C (pre.length + 2 * W + 1))
      (41 * W + 3 + 1 + (13 * W + 7)) := by
  have h1 := mapPassAt_spec cap copyOut keepS A I F R hAI hFR (by omega) (binary W a) (binary W v) [] pre []
    (false :: post) false σ (by simp) (by simp [hA.1, frame_eq_frameP]) (by simp [hA.2])
    (by rw [hI, frame_eq_frameP]; simp) hIh (by simp [hF]) hR (by simp; omega)
  rw [mapS_copy _ _ _ (by simp)] at h1
  set σ1 := (σ.sets A ([] ++ frameP (binary W v) ++ false :: [])).setv F false.toNat with hσ1
  have h2 := skipC_spec cap I C (binary W v) pre post σ1 (by simp [hσ1, Ne.symm hAI, hI, frame_eq_frameP])
    (by simp [hσ1, hIh]) (by simp [hσ1, hCF, hC]) (by simp; omega)
  rw [binary_length] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
  refine WState.eq ?_ ?_ ?_ ?_
  · rfl
  · funext x; simp only [hσ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply,
      frame_eq_frameP]
    split_ifs <;> simp_all
  · funext x; simp only [hσ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

/-- **Read one weight record** `sign :: frame (binary W |w|)`: the sign into `SG`, `|w|` into `V`. -/
def rdW (T V : Fin (ns + 1)) (C SG F R : Fin nr) : WM ns nr :=
  .seq (.ifs T (.inc SG) .skip) (.seq (WM.fwdC T C) (copyAtC V T C F R))

theorem rdW_spec (cap W : ℕ) {T V : Fin (ns + 1)} {C SG F R : Fin nr} (hTV : T ≠ V) (hFR : F ≠ R) (hCF : C ≠ F)
    (hCR : C ≠ R) (hCSG : C ≠ SG) (hSGF : SG ≠ F) (hSGR : SG ≠ R) (σ : WState ns nr) (v m : ℕ) (sgn : Bool) (pre post : List Bool)
    (hV : NumOn σ V W v) (hT : σ.st T = pre ++ (sgn :: frame (binary W m)) ++ post) (hTh : σ.sh T = pre.length)
    (hC : σ.val C = pre.length) (hSG : σ.val SG = 0) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : pre.length + 2 * W + 2 ≤ cap) :
    WExec cap (rdW T V C SG F R) σ
      ((((σ.setv SG sgn.toNat).sets V (frame (binary W m))).seth T (pre.length + 2 * W + 2)).setv C
        (pre.length + 2 * W + 2)) (54 * W + 23) := by
  have hsgn : wbit σ T = sgn := by simp [wbit, hT, hTh, rd_app0, rd_cons0]
  have h1 : WExec cap (.ifs T (.inc SG) .skip) σ (σ.setv SG sgn.toNat) 4 := by
    cases sgn
    · have e : σ.setv SG (false.toNat) = σ := by
        refine WState.eq ?_ ?_ ?_ ?_
        · rfl
        · rfl
        · funext x; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
        · rfl
      rw [e]; exact WExec.mono (WExec.ifsF hsgn (WExec.skip σ)) (by omega)
    · have hi := WExec.inc (cap := cap) SG σ (by omega)
      rw [hSG] at hi
      exact WExec.mono (WExec.ifsT hsgn hi) (by omega)
  set σ1 := σ.setv SG sgn.toNat with hσ1
  have h2 := wfwdC_spec cap T C σ1 (by simp [hσ1, hCSG, hC]; omega)
  set σ2 := (σ1.seth T (σ1.sh T + 1)).setv C (σ1.val C + 1) with hσ2
  have h3 := copyAtC_spec cap W (Ne.symm hTV) hFR hCF σ2 v m (pre ++ [sgn]) post
    ⟨by simp [hσ2, hσ1, hV.1], by simp [hσ2, hσ1, Ne.symm hTV, hV.2]⟩
    (by simp [hσ2, hσ1, hT]) (by simp [hσ2, hσ1, hTh]) (by simp [hσ2, hσ1, hCSG, hC])
    (by simp [hσ2, hσ1, Ne.symm hCF, Ne.symm hSGF, hF]) (by simp [hσ2, hσ1, Ne.symm hSGR, Ne.symm hCR, hR])
    (by simp; omega) (by omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  refine WState.eq ?_ ?_ ?_ ?_
  · funext x; simp only [hσ2, hσ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply,
      List.length_append, List.length_singleton]
    split_ifs <;> simp_all <;> omega
  · funext x; simp only [hσ2, hσ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
  · funext x; simp only [hσ2, hσ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply,
      List.length_append, List.length_singleton]
    split_ifs <;> simp_all <;> omega
  · rfl

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
