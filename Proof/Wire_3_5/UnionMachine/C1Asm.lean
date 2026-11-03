import Proof.Wire_3_5.UnionMachine.C1Rat
import Proof.Wire_3_5.UnionMachine.FrontClog
import Proof.Wire_3_5.Primitive.Writers.SymDecStreams
import Proof.Wire_3_5.Ledger.LedgerLoad
import Proof.Wire_3_5.Ledger.LedgerGrowth

/-! # C6 front, the C1 dock: C1's request word (P3:1326-1330, 3673; `Plan.selWord`)

After the carrier loop the request's pieces sit on their streams: the gates (`marks` of their words), the populations,
the gate total `1^{gt}`, the population count `1^{np}`; with `1^q` and the ledger's star multiplier
`r = rowBr cr q = 2(⌊log₂ ⌈log₂(q+2)⌉⌋ + cr)` (`Ledger.rowBr`, the ledger's `rOf`) the program writes C1's input
`frame (natWord q ++ natWord r ++ natWord gt ++ G ++ natWord np ++ P)`:
* `cpM_spec` (a `marks` stream copied raw), `clogL_spec` (`⌈log₂ x⌉` in unary, FrontClog's `clog_of_loop`);
* **`asmW_spec`**.

Paper quantity of the main type: `star:selection`'s request, as C1 reads it (`Plan.selWord`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Asm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)

section Copy
variable {ns nr : ℕ} (cap : ℕ)

/-- Copy a `marks` stream raw. -/
def cpM (s o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .whs s (.seq (emitC o OP true) (.seq (.fwd s) (.seq (.ifs s (emitC o OP true) (emitC o OP false)) (.fwd s))))

theorem cpM_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (OP : Fin nr) :
    ∀ (u : List Bool) (σ : WState ns nr) (pre : List Bool), σ.st s = pre ++ marks u → σ.sh s = pre.length →
      σ.sh o = (σ.st o).length → σ.val OP + 2 * u.length ≤ cap →
      WExec cap (cpM s o OP) σ ((appendO σ o OP (marks u)).seth s (pre.length + 2 * u.length)) (22 * u.length + 1)
  | [], σ, pre, hs, hsh, ho, _ => by
    have hb : wbit σ s = false := by unfold wbit readTapeBit; rw [hs, hsh]; simp [marks]
    have e : (appendO σ o OP (marks [])).seth s (pre.length + 2 * ([] : List Bool).length) = σ := by
      rw [show marks ([] : List Bool) = [] from rfl, appendO_nil]; simp only [List.length_nil, Nat.mul_zero,
        Nat.add_zero]; rw [← hsh, wseth_same]
    rw [e]; exact WExec.whsF hb
  | b :: u, σ, pre, hs, hsh, ho, hc => by
    have hso' : o ≠ s := fun h => hso h.symm
    have hb : wbit σ s = true := by unfold wbit readTapeBit; rw [hs, hsh]; simp [marks]
    have h1 := emitC_spec cap o OP true σ ho (by simp at hc; omega)
    set σ1 := ((σ.sets o ((σ.st o) ++ [true])).seth o (σ.sh o + 1)).setv OP (σ.val OP + 1) with hσ1
    have h2 := WExec.fwd (cap := cap) s σ1
    set σ2 := σ1.seth s (σ1.sh s + 1) with hσ2
    have hb2 : wbit σ2 s = b := by
      unfold wbit readTapeBit
      simp only [hσ2, hσ1, WState.seth_st, WState.setv_st, WState.sets_st, WState.seth_sh, WState.setv_sh,
        WState.sets_sh, Function.update_apply, if_neg hso, if_true]
      rw [hs, hsh]; simp [marks]
    have ho2 : σ2.sh o = (σ2.st o).length := by
      simp [hσ2, hσ1, Function.update_apply, hso', ho]
    have h3 : WExec cap (.ifs s (emitC o OP true) (emitC o OP false)) σ2
        (((σ2.sets o ((σ2.st o) ++ [b])).seth o (σ2.sh o + 1)).setv OP (σ2.val OP + 1)) 8 := by
      cases b
      · exact WExec.ifsF hb2 (emitC_spec cap o OP false σ2 ho2 (by simp [hσ2, hσ1] at hc ⊢; omega))
      · exact WExec.ifsT hb2 (emitC_spec cap o OP true σ2 ho2 (by simp [hσ2, hσ1] at hc ⊢; omega))
    set σ3 := ((σ2.sets o ((σ2.st o) ++ [b])).seth o (σ2.sh o + 1)).setv OP (σ2.val OP + 1) with hσ3
    have h4 := WExec.fwd (cap := cap) s σ3
    set σ4 := σ3.seth s (σ3.sh s + 1) with hσ4
    have ih := cpM_spec s o hso OP u σ4 (pre ++ [true, b])
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hso, hs, marks])
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hso, hsh]; try omega)
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hso', ho]; try omega)
      (by simp [hσ4, hσ3, hσ2, hσ1] at hc ⊢; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ih) ?_ (by simp; omega)
    apply WState.eq
    · funext j; by_cases hj : j = s
      · subst hj; simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hso]; omega
      · by_cases hjo : j = o
        · subst hjo; simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj, marks]; omega
        · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj, hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hσ4, hσ3, hσ2, hσ1, marks]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hjo]
    · funext j; by_cases hj : j = OP
      · subst hj; simp [hσ4, hσ3, hσ2, hσ1, marks]; omega
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj]
    · rfl

end Copy

/-! ## `⌈log₂ x⌉` in unary -/

section Clog
variable {ns nr : ℕ} (cap : ℕ) (C : Fin 7 ↪ Fin nr)

def g6 : Fin 6 ↪ Fin 7 := ⟨![0, 1, 3, 4, 5, 6], by decide⟩

/-- One doubling: `f := 0`, `p := 2p`, `e += 1`, `f := [p < x]`; registers `C = (x, p, e, f, t, u, w)`. -/
def clogBody : WM ns nr :=
  .seq (WM.clear (C 3)) (.seq (PrimAsm.ParseNat.dbl (C 1) (C 4)) (.seq (.inc (C 2))
    (PrimAsm.UnaryArith.gtFlagW (g6.trans C))))

/-- `e := ⌈log₂ x⌉`, `p := 2^e`. -/
def clogL : WM ns nr :=
  .seq (.inc (C 1)) (.seq (PrimAsm.UnaryArith.gtFlagW (g6.trans C)) (.whr (C 3) (clogBody C)))

/-- The loop's state after `k` doublings. -/
def clS (σ : WState ns nr) (X k : ℕ) : WState ns nr :=
  ((σ.setv (C 1) (2 ^ k)).setv (C 2) k).setv (C 3) (if 2 ^ k < X then 1 else 0)

theorem clog_loop (σ : WState ns nr) (X : ℕ) (hX : 1 ≤ X) (hx : σ.val (C 0) = X) (h4 : σ.val (C 4) = 0)
    (h5 : σ.val (C 5) = 0) (h6 : σ.val (C 6) = 0) (hcap : 4 * X + Nat.clog 2 X + 4 ≤ cap) :
    ∀ n k, k + n = Nat.clog 2 X →
      WExec cap (.whr (C 3) (clogBody C)) (clS C σ X k) (clS C σ X (Nat.clog 2 X)) (n * (200 * X + 200) + 1) := by
  have hne : ∀ {i j : Fin 7}, i ≠ j → C i ≠ C j := fun h => C.injective.ne h
  have hlt : ∀ k, 2 ^ k < X ↔ k < Nat.clog 2 X := by
    intro k
    constructor
    · intro h; by_contra hc; push Not at hc
      have := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).1 hc; omega
    · intro h; by_contra hc; push Not at hc
      have := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).2 hc; omega
  have hpc : 2 ^ Nat.clog 2 X ≤ 2 * X := by
    rcases Nat.lt_or_ge 1 X with h | h
    · have := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h
      rw [Nat.pred_eq_sub_one] at this
      have hc : 1 ≤ Nat.clog 2 X := Nat.clog_pos (by norm_num) h
      have e : 2 ^ Nat.clog 2 X = 2 * 2 ^ (Nat.clog 2 X - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    · have : Nat.clog 2 X = 0 := Nat.clog_of_right_le_one h 2
      rw [this]; simp; omega
  intro n
  induction n with
  | zero =>
    intro k hk
    rw [Nat.add_zero] at hk
    subst hk
    have hf : (clS C σ X (Nat.clog 2 X)).val (C 3) = 0 := by
      simp [clS, (hlt _).not.mpr (lt_irrefl _)]
    exact WExec.mono (WExec.whrF hf) (by omega)
  | succ n ih =>
    intro k hk
    have hk' : k < Nat.clog 2 X := by omega
    have hpk : 2 ^ k < X := (hlt k).mpr hk'
    have hf : (clS C σ X k).val (C 3) = 1 := by simp [clS, hpk]
    -- the body
    have b1 := wclear_spec cap (C 3) 1 (clS C σ X k) hf (by omega)
    set σ1 := (clS C σ X k).setv (C 3) 0 with hσ1
    have v14 : σ1.val (C 4) = 0 := by
      simp [hσ1, clS, hne (show (4 : Fin 7) ≠ 3 by decide), hne (show (4 : Fin 7) ≠ 2 by decide),
        hne (show (4 : Fin 7) ≠ 1 by decide), h4]
    have v11 : σ1.val (C 1) = 2 ^ k := by
      simp [hσ1, clS, hne (show (1 : Fin 7) ≠ 3 by decide), hne (show (1 : Fin 7) ≠ 2 by decide)]
    have b2 := PrimAsm.ParseNat.dbl_spec cap (C 1) (C 4) (hne (by decide)) σ1 v14 (by rw [v11]; omega)
    rw [v11] at b2
    set σ2 := σ1.setv (C 1) (2 * 2 ^ k) with hσ2
    have v22 : σ2.val (C 2) = k := by
      simp [hσ2, hσ1, clS, hne (show (2 : Fin 7) ≠ 1 by decide), hne (show (2 : Fin 7) ≠ 3 by decide)]
    have b3 := WExec.inc (cap := cap) (C 2) σ2 (by rw [v22]; omega)
    rw [v22] at b3
    set σ3 := σ2.setv (C 2) (k + 1) with hσ3
    have b4 := PrimAsm.UnaryArith.gtFlagW_spec cap (g6.trans C) σ3
      (by show σ3.val (C 3) = 0; simp [hσ3, hσ2, hσ1, hne (show (3 : Fin 7) ≠ 2 by decide),
        hne (show (3 : Fin 7) ≠ 1 by decide)])
      (by show σ3.val (C 4) = 0; simp [hσ3, hσ2, hne (show (4 : Fin 7) ≠ 2 by decide),
        hne (show (4 : Fin 7) ≠ 1 by decide), v14])
      (by show σ3.val (C 5) = 0; simp [hσ3, hσ2, hσ1, clS, hne (show (5 : Fin 7) ≠ 2 by decide),
        hne (show (5 : Fin 7) ≠ 1 by decide), hne (show (5 : Fin 7) ≠ 3 by decide), h5])
      (by show σ3.val (C 6) = 0; simp [hσ3, hσ2, hσ1, clS, hne (show (6 : Fin 7) ≠ 2 by decide),
        hne (show (6 : Fin 7) ≠ 1 by decide), hne (show (6 : Fin 7) ≠ 3 by decide), h6])
      (by show σ3.val (C 0) ≤ cap; simp [hσ3, hσ2, hσ1, clS, hne (show (0 : Fin 7) ≠ 2 by decide),
        hne (show (0 : Fin 7) ≠ 1 by decide), hne (show (0 : Fin 7) ≠ 3 by decide), hx]; omega)
      (by show σ3.val (C 1) ≤ cap; simp [hσ3, hσ2, hne (show (1 : Fin 7) ≠ 2 by decide)]; omega)
      (by omega)
    have v30 : σ3.val (C 0) = X := by
      simp [hσ3, hσ2, hσ1, clS, hne (show (0 : Fin 7) ≠ 2 by decide), hne (show (0 : Fin 7) ≠ 1 by decide),
        hne (show (0 : Fin 7) ≠ 3 by decide), hx]
    have v31 : σ3.val (C 1) = 2 * 2 ^ k := by simp [hσ3, hσ2, hne (show (1 : Fin 7) ≠ 2 by decide)]
    have t0 : (g6.trans C) 0 = C 0 := rfl
    have t1 : (g6.trans C) 1 = C 1 := rfl
    have t2 : (g6.trans C) 2 = C 3 := rfl
    rw [t0, t1, t2, v30, v31] at b4
    have e4 : σ3.setv (C 3) (if 2 * 2 ^ k < X then 1 else 0) = clS C σ X (k + 1) := by
      rw [hσ3, hσ2, hσ1]
      simp only [clS, pow_succ]
      refine WState.eq rfl rfl ?_ rfl
      funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases a3 : j = C 3
      · subst a3; simp [hne (show (3 : Fin 7) ≠ 2 by decide), hne (show (3 : Fin 7) ≠ 1 by decide), Nat.mul_comm]
      by_cases a2 : j = C 2
      · subst a2; simp [hne (show (2 : Fin 7) ≠ 3 by decide), hne (show (2 : Fin 7) ≠ 1 by decide)]
      by_cases a1 : j = C 1
      · subst a1; simp [hne (show (1 : Fin 7) ≠ 3 by decide), hne (show (1 : Fin 7) ≠ 2 by decide), Nat.mul_comm]
      simp [a3, a2, a1]
    rw [e4] at b4
    have hrec := ih (k + 1) (by omega)
    refine WExec.mono (WExec.whrT (by rw [hf]; omega) (WExec.seq b1 (WExec.seq b2 (WExec.seq b3 b4))) hrec) ?_
    have : 2 ^ k ≤ X := le_of_lt hpk
    nlinarith

end Clog

section ClogFull
variable {ns nr : ℕ} (cap : ℕ) (C : Fin 7 ↪ Fin nr)

theorem clogL_spec (σ : WState ns nr) (X : ℕ) (hX : 1 ≤ X) (hx : σ.val (C 0) = X) (h1 : σ.val (C 1) = 0)
    (h2 : σ.val (C 2) = 0) (h3 : σ.val (C 3) = 0) (h4 : σ.val (C 4) = 0) (h5 : σ.val (C 5) = 0)
    (h6 : σ.val (C 6) = 0) (hcap : 4 * X + Nat.clog 2 X + 4 ≤ cap) :
    WExec cap (clogL C) σ (clS C σ X (Nat.clog 2 X)) (Nat.clog 2 X * (200 * X + 200) + 200 * X + 200) := by
  have hne : ∀ {i j : Fin 7}, i ≠ j → C i ≠ C j := fun h => C.injective.ne h
  have a1 := WExec.inc (cap := cap) (C 1) σ (by omega)
  rw [h1] at a1
  set σ1 := σ.setv (C 1) (0 + 1) with hσ1
  have a2 := PrimAsm.UnaryArith.gtFlagW_spec cap (g6.trans C) σ1
    (by show σ1.val (C 3) = 0; simp [hσ1, hne (show (3 : Fin 7) ≠ 1 by decide), h3])
    (by show σ1.val (C 4) = 0; simp [hσ1, hne (show (4 : Fin 7) ≠ 1 by decide), h4])
    (by show σ1.val (C 5) = 0; simp [hσ1, hne (show (5 : Fin 7) ≠ 1 by decide), h5])
    (by show σ1.val (C 6) = 0; simp [hσ1, hne (show (6 : Fin 7) ≠ 1 by decide), h6])
    (by show σ1.val (C 0) ≤ cap; simp [hσ1, hne (show (0 : Fin 7) ≠ 1 by decide), hx]; omega)
    (by show σ1.val (C 1) ≤ cap; simp [hσ1]; omega) (by omega)
  have t0 : (g6.trans C) 0 = C 0 := rfl
  have t1 : (g6.trans C) 1 = C 1 := rfl
  have t2 : (g6.trans C) 2 = C 3 := rfl
  have v0 : σ1.val (C 0) = X := by simp [hσ1, hne (show (0 : Fin 7) ≠ 1 by decide), hx]
  have v1 : σ1.val (C 1) = 1 := by simp [hσ1]
  rw [t0, t1, t2, v0, v1] at a2
  have e0 : σ1.setv (C 3) (if 1 < X then 1 else 0) = clS C σ X 0 := by
    rw [hσ1]
    simp only [clS, pow_zero]
    refine WState.eq rfl rfl ?_ rfl
    funext j
    simp only [WState.setv_val, Function.update_apply]
    by_cases a3 : j = C 3
    · subst a3; simp [hne (show (3 : Fin 7) ≠ 2 by decide), hne (show (3 : Fin 7) ≠ 1 by decide)]
    by_cases a2 : j = C 2
    · subst a2; simp [hne (show (2 : Fin 7) ≠ 3 by decide), hne (show (2 : Fin 7) ≠ 1 by decide), h2]
    by_cases a1 : j = C 1
    · subst a1; simp [hne (show (1 : Fin 7) ≠ 3 by decide), hne (show (1 : Fin 7) ≠ 2 by decide)]
    simp [a3, a2, a1]
  rw [e0] at a2
  have hl := clog_loop cap C σ X hX hx h4 h5 h6 hcap (Nat.clog 2 X) 0 (by omega)
  refine WExec.mono (WExec.seq a1 (WExec.seq a2 hl)) ?_
  nlinarith

end ClogFull

/-! ## The layout: streams `G POPS GT NP QS OUT`; registers `0 … 7` the writer's, `8 … 14` the logarithm's -/

abbrev AS := WState 6 24

def Rw : Fin 8 ↪ Fin 24 := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
def Cc : Fin 7 ↪ Fin 24 := ⟨fun i => ⟨8 + i.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- `r += c`. -/
def incN (r : Fin 24) : ℕ → WM 6 24
  | 0 => .skip
  | c + 1 => .seq (incN r c) (.inc r)

theorem incN_spec (cap : ℕ) (r : Fin 24) : ∀ (c : ℕ) (σ : AS), σ.val r + c ≤ cap →
    WExec cap (incN r c) σ (σ.setv r (σ.val r + c)) (4 * c)
  | 0, σ, _ => by simp only [Nat.add_zero, wsetv_same]; exact WExec.skip σ
  | c + 1, σ, h => by
    have h1 := incN_spec cap r c σ (by omega)
    have h2 := WExec.inc (cap := cap) r (σ.setv r (σ.val r + c)) (by simp; omega)
    refine WExec.mono (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl) (by omega)
    simp only [WState.setv_val, Function.update_self, wsetv_setv]; congr 1

/-- **The star multiplier** `r = rowBr cr q` from `1^q`. -/
def rProg (cr : ℕ) : WM 6 24 :=
  .seq (PrimAsm.SymDec.readUW 4 17) (.seq (FinalPass.Hash4.wcopyR 17 8 19) (.seq (.inc 8) (.seq (.inc 8)
    (.seq (clogL Cc) (.seq (WM.move 10 0) (.seq (bitLenM Rw) (.seq (WM.move 4 18) (.seq (.dec 18)
      (.seq (incN 18 cr) (.seq (PrimAsm.ParseNat.dbl 18 19) (WM.clear 0)))))))))))

theorem rProg_spec (cap cr q : ℕ) (σ : AS) (h4 : σ.st 4 = List.replicate q true) (hsh : σ.sh 4 = 0)
    (hv : ∀ r, σ.val r = 0) (hcap : 20 * (q + 2) + 4 * cr + 100 ≤ cap) :
    ∃ τ : AS, WExec cap (rProg cr) σ τ (1000 * (q + 3) * (q + 3) + 30 * cr + 1000) ∧
      τ.val 17 = q ∧ τ.val 18 = Ledger.rowBr cr q ∧ (∀ r : Fin 24, r.val < 8 → τ.val r = 0) ∧
      τ.val 15 = 0 ∧ τ.val 16 = 0 ∧ τ.val 19 = 0 ∧ τ.st = σ.st ∧ τ.cell = σ.cell ∧ τ.sh 0 = σ.sh 0 ∧ τ.sh 1 = σ.sh 1 ∧
      τ.sh 2 = σ.sh 2 ∧ τ.sh 3 = σ.sh 3 ∧ τ.sh 5 = σ.sh 5 := by
  set e := Nat.clog 2 (q + 2) with he
  have heL : e = Ledger.Lq q := rfl
  have hq2 : 2 ≤ q + 2 := by omega
  have he1 : 1 ≤ e := Nat.clog_pos (by norm_num) (by omega)
  have hele : e ≤ q + 2 := by
    have := Nat.clog_le_of_le_pow (b := 2) (x := q + 2) (y := q + 2) (Nat.lt_two_pow_self).le; omega
  have hnbl : natBitLength e ≤ e + 1 := by
    unfold natBitLength; have := Nat.log_le_self 2 e; omega
  -- 1. q
  have s1 := PrimAsm.SymDec.readU_spec cap 4 17 q 0 σ h4 hsh (hv 17) (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : AS, τ = (σ.seth 4 q).setv 17 (0 + q) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  -- 2–4. x := q + 2
  have s2 := FinalPass.Hash4.wcopyR_spec cap 17 8 19 (by decide) (by decide) (by decide) σ1
    (by rw [hσ1]; simp [hv]) (by rw [hσ1]; simp [hv]) (by rw [hσ1]; simp; omega)
  have v117 : σ1.val 17 = q := by rw [hσ1]; simp
  rw [v117] at s2
  have s3 := WExec.inc (cap := cap) 8 (σ1.setv 8 q) (by simp; omega)
  have s4 := WExec.inc (cap := cap) 8 ((σ1.setv 8 q).setv 8 ((σ1.setv 8 q).val 8 + 1)) (by simp; omega)
  obtain ⟨σ4, hσ4⟩ : ∃ τ : AS, τ = σ1.setv 8 (q + 2) := ⟨_, rfl⟩
  have e4 : ((σ1.setv 8 q).setv 8 ((σ1.setv 8 q).val 8 + 1)).setv 8
      (((σ1.setv 8 q).setv 8 ((σ1.setv 8 q).val 8 + 1)).val 8 + 1) = σ4 := by
    rw [hσ4]; simp only [WState.setv_val, Function.update_self, wsetv_setv]
  rw [e4] at s4
  have g4 : ∀ r : Fin 24, r ≠ 8 → r ≠ 17 → σ4.val r = 0 := fun r a b => by
    rw [hσ4, hσ1]; simp [a, b, hv]
  -- 5. the logarithm
  have s5 := clogL_spec cap Cc σ4 (q + 2) (by omega) (by rw [hσ4]; rfl)
    (g4 9 (by decide) (by decide)) (g4 10 (by decide) (by decide)) (g4 11 (by decide) (by decide))
    (g4 12 (by decide) (by decide)) (g4 13 (by decide) (by decide)) (g4 14 (by decide) (by decide)) (by omega)
  rw [← he] at s5
  obtain ⟨σ5, hσ5⟩ : ∃ τ : AS, τ = clS Cc σ4 (q + 2) e := ⟨_, rfl⟩
  rw [← hσ5] at s5
  have hf0 : ¬ 2 ^ e < q + 2 := by
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (q + 2); rw [← he] at this; omega
  have v5 : ∀ r : Fin 24, r ≠ 8 → r ≠ 17 → r ≠ 9 → r ≠ 10 → σ5.val r = 0 := fun r a b c d => by
    rw [hσ5]; unfold clS
    by_cases h11 : r = 11
    · subst h11; simp [Cc, hf0]
    · have c1 : r ≠ Cc 1 := c
      have c2 : r ≠ Cc 2 := d
      have c3 : r ≠ Cc 3 := h11
      simp [c1, c2, c3]; exact g4 r a b
  have v510 : σ5.val 10 = e := by rw [hσ5]; simp [clS, Cc]
  have v517 : σ5.val 17 = q := by
    rw [hσ5]; simp [clS, Cc]; rw [hσ4]; simp; exact v117
  -- 6. R 0 := e
  have s6 := wmove_spec cap 10 0 (by decide) e σ5 v510 (by rw [v510]; omega)
    (by rw [v510, v5 0 (by decide) (by decide) (by decide) (by decide)]; omega)
  rw [v5 0 (by decide) (by decide) (by decide) (by decide), v510, Nat.zero_add] at s6
  obtain ⟨σ6, hσ6⟩ : ∃ τ : AS, τ = (σ5.setv 10 0).setv 0 e := ⟨_, rfl⟩
  rw [← hσ6] at s6
  have v6 : ∀ r : Fin 24, r ≠ 8 → r ≠ 17 → r ≠ 9 → r ≠ 0 → σ6.val r = 0 := fun r a b c d => by
    rw [hσ6]; by_cases h10 : r = 10
    · subst h10; simp
    · simp [d, h10]; exact v5 r a b c h10
  -- 7. R 4 := nbl e
  have s7 := bitLenM_spec cap Rw σ6 (v6 1 (by decide) (by decide) (by decide) (by decide))
    (v6 2 (by decide) (by decide) (by decide) (by decide)) (v6 3 (by decide) (by decide) (by decide) (by decide))
    (v6 4 (by decide) (by decide) (by decide) (by decide)) (v6 6 (by decide) (by decide) (by decide) (by decide))
    (by show σ6.val 0 + 2 ≤ cap; rw [hσ6]; simp; omega)
  have v60 : σ6.val 0 = e := by rw [hσ6]; simp
  have tr0 : Rw 0 = 0 := rfl
  have tr4 : Rw 4 = 4 := rfl
  rw [tr0, tr4, v60] at s7
  -- 8. rv := nbl e
  have s8 := wmove_spec cap 4 18 (by decide) (natBitLength e) (σ6.setv 4 (natBitLength e)) (by simp)
    (by simp; omega) (by simp; rw [v6 18 (by decide) (by decide) (by decide) (by decide)]; omega)
  obtain ⟨σ8, hσ8⟩ : ∃ τ : AS, τ = ((σ6.setv 4 (natBitLength e)).setv 4 0).setv 18 (natBitLength e) := ⟨_, rfl⟩
  have e8 : ((σ6.setv 4 (natBitLength e)).setv 4 0).setv 18 ((σ6.setv 4 (natBitLength e)).val 18 +
      (σ6.setv 4 (natBitLength e)).val 4) = σ8 := by
    rw [hσ8]; simp [v6 18 (by decide) (by decide) (by decide) (by decide)]
  rw [e8] at s8
  -- 9. rv := log e
  have v818 : σ8.val 18 = natBitLength e := by rw [hσ8]; simp
  have s9 := WExec.dec (cap := cap) 18 σ8 (by rw [v818]; omega)
  rw [v818] at s9
  -- 10. rv += cr
  have s10 := incN_spec cap 18 cr (σ8.setv 18 (natBitLength e - 1)) (by simp; omega)
  -- 11. rv := 2 rv
  have s11 := PrimAsm.ParseNat.dbl_spec cap 18 19 (by decide)
    ((σ8.setv 18 (natBitLength e - 1)).setv 18 ((σ8.setv 18 (natBitLength e - 1)).val 18 + cr))
    (by rw [hσ8]; simp [v6 19 (by decide) (by decide) (by decide) (by decide)]) (by simp; omega)
  -- 12. R 0 := 0
  set σ11 := ((σ8.setv 18 (natBitLength e - 1)).setv 18 ((σ8.setv 18 (natBitLength e - 1)).val 18 + cr)).setv 18
    (2 * ((σ8.setv 18 (natBitLength e - 1)).setv 18 ((σ8.setv 18 (natBitLength e - 1)).val 18 + cr)).val 18)
    with hσ11
  have v110 : σ11.val 0 = e := by rw [hσ11, hσ8]; simp; exact v60
  have s12 := wclear_spec cap 0 e σ11 v110 (by rw [v110]; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 s12))))))))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hbig2 : e * (200 * (q + 2) + 200) + 200 * (q + 2) + 200 + 400 * (q + 3) ≤ 1000 * (q + 3) * (q + 3) := by
      have h1 : e * (200 * (q + 2) + 200) ≤ (q + 2) * (200 * (q + 2) + 200) := Nat.mul_le_mul_right _ hele
      nlinarith
    have hk : ((σ8.setv 18 (natBitLength e - 1)).setv 18 ((σ8.setv 18 (natBitLength e - 1)).val 18 + cr)).val 18 =
        natBitLength e - 1 + cr := by simp
    have h17 := v517
    have h18 := v818
    have h0 := v110
    have h117 : σ1.val 17 = q := v117
    omega
  · rw [hσ11, hσ8]; simp; rw [hσ6]; simp; exact v517
  · rw [hσ11, hσ8]; simp
    unfold Ledger.rowBr
    rw [← heL]
    unfold natBitLength; omega
  · intro r hr
    simp only [WState.setv_val, Function.update_apply]
    by_cases h0 : r = 0
    · simp [h0]
    · have hr18 : r ≠ 18 := fun h => by subst h; simp at hr
      simp only [h0, if_false, hσ11, WState.setv_val, Function.update_apply, hr18, hσ8]
      by_cases h4 : r = 4
      · subst h4; simp
      · simp only [h4, if_false]
        exact v6 r (fun h => by subst h; simp at hr) (fun h => by subst h; simp at hr)
          (fun h => by subst h; simp at hr) h0
  · simp [hσ11, hσ8]; exact v6 15 (by decide) (by decide) (by decide) (by decide)
  · simp [hσ11, hσ8]; exact v6 16 (by decide) (by decide) (by decide) (by decide)
  · simp [hσ11, hσ8]; exact v6 19 (by decide) (by decide) (by decide) (by decide)
  · simp [hσ11, hσ8, hσ6, hσ5, clS, hσ4, hσ1]
  · simp [hσ11, hσ8, hσ6, hσ5, clS, hσ4, hσ1]
  · simp [hσ11, hσ8, hσ6, hσ5, clS, hσ4, hσ1]
  · simp [hσ11, hσ8, hσ6, hσ5, clS, hσ4, hσ1]
  · simp [hσ11, hσ8, hσ6, hσ5, clS, hσ4, hσ1]
  · simp [hσ11, hσ8, hσ6, hσ5, clS, hσ4, hσ1]
  · simp [hσ11, hσ8, hσ6, hσ5, clS, hσ4, hσ1]

/-- One field: `natWord (R 0)` written, then `R 0 := 0`. -/
theorem wn_step (cap : ℕ) (σ : AS) (v : ℕ) (h0 : σ.val 0 = v) (hz : ∀ i : Fin 24, 1 ≤ i.val → i.val ≤ 6 → σ.val i = 0)
    (ho : σ.sh 5 = (σ.st 5).length) (hcap : v + σ.val 7 + 6 * natBitLength v + 6 ≤ cap) :
    WExec cap (.seq (writeNatM 5 Rw) (WM.clear 0)) σ ((appendO σ 5 7 (marks (natWord v))).setv 0 0)
      ((natBitLength v + 10) * (100 * v + 200) + 1 + (3 * v + 1)) := by
  have w := writeNatM_spec cap 5 Rw σ (hz 1 (by decide) (by decide)) (hz 2 (by decide) (by decide))
    (hz 3 (by decide) (by decide)) (hz 4 (by decide) (by decide)) (hz 5 (by decide) (by decide))
    (hz 6 (by decide) (by decide)) ho (by
      have t0 : Rw 0 = 0 := rfl
      have t7 : Rw 7 = 7 := rfl
      rw [t0, t7, h0]; exact hcap)
  have t0 : Rw 0 = 0 := rfl
  have t7 : Rw 7 = 7 := rfl
  rw [t0, t7, h0] at w
  have c := wclear_spec cap 0 v (appendO σ 5 7 (marks (natWord v))) (by simp [h0]) (by simp [h0]; omega)
  exact WExec.seq w c

/-- **The writes**: `q`, `r`, `gt`, the gates, `np`, the populations, the frame's end. -/
def wProg : WM 6 24 :=
  .seq (PrimAsm.SymDec.readUW 2 15) (.seq (PrimAsm.SymDec.readUW 3 16)
    (.seq (FinalPass.Hash4.wcopyR 17 0 19) (.seq (.seq (writeNatM 5 Rw) (WM.clear 0))
      (.seq (WM.move 18 0) (.seq (.seq (writeNatM 5 Rw) (WM.clear 0))
        (.seq (WM.move 15 0) (.seq (.seq (writeNatM 5 Rw) (WM.clear 0))
          (.seq (cpM 0 5 7) (.seq (WM.move 16 0) (.seq (.seq (writeNatM 5 Rw) (WM.clear 0))
            (.seq (cpM 1 5 7) (emitC 5 7 false))))))))))))

theorem frameM (w : List Bool) : frame w = marks w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => show true :: b :: frame w = true :: b :: marks w ++ [false]; rw [ih]; rfl

/-- C1's request word from its pieces. -/
def reqWord (q r gt np : ℕ) (Gs Ps : List Bool) : List Bool :=
  natWord q ++ natWord r ++ natWord gt ++ Gs ++ natWord np ++ Ps

theorem frame_reqWord (q r gt np : ℕ) (Gs Ps : List Bool) :
    frame (reqWord q r gt np Gs Ps) = marks (natWord q) ++ marks (natWord r) ++ marks (natWord gt) ++ marks Gs ++
      marks (natWord np) ++ marks Ps ++ [false] := by
  rw [frameM]; unfold reqWord; simp [marks_append]

/-- One field's cost. -/
def wnC (v : ℕ) : ℕ := (natBitLength v + 10) * (100 * v + 200) + 1 + (3 * v + 1)

/-- The writes' cost. -/
def wCost (q r gt np : ℕ) (Gs Ps : List Bool) : ℕ :=
  (7 * gt + 1) + 1 + ((7 * np + 1) + 1 + ((18 * q + 3) + 1 + (wnC q + 1 + ((7 * r + 1) + 1 + (wnC r + 1 +
    ((7 * gt + 1) + 1 + (wnC gt + 1 + ((22 * Gs.length + 1) + 1 + ((7 * np + 1) + 1 + (wnC np + 1 +
      ((22 * Ps.length + 1) + 1 + 7)))))))))))

theorem wProg_spec (cap q r gt np : ℕ) (Gs Ps : List Bool) (ρ : AS) (h17 : ρ.val 17 = q) (h18 : ρ.val 18 = r)
    (hz : ∀ i : Fin 24, i.val < 8 → ρ.val i = 0) (h15 : ρ.val 15 = 0) (h16 : ρ.val 16 = 0) (h19 : ρ.val 19 = 0)
    (s0 : ρ.st 0 = marks Gs) (s1 : ρ.st 1 = marks Ps) (s2 : ρ.st 2 = List.replicate gt true)
    (s3 : ρ.st 3 = List.replicate np true) (s5 : ρ.st 5 = []) (sh0 : ρ.sh 0 = 0) (sh1 : ρ.sh 1 = 0) (sh2 : ρ.sh 2 = 0)
    (sh3 : ρ.sh 3 = 0) (sh5 : ρ.sh 5 = 0)
    (hcap : q + r + gt + np + 6 * (natBitLength q + natBitLength r + natBitLength gt + natBitLength np) +
      (frame (reqWord q r gt np Gs Ps)).length + 50 ≤ cap) :
    ∃ τ : AS, WExec cap wProg ρ τ (wCost q r gt np Gs Ps) ∧ τ.st 5 = frame (reqWord q r gt np Gs Ps) ∧
      (∀ i : Fin 7, i ≠ 5 → τ.st i = ρ.st i) := by
  have hfl := frame_reqWord q r gt np Gs Ps
  have hlen := congrArg List.length hfl
  simp only [List.length_append, List.length_singleton] at hlen
  -- the counts
  have w1 := PrimAsm.SymDec.readU_spec cap 2 15 gt 0 ρ s2 sh2 h15 (by omega)
  obtain ⟨ρ1, hρ1⟩ : ∃ τ : AS, τ = (ρ.seth 2 gt).setv 15 (0 + gt) := ⟨_, rfl⟩
  rw [← hρ1] at w1
  have w2 := PrimAsm.SymDec.readU_spec cap 3 16 np 0 ρ1 (by rw [hρ1]; simpa using s3) (by rw [hρ1]; simp [sh3])
    (by rw [hρ1]; simp [h16]) (by omega)
  obtain ⟨ρ2, hρ2⟩ : ∃ τ : AS, τ = (ρ1.seth 3 np).setv 16 (0 + np) := ⟨_, rfl⟩
  rw [← hρ2] at w2
  have g2 : ∀ i : Fin 24, i ≠ 15 → i ≠ 16 → ρ2.val i = ρ.val i := fun i a b => by rw [hρ2, hρ1]; simp [a, b]
  have t2 : ρ2.st = ρ.st := by rw [hρ2, hρ1]; rfl
  have sh25 : ρ2.sh 5 = 0 := by rw [hρ2, hρ1]; simp [sh5]
  -- q
  have w3 := FinalPass.Hash4.wcopyR_spec cap 17 0 19 (by decide) (by decide) (by decide) ρ2
    (by rw [g2 0 (by decide) (by decide)]; exact hz 0 (by decide)) (by rw [g2 19 (by decide) (by decide), h19])
    (by rw [g2 17 (by decide) (by decide), h17]; omega)
  rw [g2 17 (by decide) (by decide), h17] at w3
  obtain ⟨ρ3, hρ3⟩ : ∃ τ : AS, τ = ρ2.setv 0 q := ⟨_, rfl⟩
  rw [← hρ3] at w3
  have w4 := wn_step cap ρ3 q (by rw [hρ3]; simp)
    (fun i a b => by rw [hρ3]; simp [show i ≠ 0 from fun h => by subst h; simp at a]; rw [g2 i (by
      intro h; subst h; simp at b) (by intro h; subst h; simp at b)]; exact hz i (by omega))
    (by rw [hρ3]; simp [t2, s5, sh25])
    (by rw [hρ3]; simp [show (7 : Fin 24) ≠ 0 by decide]; rw [g2 7 (by decide) (by decide), hz 7 (by decide)]; omega)
  obtain ⟨ρ4, hρ4⟩ : ∃ τ : AS, τ = (appendO ρ3 5 7 (marks (natWord q))).setv 0 0 := ⟨_, rfl⟩
  rw [← hρ4] at w4
  -- r
  have v418 : ρ4.val 18 = r := by rw [hρ4, hρ3]; simp; rw [g2 18 (by decide) (by decide), h18]
  have v40 : ρ4.val 0 = 0 := by rw [hρ4]; simp
  have w5 := wmove_spec cap 18 0 (by decide) r ρ4 v418 (by rw [v418]; omega) (by rw [v418, v40]; omega)
  rw [v418, v40, Nat.zero_add] at w5
  obtain ⟨ρ5, hρ5⟩ : ∃ τ : AS, τ = (ρ4.setv 18 0).setv 0 r := ⟨_, rfl⟩
  rw [← hρ5] at w5
  have v57 : ρ5.val 7 = (marks (natWord q)).length := by
    rw [hρ5, hρ4, hρ3]; simp; rw [g2 7 (by decide) (by decide), hz 7 (by decide)]
  have w6 := wn_step cap ρ5 r (by rw [hρ5]; simp)
    (fun i a b => by
      rw [hρ5, hρ4, hρ3]
      have i0 : i ≠ 0 := fun h => by subst h; simp at a
      have i7 : i ≠ 7 := fun h => by subst h; simp at b
      have i18 : i ≠ 18 := fun h => by subst h; simp at b
      simp [i0, i7, i18]; rw [g2 i (fun h => by subst h; simp at b) (fun h => by subst h; simp at b)]
      exact hz i (by omega))
    (by rw [hρ5, hρ4, hρ3]; simp [t2, s5, sh25])
    (by rw [v57]; simp only [C1Rng.marks_length] at hlen ⊢; omega)
  obtain ⟨ρ6, hρ6⟩ : ∃ τ : AS, τ = (appendO ρ5 5 7 (marks (natWord r))).setv 0 0 := ⟨_, rfl⟩
  rw [← hρ6] at w6
  -- gt
  have v615 : ρ6.val 15 = gt := by
    rw [hρ6, hρ5, hρ4, hρ3]; simp; rw [hρ2, hρ1]; simp
  have v60 : ρ6.val 0 = 0 := by rw [hρ6]; simp
  have w7 := wmove_spec cap 15 0 (by decide) gt ρ6 v615 (by rw [v615]; omega) (by rw [v615, v60]; omega)
  rw [v615, v60, Nat.zero_add] at w7
  obtain ⟨ρ7, hρ7⟩ : ∃ τ : AS, τ = (ρ6.setv 15 0).setv 0 gt := ⟨_, rfl⟩
  rw [← hρ7] at w7
  have v77 : ρ7.val 7 = (marks (natWord q)).length + (marks (natWord r)).length := by
    rw [hρ7, hρ6]; simp; rw [v57]; simp [C1Rng.marks_length]
  have gz7 : ∀ i : Fin 24, 1 ≤ i.val → i.val ≤ 6 → ρ7.val i = 0 := fun i a b => by
    rw [hρ7, hρ6, hρ5, hρ4, hρ3]
    have i0 : i ≠ 0 := fun h => by subst h; simp at a
    have i7 : i ≠ 7 := fun h => by subst h; simp at b
    have i18 : i ≠ 18 := fun h => by subst h; simp at b
    have i15 : i ≠ 15 := fun h => by subst h; simp at b
    simp [i0, i7, i18, i15]; rw [g2 i (fun h => by subst h; simp at b) (fun h => by subst h; simp at b)]
    exact hz i (by omega)
  have st7 : ρ7.st 5 = marks (natWord q) ++ marks (natWord r) := by
    rw [hρ7, hρ6, hρ5, hρ4, hρ3]; simp [t2, s5]
  have sh7 : ρ7.sh 5 = (ρ7.st 5).length := by
    rw [st7, hρ7, hρ6, hρ5, hρ4, hρ3]; simp [sh25]
  have w8 := wn_step cap ρ7 gt (by rw [hρ7]; simp) gz7 sh7
    (by rw [v77]; simp only [C1Rng.marks_length] at hlen ⊢; omega)
  obtain ⟨ρ8, hρ8⟩ : ∃ τ : AS, τ = (appendO ρ7 5 7 (marks (natWord gt))).setv 0 0 := ⟨_, rfl⟩
  rw [← hρ8] at w8
  -- the gates
  have st80 : ρ8.st 0 = [] ++ marks Gs := by
    rw [hρ8, hρ7, hρ6, hρ5, hρ4, hρ3]; simp [show (0 : Fin 7) ≠ 5 by decide, t2, s0]
  have sh80 : ρ8.sh 0 = ([] : List Bool).length := by
    rw [hρ8, hρ7, hρ6, hρ5, hρ4, hρ3]; simp [show (0 : Fin 7) ≠ 5 by decide]; rw [hρ2, hρ1]; simp [sh0]
  have sh85 : ρ8.sh 5 = (ρ8.st 5).length := by rw [hρ8]; simp [sh7]
  have v87 : ρ8.val 7 = (marks (natWord q)).length + (marks (natWord r)).length + (marks (natWord gt)).length := by
    rw [hρ8]; simp; rw [v77]; simp [C1Rng.marks_length]
  have w9 := cpM_spec cap 0 5 (by decide) 7 Gs ρ8 [] st80 sh80 sh85
    (by rw [v87]; simp only [C1Rng.marks_length] at hlen ⊢; omega)
  obtain ⟨ρ9, hρ9⟩ : ∃ τ : AS, τ = (appendO ρ8 5 7 (marks Gs)).seth 0 (([] : List Bool).length + 2 * Gs.length) :=
    ⟨_, rfl⟩
  rw [← hρ9] at w9
  -- np
  have v916 : ρ9.val 16 = np := by
    rw [hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3]; simp; rw [hρ2]; simp
  have v90 : ρ9.val 0 = 0 := by rw [hρ9, hρ8]; simp
  have w10 := wmove_spec cap 16 0 (by decide) np ρ9 v916 (by rw [v916]; omega) (by rw [v916, v90]; omega)
  rw [v916, v90, Nat.zero_add] at w10
  obtain ⟨ρ10, hρ10⟩ : ∃ τ : AS, τ = (ρ9.setv 16 0).setv 0 np := ⟨_, rfl⟩
  rw [← hρ10] at w10
  have gz10 : ∀ i : Fin 24, 1 ≤ i.val → i.val ≤ 6 → ρ10.val i = 0 := fun i a b => by
    rw [hρ10, hρ9, hρ8]
    have i0 : i ≠ 0 := fun h => by subst h; simp at a
    have i7 : i ≠ 7 := fun h => by subst h; simp at b
    have i16 : i ≠ 16 := fun h => by subst h; simp at b
    simp [i0, i7, i16]; exact gz7 i a b
  have st10 : ρ10.st 5 = marks (natWord q) ++ marks (natWord r) ++ marks (natWord gt) ++ marks Gs := by
    rw [hρ10, hρ9, hρ8]; simp [st7]
  have sh10 : ρ10.sh 5 = (ρ10.st 5).length := by
    rw [hρ10, hρ9, hρ8]; simp [show (5 : Fin 7) ≠ 0 by decide, sh7]; ring
  have v107 : ρ10.val 7 = (marks (natWord q)).length + (marks (natWord r)).length + (marks (natWord gt)).length +
      (marks Gs).length := by
    rw [hρ10, hρ9]; simp; rw [v87]; simp [C1Rng.marks_length]
  have w11 := wn_step cap ρ10 np (by rw [hρ10]; simp) gz10 sh10
    (by rw [v107]; simp only [C1Rng.marks_length] at hlen ⊢; omega)
  obtain ⟨ρ11, hρ11⟩ : ∃ τ : AS, τ = (appendO ρ10 5 7 (marks (natWord np))).setv 0 0 := ⟨_, rfl⟩
  rw [← hρ11] at w11
  -- the populations
  have st111 : ρ11.st 1 = [] ++ marks Ps := by
    rw [hρ11, hρ10, hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3]; simp [show (1 : Fin 7) ≠ 5 by decide, t2, s1]
  have sh111 : ρ11.sh 1 = ([] : List Bool).length := by
    rw [hρ11, hρ10, hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3]
    simp [show (1 : Fin 7) ≠ 5 by decide, show (1 : Fin 7) ≠ 0 by decide]; rw [hρ2, hρ1]; simp [sh1]
  have sh115 : ρ11.sh 5 = (ρ11.st 5).length := by rw [hρ11]; simp [sh10]
  have v117 : ρ11.val 7 = (marks (natWord q)).length + (marks (natWord r)).length + (marks (natWord gt)).length +
      (marks Gs).length + (marks (natWord np)).length := by
    rw [hρ11]; simp; rw [v107]; simp [C1Rng.marks_length]
  have w12 := cpM_spec cap 1 5 (by decide) 7 Ps ρ11 [] st111 sh111 sh115
    (by rw [v117]; simp only [C1Rng.marks_length] at hlen ⊢; omega)
  obtain ⟨ρ12, hρ12⟩ : ∃ τ : AS, τ = (appendO ρ11 5 7 (marks Ps)).seth 1 (([] : List Bool).length + 2 * Ps.length) :=
    ⟨_, rfl⟩
  rw [← hρ12] at w12
  -- the frame's end
  have sh125 : ρ12.sh 5 = (ρ12.st 5).length := by
    rw [hρ12]; simp [show (5 : Fin 7) ≠ 1 by decide, sh115]
  have v127 : ρ12.val 7 < cap := by
    rw [hρ12]; simp; rw [v117]; simp only [C1Rng.marks_length] at hlen ⊢; omega
  have w13 := emitC_spec cap 5 7 false ρ12 sh125 v127
  refine ⟨_, WExec.mono (WExec.seq w1 (WExec.seq w2 (WExec.seq w3 (WExec.seq w4 (WExec.seq w5 (WExec.seq w6
    (WExec.seq w7 (WExec.seq w8 (WExec.seq w9 (WExec.seq w10 (WExec.seq w11 (WExec.seq w12 w13))))))))))))
    (le_of_eq (by unfold wCost wnC; rfl)), ?_, ?_⟩
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [hfl, hρ12, hρ11]; simp [st10]
  · intro i hi
    simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply, hi, if_false]
    rw [hρ12, hρ11, hρ10, hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3]
    simp [hi, t2]

/-- **C1's request word.** -/
def asmW (cr : ℕ) : WM 6 24 := .seq (rProg cr) wProg

/-- The assembly's cost. -/
def asmCost (cr q gt np : ℕ) (Gs Ps : List Bool) : ℕ :=
  (1000 * (q + 3) * (q + 3) + 30 * cr + 1000) + 1 + wCost q (Ledger.rowBr cr q) gt np Gs Ps

theorem asmW_spec (cap cr q gt np : ℕ) (Gs Ps : List Bool) (σ : AS) (s0 : σ.st 0 = marks Gs) (s1 : σ.st 1 = marks Ps)
    (s2 : σ.st 2 = List.replicate gt true) (s3 : σ.st 3 = List.replicate np true) (s4 : σ.st 4 = List.replicate q true)
    (s5 : σ.st 5 = []) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0)
    (hcap1 : 20 * (q + 2) + 4 * cr + 100 ≤ cap)
    (hcap2 : q + Ledger.rowBr cr q + gt + np + 6 * (natBitLength q + natBitLength (Ledger.rowBr cr q) +
      natBitLength gt + natBitLength np) + (frame (reqWord q (Ledger.rowBr cr q) gt np Gs Ps)).length + 50 ≤ cap) :
    ∃ τ : AS, WExec cap (asmW cr) σ τ (asmCost cr q gt np Gs Ps) ∧
      τ.st 5 = frame (reqWord q (Ledger.rowBr cr q) gt np Gs Ps) ∧ (∀ i : Fin 7, i ≠ 5 → τ.st i = σ.st i) := by
  obtain ⟨τ1, e1, v17, v18, vz, v15, v16, v19, st1, -, sh0, sh1, sh2, sh3, sh5⟩ :=
    rProg_spec cap cr q σ s4 (hsh 4) hv hcap1
  obtain ⟨τ, e2, t5, tt⟩ := wProg_spec cap q (Ledger.rowBr cr q) gt np Gs Ps τ1 v17 v18 vz v15 v16 v19
    (by rw [st1, s0]) (by rw [st1, s1]) (by rw [st1, s2]) (by rw [st1, s3]) (by rw [st1, s5])
    (by rw [sh0, hsh]) (by rw [sh1, hsh]) (by rw [sh2, hsh]) (by rw [sh3, hsh]) (by rw [sh5, hsh]) hcap2
  exact ⟨τ, WExec.seq e1 e2, t5, fun i hi => by rw [tt i hi, st1]⟩

end NearCubicWires.WireExponent3_5.UnionMachine.C1Asm
