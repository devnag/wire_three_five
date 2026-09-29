import Proof.Wire_3_5.UnionMachine.FrontEntriesRef
import Proof.Wire_3_5.UnionMachine.FrontOracleField

/-! # C6 front, U1b: the validator of the guess's grid sums (P3:3669-3671)

Realizes "one sparse grid sum for each distinct PCPP variable. It rejects malformed descriptions [...] and
coefficients outside the fixed grid" (P3:3669-3671) for the entries after the oracle field (the codec,
`FrontEntriesRef.entScan`): a register program (C5's `WM`) reads the framed rest of the guess `frame w` and the entry
count `1^E`, and sets its cell to `(entScan E w).isSome`: `E` entries, each the grid word `b 1 0 x` (no negative zero)
and a canonical natural field (the atom's code), then zero padding only. It writes nothing else (the codes and signs
are re-read from the validated word by PA's readers where they are used).

Every phase after the first failure is skipped (`ifr BAD`), so a failure only needs a bounded cursor.
Main statement: **`entP_spec`**. Paper quantity: the validity of the guess's grid sums. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontEntries
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef

/-! ## Layout: streams `W E`; registers `K C T LB BAD F LP NEG PW PE` -/

abbrev ES := WState 1 10

local notation "sW" => (0 : Fin 2)
local notation "sE" => (1 : Fin 2)
local notation "rK" => (0 : Fin 10)
local notation "rC" => (1 : Fin 10)
local notation "rT" => (2 : Fin 10)
local notation "rLB" => (3 : Fin 10)
local notation "rBAD" => (4 : Fin 10)
local notation "rF" => (5 : Fin 10)
local notation "rLP" => (6 : Fin 10)
local notation "rNEG" => (7 : Fin 10)
local notation "rPW" => (8 : Fin 10)
local notation "rPE" => (9 : Fin 10)

/-- The validator's data: the two heads (each equal to its counter), the eight work registers, the cell. -/
structure D where
  pw : ℕ
  pe : ℕ
  K : ℕ
  C : ℕ
  T : ℕ
  LB : ℕ
  BAD : ℕ
  F : ℕ
  LP : ℕ
  NEG : ℕ
  cell : Bool

/-- The state of the data, on the witness rest `frame w` and the count `1^E`. -/
def st (w : List Bool) (E : ℕ) (d : D) : ES :=
  ⟨![d.pw, d.pe], ![frame w, List.replicate E true],
    ![d.K, d.C, d.T, d.LB, d.BAD, d.F, d.LP, d.NEG, d.pw, d.pe], d.cell⟩

def D.reg (d : D) (r : Fin 10) : ℕ := ![d.K, d.C, d.T, d.LB, d.BAD, d.F, d.LP, d.NEG, d.pw, d.pe] r

def D.setReg (d : D) (r : Fin 10) (x : ℕ) : D :=
  if r = rK then { d with K := x } else if r = rC then { d with C := x } else if r = rT then { d with T := x }
  else if r = rLB then { d with LB := x } else if r = rBAD then { d with BAD := x } else if r = rF then { d with F := x }
  else if r = rLP then { d with LP := x } else if r = rNEG then { d with NEG := x } else d

/-- `BAD` after the magnitude bit `b`: set on a negative zero. -/
def xbBad (d : D) (b : Bool) : ℕ := if gridOK (decide (d.NEG ≠ 0)) b then 0 else 1

variable (cap : ℕ) (w : List Bool) (E : ℕ)

set_option hygiene false in
/-- Close `st w E X = st w E Y` for data records `X`, `Y` built from `d`. -/
macro "dfinE" : tactic =>
  `(tactic| (congr 1 <;> cases d <;> (try simp_all [D.setReg, D.reg, xbBad, gridOK]) <;> omega))

theorem st_val (d : D) (r : Fin 10) : (st w E d).val r = d.reg r := rfl

theorem st_setv (d : D) (r : Fin 10) (hr : r.val < 8) (x : ℕ) : (st w E d).setv r x = st w E (d.setReg r x) := by
  fin_cases r <;> simp at hr <;>
    (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | rfl
        | (funext i; fin_cases i <;> simp [st, D.setReg, Function.update_apply]))

theorem wbit_W (d : D) : wbit (st w E d) sW = readTapeBit (frame w) d.pw := rfl
theorem wbit_E (d : D) : wbit (st w E d) sE = readTapeBit (List.replicate E true) d.pe := rfl

/-! ## One-instruction steps -/

theorem x_inc (d : D) (r : Fin 10) (hr : r.val < 8) (hc : d.reg r < cap) :
    WExec cap (.inc r) (st w E d) (st w E (d.setReg r (d.reg r + 1))) 3 := by
  have h := WExec.inc (cap := cap) r (st w E d) (by rw [st_val]; exact hc)
  rwa [st_val, st_setv w E d r hr] at h

theorem x_dec (d : D) (r : Fin 10) (hr : r.val < 8) (hc : d.reg r ≤ cap) :
    WExec cap (.dec r) (st w E d) (st w E (d.setReg r (d.reg r - 1))) 1 := by
  have h := WExec.dec (cap := cap) r (st w E d) (by rw [st_val]; exact hc)
  rwa [st_val, st_setv w E d r hr] at h

theorem x_setF (d : D) (r : Fin 10) (hr : r.val < 8) (h1 : d.reg r ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (WM.setF r) (st w E d) (st w E (d.setReg r 1)) 4 := by
  have h := wsetF_spec cap r (st w E d) (by rw [st_val]; exact h1) hcap
  rwa [st_setv w E d r hr] at h

theorem x_clear (d : D) (r : Fin 10) (hr : r.val < 8) (hc : d.reg r ≤ cap) :
    WExec cap (WM.clear r) (st w E d) (st w E (d.setReg r 0)) (3 * d.reg r + 1) := by
  have h := wclear_spec cap r (d.reg r) (st w E d) (st_val w E d r) (by rw [st_val]; exact hc)
  rwa [st_setv w E d r hr] at h

theorem x_fwdW (d : D) (hc : d.pw < cap) :
    WExec cap (WM.fwdC sW rPW) (st w E d) (st w E { d with pw := d.pw + 1 }) 5 := by
  refine WExec.cast cap (wfwdC_spec cap sW rPW (st w E d) hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_fwdE (d : D) (hc : d.pe < cap) :
    WExec cap (WM.fwdC sE rPE) (st w E d) (st w E { d with pe := d.pe + 1 }) 5 := by
  refine WExec.cast cap (wfwdC_spec cap sE rPE (st w E d) hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_setc (d : D) (b : Bool) : WExec cap (.setc b) (st w E d) (st w E { d with cell := b }) 1 :=
  WExec.cast cap (WExec.setc b (st w E d)) rfl le_rfl

theorem x_rewW (d : D) (hc : d.pw ≤ cap) :
    WExec cap (WM.rewind sW rPW) (st w E d) (st w E { d with pw := 0 }) (5 * d.pw + 1) := by
  refine WExec.cast cap (wrewind_spec cap sW rPW d.pw (st w E d) rfl hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_rewE (d : D) (hc : d.pe ≤ cap) :
    WExec cap (WM.rewind sE rPE) (st w E d) (st w E { d with pe := 0 }) (5 * d.pe + 1) := by
  refine WExec.cast cap (wrewind_spec cap sE rPE d.pe (st w E d) rfl hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

/-- A guarded phase is skipped once `BAD` is up. -/
theorem x_guard_bad (P : WM 1 10) (d : D) (hB : d.BAD ≠ 0) :
    WExec cap (.ifr rBAD .skip P) (st w E d) (st w E d) 1 :=
  WExec.ifrT (by rw [st_val]; simpa [D.reg] using hB) (WExec.skip _)

theorem x_guard_ok (P : WM 1 10) (d d' : D) (n : ℕ) (hB : d.BAD = 0) (h : WExec cap P (st w E d) (st w E d') n) :
    WExec cap (.ifr rBAD .skip P) (st w E d) (st w E d') (n + 1) :=
  WExec.ifrF (by rw [st_val]; simpa [D.reg] using hB) h

/-! ## The program -/

def fwdW : WM 1 10 := WM.fwdC sW rPW

/-- The sign bit (kept in `NEG`), the `1`, the `0`, the magnitude bit (no negative zero). -/
def sgnP : WM 1 10 := .ifs sW (.seq fwdW (.seq (.ifs sW (WM.setF rNEG) .skip) fwdW)) (WM.setF rBAD)
def oneP : WM 1 10 := .ifs sW (.seq fwdW (.seq (.ifs sW .skip (WM.setF rBAD)) fwdW)) (WM.setF rBAD)
def zroP : WM 1 10 := .ifs sW (.seq fwdW (.seq (.ifs sW (WM.setF rBAD) .skip) fwdW)) (WM.setF rBAD)
def xbP : WM 1 10 := .ifs sW (.seq fwdW (.seq (.ifs sW .skip (.ifr rNEG (WM.setF rBAD) .skip)) fwdW)) (WM.setF rBAD)

/-- The code's field: the unary prefix, `C := K`, the payload (its last bit kept), the canonical top bit. -/
def onesBody : WM 1 10 :=
  .ifs sW (.seq fwdW (.ifs sW (.seq (.inc rK) fwdW) (.seq (.dec rF) fwdW))) (.seq (.dec rF) (WM.setF rBAD))
def onesP : WM 1 10 := .seq (.inc rF) (.whr rF onesBody)
def dupP : WM 1 10 := .seq (Hash4.wdup rK rC rT) (WM.move rT rK)
def copyBody : WM 1 10 :=
  .seq (.dec rC) (.ifs sW (.seq fwdW (.seq (.ifs sW (WM.setF rLB) (WM.clear rLB)) fwdW))
    (.seq (WM.setF rBAD) (WM.clear rC)))
def copyP : WM 1 10 := .whr rC copyBody
def canonP : WM 1 10 := .ifr rK (.seq (.dec rK) (.ifr rK (.ifr rLB .skip (WM.setF rBAD)) .skip)) (WM.setF rBAD)
def clrP : WM 1 10 := .seq (WM.clear rK) (.seq (WM.clear rLB) (WM.clear rNEG))

/-- A phase skipped once `BAD` is up. -/
def g (P : WM 1 10) : WM 1 10 := .ifr rBAD .skip P

/-- One entry: the sign word, the code's field, the clears. -/
def entryCore : WM 1 10 :=
  .seq (.seq (g sgnP) (.seq (g oneP) (.seq (g zroP) (g xbP))))
    (.seq (.seq (g onesP) (.seq (g dupP) (.seq (g copyP) (g canonP)))) clrP)

/-- The loop flag: another entry is due and nothing failed. -/
def updP : WM 1 10 := .seq (WM.clear rLP) (.ifs sE (.ifr rBAD .skip (.inc rLP)) .skip)
def entryBody : WM 1 10 := .seq entryCore (.seq (WM.fwdC sE rPE) updP)
def mainP : WM 1 10 := .seq (.ifs sE (.inc rLP) .skip) (.whr rLP entryBody)

/-- The zero padding. -/
def trailP : WM 1 10 := .whs sW (.seq fwdW (.seq (.ifs sW (WM.setF rBAD) .skip) fwdW))
def verdP : WM 1 10 := .ifr rBAD (.setc false) (.setc true)
def cleanP : WM 1 10 := .seq (WM.rewind sW rPW) (.seq (WM.rewind sE rPE) (WM.clear rBAD))

/-- **The entries validator.** -/
def entP : WM 1 10 := .seq mainP (.seq trailP (.seq verdP cleanP))

/-! ## Reading the framed rest -/

theorem mark_at (p : ℕ) : readTapeBit (frame w) (2 * p) = decide (p < w.length) :=
  FrontOracleField.frame_mark w p

theorem bit_at (p : ℕ) : readTapeBit (frame w) (2 * p + 1) = w.getD p false :=
  FrontOracleField.frame_bit w p

/-! ## The sign's four bits -/

/-- One sign bit present: step past it, the bit into `NEG`. -/
theorem sgn_ok (d : D) (p : ℕ) (bb : Bool) (hbb : w.getD p false = bb) (hp : d.pw = 2 * p) (hl : p < w.length)
    (hNEG : d.NEG = 0) (hc : 2 * p + 2 ≤ cap) :
    WExec cap sgnP (st w E d) (st w E { d with pw := 2 * p + 2, NEG := bb.toNat }) 18 := by
  subst hbb
  have s1 := x_fwdW cap w E d (by omega)
  have hb : wbit (st w E { d with pw := d.pw + 1 }) sW = w.getD p false := by
    rw [wbit_W]; simp only; rw [hp, bit_at]
  have s2 : WExec cap (.ifs sW (WM.setF rNEG) .skip) (st w E { d with pw := d.pw + 1 })
      (st w E { d with pw := d.pw + 1, NEG := (w.getD p false).toNat }) 5 := by
    cases hbit : w.getD p false with
    | true =>
      have h := x_setF cap w E { d with pw := d.pw + 1 } rNEG (by decide) (by simp [D.reg, hNEG]) (by omega)
      refine WExec.cast cap (WExec.ifsT (by rw [hb, hbit]) h) ?_ (by omega)
      dfinE
    | false =>
      refine WExec.cast cap (WExec.ifsF (by rw [hb, hbit]) (WExec.skip _)) ?_ (by omega)
      dfinE
  have s3 := x_fwdW cap w E { d with pw := d.pw + 1, NEG := (w.getD p false).toNat } (by simp; omega)
  refine WExec.cast cap (WExec.ifsT (by rw [wbit_W, hp, mark_at]; simpa using hl) (s1.seq (s2.seq s3))) ?_
    (by omega)
  dfinE

/-- A missing bit (the end of the word): `BAD`. -/
theorem miss (P : WM 1 10) (d : D) (p : ℕ) (hp : d.pw = 2 * p) (hl : w.length ≤ p) (hB : d.BAD ≤ 1)
    (hcap : 1 ≤ cap) :
    WExec cap (.ifs sW P (WM.setF rBAD)) (st w E d) (st w E { d with BAD := 1 }) 5 := by
  have h := x_setF cap w E d rBAD (by decide) (by simpa [D.reg] using hB) hcap
  refine WExec.cast cap (WExec.ifsF (by rw [wbit_W, hp, mark_at]; simpa using hl) h) ?_ (by omega)
  dfinE

/-- A fixed bit present (`one`: expected `1`; `zro`: expected `0`): step past it, `BAD` on a mismatch. -/
theorem one_at (d : D) (p : ℕ) (bb : Bool) (hbb : w.getD p false = bb) (hp : d.pw = 2 * p) (hl : p < w.length)
    (hB : d.BAD = 0) (hc : 2 * p + 2 ≤ cap) :
    WExec cap oneP (st w E d) (st w E { d with pw := 2 * p + 2, BAD := if bb then 0 else 1 }) 18 := by
  subst hbb
  have s1 := x_fwdW cap w E d (by omega)
  have hb : wbit (st w E { d with pw := d.pw + 1 }) sW = w.getD p false := by
    rw [wbit_W]; simp only; rw [hp, bit_at]
  have s2 : WExec cap (.ifs sW .skip (WM.setF rBAD)) (st w E { d with pw := d.pw + 1 })
      (st w E { d with pw := d.pw + 1, BAD := if w.getD p false then 0 else 1 }) 5 := by
    cases hbit : w.getD p false with
    | true =>
      refine WExec.cast cap (WExec.ifsT (by rw [hb, hbit]) (WExec.skip _)) ?_ (by omega)
      dfinE
    | false =>
      have h := x_setF cap w E { d with pw := d.pw + 1 } rBAD (by decide) (by simp [D.reg, hB]) (by omega)
      refine WExec.cast cap (WExec.ifsF (by rw [hb, hbit]) h) ?_ (by omega)
      dfinE
  have s3 := x_fwdW cap w E { d with pw := d.pw + 1, BAD := if w.getD p false then 0 else 1 } (by simp; omega)
  refine WExec.cast cap (WExec.ifsT (by rw [wbit_W, hp, mark_at]; simpa using hl) (s1.seq (s2.seq s3))) ?_
    (by omega)
  dfinE

theorem zro_at (d : D) (p : ℕ) (bb : Bool) (hbb : w.getD p false = bb) (hp : d.pw = 2 * p) (hl : p < w.length)
    (hB : d.BAD = 0) (hc : 2 * p + 2 ≤ cap) :
    WExec cap zroP (st w E d) (st w E { d with pw := 2 * p + 2, BAD := if bb then 1 else 0 }) 18 := by
  subst hbb
  have s1 := x_fwdW cap w E d (by omega)
  have hb : wbit (st w E { d with pw := d.pw + 1 }) sW = w.getD p false := by
    rw [wbit_W]; simp only; rw [hp, bit_at]
  have s2 : WExec cap (.ifs sW (WM.setF rBAD) .skip) (st w E { d with pw := d.pw + 1 })
      (st w E { d with pw := d.pw + 1, BAD := if w.getD p false then 1 else 0 }) 5 := by
    cases hbit : w.getD p false with
    | true =>
      have h := x_setF cap w E { d with pw := d.pw + 1 } rBAD (by decide) (by simp [D.reg, hB]) (by omega)
      refine WExec.cast cap (WExec.ifsT (by rw [hb, hbit]) h) ?_ (by omega)
      dfinE
    | false =>
      refine WExec.cast cap (WExec.ifsF (by rw [hb, hbit]) (WExec.skip _)) ?_ (by omega)
      dfinE
  have s3 := x_fwdW cap w E { d with pw := d.pw + 1, BAD := if w.getD p false then 1 else 0 } (by simp; omega)
  refine WExec.cast cap (WExec.ifsT (by rw [wbit_W, hp, mark_at]; simpa using hl) (s1.seq (s2.seq s3))) ?_
    (by omega)
  dfinE

/-- The magnitude bit present: step past it, `BAD` on a negative zero. -/
theorem xb_at (d : D) (p : ℕ) (bb : Bool) (hbb : w.getD p false = bb) (hp : d.pw = 2 * p) (hl : p < w.length)
    (hB : d.BAD = 0) (hN : d.NEG ≤ 1) (hc : 2 * p + 2 ≤ cap) :
    WExec cap xbP (st w E d) (st w E { d with pw := 2 * p + 2, BAD := xbBad d bb }) 19 := by
  subst hbb
  have s1 := x_fwdW cap w E d (by omega)
  have hb : wbit (st w E { d with pw := d.pw + 1 }) sW = w.getD p false := by
    rw [wbit_W]; simp only; rw [hp, bit_at]
  have s2 : WExec cap (.ifs sW .skip (.ifr rNEG (WM.setF rBAD) .skip)) (st w E { d with pw := d.pw + 1 })
      (st w E { d with pw := d.pw + 1, BAD := xbBad d (w.getD p false) }) 6 := by
    cases hbit : w.getD p false with
    | true =>
      refine WExec.cast cap (WExec.ifsT (by rw [hb, hbit]) (WExec.skip _)) ?_ (by omega)
      dfinE
    | false =>
      by_cases hn : d.NEG = 0
      · refine WExec.cast cap (WExec.ifsF (by rw [hb, hbit]) (WExec.ifrF (by rw [st_val]; simpa [D.reg] using hn)
          (WExec.skip _))) ?_ (by omega)
        dfinE
      · have h := x_setF cap w E { d with pw := d.pw + 1 } rBAD (by decide) (by simp [D.reg, hB]) (by omega)
        refine WExec.cast cap (WExec.ifsF (by rw [hb, hbit]) (WExec.ifrT (by rw [st_val]; simpa [D.reg] using hn)
          h)) ?_ (by omega)
        dfinE
  have s3 := x_fwdW cap w E { d with pw := d.pw + 1, BAD := xbBad d (w.getD p false) } (by simp; omega)
  refine WExec.cast cap (WExec.ifsT (by rw [wbit_W, hp, mark_at]; simpa using hl) (s1.seq (s2.seq s3))) ?_
    (by omega)
  dfinE

/-! ## The code's field -/

theorem mark_drop (p j : ℕ) : readTapeBit (frame w) (2 * (p + j)) = decide (j < (w.drop p).length) := by
  rw [mark_at]; simp; omega

theorem bit_drop (p j : ℕ) : readTapeBit (frame w) (2 * (p + j) + 1) = (w.drop p).getD j false := by
  rw [bit_at]; simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem ones_round (d : D) (hm : readTapeBit (frame w) d.pw = true) (hb : readTapeBit (frame w) (d.pw + 1) = true)
    (hc : d.pw + 2 ≤ cap) (hK : d.K + 1 ≤ cap) :
    WExec cap onesBody (st w E d) (st w E { d with pw := d.pw + 2, K := d.K + 1 }) 17 := by
  have s1 := x_fwdW cap w E d (by omega)
  have s2 := x_inc cap w E { d with pw := d.pw + 1 } rK (by decide) (by simp [D.reg]; omega)
  have s3 := x_fwdW cap w E (({ d with pw := d.pw + 1 } : D).setReg rK (({ d with pw := d.pw + 1 } : D).reg rK + 1))
    (by simp [D.setReg]; omega)
  refine WExec.cast cap (WExec.ifsT (by rw [wbit_W]; exact hm) (s1.seq (WExec.ifsT (by rw [wbit_W]; exact hb)
    (s2.seq s3)))) ?_ (by omega)
  dfinE

theorem ones_sep (d : D) (hm : readTapeBit (frame w) d.pw = true)
    (hb : readTapeBit (frame w) (d.pw + 1) = false) (hc : d.pw + 2 ≤ cap) (hF : d.F = 1) :
    WExec cap onesBody (st w E d) (st w E { d with pw := d.pw + 2, F := 0 }) 15 := by
  have s1 := x_fwdW cap w E d (by omega)
  have s2 := x_dec cap w E { d with pw := d.pw + 1 } rF (by decide) (by simp [D.reg, hF]; omega)
  have s3 := x_fwdW cap w E (({ d with pw := d.pw + 1 } : D).setReg rF (({ d with pw := d.pw + 1 } : D).reg rF - 1))
    (by simp [D.setReg]; omega)
  refine WExec.cast cap (WExec.ifsT (by rw [wbit_W]; exact hm) (s1.seq (WExec.ifsF (by rw [wbit_W]; exact hb)
    (s2.seq s3)))) ?_ (by omega)
  dfinE

theorem ones_end (d : D) (hm : readTapeBit (frame w) d.pw = false) (hF : d.F = 1) (hB : d.BAD ≤ 1)
    (hcap : 1 ≤ cap) :
    WExec cap onesBody (st w E d) (st w E { d with F := 0, BAD := 1 }) 7 := by
  have s1 := x_dec cap w E d rF (by decide) (by simp [D.reg, hF]; omega)
  have s2 := x_setF cap w E (d.setReg rF (d.reg rF - 1)) rBAD (by decide) (by simp [D.setReg, D.reg]; omega) hcap
  refine WExec.cast cap (WExec.ifsF (by rw [wbit_W]; exact hm) (s1.seq s2)) ?_ (by omega)
  dfinE

/-- **The unary prefix** of the field at logical position `p` (`t = w.drop p`): `K = ones t`; past the separator,
or at the end with `BAD`. -/
theorem ones_loop (hcap : 2 * w.length + 2 ≤ cap) (p : ℕ) :
    ∀ (m : ℕ) (d : D) (j : ℕ), j + m = ones (w.drop p) → d.pw = 2 * (p + j) → d.K = j → d.F = 1 → d.BAD ≤ 1 →
      WExec cap (.whr rF onesBody) (st w E d)
        (st w E (if ones (w.drop p) < (w.drop p).length then
          { d with pw := 2 * (p + ones (w.drop p)) + 2, K := ones (w.drop p), F := 0 }
          else { d with pw := 2 * (p + ones (w.drop p)), K := ones (w.drop p), F := 0, BAD := 1 })) (19 * m + 18) := by
  have hle := ones_le (w.drop p)
  have hL : (w.drop p).length = w.length - p := List.length_drop
  intro m
  induction m with
  | zero =>
    intro d j hj hpw hK hF hB
    have hjk : j = ones (w.drop p) := by omega
    subst hjk
    by_cases hlt : ones (w.drop p) < (w.drop p).length
    · rw [if_pos hlt]
      have hm : readTapeBit (frame w) d.pw = true := by rw [hpw, mark_drop]; simpa using hlt
      have hb : readTapeBit (frame w) (d.pw + 1) = false := by
        rw [hpw, bit_drop]
        have := ones_stop (w.drop p) hlt
        rw [List.getD_eq_getElem _ _ hlt] at this ⊢
        exact this
      have r := ones_sep cap w E d hm hb (by omega) hF
      have e := WExec.whrF (cap := cap) (r := rF) (P := onesBody) (σ := st w E { d with pw := d.pw + 2, F := 0 }) rfl
      refine WExec.cast cap (WExec.whrT (by simp [st, hF]) r e) ?_ (by omega)
      dfinE
    · rw [if_neg hlt]
      have hm : readTapeBit (frame w) d.pw = false := by rw [hpw, mark_drop]; simpa using hlt
      have r := ones_end cap w E d hm hF hB (by omega)
      have e := WExec.whrF (cap := cap) (r := rF) (P := onesBody) (σ := st w E { d with F := 0, BAD := 1 }) rfl
      refine WExec.cast cap (WExec.whrT (by simp [st, hF]) r e) ?_ (by omega)
      dfinE
  | succ m ih =>
    intro d j hj hpw hK hF hB
    have hjl : j < (w.drop p).length := by omega
    have hm : readTapeBit (frame w) d.pw = true := by rw [hpw, mark_drop]; simpa using hjl
    have hb : readTapeBit (frame w) (d.pw + 1) = true := by
      rw [hpw, bit_drop]; exact FrontOracleField.ones_true (w.drop p) j (by omega)
    have r := ones_round cap w E d hm hb (by rw [hpw]; omega) (by rw [hK]; omega)
    have rest := ih { d with pw := d.pw + 2, K := d.K + 1 } (j + 1) (by omega) (by simp [hpw]; ring)
      (by simp [hK]) (by simp [hF]) (by simp [hB])
    have e : ∀ d' : D, d'.pe = d.pe → d'.C = d.C → d'.T = d.T → d'.LB = d.LB → d'.BAD = d.BAD → d'.LP = d.LP →
        d'.NEG = d.NEG → d'.cell = d.cell →
        (if ones (w.drop p) < (w.drop p).length then
          { d' with pw := 2 * (p + ones (w.drop p)) + 2, K := ones (w.drop p), F := 0 }
          else { d' with pw := 2 * (p + ones (w.drop p)), K := ones (w.drop p), F := 0, BAD := 1 }) =
        (if ones (w.drop p) < (w.drop p).length then
          { d with pw := 2 * (p + ones (w.drop p)) + 2, K := ones (w.drop p), F := 0 }
          else { d with pw := 2 * (p + ones (w.drop p)), K := ones (w.drop p), F := 0, BAD := 1 }) := by
      intro d' h1 h2 h3 h4 h5 h6 h7 h8
      cases d; cases d'; simp_all
    rw [e _ rfl rfl rfl rfl rfl rfl rfl rfl] at rest
    exact WExec.mono (WExec.whrT (by simp [st, hF]) r rest) (by omega)

theorem dup_spec (d : D) (hC : d.C = 0) (hT : d.T = 0) (hK : d.K ≤ cap) :
    WExec cap dupP (st w E d) (st w E { d with C := d.K }) (18 * d.K + 3) := by
  have h1 := Hash4.wdup_spec cap rK rC rT (by decide) (by decide) (by decide) d.K (st w E d) rfl hK
    (by rw [st_val]; simp [D.reg, hC]; omega) (by rw [st_val]; simp [D.reg, hT]; omega)
  rw [st_val, st_val, st_setv w E d rK (by decide), st_setv w E _ rC (by decide), st_setv w E _ rT (by decide)] at h1
  have h2 := wmove_spec cap rT rK (by decide) d.K
    (st w E (((d.setReg rK 0).setReg rC (d.reg rC + d.K)).setReg rT (d.reg rT + d.K)))
    (by rw [st_val]; simp [D.setReg, D.reg, hT]) (by rw [st_val]; simp [D.setReg, D.reg, hT]; omega)
    (by rw [st_val, st_val]; simp [D.setReg, D.reg, hT]; omega)
  rw [st_val, st_val, st_setv w E _ rT (by decide), st_setv w E _ rK (by decide)] at h2
  refine WExec.cast cap (h1.seq h2) ?_ (by omega)
  dfinE

/-- One payload bit read (`C ≥ 1`, present): its value into `LB`. -/
def cpNext (d : D) (b : Bool) : D := { d with pw := d.pw + 2, C := d.C - 1, LB := b.toNat }

theorem copy_round (d : D) (hC : 1 ≤ d.C) (hCc : d.C ≤ cap) (hm : readTapeBit (frame w) d.pw = true)
    (hc : d.pw + 2 ≤ cap) (hLB : d.LB ≤ 1) :
    WExec cap copyBody (st w E d) (st w E (cpNext d (readTapeBit (frame w) (d.pw + 1)))) 22 := by
  have s1 := x_dec cap w E d rC (by decide) (by simp [D.reg]; omega)
  have e1 : d.setReg rC (d.reg rC - 1) = { d with C := d.C - 1 } := by cases d; simp [D.setReg, D.reg]
  rw [e1] at s1
  have s2 := x_fwdW cap w E { d with C := d.C - 1 } (by simp; omega)
  set b := readTapeBit (frame w) (d.pw + 1) with hb
  set d2 := ({ d with C := d.C - 1, pw := d.pw + 1 } : D) with hd2
  have s3 : WExec cap (.ifs sW (WM.setF rLB) (WM.clear rLB)) (st w E d2) (st w E { d2 with LB := b.toNat }) 5 := by
    have hbit : wbit (st w E d2) sW = b := by rw [wbit_W]
    cases hbv : b with
    | true =>
      have t := x_setF cap w E d2 rLB (by decide) (by simp [D.reg, hd2]; omega) (by omega)
      refine WExec.cast cap (WExec.ifsT (by rw [hbit, hbv]) t) ?_ (by omega)
      congr 1 <;> simp [D.setReg]
    | false =>
      have t := x_clear cap w E d2 rLB (by decide) (by simp [D.reg, hd2]; omega)
      refine WExec.cast cap (WExec.ifsF (by rw [hbit, hbv]) t) ?_ (by simp [D.reg, hd2]; omega)
      congr 1 <;> simp [D.setReg]
  have s4 := x_fwdW cap w E { d2 with LB := b.toNat } (by simp [hd2]; omega)
  refine WExec.cast cap (s1.seq (WExec.ifsT (by rw [wbit_W]; exact hm) (s2.seq (s3.seq s4)))) ?_ (by omega)
  rw [hd2]; congr 1 <;> cases d <;> simp [cpNext]

theorem copy_miss (d : D) (hC : 1 ≤ d.C) (hCc : d.C ≤ cap) (hm : readTapeBit (frame w) d.pw = false)
    (hB : d.BAD ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap copyBody (st w E d) (st w E { d with C := 0, BAD := 1 }) (3 * d.C + 9) := by
  have s1 := x_dec cap w E d rC (by decide) (by simp [D.reg]; omega)
  have e1 : d.setReg rC (d.reg rC - 1) = { d with C := d.C - 1 } := by cases d; simp [D.setReg, D.reg]
  rw [e1] at s1
  have s2 := x_setF cap w E { d with C := d.C - 1 } rBAD (by decide) (by simp [D.reg]; omega) hcap
  have e2 : ({ d with C := d.C - 1 } : D).setReg rBAD 1 = { d with C := d.C - 1, BAD := 1 } := by
    cases d; simp [D.setReg]
  rw [e2] at s2
  have s3 := x_clear cap w E { d with C := d.C - 1, BAD := 1 } rC (by decide) (by simp [D.reg]; omega)
  refine WExec.cast cap (s1.seq (WExec.ifsF (by rw [wbit_W]; exact hm) (s2.seq s3))) ?_ (by simp [D.reg]; omega)
  dfinE

/-- The data after `i` payload bits read. -/
def cpIter (e : D) : ℕ → D
  | 0 => e
  | i + 1 => cpNext (cpIter e i) (readTapeBit (frame w) ((cpIter e i).pw + 1))

theorem cpIter_eq (e : D) : ∀ i, cpIter w e i =
    { e with
      pw := e.pw + 2 * i, C := e.C - i,
      LB := if i = 0 then e.LB else (readTapeBit (frame w) (e.pw + 2 * (i - 1) + 1)).toNat }
  | 0 => by cases e; simp [cpIter]
  | i + 1 => by
    rw [cpIter, cpIter_eq e i]
    simp only [cpNext]
    cases e
    simp <;> omega

/-- **The payload** of the field (from logical position `p₁`, `C = k`): `c = min k (L − p₁)` bits read; short of `k`:
`BAD`. -/
theorem copy_loop (hcap : 2 * w.length + 2 ≤ cap) (e : D) (p1 k c : ℕ) (hp1 : p1 ≤ w.length)
    (hk : k ≤ w.length) (hcdef : c = min k (w.length - p1)) (hpw : e.pw = 2 * p1) (hC : e.C = k)
    (hLB : e.LB ≤ 1) (hB : e.BAD ≤ 1) :
    ∀ m i, i + m = c → WExec cap copyP (st w E (cpIter w e i))
      (st w E (if c < k then { cpIter w e c with C := 0, BAD := 1 } else cpIter w e c)) (26 * m + 3 * k + 12) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have hic : i = c := by omega
    subst hic
    by_cases hck : i < k
    · rw [if_pos hck]
      have hend : p1 + i = w.length := by omega
      have hm : readTapeBit (frame w) (cpIter w e i).pw = false := by
        rw [cpIter_eq, hpw, show 2 * p1 + 2 * i = 2 * (p1 + i) by ring, mark_at, hend]; simp
      have r := copy_miss cap w E (cpIter w e i) (by rw [cpIter_eq]; simp; omega) (by rw [cpIter_eq]; simp; omega) hm
        (by rw [cpIter_eq]; simpa using hB) (by omega)
      have ex := WExec.whrF (cap := cap) (r := rC) (P := copyBody) (σ := st w E { cpIter w e i with C := 0, BAD := 1 })
        rfl
      refine WExec.mono (WExec.whrT (by rw [st_val, cpIter_eq]; simp [D.reg]; omega) r ex) ?_
      rw [cpIter_eq]; simp; omega
    · rw [if_neg hck]
      exact WExec.mono (WExec.whrF (by rw [st_val, cpIter_eq]; simp [D.reg]; omega)) (by omega)
  | succ m ih =>
    intro i hi
    have hilt : p1 + i < w.length := by omega
    have hm : readTapeBit (frame w) (cpIter w e i).pw = true := by
      rw [cpIter_eq, hpw, show 2 * p1 + 2 * i = 2 * (p1 + i) by ring, mark_at]; simpa using hilt
    have r := copy_round cap w E (cpIter w e i) (by rw [cpIter_eq]; simp; omega) (by rw [cpIter_eq]; simp; omega) hm
      (by rw [cpIter_eq]; simp; omega) (by rw [cpIter_eq]; dsimp only; split_ifs <;> simp [hLB, Bool.toNat_le])
    have rest := ih (i + 1) (by omega)
    exact WExec.mono (WExec.whrT (by rw [st_val, cpIter_eq]; simp [D.reg]; omega) r rest) (by omega)

/-! ## The canonical top bit, the clears -/

/-- `BAD` after the canonical test: `K ≥ 1` and (`K = 1` or the last bit is `1`). -/
def canonBad (K LB : ℕ) : ℕ := if K = 0 then 1 else if K = 1 then 0 else if LB = 0 then 1 else 0

theorem canon_spec (d : D) (hB : d.BAD = 0) (hK : d.K ≤ cap) (hcap : 1 ≤ cap) :
    WExec cap canonP (st w E d) (st w E { d with K := d.K - 1, BAD := canonBad d.K d.LB }) 10 := by
  by_cases hK0 : d.K = 0
  · have h := x_setF cap w E d rBAD (by decide) (by simp [D.reg, hB]) hcap
    refine WExec.cast cap (WExec.ifrF (by rw [st_val]; simpa [D.reg] using hK0) h) ?_ (by omega)
    congr 1 <;> cases d <;> simp_all [D.setReg, canonBad]
  · have s1 := x_dec cap w E d rK (by decide) (by simp [D.reg]; omega)
    have e1 : d.setReg rK (d.reg rK - 1) = { d with K := d.K - 1 } := by cases d; simp [D.setReg, D.reg]
    rw [e1] at s1
    by_cases hK1 : d.K - 1 = 0
    · refine WExec.cast cap (WExec.ifrT (by rw [st_val]; simpa [D.reg] using hK0) (s1.seq (WExec.ifrF
        (by rw [st_val]; simpa [D.reg] using hK1) (WExec.skip _)))) ?_ (by omega)
      congr 1 <;> cases d <;> simp_all [canonBad] <;> omega
    · by_cases hL : d.LB = 0
      · have s2 := x_setF cap w E { d with K := d.K - 1 } rBAD (by decide) (by simp [D.reg, hB]) hcap
        refine WExec.cast cap (WExec.ifrT (by rw [st_val]; simpa [D.reg] using hK0) (s1.seq (WExec.ifrT
          (by rw [st_val]; simpa [D.reg] using hK1) (WExec.ifrF (by rw [st_val]; simpa [D.reg] using hL) s2))))
          ?_ (by omega)
        congr 1 <;> cases d <;> simp_all [D.setReg, canonBad] <;> omega
      · refine WExec.cast cap (WExec.ifrT (by rw [st_val]; simpa [D.reg] using hK0) (s1.seq (WExec.ifrT
          (by rw [st_val]; simpa [D.reg] using hK1) (WExec.ifrT (by rw [st_val]; simpa [D.reg] using hL)
            (WExec.skip _))))) ?_ (by omega)
        congr 1 <;> cases d <;> simp_all [canonBad] <;> omega

theorem clr_spec (d : D) (hK : d.K ≤ cap) (hL : d.LB ≤ cap) (hN : d.NEG ≤ cap) :
    WExec cap clrP (st w E d) (st w E { d with K := 0, LB := 0, NEG := 0 }) (3 * d.K + 3 * d.LB + 3 * d.NEG + 5) := by
  have s1 := x_clear cap w E d rK (by decide) (by simpa [D.reg] using hK)
  have e1 : d.setReg rK 0 = { d with K := 0 } := by cases d; simp [D.setReg]
  rw [e1] at s1
  have s2 := x_clear cap w E { d with K := 0 } rLB (by decide) (by simpa [D.reg] using hL)
  have e2 : ({ d with K := 0 } : D).setReg rLB 0 = { d with K := 0, LB := 0 } := by cases d; simp [D.setReg]
  rw [e2] at s2
  have s3 := x_clear cap w E { d with K := 0, LB := 0 } rNEG (by decide) (by simpa [D.reg] using hN)
  have e3 : ({ d with K := 0, LB := 0 } : D).setReg rNEG 0 = { d with K := 0, LB := 0, NEG := 0 } := by
    cases d; simp [D.setReg]
  rw [e3] at s3
  refine WExec.mono (s1.seq (s2.seq s3)) ?_
  simp [D.reg]; omega

/-! ## One code field -/

/-- The field's phases, each skipped after a failure. -/
def natSeq : WM 1 10 := .seq (g onesP) (.seq (g dupP) (.seq (g copyP) (g canonP)))

/-- What a phase sequence leaves: a bounded record with the zero scratch, the verdict `BAD ∈ {0,1}`. -/
structure Tidy (w : List Bool) (d d' : D) : Prop where
  pe : d'.pe = d.pe
  LP : d'.LP = d.LP
  cell : d'.cell = d.cell
  C : d'.C = 0
  T : d'.T = 0
  F : d'.F = 0
  K : d'.K ≤ w.length
  LB : d'.LB ≤ 1
  BAD : d'.BAD ≤ 1
  pw : d'.pw ≤ 2 * w.length + 2

/-- **One code field** at logical position `p`: passes exactly on the scan, and then ends past the field. -/
theorem nat_spec (hcap : 2 * w.length + 2 ≤ cap) (d : D) (p : ℕ) (hpw : d.pw = 2 * p) (hp : p ≤ w.length)
    (hB : d.BAD = 0) (hK : d.K = 0) (hC : d.C = 0) (hT : d.T = 0) (hLB : d.LB = 0) (hF : d.F = 0) :
    ∃ d' n, WExec cap natSeq (st w E d) (st w E d') n ∧ n ≤ 100 * (w.length + 1) ∧ Tidy w d d' ∧
      d'.NEG = d.NEG ∧ (d'.BAD = 0 ↔ scanOK (w.drop p) = true) ∧
      (d'.BAD = 0 → d'.pw = 2 * (p + 2 * ones (w.drop p) + 1)) := by
  set t := w.drop p with ht
  set k := ones t with hk
  have hL : t.length = w.length - p := by rw [ht, List.length_drop]
  have hkL : k ≤ t.length := ones_le t
  -- the unary prefix
  have s0 := x_inc cap w E d rF (by decide) (by simp [D.reg, hF]; omega)
  have e0 : d.setReg rF (d.reg rF + 1) = { d with F := 1 } := by cases d; simp_all [D.setReg, D.reg]
  rw [e0] at s0
  have s1 := ones_loop cap w E hcap p k { d with F := 1 } 0 (Nat.zero_add _) (by simp [hpw]) (by simp [hK]) rfl
    (by simp [hB])
  have g1 := x_guard_ok cap w E onesP d _ _ hB (s0.seq s1)
  by_cases hlt : k < t.length
  · rw [if_pos hlt] at g1
    set e1 : D := { ({ d with F := 1 } : D) with pw := 2 * (p + k) + 2, K := k, F := 0 } with he1
    have hB1 : e1.BAD = 0 := by simp [he1, hB]
    have s2 := dup_spec cap w E e1 (by simp [he1, hC]) (by simp [he1, hT]) (by simp [he1]; omega)
    have g2 := x_guard_ok cap w E dupP e1 _ _ hB1 s2
    set e2 : D := { e1 with C := e1.K } with he2
    set c := min k (w.length - (p + k + 1)) with hc
    have s3 := copy_loop cap w E hcap e2 (p + k + 1) k c (by omega) (by omega) rfl (by simp [he2, he1]; ring)
      (by simp [he2, he1]) (by simp [he2, he1, hLB]) (by simp [he2, he1, hB]) c 0 (by omega)
    have g3 := x_guard_ok cap w E copyP e2 _ _ (by simp [he2, hB1]) s3
    by_cases hck : c < k
    · rw [if_pos hck] at g3
      set e3 : D := { cpIter w e2 c with C := 0, BAD := 1 } with he3
      have g4 := x_guard_bad cap w E canonP e3 (by simp [he3])
      refine ⟨e3, _, (g1.seq (g2.seq (g3.seq g4))), ?_, ?_, ?_, ?_, ?_⟩
      · rw [cpIter_eq] at *; simp only [he3, he2, he1] at *; omega
      · rw [he3, cpIter_eq]
        refine ⟨by simp [he2, he1], by simp [he2, he1], by simp [he2, he1], by simp, by simp [he2, he1, hT],
          by simp [he2, he1], by simp [he2, he1]; omega, ?_, by simp, ?_⟩
        · simp only; split_ifs <;> simp [he2, he1, hLB, Bool.toNat_le]
        · simp [he2, he1]; omega
      · simp [he3, cpIter_eq, he2, he1]
      · simp only [he3, show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
        simp only [scanOK, ← hk, Bool.and_eq_false_iff]
        left; right; simp; omega
      · intro h; simp [he3] at h
    · rw [if_neg hck] at g3
      have hck' : c = k := by omega
      set e3 : D := cpIter w e2 c with he3
      have hB3 : e3.BAD = 0 := by simp [he3, cpIter_eq, he2, hB1]
      have s4 := canon_spec cap w E e3 hB3 (by simp [he3, cpIter_eq, he2, he1]; omega) (by omega)
      have g4 := x_guard_ok cap w E canonP e3 _ _ hB3 s4
      -- the last payload bit
      have hLB3 : e3.LB = if k = 0 then 0 else ((w.drop p).getD (2 * k) false).toNat := by
        rw [he3, cpIter_eq]
        simp only [he2, he1]
        by_cases hk0 : k = 0
        · simp [hk0, hck', hLB]
        · rw [if_neg (by omega), if_neg hk0, hck']
          congr 1
          rw [show 2 * (p + k) + 2 + 2 * (k - 1) + 1 = 2 * (p + 2 * k) + 1 by omega, bit_drop]
      refine ⟨{ e3 with K := e3.K - 1, BAD := canonBad e3.K e3.LB }, _, (g1.seq (g2.seq (g3.seq g4))), ?_, ?_, ?_,
        ?_, ?_⟩
      · rw [he3, cpIter_eq] at *; simp only [he2, he1] at *; omega
      · refine ⟨by simp [he3, cpIter_eq, he2, he1], by simp [he3, cpIter_eq, he2, he1],
          by simp [he3, cpIter_eq, he2, he1], by simp [he3, cpIter_eq, he2, he1]; omega,
          by simp [he3, cpIter_eq, he2, he1, hT], by simp [he3, cpIter_eq, he2, he1],
          by simp [he3, cpIter_eq, he2, he1]; omega, ?_, ?_, ?_⟩
        · show e3.LB ≤ 1
          rw [hLB3]; split_ifs <;> simp [Bool.toNat_le]
        · simp only [canonBad]; split_ifs <;> omega
        · simp [he3, cpIter_eq, he2, he1]; omega
      · simp [he3, cpIter_eq, he2, he1]
      · show canonBad e3.K e3.LB = 0 ↔ _
        have hK3 : e3.K = k := by simp [he3, cpIter_eq, he2, he1]
        rw [hK3, hLB3]
        simp only [scanOK, ← hk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
        have h2 : 2 * k + 1 ≤ t.length := by omega
        simp only [canonBad]
        by_cases hk0 : k = 0
        · simp [hk0]
        · by_cases hk1 : k = 1
          · simp [hk1]; omega
          · cases hb : (w.drop p).getD (2 * k) false <;> simp [hk0, hk1, hb, ← ht] <;> omega
      · intro _
        show e3.pw = _
        simp [he3, cpIter_eq, he2, he1, hck']; ring
  · rw [if_neg hlt] at g1
    set e1 : D := { ({ d with F := 1 } : D) with pw := 2 * (p + k), K := k, F := 0, BAD := 1 } with he1
    have g2 := x_guard_bad cap w E dupP e1 (by simp [he1])
    have g3 := x_guard_bad cap w E copyP e1 (by simp [he1])
    have g4 := x_guard_bad cap w E canonP e1 (by simp [he1])
    refine ⟨e1, _, (g1.seq (g2.seq (g3.seq g4))), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [he1] at *; omega
    · refine ⟨by simp [he1], by simp [he1], by simp [he1], by simp [he1, hC], by simp [he1, hT], by simp [he1],
        by simp [he1]; omega, by simp [he1, hLB], by simp [he1], by simp [he1]; omega⟩
    · simp [he1]
    · simp only [he1, show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
      simp only [scanOK, ← hk, Bool.and_eq_false_iff]
      left; right; simp; omega
    · intro h; simp [he1] at h

/-! ## The sign's four bits, guarded -/

def signSeq : WM 1 10 := .seq (g sgnP) (.seq (g oneP) (.seq (g zroP) (g xbP)))

/-- What the sign phases keep. -/
structure SKeep (d d' : D) : Prop where
  pe : d'.pe = d.pe
  K : d'.K = d.K
  C : d'.C = d.C
  T : d'.T = d.T
  LB : d'.LB = d.LB
  F : d'.F = d.F
  LP : d'.LP = d.LP
  cell : d'.cell = d.cell

theorem getD_drop (p i : ℕ) : (w.drop p).getD i false = w.getD (p + i) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem drop_cons4 (p : ℕ) (h : p + 3 < w.length) :
    w.drop p = w.getD p false :: w.getD (p + 1) false :: w.getD (p + 2) false :: w.getD (p + 3) false ::
      w.drop (p + 4) := by
  rw [List.drop_eq_getElem_cons (show p < w.length by omega),
    List.drop_eq_getElem_cons (show p + 1 < w.length by omega),
    List.drop_eq_getElem_cons (show p + 1 + 1 < w.length by omega),
    List.drop_eq_getElem_cons (show p + 1 + 1 + 1 < w.length by omega),
    List.getD_eq_getElem _ _ (show p < w.length by omega), List.getD_eq_getElem _ _ (show p + 1 < w.length by omega),
    List.getD_eq_getElem _ _ (show p + 2 < w.length by omega), List.getD_eq_getElem _ _ (show p + 3 < w.length by omega)]

theorem sgnOK_cons (b x y z : Bool) (t : List Bool) : sgnOK' (b :: x :: y :: z :: t) = (x && !y && gridOK b z) := by
  cases x <;> cases y <;> simp [sgnOK']

theorem sgnOK_short (u : List Bool) (h : u.length ≤ 3) : sgnOK' u = false := by
  match u, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [a, b], _ => cases b <;> rfl
  | [a, b, c], _ => cases b <;> cases c <;> rfl

theorem gridOK_toNat (b x : Bool) : gridOK (decide (b.toNat ≠ 0)) x = gridOK b x := by cases b <;> rfl

/-- **The sign word** at logical position `p`: passes exactly on `sgnOK'`, and then ends four bits on. -/
theorem sign_spec (hcap : 2 * w.length + 2 ≤ cap) (d : D) (p : ℕ) (hpw : d.pw = 2 * p) (hp : p ≤ w.length)
    (hB : d.BAD = 0) (hN : d.NEG = 0) :
    ∃ d' n, WExec cap signSeq (st w E d) (st w E d') n ∧ n ≤ 80 ∧ SKeep d d' ∧ d'.NEG ≤ 1 ∧ d'.BAD ≤ 1 ∧
      d'.pw ≤ 2 * w.length ∧ (d'.BAD = 0 ↔ sgnOK' (w.drop p) = true) ∧ (d'.BAD = 0 → d'.pw = 2 * (p + 4)) := by
  obtain ⟨b0, hb0⟩ : ∃ b, w.getD p false = b := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ b, w.getD (p + 1) false = b := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ b, w.getD (p + 2) false = b := ⟨_, rfl⟩
  obtain ⟨b3, hb3⟩ : ∃ b, w.getD (p + 3) false = b := ⟨_, rfl⟩
  have hN0 : b0.toNat ≤ 1 := Bool.toNat_le b0
  have short : ∀ m, p + m ≥ w.length → m ≤ 3 → sgnOK' (w.drop p) = false := fun m h1 h2 =>
    sgnOK_short _ (by simp; omega)
  by_cases h0 : p < w.length
  · have s1 := sgn_ok cap w E d p b0 hb0 hpw h0 hN (by omega)
    set d1 : D := { d with pw := 2 * p + 2, NEG := b0.toNat } with hd1
    have g1 := x_guard_ok cap w E sgnP d d1 _ hB s1
    have hB1 : d1.BAD = 0 := by simp [hd1, hB]
    by_cases h1 : p + 1 < w.length
    · have s2 := one_at cap w E d1 (p + 1) b1 hb1 (by simp [hd1]; ring) h1 hB1 (by omega)
      set d2 : D := { d1 with pw := 2 * (p + 1) + 2, BAD := if b1 then 0 else 1 } with hd2
      have g2 := x_guard_ok cap w E oneP d1 d2 _ hB1 s2
      cases b1 with
      | true =>
        have hB2 : d2.BAD = 0 := by simp [hd2]
        by_cases h2 : p + 2 < w.length
        · have s3 := zro_at cap w E d2 (p + 2) b2 hb2 (by simp [hd2]; ring) h2 hB2 (by omega)
          set d3 : D := { d2 with pw := 2 * (p + 2) + 2, BAD := if b2 then 1 else 0 } with hd3
          have g3 := x_guard_ok cap w E zroP d2 d3 _ hB2 s3
          cases b2 with
          | false =>
            have hB3 : d3.BAD = 0 := by simp [hd3]
            by_cases h3 : p + 3 < w.length
            · have hN3 : d3.NEG ≤ 1 := by simp [hd3, hd2, hd1, hN0]
              have s4 := xb_at cap w E d3 (p + 3) b3 hb3 (by simp [hd3]; ring) h3 hB3 hN3 (by omega)
              have g4 := x_guard_ok cap w E xbP d3 _ _ hB3 s4
              refine ⟨_, _, g1.seq (g2.seq (g3.seq g4)), ?cost1, ⟨?a11, ?a21, ?a31, ?a41, ?a51, ?a61, ?a71, ?a81⟩, ?neg1, ?bad1,
                ?pwb1, ?iff1, ?pos1⟩
              case iff1 =>
                rw [drop_cons4 w p h3, hb0, hb1, hb2, hb3, sgnOK_cons]
                simp only [xbBad, hd3, hd2, hd1, gridOK_toNat]
                split_ifs with hg <;> simp [hg]
              case pos1 => intro _; simp; ring
              case bad1 => simp only [xbBad]; split_ifs <;> omega
              case pwb1 => simp; omega
              all_goals first | omega | (simp [hd3, hd2, hd1, hN0]; done)
            · have g4 := x_guard_ok cap w E xbP d3 { d3 with BAD := 1 } _ hB3
                (miss cap w E (.seq fwdW (.seq (.ifs sW .skip (.ifr rNEG (WM.setF rBAD) .skip)) fwdW)) d3 (p + 3)
                  (by simp [hd3]; ring) (by omega) (by simp [hB3]) (by omega))
              refine ⟨_, _, g1.seq (g2.seq (g3.seq g4)), ?cost2, ⟨?a12, ?a22, ?a32, ?a42, ?a52, ?a62, ?a72, ?a82⟩, ?neg2, ?bad2,
                ?pwb2, ?iff2, ?pos2⟩
              case iff2 =>
                simp only [show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
                exact short 3 (by omega) le_rfl
              case pos2 => intro h; simp at h
              case pwb2 => simp [hd3]; omega
              all_goals first | omega | (simp [hd3, hd2, hd1, hN0]; done)
          | true =>
            have g4 := x_guard_bad cap w E xbP d3 (by simp [hd3])
            refine ⟨_, _, g1.seq (g2.seq (g3.seq g4)), ?cost3, ⟨?a13, ?a23, ?a33, ?a43, ?a53, ?a63, ?a73, ?a83⟩, ?neg3, ?bad3,
              ?pwb3, ?iff3, ?pos3⟩
            case iff3 =>
              simp only [hd3, if_true, show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
              by_cases h3 : p + 3 < w.length
              · rw [drop_cons4 w p h3, hb0, hb1, hb2, hb3, sgnOK_cons]; simp
              · exact short 3 (by omega) le_rfl
            case pos3 => intro h; simp [hd3] at h
            case pwb3 => simp [hd3]; omega
            all_goals first | omega | (simp [hd3, hd2, hd1, hN0]; done)
        · have g3 := x_guard_ok cap w E zroP d2 { d2 with BAD := 1 } _ hB2
            (miss cap w E (.seq fwdW (.seq (.ifs sW (WM.setF rBAD) .skip) fwdW)) d2 (p + 2) (by simp [hd2]; ring)
              (by omega) (by simp [hB2]) (by omega))
          have g4 := x_guard_bad cap w E xbP { d2 with BAD := 1 } (by simp)
          refine ⟨_, _, g1.seq (g2.seq (g3.seq g4)), ?cost4, ⟨?a14, ?a24, ?a34, ?a44, ?a54, ?a64, ?a74, ?a84⟩, ?neg4, ?bad4,
            ?pwb4, ?iff4, ?pos4⟩
          case iff4 =>
            simp only [show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
            exact short 2 (by omega) (by omega)
          case pos4 => intro h; simp at h
          case pwb4 => simp [hd2]; omega
          all_goals first | omega | (simp [hd2, hd1, hN0]; done)
      | false =>
        have g3 := x_guard_bad cap w E zroP d2 (by simp [hd2])
        have g4 := x_guard_bad cap w E xbP d2 (by simp [hd2])
        refine ⟨_, _, g1.seq (g2.seq (g3.seq g4)), ?cost5, ⟨?a15, ?a25, ?a35, ?a45, ?a55, ?a65, ?a75, ?a85⟩, ?neg5, ?bad5,
          ?pwb5, ?iff5, ?pos5⟩
        case iff5 =>
          simp only [hd2, show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true, Bool.false_eq_true, if_false]
          by_cases h3 : p + 3 < w.length
          · rw [drop_cons4 w p h3, hb0, hb1, hb2, hb3, sgnOK_cons]; simp
          · by_cases h2 : p + 2 < w.length
            · have hu : w.drop p = [b0, false, b2] := by
                apply List.ext_getElem
                · simp; omega
                · intro i hi1 hi2
                  have hl : (w.drop p).length = 3 := by simp; omega
                  have hi3 : i < 3 := by omega
                  interval_cases i
                  · have := getD_drop w p 0; rw [List.getD_eq_getElem _ _ (by omega)] at this
                    simp only [Nat.add_zero] at this; rw [this, hb0]; rfl
                  · have := getD_drop w p 1; rw [List.getD_eq_getElem _ _ (by omega)] at this
                    rw [this, hb1]; rfl
                  · have := getD_drop w p 2; rw [List.getD_eq_getElem _ _ (by omega)] at this
                    rw [this, hb2]; rfl
              rw [hu]; cases b0 <;> cases b2 <;> rfl
            · exact short 2 (by omega) (by omega)
        case pos5 => intro h; simp [hd2] at h
        case pwb5 => simp [hd2]; omega
        all_goals first | omega | (simp [hd2, hd1, hN0]; done)
    · have g2 := x_guard_ok cap w E oneP d1 { d1 with BAD := 1 } _ hB1
        (miss cap w E (.seq fwdW (.seq (.ifs sW .skip (WM.setF rBAD)) fwdW)) d1 (p + 1) (by simp [hd1]; ring)
          (by omega) (by simp [hB1]) (by omega))
      have g3 := x_guard_bad cap w E zroP { d1 with BAD := 1 } (by simp)
      have g4 := x_guard_bad cap w E xbP { d1 with BAD := 1 } (by simp)
      refine ⟨_, _, g1.seq (g2.seq (g3.seq g4)), ?cost6, ⟨?a16, ?a26, ?a36, ?a46, ?a56, ?a66, ?a76, ?a86⟩, ?neg6, ?bad6,
        ?pwb6, ?iff6, ?pos6⟩
      case iff6 =>
        simp only [show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
        exact short 1 (by omega) (by omega)
      case pos6 => intro h; simp at h
      case pwb6 => simp [hd1]; omega
      all_goals first | omega | (simp [hd1, hN0]; done)
  · have g1 := x_guard_ok cap w E sgnP d { d with BAD := 1 } _ hB
      (miss cap w E (.seq fwdW (.seq (.ifs sW (WM.setF rNEG) .skip) fwdW)) d p hpw (by omega) (by simp [hB])
        (by omega))
    have g2 := x_guard_bad cap w E oneP { d with BAD := 1 } (by simp)
    have g3 := x_guard_bad cap w E zroP { d with BAD := 1 } (by simp)
    have g4 := x_guard_bad cap w E xbP { d with BAD := 1 } (by simp)
    refine ⟨_, _, g1.seq (g2.seq (g3.seq g4)), ?cost7, ⟨?a17, ?a27, ?a37, ?a47, ?a57, ?a67, ?a77, ?a87⟩, ?neg7, ?bad7,
      ?pwb7, ?iff7, ?pos7⟩
    case iff7 =>
      simp only [show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
      exact short 0 (by omega) (by omega)
    case pos7 => intro h; simp at h
    case pwb7 => simp; omega
    all_goals first | omega | (simp [hN]; done)

/-! ## One entry -/

/-- The data at an entry boundary: every work register `0` but the loop flag. -/
structure Clean (d : D) : Prop where
  K : d.K = 0
  C : d.C = 0
  T : d.T = 0
  LB : d.LB = 0
  F : d.F = 0
  NEG : d.NEG = 0

theorem natSeq_bad (d : D) (hB : d.BAD ≠ 0) : WExec cap natSeq (st w E d) (st w E d) 7 :=
  WExec.mono ((x_guard_bad cap w E onesP d hB).seq ((x_guard_bad cap w E dupP d hB).seq
    ((x_guard_bad cap w E copyP d hB).seq (x_guard_bad cap w E canonP d hB)))) (by omega)

/-- **One entry** at logical position `p`: passes exactly on the entry reader (a grid sign, a canonical code), and
then ends past it; every work register cleared. -/
theorem entry_spec (hcap : 2 * w.length + 2 ≤ cap) (d : D) (p : ℕ) (hpw : d.pw = 2 * p) (hp : p ≤ w.length)
    (hB : d.BAD = 0) (hc : Clean d) :
    ∃ d' n, WExec cap entryCore (st w E d) (st w E d') n ∧ n ≤ 200 * (w.length + 1) ∧ Clean d' ∧
      d'.pe = d.pe ∧ d'.LP = d.LP ∧ d'.cell = d.cell ∧ d'.BAD ≤ 1 ∧ d'.pw ≤ 2 * w.length + 2 ∧
      (d'.BAD = 0 ↔ (entStep (w.drop p)).isSome = true) ∧
      (∀ sp r, entStep (w.drop p) = some (sp, r) → d'.pw = 2 * (w.length - r.2.length)) := by
  obtain ⟨d1, n1, h1, hn1, k1, hN1, hB1, hpw1, hiff1, hpos1⟩ := sign_spec cap w E hcap d p hpw hp hB hc.NEG
  have hstep := entStep_isSome (w.drop p)
  by_cases hs : d1.BAD = 0
  · have hsg := hiff1.1 hs
    have hp4 := hpos1 hs
    have hlen : p + 4 ≤ w.length := by
      by_contra hh
      have := sgnOK_short (w.drop p) (by simp; omega)
      rw [this] at hsg; exact absurd hsg (by decide)
    obtain ⟨d2, n2, h2, hn2, t2, hN2, hiff2, hpos2⟩ := nat_spec cap w E hcap d1 (p + 4) hp4 hlen hs
      (by rw [k1.K, hc.K]) (by rw [k1.C, hc.C]) (by rw [k1.T, hc.T]) (by rw [k1.LB, hc.LB]) (by rw [k1.F, hc.F])
    have h3 := clr_spec cap w E d2 (by have := t2.K; omega) (by have := t2.LB; omega) (by rw [hN2]; omega)
    refine ⟨_, _, h1.seq (h2.seq h3), ?_, ⟨rfl, t2.C, t2.T, rfl, t2.F, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := t2.K; have := t2.LB; rw [hN2] at *; omega
    · simp [t2.pe, k1.pe]
    · simp [t2.LP, k1.LP]
    · simp [t2.cell, k1.cell]
    · exact t2.BAD
    · exact t2.pw
    · show d2.BAD = 0 ↔ _
      rw [hiff2, hstep, hsg, List.drop_drop]; simp [Nat.add_comm]
    · intro sp r hr
      obtain ⟨hr1, hr2⟩ := entStep_rest (w.drop p) sp r.1 r.2 (by rw [hr])
      rw [List.drop_drop] at hr1 hr2
      have hsc : scanOK (w.drop (p + 4)) = true := by
        have := hstep; rw [hr] at this; simp [hsg] at this; simpa [List.drop_drop] using this
      show d2.pw = _
      rw [hpos2 (hiff2.2 hsc), hr1]
      simp only [List.drop_drop, List.length_drop] at hr2 ⊢
      omega
  · have hB1' : d1.BAD = 1 := by omega
    have h2 := natSeq_bad cap w E d1 hs
    have h3 := clr_spec cap w E d1 (by rw [k1.K, hc.K]; omega) (by rw [k1.LB, hc.LB]; omega) (by omega)
    refine ⟨_, _, h1.seq (h2.seq h3), ?_, ⟨rfl, by rw [k1.C, hc.C], by rw [k1.T, hc.T], rfl, by rw [k1.F, hc.F], rfl⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k1.K, hc.K, k1.LB, hc.LB]; omega
    · simp [k1.pe]
    · simp [k1.LP]
    · simp [k1.cell]
    · simp [hB1']
    · simp; omega
    · simp only [hB1', show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
      rw [hstep]
      have : sgnOK' (w.drop p) = false := by
        cases h : sgnOK' (w.drop p)
        · rfl
        · exact absurd (hiff1.2 h) hs
      simp [this]
    · intro sp r hr
      exfalso
      have : (entStep (w.drop p)).isSome = true := by rw [hr]; rfl
      rw [hstep] at this
      simp only [Bool.and_eq_true] at this
      exact hs (hiff1.2 this.1)

/-! ## The entries loop -/

theorem upd_spec (d : D) (hLP : d.LP = 1) (hB : d.BAD ≤ 1) (hcap : 2 ≤ cap) :
    WExec cap updP (st w E d)
      (st w E { d with LP := if d.pe < E ∧ d.BAD = 0 then 1 else 0 }) 10 := by
  have s1 := x_clear cap w E d rLP (by decide) (by simp [D.reg, hLP]; omega)
  have e1 : d.setReg rLP 0 = { d with LP := 0 } := by cases d; simp [D.setReg]
  rw [e1] at s1
  have hbit : wbit (st w E { d with LP := 0 }) sE = decide (d.pe < E) := by
    rw [wbit_E]; simp only [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp_all
  by_cases hE : d.pe < E
  · by_cases hB0 : d.BAD = 0
    · have s2 := x_inc cap w E { d with LP := 0 } rLP (by decide) (by simp [D.reg]; omega)
      refine WExec.cast cap (s1.seq (WExec.ifsT (by rw [hbit]; simpa using hE) (WExec.ifrF
        (by rw [st_val]; simpa [D.reg] using hB0) s2))) ?_ (by simp [D.reg, hLP])
      congr 1; cases d; simp_all [D.setReg, D.reg]
    · refine WExec.cast cap (s1.seq (WExec.ifsT (by rw [hbit]; simpa using hE) (WExec.ifrT
        (by rw [st_val]; simpa [D.reg] using hB0) (WExec.skip _)))) ?_ (by simp [D.reg, hLP])
      congr 1; cases d; simp_all
  · refine WExec.cast cap (s1.seq (WExec.ifsF (by rw [hbit]; simpa using hE) (WExec.skip _))) ?_
      (by simp [D.reg, hLP])
    congr 1; cases d; simp_all

/-- What the loop leaves. -/
structure LoopOut (d d' : D) : Prop where
  clean : Clean d'
  LP : d'.LP = 0
  cell : d'.cell = d.cell
  pe : d'.pe ≤ w.length + 1
  BAD : d'.BAD ≤ 1
  pw : d'.pw ≤ 2 * w.length + 2
  ok : d'.BAD = 0 ↔ (restAfter E w).isSome = true
  pos : ∀ r, restAfter E w = some r → d'.pw = 2 * (w.length - r.length)

/-- **The entries loop**: from `j` entries read (position `p`), to the verdict on `E` entries. -/
theorem loop_spec (hcap : 2 * w.length + 4 ≤ cap) :
    ∀ (m : ℕ) (d : D) (j p : ℕ), w.length - p < m → d.pw = 2 * p → p ≤ w.length → d.pe = j → j ≤ E → j ≤ p →
      d.LP = (if j < E then 1 else 0) → d.BAD = 0 → Clean d → restAfter j w = some (w.drop p) →
      ∃ d' n, WExec cap (.whr rLP entryBody) (st w E d) (st w E d') n ∧ n ≤ m * (220 * (w.length + 1)) + 1 ∧
        LoopOut w E d d' := by
  intro m
  induction m with
  | zero => intro d j p h; omega
  | succ m ih =>
    intro d j p hm hpw hp hpe hjE hjp hLP hB hc hr
    by_cases hjE' : j < E
    · rw [if_pos hjE'] at hLP
      obtain ⟨d1, n1, h1, hn1, c1, pe1, LP1, cell1, B1, pw1, iff1, pos1⟩ :=
        entry_spec cap w E (by omega) d p hpw hp hB hc
      have s2 := x_fwdE cap w E d1 (by rw [pe1]; omega)
      have s3 := upd_spec cap w E { d1 with pe := d1.pe + 1 } (by simp [LP1, hLP]) (by simpa using B1) (by omega)
      set d3 : D := { ({ d1 with pe := d1.pe + 1 } : D) with
        LP := if ({ d1 with pe := d1.pe + 1 } : D).pe < E ∧ ({ d1 with pe := d1.pe + 1 } : D).BAD = 0 then 1 else 0 }
        with hd3
      have body : WExec cap entryBody (st w E d) (st w E d3) (n1 + 1 + (5 + 1 + 10)) := h1.seq (s2.seq s3)
      have hpe3 : d3.pe = j + 1 := by simp [hd3, pe1, hpe]
      have cl3 : Clean d3 := ⟨by simp [hd3, c1.K], by simp [hd3, c1.C], by simp [hd3, c1.T], by simp [hd3, c1.LB],
        by simp [hd3, c1.F], by simp [hd3, c1.NEG]⟩
      by_cases hok : d1.BAD = 0
      · -- the entry passed
        obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (iff1.1 hok)
        obtain ⟨sp, r⟩ := e
        have hp1 := pos1 sp r he
        obtain ⟨hr1, hr2⟩ := entStep_rest (w.drop p) sp r.1 r.2 (by rw [he])
        simp only [List.drop_drop] at hr1 hr2
        have hrl : r.2.length = w.length - (p + 4 + (2 * ones (w.drop (p + 4)) + 1)) := by
          rw [hr1]; simp only [List.length_drop]
        simp only [List.length_drop] at hr2
        set p' := p + 4 + (2 * ones (w.drop (p + 4)) + 1) with hp'
        have hrj : restAfter (j + 1) w = some (w.drop p') := by
          rw [restAfter_succ', hr, Option.bind_some, he, Option.map_some, hr1]
        by_cases hjE2 : j + 1 < E
        · have hLP3 : d3.LP = 1 := by simp [hd3, pe1, hpe, hjE2, hok]
          obtain ⟨d', n', h', hn', out⟩ := ih d3 (j + 1) p' (by omega) (by rw [hd3]; simp [hp1, hrl]; omega)
            (by omega) hpe3 (by omega) (by omega) (by rw [if_pos hjE2]; exact hLP3) (by simp [hd3, hok])
            cl3 hrj
          refine ⟨d', _, WExec.whrT (by rw [st_val]; simp [D.reg, hLP]) body h', ?_, ?_⟩
          · have : (m + 1) * (220 * (w.length + 1)) = m * (220 * (w.length + 1)) + 220 * (w.length + 1) := by ring
            omega
          · exact ⟨out.clean, out.LP, by rw [out.cell]; simp [hd3, cell1], out.pe, out.BAD, out.pw, out.ok, out.pos⟩
        · have hEj : E = j + 1 := by omega
          have hLP3 : d3.LP = 0 := by simp [hd3, pe1, hpe, hjE2]
          have ex := WExec.whrF (cap := cap) (r := rLP) (P := entryBody) (σ := st w E d3)
            (by rw [st_val]; simpa [D.reg] using hLP3)
          refine ⟨d3, _, WExec.whrT (by rw [st_val]; simp [D.reg, hLP]) body ex, ?_,
            ⟨cl3, hLP3, by simp [hd3, cell1], by rw [hpe3]; omega, by simp [hd3, B1],
              by simp [hd3]; omega, ?_, ?_⟩⟩
          · have : (m + 1) * (220 * (w.length + 1)) = m * (220 * (w.length + 1)) + 220 * (w.length + 1) := by ring
            omega
          · rw [hEj, hrj]; simp [hd3, hok]
          · intro r' hr'
            rw [hEj, hrj] at hr'
            simp only [Option.some.injEq] at hr'
            subst hr'
            simp only [hd3]; rw [hp1, hrl]; simp
      · -- the entry failed: `BAD`, the loop stops
        have hB1 : d1.BAD = 1 := by omega
        have hLP3 : d3.LP = 0 := by simp [hd3, hB1]
        have ex := WExec.whrF (cap := cap) (r := rLP) (P := entryBody) (σ := st w E d3)
          (by rw [st_val]; simpa [D.reg] using hLP3)
        have hnone : restAfter E w = none := by
          have h1' : restAfter (j + 1) w = none := by
            rw [restAfter_succ', hr, Option.bind_some]
            have : entStep (w.drop p) = none := by
              cases h : entStep (w.drop p)
              · rfl
              · exact absurd (iff1.2 (by rw [h]; rfl)) hok
            rw [this]; rfl
          rw [show E = (j + 1) + (E - (j + 1)) by omega, restAfter_add, h1']; rfl
        refine ⟨d3, _, WExec.whrT (by rw [st_val]; simp [D.reg, hLP]) body ex, ?_,
          ⟨cl3, hLP3, by simp [hd3, cell1], by rw [hpe3]; omega, by simp [hd3, B1],
            by simp [hd3]; omega, ?_, ?_⟩⟩
        · have : (m + 1) * (220 * (w.length + 1)) = m * (220 * (w.length + 1)) + 220 * (w.length + 1) := by ring
          omega
        · simp [hd3, hB1, hnone]
        · intro r' hr'; rw [hnone] at hr'; cases hr'
    · -- no entry is due
      rw [if_neg hjE'] at hLP
      have hjE2 : j = E := by omega
      subst hjE2
      refine ⟨d, _, WExec.whrF (by rw [st_val]; simpa [D.reg] using hLP), by omega,
        ⟨hc, hLP, rfl, by omega, by omega, by omega, ?_, ?_⟩⟩
      · simp [hB, hr]
      · intro r' hr'; rw [hr] at hr'; simp only [Option.some.injEq] at hr'; subst hr'
        rw [hpw]; simp; omega

/-! ## The zero padding, the verdict, the rewinds -/

def trailBody : WM 1 10 := .seq fwdW (.seq (.ifs sW (WM.setF rBAD) .skip) fwdW)

theorem trail_round (d : D) (hB : d.BAD ≤ 1) (hc : d.pw + 2 ≤ cap) :
    WExec cap trailBody (st w E d)
      (st w E { d with pw := d.pw + 2, BAD := if readTapeBit (frame w) (d.pw + 1) then 1 else d.BAD }) 17 := by
  have s1 := x_fwdW cap w E d (by omega)
  have hb : wbit (st w E { d with pw := d.pw + 1 }) sW = readTapeBit (frame w) (d.pw + 1) := by rw [wbit_W]
  have s2 : WExec cap (.ifs sW (WM.setF rBAD) .skip) (st w E { d with pw := d.pw + 1 })
      (st w E { d with pw := d.pw + 1, BAD := if readTapeBit (frame w) (d.pw + 1) then 1 else d.BAD }) 5 := by
    cases hbit : readTapeBit (frame w) (d.pw + 1) with
    | true =>
      have h := x_setF cap w E { d with pw := d.pw + 1 } rBAD (by decide) (by simpa [D.reg] using hB) (by omega)
      refine WExec.cast cap (WExec.ifsT (by rw [hb, hbit]) h) ?_ (by omega)
      congr 1 <;> cases d <;> simp_all [D.setReg]
    | false =>
      refine WExec.cast cap (WExec.ifsF (by rw [hb, hbit]) (WExec.skip _)) ?_ (by omega)
      congr 1 <;> cases d <;> simp_all
  have s3 := x_fwdW cap w E { d with pw := d.pw + 1, BAD := if readTapeBit (frame w) (d.pw + 1) then 1 else d.BAD }
    (by simp; omega)
  refine WExec.cast cap (s1.seq (s2.seq s3)) ?_ (by omega)
  congr 1 <;> cases d <;> simp_all <;> omega

/-- **The zero padding** from logical position `q`: `BAD` on any `1`. -/
theorem trail_ok (hcap : 2 * w.length + 2 ≤ cap) :
    ∀ (m : ℕ) (d : D) (q : ℕ), w.length - q = m → d.pw = 2 * q → q ≤ w.length → d.BAD ≤ 1 →
      WExec cap (.whs sW trailBody) (st w E d)
        (st w E { d with pw := 2 * w.length, BAD := if (w.drop q).all (fun b => !b) then d.BAD else 1 })
        (19 * m + 1) := by
  intro m
  induction m with
  | zero =>
    intro d q hm hpw hq hB
    have hq' : q = w.length := by omega
    subst hq'
    have e : ({ d with pw := 2 * w.length, BAD := if (w.drop w.length).all (fun b => !b) then d.BAD else 1 } : D) = d := by
      cases d; simp_all
    rw [e]
    exact WExec.whsF (by rw [wbit_W, hpw, mark_at]; simp)
  | succ m ih =>
    intro d q hm hpw hq hB
    have hlt : q < w.length := by omega
    have r := trail_round cap w E d hB (by omega)
    set d1 : D := { d with pw := d.pw + 2, BAD := if readTapeBit (frame w) (d.pw + 1) then 1 else d.BAD } with hd1
    have rest := ih d1 (q + 1) (by omega) (by simp [hd1, hpw]; ring) (by omega)
      (by simp only [hd1]; split_ifs <;> omega)
    refine WExec.cast cap (WExec.mono (WExec.whsT (by rw [wbit_W, hpw, mark_at]; simpa using hlt) r rest)
      (by omega)) ?_ le_rfl
    congr 1
    have hdrop : w.drop q = w.getD q false :: w.drop (q + 1) := by
      rw [List.drop_eq_getElem_cons hlt, List.getD_eq_getElem _ _ hlt]
    have hbit : readTapeBit (frame w) (d.pw + 1) = w.getD q false := by rw [hpw, bit_at]
    rw [hd1, hbit, hdrop]
    cases d
    cases hg : w.getD q false <;> simp_all

/-- After a failure the padding pass keeps `BAD` and stops by the end of the witness (from any head). -/
theorem trail_bad (hcap : 2 * w.length + 4 ≤ cap) :
    ∀ (m : ℕ) (d : D), 2 * w.length + 2 - d.pw ≤ m → d.pw ≤ 2 * w.length + 2 → d.BAD = 1 →
      ∃ pw' n, WExec cap (.whs sW trailBody) (st w E d) (st w E { d with pw := pw' }) n ∧ n ≤ 19 * m + 1 ∧
        pw' ≤ 2 * w.length + 3 := by
  intro m
  induction m with
  | zero =>
    intro d hm hpw hB
    refine ⟨d.pw, 1, ?_, by omega, by omega⟩
    have hge : 2 * w.length + 1 ≤ d.pw := by omega
    have e : ({ d with pw := d.pw } : D) = d := by cases d; rfl
    rw [e]
    refine WExec.whsF ?_
    rw [wbit_W]; unfold readTapeBit
    rw [List.getD_eq_default _ _ (by simp [frame_eq_frameP, FrontOracleField.frameP_length]; omega)]
  | succ m ih =>
    intro d hm hpw hB
    by_cases hbit : readTapeBit (frame w) d.pw = true
    · have hlt : d.pw < 2 * w.length + 1 := by
        by_contra hh
        rw [readTapeBit, List.getD_eq_default _ _ (by simp [frame_eq_frameP, FrontOracleField.frameP_length]; omega)]
          at hbit
        exact absurd hbit (by decide)
      have r := trail_round cap w E d (by omega) (by omega)
      set d1 : D := { d with pw := d.pw + 2, BAD := if readTapeBit (frame w) (d.pw + 1) then 1 else d.BAD } with hd1
      have hB1 : d1.BAD = 1 := by simp only [hd1]; split_ifs <;> omega
      obtain ⟨pw', n', h', hn', hpw'⟩ := ih d1 (by simp [hd1]; omega) (by simp [hd1]; omega) hB1
      have e : ({ d1 with pw := pw' } : D) = { d with pw := pw' } := by
        simp only [hd1]; cases d; simp_all
      rw [e] at h'
      exact ⟨pw', _, WExec.whsT (by rw [wbit_W]; exact hbit) r h', by omega, hpw'⟩
    · refine ⟨d.pw, 1, ?_, by omega, by omega⟩
      have e : ({ d with pw := d.pw } : D) = d := by cases d; rfl
      rw [e]
      exact WExec.whsF (by rw [wbit_W]; simpa using hbit)

theorem verd_spec (d : D) :
    WExec cap verdP (st w E d) (st w E { d with cell := decide (d.BAD = 0) }) 2 := by
  by_cases h : d.BAD = 0
  · refine WExec.cast cap (WExec.ifrF (by rw [st_val]; simpa [D.reg] using h) (x_setc cap w E d true)) ?_ le_rfl
    simp [h]
  · refine WExec.cast cap (WExec.ifrT (by rw [st_val]; simpa [D.reg] using h) (x_setc cap w E d false)) ?_ le_rfl
    simp [h]

theorem clean_spec (d : D) (h1 : d.pw ≤ cap) (h2 : d.pe ≤ cap) (h3 : d.BAD ≤ cap) :
    WExec cap cleanP (st w E d) (st w E { d with pw := 0, pe := 0, BAD := 0 })
      (5 * d.pw + 1 + 1 + (5 * d.pe + 1 + 1 + (3 * d.BAD + 1))) := by
  have s1 := x_rewW cap w E d h1
  have s2 := x_rewE cap w E { d with pw := 0 } (by simpa using h2)
  have s3 := x_clear cap w E { d with pw := 0, pe := 0 } rBAD (by decide) (by simpa [D.reg] using h3)
  have e3 : ({ d with pw := 0, pe := 0 } : D).setReg rBAD 0 = { d with pw := 0, pe := 0, BAD := 0 } := by
    cases d; simp [D.setReg]
  rw [e3] at s3
  exact WExec.mono (s1.seq (s2.seq s3)) (by simp [D.reg])

/-! ## The validator -/

def entCost (n : ℕ) : ℕ := 300 * (n + 2) * (n + 2)

def d0 (c0 : Bool) : D := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c0⟩
def dF (c : Bool) : D := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c⟩

/-- **The entries validator**: from the framed rest `frame w` and `1^E` (capacity `2|w| + 4`), the cell becomes
`(entScan E w).isSome` (`E` grid entries then zero padding), every head and register back at `0`. -/
theorem entP_spec (c0 : Bool) (hcap : 2 * w.length + 4 ≤ cap) :
    ∃ n, n ≤ entCost w.length ∧
      WExec cap entP (st w E (d0 c0)) (st w E (dF (entScan E w).isSome)) n := by
  -- the loop flag
  have i1 : WExec cap (.ifs sE (.inc rLP) .skip) (st w E (d0 c0))
      (st w E { d0 c0 with LP := if 0 < E then 1 else 0 }) 4 := by
    by_cases hE : 0 < E
    · have h := x_inc cap w E (d0 c0) rLP (by decide) (by simp [D.reg, d0]; omega)
      refine WExec.cast cap (WExec.ifsT (by rw [wbit_E]; simp only [d0]; cases E <;> simp_all [readTapeBit]) h) ?_
        (by omega)
      congr 1; simp [D.setReg, D.reg, d0, hE]
    · refine WExec.cast cap (WExec.ifsF (by rw [wbit_E]; simp only [d0]; cases E <;> simp_all [readTapeBit])
        (WExec.skip _)) ?_
        (by omega)
      congr 1; simp [d0, hE]
  obtain ⟨d1, n1, h1, hn1, out⟩ := loop_spec cap w E hcap (w.length + 1) { d0 c0 with LP := if 0 < E then 1 else 0 }
    0 0 (by omega) rfl (by omega) rfl (by omega) le_rfl (by simp) rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    (by simp [restAfter])
  -- the padding
  have hfin : ∃ d2 n2, WExec cap (.whs sW trailBody) (st w E d1) (st w E d2) n2 ∧ n2 ≤ 19 * (2 * w.length + 3) + 1 ∧
      d2.pw ≤ 2 * w.length + 3 ∧ d2.pe = d1.pe ∧ d2.BAD ≤ 1 ∧ Clean d2 ∧ d2.LP = 0 ∧ d2.cell = d1.cell ∧
      (d2.BAD = 0 ↔ (entScan E w).isSome = true) := by
    cases hr : restAfter E w with
    | none =>
      have hB1 : d1.BAD = 1 := by
        have := out.BAD
        by_contra hh
        have := out.ok.1 (by omega); rw [hr] at this; exact absurd this (by decide)
      obtain ⟨pw', n', h', hn', hpw'⟩ := trail_bad cap w E hcap (2 * w.length + 2) d1 (by omega) out.pw hB1
      refine ⟨_, _, h', by omega, by simpa using hpw', rfl, by simp [hB1], ?_, by simp [out.LP], by simp [out.cell], ?_⟩
      · exact ⟨by simp [out.clean.K], by simp [out.clean.C], by simp [out.clean.T], by simp [out.clean.LB],
          by simp [out.clean.F], by simp [out.clean.NEG]⟩
      · simp only [hB1, show (1 : ℕ) ≠ 0 by decide, false_iff, Bool.not_eq_true]
        rw [← Bool.not_eq_true, entScan_isSome, hr]; simp
    | some r =>
      have hB1 : d1.BAD = 0 := out.ok.2 (by rw [hr]; rfl)
      have hpw1 := out.pos r hr
      have hrl : r.length ≤ w.length := by
        have : restAfter E w = some r := hr
        clear hr
        -- a rest is a suffix
        have key : ∀ n u r', restAfter n u = some r' → r'.length ≤ u.length := by
          intro n
          induction n with
          | zero => intro u r' h; simp [restAfter] at h; rw [h]
          | succ n ih =>
            intro u r' h
            simp only [restAfter] at h
            cases he : entStep u with
            | none => rw [he] at h; cases h
            | some e =>
              rw [he, Option.bind_some] at h
              have h1 := ih _ _ h
              obtain ⟨sp, pl, rr⟩ := e
              obtain ⟨hrr, -⟩ := entStep_rest u sp pl rr he
              rw [hrr] at h1
              simp at h1; omega
        exact key E w r this
      have ht := trail_ok cap w E (by omega) (w.length - (w.length - r.length)) d1 (w.length - r.length) rfl hpw1
        (by omega) (by omega)
      refine ⟨_, _, ht, by omega, by simp, rfl, by split_ifs <;> simp [hB1], ?_, by simp [out.LP], by simp [out.cell], ?_⟩
      · exact ⟨by simp [out.clean.K], by simp [out.clean.C], by simp [out.clean.T], by simp [out.clean.LB],
          by simp [out.clean.F], by simp [out.clean.NEG]⟩
      · have hdr : w.drop (w.length - r.length) = r := by
          have hs : ∀ n u r', restAfter n u = some r' → u.drop (u.length - r'.length) = r' := by
            intro n
            induction n with
            | zero => intro u r' h; simp [restAfter] at h; rw [h]; simp
            | succ n ih =>
              intro u r' h
              simp only [restAfter] at h
              cases he : entStep u with
              | none => rw [he] at h; cases h
              | some e =>
                rw [he, Option.bind_some] at h
                obtain ⟨sp, pl, rr⟩ := e
                have h1 := ih _ _ h
                obtain ⟨hrr, hle⟩ := entStep_rest u sp pl rr he
                have hrl' : r'.length ≤ rr.length := by
                  have := congrArg List.length h1; simp at this; omega
                rw [hrr, List.drop_drop, List.drop_drop] at h1
                rw [hrr] at hrl'
                simp only [List.length_drop] at hle hrl' h1 ⊢
                rw [← h1]
                congr 1
                simp only [List.length_drop]
                omega
          exact hs E w r hr
        rw [hdr, entScan_isSome, hr]
        simp [hB1]
  obtain ⟨d2, n2, h2, hn2, pw2, pe2, B2, c2, LP2, cell2, iff2⟩ := hfin
  have h3 := verd_spec cap w E d2
  have h4 := clean_spec cap w E { d2 with cell := decide (d2.BAD = 0) } (by simp; omega)
    (by simp [pe2]; have := out.pe; omega) (by simp; omega)
  refine ⟨_, ?_, WExec.cast cap ((i1.seq h1).seq (h2.seq (h3.seq h4))) ?_ le_rfl⟩
  · simp only [entCost]
    have := out.pe
    nlinarith
  · congr 1
    have hc : decide (d2.BAD = 0) = (entScan E w).isSome := by
      cases h : (entScan E w).isSome
      · simp only [decide_eq_false_iff_not]; intro hh; rw [iff2.1 hh] at h; cases h
      · simp only [decide_eq_true_eq]; exact iff2.2 h
    simp only [dF]
    obtain ⟨_, _, K, C, T, LB, _, F, LP, NEG, _⟩ := d2
    simp_all [Clean.K]
    exact ⟨c2.K, c2.C, c2.T, c2.LB, c2.F, c2.NEG⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FrontEntries
