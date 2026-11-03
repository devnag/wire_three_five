import Proof.Wire_3_5.UnionMachine.FrontOracleField
import Proof.Wire_3_5.UnionMachine.CodecBound
import Proof.CaseAnalysis.PairClockExact
import Proof.PCP.PCPPNativeRequestSchema

/-! # C6 front, U1a: the oracle's size check (P3:3669)

Realizes the size bound of "The weak machine guesses one size-`q^G` general oracle" (P3:3669), the conjunct
`decide (g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N))` of `unionSlackCheck` (and `FrontAtW.len`): a
register program (C5's `WM`) reads v8's decoder flag `[b]`, the raw typed descriptor `PCPPNative.descriptor c` (whose
second field is `natWord c.size`, base `descriptor_eq`) and the width `1^q`, and sets its cell to
`decide (c.size ≤ oracleSizeBound G q)` (to `false` when `b = false`).

The bound is base's exact pairing clock: `size ≤ oracleSizeBound G q ↔ size + 1 ≤ (q+1)^D` with `D = 2^(oracleDepth
G)` (base `CloseoutPairClock.size_guard`). The program reads `s = c.size` into a register (Horner from the field's top
bit), divides it by `q + 1` (walking `1^q` cyclically) `D` times and tests for zero: `s / (q+1)^D = 0 ↔ s < (q+1)^D`.
Every register stays at most `s`, and a decodable oracle's size is at most its code's bit length plus one
(**`size_le_code`**), so the register capacity is linear in the witness and the time is `O(D·(|w|+2)²)`, independent of
the pairing clock's degree (base's `OracleCap.cap_run` writes `1^((q+1)^(2D))`).
Main statements: **`sizeP_true`**, **`sizeP_false`**. Paper quantity: the oracle's size bound `|O| ≤ q^G`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairRepresentation (natWord)

/-! ## The size of a decodable oracle -/

/-- **A decodable oracle's size is at most its code's bit length plus one** (its nodes form a balanced list inside a
tagged pair). -/
theorem size_le_code {q v : ℕ} {c : BooleanCircuit q}
    (h : CanonicalWitnessCodec.decodeBooleanCircuit q v = some c) : c.size ≤ natBitLength v + 1 := by
  have he := CanonicalWitnessCodec.encodeBooleanCircuit_of_decode h
  unfold ExecutableInterfaces.encodeBooleanCircuit at he
  have ht := CodecBound.nbl_tagged [CanonicalBinary.encodeBalancedList (c.nodes.map ExecutableInterfaces.encodeBooleanNode),
    CanonicalBinary.encodeNat c.output.val]
  have hb := CodecBound.length_le_balanced (c.nodes.map ExecutableInterfaces.encodeBooleanNode)
  have hp := CodecBound.nbl_pos (CanonicalBinary.encodeNat c.output.val)
  rw [he] at ht
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    List.length_map] at ht hb
  unfold BooleanCircuit.size
  omega

/-- A code read off a payload has at most the payload's length in bits. -/
theorem nbl_value_le (p : List Bool) (hp : p ≠ []) : natBitLength (value p) ≤ p.length := by
  unfold natBitLength
  have hlt := value_lt p
  have hl : 1 ≤ p.length := List.length_pos_iff.2 hp
  rcases Nat.eq_zero_or_pos (value p) with h0 | hpos
  · rw [h0]; simp; omega
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hlt
    omega

/-! ## The arithmetic -/

/-- Horner from the top bit: one more bit of the field. -/
theorem value_drop_pred (bs : List Bool) (j : ℕ) (h1 : 1 ≤ j) (hj : j ≤ bs.length) :
    value (bs.drop (j - 1)) = (bs.getD (j - 1) false).toNat + 2 * value (bs.drop j) := by
  have hlt : j - 1 < bs.length := by omega
  rw [List.drop_eq_getElem_cons hlt, show j - 1 + 1 = j by omega]
  simp [value, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]

theorem value_drop_le : ∀ (bs : List Bool) (j : ℕ), value (bs.drop j) ≤ value bs
  | [], j => by simp
  | b :: t, 0 => le_rfl
  | b :: t, j + 1 => by
    simp only [List.drop_succ_cons, value]
    have := value_drop_le t j
    omega

/-- `D` divisions by `q + 1` leave zero exactly below `(q+1)^D`: the pairing clock's test. -/
theorem div_pow_eq_zero_iff (G q s : ℕ) :
    s / (q + 1) ^ (2 ^ RecoveryScheduleEnvelope.oracleDepth G) = 0 ↔ s ≤ RecoveryScheduleEnvelope.oracleSizeBound G q := by
  rw [RepairSource.CloseoutPairClock.size_guard, Nat.div_eq_zero_iff_lt (by positivity)]
  omega

/-! ## Layout: streams `F D U` (flag, raw descriptor, `1^q`); registers `X Y K T P PD` -/

abbrev SS := WState 2 6

local notation "sF" => (0 : Fin 3)
local notation "sD" => (1 : Fin 3)
local notation "sU" => (2 : Fin 3)
local notation "rX" => (0 : Fin 6)
local notation "rY" => (1 : Fin 6)
local notation "rK" => (2 : Fin 6)
local notation "rT" => (3 : Fin 6)
local notation "rP" => (4 : Fin 6)
local notation "rPD" => (5 : Fin 6)

/-- The check's data: the two moving heads (each equal to its counter), the four work registers, the cell. -/
structure D where
  pd : ℕ
  pu : ℕ
  X : ℕ
  Y : ℕ
  K : ℕ
  T : ℕ
  cell : Bool

/-- The state of the data, on the flag `[b]`, the raw descriptor `desc` and the width `1^q`. -/
def st (b : Bool) (desc : List Bool) (q : ℕ) (d : D) : SS :=
  ⟨![0, d.pd, d.pu], ![[b], desc, List.replicate q true], ![d.X, d.Y, d.K, d.T, d.pu, d.pd], d.cell⟩

def D.reg (d : D) (r : Fin 6) : ℕ := ![d.X, d.Y, d.K, d.T, d.pu, d.pd] r

def D.setReg (d : D) (r : Fin 6) (x : ℕ) : D :=
  if r = rX then { d with X := x } else if r = rY then { d with Y := x } else if r = rK then { d with K := x }
  else if r = rT then { d with T := x } else d

/-- The start and the end: everything zero, the cell `v`. -/
def d0 : D := ⟨0, 0, 0, 0, 0, 0, false⟩
def dF (v : Bool) : D := ⟨0, 0, 0, 0, 0, 0, v⟩

variable (cap : ℕ) (b : Bool) (desc : List Bool) (q : ℕ)

set_option hygiene false in
/-- Close `st b desc q X = st b desc q Y` for data records `X`, `Y` built from `d`. -/
macro "dfinS" : tactic =>
  `(tactic| (congr 1 <;> cases d <;> (try simp_all [D.setReg, D.reg]) <;> omega))

theorem st_val (d : D) (r : Fin 6) : (st b desc q d).val r = d.reg r := rfl

theorem st_setv (d : D) (r : Fin 6) (hr : r.val < 4) (x : ℕ) :
    (st b desc q d).setv r x = st b desc q (d.setReg r x) := by
  fin_cases r <;> simp at hr <;>
    (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | rfl
        | (funext i; fin_cases i <;> simp [st, D.setReg, Function.update_apply]))

theorem wbit_F (d : D) : wbit (st b desc q d) sF = b := by
  simp [wbit, st, readTapeBit]

theorem wbit_D (d : D) : wbit (st b desc q d) sD = readTapeBit desc d.pd := rfl

theorem wbit_U (d : D) : wbit (st b desc q d) sU = decide (d.pu < q) := by
  simp only [wbit, st, readTapeBit]
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> simp_all

/-! ## One-instruction steps -/

theorem x_inc (d : D) (r : Fin 6) (hr : r.val < 4) (hc : d.reg r < cap) :
    WExec cap (.inc r) (st b desc q d) (st b desc q (d.setReg r (d.reg r + 1))) 3 := by
  have h := WExec.inc (cap := cap) r (st b desc q d) (by rw [st_val]; exact hc)
  rwa [st_val, st_setv b desc q d r hr] at h

theorem x_dec (d : D) (r : Fin 6) (hr : r.val < 4) (hc : d.reg r ≤ cap) :
    WExec cap (.dec r) (st b desc q d) (st b desc q (d.setReg r (d.reg r - 1))) 1 := by
  have h := WExec.dec (cap := cap) r (st b desc q d) (by rw [st_val]; exact hc)
  rwa [st_val, st_setv b desc q d r hr] at h

theorem x_clear (d : D) (r : Fin 6) (hr : r.val < 4) (hc : d.reg r ≤ cap) :
    WExec cap (WM.clear r) (st b desc q d) (st b desc q (d.setReg r 0)) (3 * d.reg r + 1) := by
  have h := wclear_spec cap r (d.reg r) (st b desc q d) (st_val b desc q d r) (by rw [st_val]; exact hc)
  rwa [st_setv b desc q d r hr] at h

theorem x_move (d : D) (r s : Fin 6) (hr : r.val < 4) (hs : s.val < 4) (hrs : r ≠ s) (hc : d.reg r ≤ cap)
    (hc' : d.reg s + d.reg r ≤ cap) :
    WExec cap (WM.move r s) (st b desc q d) (st b desc q ((d.setReg r 0).setReg s (d.reg s + d.reg r)))
      (7 * d.reg r + 1) := by
  have h := wmove_spec cap r s hrs (d.reg r) (st b desc q d) (st_val b desc q d r) (by rw [st_val]; exact hc)
    (by rw [st_val, st_val]; exact hc')
  rwa [st_val, st_val, st_setv b desc q d r hr, st_setv b desc q _ s hs] at h

theorem x_fwdD (d : D) (hc : d.pd < cap) :
    WExec cap (WM.fwdC sD rPD) (st b desc q d) (st b desc q { d with pd := d.pd + 1 }) 5 := by
  refine WExec.cast cap (wfwdC_spec cap sD rPD (st b desc q d) hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_fwdU (d : D) (hc : d.pu < cap) :
    WExec cap (WM.fwdC sU rP) (st b desc q d) (st b desc q { d with pu := d.pu + 1 }) 5 := by
  refine WExec.cast cap (wfwdC_spec cap sU rP (st b desc q d) hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

/-- One step back on the descriptor, the counter down. -/
def bwdD : WM 2 6 := .seq (.bwd sD) (.dec rPD)

theorem x_bwdD (d : D) (hc : d.pd ≤ cap) :
    WExec cap bwdD (st b desc q d) (st b desc q { d with pd := d.pd - 1 }) 3 := by
  have h1 := WExec.bwd (cap := cap) sD (st b desc q d)
  have h2 := WExec.dec (cap := cap) rPD ((st b desc q d).seth sD ((st b desc q d).sh sD - 1)) (by
    simpa [st, WState.seth] using hc)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, WState.seth, WState.setv, Function.update_apply])

theorem x_rewD (d : D) (hc : d.pd ≤ cap) :
    WExec cap (WM.rewind sD rPD) (st b desc q d) (st b desc q { d with pd := 0 }) (5 * d.pd + 1) := by
  refine WExec.cast cap (wrewind_spec cap sD rPD d.pd (st b desc q d) rfl hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_rewU (d : D) (hc : d.pu ≤ cap) :
    WExec cap (WM.rewind sU rP) (st b desc q d) (st b desc q { d with pu := 0 }) (5 * d.pu + 1) := by
  refine WExec.cast cap (wrewind_spec cap sU rP d.pu (st b desc q d) rfl hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_setc (d : D) (v : Bool) : WExec cap (.setc v) (st b desc q d) (st b desc q { d with cell := v }) 1 :=
  WExec.cast cap (WExec.setc v (st b desc q d)) rfl le_rfl

/-! ## The program -/

/-- The leading ones of a field, counted in `K`. -/
def onesK : WM 2 6 := .whs sD (.seq (WM.fwdC sD rPD) (.inc rK))
/-- Past `K` bits. -/
def skipK : WM 2 6 := .whr rK (.seq (.dec rK) (WM.fwdC sD rPD))
/-- Past `K` bits, their count kept in `T`. -/
def skipKT : WM 2 6 := .whr rK (.seq (.dec rK) (.seq (.inc rT) (WM.fwdC sD rPD)))
/-- `X := 2X` (through `Y`). -/
def dbl : WM 2 6 := .seq (WM.move rX rY) (.whr rY (.seq (.dec rY) (.seq (.inc rX) (.inc rX))))
/-- Horner from the field's top bit down: `X := 2X + bit`, `T` times. -/
def horner : WM 2 6 := .whr rT (.seq (.dec rT) (.seq bwdD (.seq dbl (.ifs sD (.inc rX) .skip))))
/-- The descriptor's first field (the arity) skipped, the second (the size) read into `X`. -/
def parse : WM 2 6 :=
  .seq onesK (.seq (WM.fwdC sD rPD) (.seq skipK (.seq onesK (.seq (WM.fwdC sD rPD) (.seq skipKT horner)))))

/-- One unit of the division: a step along `1^q`, or (at its end) one more quotient unit and back to the start. -/
def unitP : WM 2 6 := .seq (.dec rX) (.ifs sU (WM.fwdC sU rP) (.seq (.inc rY) (WM.rewind sU rP)))
/-- `X := X / (q+1)`. -/
def divOnce : WM 2 6 := .seq (.whr rX unitP) (.seq (WM.rewind sU rP) (WM.move rY rX))
/-- `n` divisions. -/
def divs : ℕ → WM 2 6
  | 0 => .skip
  | n + 1 => .seq divOnce (divs n)

/-- The verdict (`X = 0`), then the clears. -/
def tailP : WM 2 6 := .seq (.ifr rX (.setc false) (.setc true)) (.seq (WM.clear rX) (WM.rewind sD rPD))

/-- The check on a decoded oracle. -/
def coreP (Dg : ℕ) : WM 2 6 := .seq parse (.seq (divs Dg) tailP)

/-- **The size check**: on v8's flag, the check; else the cell stays `false`. -/
def sizeP (Dg : ℕ) : WM 2 6 := .ifs sF (coreP Dg) (.setc false)

/-! ## The field's reads -/

theorem onesK_spec : ∀ (j : ℕ) (d : D), (∀ i, i < j → readTapeBit desc (d.pd + i) = true) →
    readTapeBit desc (d.pd + j) = false → d.pd + j ≤ cap → d.K + j ≤ cap →
    WExec cap onesK (st b desc q d) (st b desc q { d with pd := d.pd + j, K := d.K + j }) (11 * j + 1)
  | 0, d, _, h0, _, _ => by
    refine WExec.cast cap (WExec.whsF (by rw [wbit_D]; simpa using h0)) ?_ (by omega)
    dfinS
  | j + 1, d, hs, h0, hc, hK => by
    have s1 := x_fwdD cap b desc q d (by omega)
    have s2 := x_inc cap b desc q { d with pd := d.pd + 1 } rK (by decide) (by simp [D.reg]; omega)
    have ih := onesK_spec j (({ d with pd := d.pd + 1 } : D).setReg rK (({ d with pd := d.pd + 1 } : D).reg rK + 1))
      (by intro i hi; have := hs (i + 1) (by omega); simp [D.setReg, D.reg]; rwa [show d.pd + 1 + i = d.pd + (i + 1)
        by omega])
      (by simp [D.setReg, D.reg]; rwa [show d.pd + 1 + j = d.pd + (j + 1) by omega])
      (by simp [D.setReg, D.reg]; omega) (by simp [D.setReg, D.reg]; omega)
    refine WExec.cast cap (WExec.whsT (by rw [wbit_D]; simpa using hs 0 (by omega)) (s1.seq s2) ih) ?_ (by omega)
    dfinS

theorem skipK_spec : ∀ (j : ℕ) (d : D), d.K = j → d.pd + j ≤ cap →
    WExec cap skipK (st b desc q d) (st b desc q { d with pd := d.pd + j, K := 0 }) (9 * j + 1)
  | 0, d, hK, _ => by
    refine WExec.cast cap (WExec.whrF (by rw [st_val]; simpa [D.reg] using hK)) ?_ (by omega)
    dfinS
  | j + 1, d, hK, hc => by
    have s1 := x_dec cap b desc q d rK (by decide) (by simp [D.reg]; omega)
    have s2 := x_fwdD cap b desc q (d.setReg rK (d.reg rK - 1)) (by simp [D.setReg]; omega)
    have ih := skipK_spec j { d.setReg rK (d.reg rK - 1) with pd := (d.setReg rK (d.reg rK - 1)).pd + 1 }
      (by simp [D.setReg, D.reg]; omega) (by simp [D.setReg]; omega)
    refine WExec.cast cap (WExec.whrT (by rw [st_val]; simp [D.reg]; omega) (s1.seq s2) ih) ?_ (by omega)
    dfinS

theorem skipKT_spec : ∀ (j : ℕ) (d : D), d.K = j → d.pd + j ≤ cap → d.T + j ≤ cap →
    WExec cap skipKT (st b desc q d) (st b desc q { d with pd := d.pd + j, K := 0, T := d.T + j }) (13 * j + 1)
  | 0, d, hK, _, _ => by
    refine WExec.cast cap (WExec.whrF (by rw [st_val]; simpa [D.reg] using hK)) ?_ (by omega)
    dfinS
  | j + 1, d, hK, hc, hT => by
    have s1 := x_dec cap b desc q d rK (by decide) (by simp [D.reg]; omega)
    have s2 := x_inc cap b desc q (d.setReg rK (d.reg rK - 1)) rT (by decide) (by simp [D.setReg, D.reg]; omega)
    have s3 := x_fwdD cap b desc q ((d.setReg rK (d.reg rK - 1)).setReg rT ((d.setReg rK (d.reg rK - 1)).reg rT + 1))
      (by simp [D.setReg]; omega)
    have ih := skipKT_spec j
      { (d.setReg rK (d.reg rK - 1)).setReg rT ((d.setReg rK (d.reg rK - 1)).reg rT + 1) with
        pd := ((d.setReg rK (d.reg rK - 1)).setReg rT ((d.setReg rK (d.reg rK - 1)).reg rT + 1)).pd + 1 }
      (by simp [D.setReg, D.reg]; omega) (by simp [D.setReg]; omega) (by simp [D.setReg, D.reg]; omega)
    refine WExec.cast cap (WExec.whrT (by rw [st_val]; simp [D.reg]; omega) (s1.seq (s2.seq s3)) ih) ?_
      (by omega)
    dfinS

theorem dblLoop_spec : ∀ (j : ℕ) (d : D), d.Y = j → d.X + 2 * j ≤ cap →
    WExec cap (.whr rY (.seq (.dec rY) (.seq (.inc rX) (.inc rX)))) (st b desc q d)
      (st b desc q { d with X := d.X + 2 * j, Y := 0 }) (11 * j + 1)
  | 0, d, hY, _ => by
    refine WExec.cast cap (WExec.whrF (by rw [st_val]; simpa [D.reg] using hY)) ?_ (by omega)
    dfinS
  | j + 1, d, hY, hc => by
    have s1 := x_dec cap b desc q d rY (by decide) (by simp [D.reg]; omega)
    have s2 := x_inc cap b desc q (d.setReg rY (d.reg rY - 1)) rX (by decide) (by simp [D.setReg, D.reg]; omega)
    have s3 := x_inc cap b desc q ((d.setReg rY (d.reg rY - 1)).setReg rX ((d.setReg rY (d.reg rY - 1)).reg rX + 1))
      rX (by decide) (by simp [D.setReg, D.reg]; omega)
    have ih := dblLoop_spec j (((d.setReg rY (d.reg rY - 1)).setReg rX ((d.setReg rY (d.reg rY - 1)).reg rX + 1)).setReg
      rX (((d.setReg rY (d.reg rY - 1)).setReg rX ((d.setReg rY (d.reg rY - 1)).reg rX + 1)).reg rX + 1))
      (by simp [D.setReg, D.reg]; omega) (by simp [D.setReg, D.reg]; omega)
    refine WExec.cast cap (WExec.whrT (by rw [st_val]; simp [D.reg]; omega) (s1.seq (s2.seq s3)) ih) ?_
      (by omega)
    dfinS

theorem dbl_spec (d : D) (hY : d.Y = 0) (hc : 2 * d.X ≤ cap) :
    WExec cap dbl (st b desc q d) (st b desc q { d with X := 2 * d.X, Y := 0 }) (18 * d.X + 3) := by
  have s1 := x_move cap b desc q d rX rY (by decide) (by decide) (by decide) (by simp [D.reg]; omega)
    (by simp [D.reg]; omega)
  have s2 := dblLoop_spec cap b desc q d.X ((d.setReg rX 0).setReg rY ((d.setReg rX 0).reg rY + d.reg rX))
    (by simp [D.setReg, D.reg, hY]) (by simp [D.setReg, D.reg]; omega)
  refine WExec.cast cap (s1.seq s2) ?_ (by simp [D.reg]; omega)
  dfinS

/-- Close `st b desc q X = st b desc q Y` for explicit data records. -/
macro "rfin" : tactic => `(tactic| (congr 1 <;> simp [D.setReg, D.reg] <;> omega))

/-- **Horner**: from the end of the field `bs` (at `base + j`, `X = value (bs.drop j)`), back to its start with
`X = value bs`. -/
theorem horner_spec (bs : List Bool) (base : ℕ)
    (hbits : ∀ i, i < bs.length → readTapeBit desc (base + i) = bs.getD i false) (hcap : value bs + 1 ≤ cap)
    (hpd : base + bs.length ≤ cap) (K pu : ℕ) (c : Bool) :
    ∀ (j : ℕ), j ≤ bs.length → ∃ n, n ≤ j * (18 * value bs + 16) + 1 ∧
      WExec cap horner (st b desc q ⟨base + j, pu, value (bs.drop j), 0, K, j, c⟩)
        (st b desc q ⟨base, pu, value bs, 0, K, 0, c⟩) n
  | 0, _ => ⟨1, by omega, WExec.cast cap (WExec.whrF (by rw [st_val]; rfl)) (by simp) le_rfl⟩
  | j + 1, hj => by
    have hv := value_drop_pred bs (j + 1) (by omega) hj
    rw [show j + 1 - 1 = j by omega] at hv
    have hle := value_drop_le bs j
    obtain ⟨n', hn', ih⟩ := horner_spec bs base hbits hcap hpd K pu c j (by omega)
    generalize hv0 : value (bs.drop (j + 1)) = v0 at hv
    generalize hv1 : value (bs.drop j) = v1 at hv hle ih
    generalize hbb : bs.getD j false = bb at hv
    have hbit0 : readTapeBit desc (base + j) = bb := by rw [← hbb]; exact hbits j (by omega)
    have s1 : WExec cap (.dec rT) (st b desc q ⟨base + (j + 1), pu, v0, 0, K, j + 1, c⟩)
        (st b desc q ⟨base + (j + 1), pu, v0, 0, K, j, c⟩) 1 :=
      WExec.cast cap (x_dec cap b desc q _ rT (by decide) (by simp [D.reg]; omega)) (by rfin) le_rfl
    have s2 : WExec cap bwdD (st b desc q ⟨base + (j + 1), pu, v0, 0, K, j, c⟩)
        (st b desc q ⟨base + j, pu, v0, 0, K, j, c⟩) 3 :=
      WExec.cast cap (x_bwdD cap b desc q _ (by simp; omega)) (by rfin) le_rfl
    have s3 : WExec cap dbl (st b desc q ⟨base + j, pu, v0, 0, K, j, c⟩)
        (st b desc q ⟨base + j, pu, 2 * v0, 0, K, j, c⟩) (18 * v0 + 3) :=
      WExec.cast cap (dbl_spec cap b desc q _ rfl (by simp; omega)) (by rfin) le_rfl
    have s4 : ∃ n4, n4 ≤ 4 ∧ WExec cap (.ifs sD (.inc rX) .skip) (st b desc q ⟨base + j, pu, 2 * v0, 0, K, j, c⟩)
        (st b desc q ⟨base + j, pu, v1, 0, K, j, c⟩) n4 := by
      cases bb with
      | true =>
        refine ⟨4, le_rfl, WExec.ifsT (by rw [wbit_D]; exact hbit0)
          (WExec.cast cap (x_inc cap b desc q _ rX (by decide) (by simp [D.reg] at hv ⊢; omega)) (by
            simp at hv; rfin) le_rfl)⟩
      | false =>
        refine ⟨1, by omega, WExec.ifsF (by rw [wbit_D]; exact hbit0) (WExec.cast cap (WExec.skip _) (by
          simp at hv; rfin) (by omega))⟩
    obtain ⟨n4, hn4, s4⟩ := s4
    have hv0le : v0 ≤ value bs := by
      have := value_drop_le bs (j + 1); omega
    have hmul : (j + 1) * (18 * value bs + 16) = j * (18 * value bs + 16) + (18 * value bs + 16) := by ring
    exact ⟨_, by omega, WExec.whrT (by rw [st_val]; simp [D.reg]) (s1.seq (s2.seq (s3.seq s4))) ih⟩

/-! ## The descriptor's two fields -/

theorem rd_app (l1 l2 : List Bool) (i : ℕ) : readTapeBit (l1 ++ l2) (l1.length + i) = readTapeBit l2 i := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem rd_ones (k i : ℕ) (t : List Bool) (hi : i < k) : readTapeBit (List.replicate k true ++ false :: t) i = true := by
  unfold readTapeBit
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]

theorem rd_sep (k : ℕ) (t : List Bool) : readTapeBit (List.replicate k true ++ false :: t) k = false := by
  have := rd_app (List.replicate k true) (false :: t) 0
  simp only [List.length_replicate, Nat.add_zero] at this
  rw [this]; rfl

theorem rd_tail (k i : ℕ) (t : List Bool) :
    readTapeBit (List.replicate k true ++ false :: t) (k + 1 + i) = t.getD i false := by
  have := rd_app (List.replicate k true ++ [false]) t i
  simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_replicate,
    List.length_singleton] at this
  rw [this]; rfl

/-- A field `1^k 0 b` (`|b| = k`) has length `2k + 1`. -/
theorem field_length (k : ℕ) (b : List Bool) (hb : b.length = k) :
    (List.replicate k true ++ false :: b).length = 2 * k + 1 := by
  simp [hb]; omega

theorem rd_field_ones (k i : ℕ) (b X : List Bool) (hi : i < k) :
    readTapeBit ((List.replicate k true ++ false :: b) ++ X) i = true := by
  rw [List.append_assoc, List.cons_append]; exact rd_ones k i _ hi

theorem rd_field_sep (k : ℕ) (b X : List Bool) : readTapeBit ((List.replicate k true ++ false :: b) ++ X) k = false := by
  rw [List.append_assoc, List.cons_append]; exact rd_sep k _

theorem rd_field_bit (k i : ℕ) (b X : List Bool) (hb : b.length = k) (hi : i < k) :
    readTapeBit ((List.replicate k true ++ false :: b) ++ X) (k + 1 + i) = b.getD i false := by
  rw [List.append_assoc, List.cons_append, rd_tail, List.getD_append _ _ _ _ (by omega)]

/-- **The parse**: past the first field `1^{k₁} 0 b₁`, the second field's value into `X`. -/
theorem parse_spec (k1 k2 : ℕ) (b1 bs rest : List Bool) (hb1 : b1.length = k1) (hbs : bs.length = k2)
    (hdesc : desc = (List.replicate k1 true ++ false :: b1) ++ ((List.replicate k2 true ++ false :: bs) ++ rest))
    (hcap1 : 2 * k1 + 2 * k2 + 2 ≤ cap) (hcap2 : value bs + 1 ≤ cap) (c : Bool) :
    ∃ n, n ≤ 20 * k1 + 24 * k2 + k2 * (18 * value bs + 16) + 21 ∧
      WExec cap parse (st b desc q ⟨0, 0, 0, 0, 0, 0, c⟩) (st b desc q ⟨2 * k1 + 2 + k2, 0, value bs, 0, 0, 0, c⟩) n := by
  have hl1 := field_length k1 b1 hb1
  set F1 := List.replicate k1 true ++ false :: b1 with hF1
  set F2 := List.replicate k2 true ++ false :: bs with hF2
  have rdA : ∀ i, i < k1 → readTapeBit desc i = true := fun i hi => by rw [hdesc]; exact rd_field_ones k1 i b1 _ hi
  have rdA' : readTapeBit desc k1 = false := by rw [hdesc]; exact rd_field_sep k1 b1 _
  have rdB : ∀ i, i < k2 → readTapeBit desc (2 * k1 + 1 + i) = true := fun i hi => by
    rw [hdesc, ← hl1, rd_app]; exact rd_field_ones k2 i bs _ hi
  have rdB' : readTapeBit desc (2 * k1 + 1 + k2) = false := by
    rw [hdesc, ← hl1, rd_app]; exact rd_field_sep k2 bs _
  have rdC : ∀ i, i < bs.length → readTapeBit desc (2 * k1 + 2 + k2 + i) = bs.getD i false := fun i hi => by
    rw [hdesc, show 2 * k1 + 2 + k2 + i = F1.length + (k2 + 1 + i) by rw [hl1]; omega, rd_app]
    exact rd_field_bit k2 i bs rest hbs (by omega)
  -- the first field's ones
  have s1 : WExec cap onesK (st b desc q ⟨0, 0, 0, 0, 0, 0, c⟩) (st b desc q ⟨k1, 0, 0, 0, k1, 0, c⟩) (11 * k1 + 1) :=
    WExec.cast cap (onesK_spec cap b desc q k1 ⟨0, 0, 0, 0, 0, 0, c⟩
      (by intro i hi; simpa using rdA i hi) (by simpa using rdA') (by simp; omega) (by simp; omega)) (by rfin) le_rfl
  have s2 : WExec cap (WM.fwdC sD rPD) (st b desc q ⟨k1, 0, 0, 0, k1, 0, c⟩)
      (st b desc q ⟨k1 + 1, 0, 0, 0, k1, 0, c⟩) 5 :=
    WExec.cast cap (x_fwdD cap b desc q _ (by simp; omega)) (by rfin) le_rfl
  have s3 : WExec cap skipK (st b desc q ⟨k1 + 1, 0, 0, 0, k1, 0, c⟩) (st b desc q ⟨2 * k1 + 1, 0, 0, 0, 0, 0, c⟩)
      (9 * k1 + 1) :=
    WExec.cast cap (skipK_spec cap b desc q k1 _ rfl (by simp; omega)) (by rfin) le_rfl
  -- the second field's ones
  have s4 : WExec cap onesK (st b desc q ⟨2 * k1 + 1, 0, 0, 0, 0, 0, c⟩)
      (st b desc q ⟨2 * k1 + 1 + k2, 0, 0, 0, k2, 0, c⟩) (11 * k2 + 1) :=
    WExec.cast cap (onesK_spec cap b desc q k2 ⟨2 * k1 + 1, 0, 0, 0, 0, 0, c⟩
      (by intro i hi; exact rdB i hi) rdB' (by simp; omega) (by simp; omega)) (by rfin) le_rfl
  have s5 : WExec cap (WM.fwdC sD rPD) (st b desc q ⟨2 * k1 + 1 + k2, 0, 0, 0, k2, 0, c⟩)
      (st b desc q ⟨2 * k1 + 2 + k2, 0, 0, 0, k2, 0, c⟩) 5 :=
    WExec.cast cap (x_fwdD cap b desc q _ (by simp; omega)) (by rfin) le_rfl
  have hdrop : value (bs.drop k2) = 0 := by rw [← hbs, List.drop_length]; rfl
  have s6 : WExec cap skipKT (st b desc q ⟨2 * k1 + 2 + k2, 0, 0, 0, k2, 0, c⟩)
      (st b desc q ⟨2 * k1 + 2 + k2 + k2, 0, value (bs.drop k2), 0, 0, k2, c⟩) (13 * k2 + 1) :=
    WExec.cast cap (skipKT_spec cap b desc q k2 _ rfl (by simp; omega) (by simp; omega)) (by rw [hdrop]; rfin) le_rfl
  -- Horner over the second field's bits
  obtain ⟨n7, hn7, s7⟩ := horner_spec cap b desc q bs (2 * k1 + 2 + k2) rdC hcap2 (by omega) 0 0 c k2 (by omega)
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))⟩
  omega

/-! ## The division by `q + 1` -/

/-- **The division loop**: `x` units walked cyclically along `1^q` (`q` steps, then one quotient unit and back), from
`p` steps into the current round and `y` quotient units; the time is `16x + 6p + 1` (each return paid by its `q`
steps). -/
theorem unit_spec (S : ℕ) (hS : S + 1 ≤ cap) (pd K T : ℕ) (c : Bool) :
    ∀ (x y p : ℕ), p ≤ q → y * (q + 1) + p + x ≤ S → ∃ n, n ≤ 16 * x + 6 * p + 1 ∧
      WExec cap (.whr rX unitP) (st b desc q ⟨pd, p, x, y, K, T, c⟩)
        (st b desc q ⟨pd, (p + x) % (q + 1), 0, y + (p + x) / (q + 1), K, T, c⟩) n
  | 0, y, p, hp, _ => by
    refine ⟨1, by omega, WExec.cast cap (WExec.whrF (by rw [st_val]; rfl)) ?_ le_rfl⟩
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  | x + 1, y, p, hp, hS' => by
    have hy : y ≤ y * (q + 1) := Nat.le_mul_of_pos_right y (by omega)
    have s1 : WExec cap (.dec rX) (st b desc q ⟨pd, p, x + 1, y, K, T, c⟩) (st b desc q ⟨pd, p, x, y, K, T, c⟩) 1 :=
      WExec.cast cap (x_dec cap b desc q _ rX (by decide) (by simp [D.reg]; omega)) (by rfin) le_rfl
    by_cases hpq : p < q
    · have s2 : WExec cap (.ifs sU (WM.fwdC sU rP) (.seq (.inc rY) (WM.rewind sU rP)))
          (st b desc q ⟨pd, p, x, y, K, T, c⟩) (st b desc q ⟨pd, p + 1, x, y, K, T, c⟩) 6 :=
        WExec.ifsT (by rw [wbit_U]; simpa using hpq)
          (WExec.cast cap (x_fwdU cap b desc q _ (by simp; omega)) (by rfin) le_rfl)
      obtain ⟨n', hn', ih⟩ := unit_spec S hS pd K T c x y (p + 1) (by omega) (by omega)
      rw [show p + 1 + x = p + (x + 1) by omega] at ih
      exact ⟨_, by omega, WExec.whrT (by rw [st_val]; simp [D.reg]) (s1.seq s2) ih⟩
    · have hpq' : q = p := by omega
      subst hpq'
      have s2a : WExec cap (.inc rY) (st b desc q ⟨pd, q, x, y, K, T, c⟩) (st b desc q ⟨pd, q, x, y + 1, K, T, c⟩) 3 :=
        WExec.cast cap (x_inc cap b desc q _ rY (by decide) (by simp [D.reg]; omega)) (by rfin) le_rfl
      have s2b : WExec cap (WM.rewind sU rP) (st b desc q ⟨pd, q, x, y + 1, K, T, c⟩)
          (st b desc q ⟨pd, 0, x, y + 1, K, T, c⟩) (5 * q + 1) :=
        WExec.cast cap (x_rewU cap b desc q _ (by simp; omega)) (by rfin) le_rfl
      have s2 : WExec cap (.ifs sU (WM.fwdC sU rP) (.seq (.inc rY) (WM.rewind sU rP)))
          (st b desc q ⟨pd, q, x, y, K, T, c⟩) (st b desc q ⟨pd, 0, x, y + 1, K, T, c⟩) (5 * q + 6) :=
        WExec.cast cap (WExec.ifsF (by rw [wbit_U]; simp) (s2a.seq s2b)) rfl (by omega)
      have hmul : (y + 1) * (q + 1) = y * (q + 1) + q + 1 := by ring
      obtain ⟨n', hn', ih⟩ := unit_spec S hS pd K T c x (y + 1) 0 (by omega) (by omega)
      have e1 : (q + (x + 1)) % (q + 1) = (0 + x) % (q + 1) := by
        rw [show q + (x + 1) = x + (q + 1) by omega, Nat.add_mod_right, Nat.zero_add]
      have e2 : y + (q + (x + 1)) / (q + 1) = y + 1 + (0 + x) / (q + 1) := by
        rw [show q + (x + 1) = x + 1 * (q + 1) by omega, Nat.add_mul_div_right _ _ (by omega), Nat.zero_add]; omega
      rw [e1, e2]
      exact ⟨_, by omega, WExec.whrT (by rw [st_val]; simp [D.reg]) (s1.seq s2) ih⟩

/-- **One division**: `X := X / (q+1)`, the width's head back at its start. -/
theorem divOnce_spec (S : ℕ) (hS : S + 1 ≤ cap) (pd K T : ℕ) (c : Bool) (x : ℕ) (hx : x ≤ S) :
    ∃ n, n ≤ 28 * x + 6 ∧ WExec cap divOnce (st b desc q ⟨pd, 0, x, 0, K, T, c⟩)
      (st b desc q ⟨pd, 0, x / (q + 1), 0, K, T, c⟩) n := by
  obtain ⟨n1, hn1, s1⟩ := unit_spec cap b desc q S hS pd K T c x 0 0 (by omega) (by simp; omega)
  simp only [Nat.zero_add] at s1
  have hm : x % (q + 1) ≤ x := Nat.mod_le x (q + 1)
  have hd : x / (q + 1) ≤ x := Nat.div_le_self x (q + 1)
  have s2 : WExec cap (WM.rewind sU rP) (st b desc q ⟨pd, x % (q + 1), 0, x / (q + 1), K, T, c⟩)
      (st b desc q ⟨pd, 0, 0, x / (q + 1), K, T, c⟩) (5 * (x % (q + 1)) + 1) :=
    WExec.cast cap (x_rewU cap b desc q _ (by simp; omega)) (by rfin) le_rfl
  have s3 : WExec cap (WM.move rY rX) (st b desc q ⟨pd, 0, 0, x / (q + 1), K, T, c⟩)
      (st b desc q ⟨pd, 0, x / (q + 1), 0, K, T, c⟩) (7 * (x / (q + 1)) + 1) :=
    WExec.cast cap (x_move cap b desc q _ rY rX (by decide) (by decide) (by decide) (by simp [D.reg]; omega)
      (by simp [D.reg]; omega)) (by rfin) (by simp [D.reg])
  exact ⟨_, by omega, s1.seq (s2.seq s3)⟩

/-- **`n` divisions**: `X := X / (q+1)^n`. -/
theorem divs_spec (S : ℕ) (hS : S + 1 ≤ cap) (pd K T : ℕ) (c : Bool) :
    ∀ (n x : ℕ), x ≤ S → ∃ m, m ≤ n * (28 * S + 7) ∧ WExec cap (divs n) (st b desc q ⟨pd, 0, x, 0, K, T, c⟩)
      (st b desc q ⟨pd, 0, x / (q + 1) ^ n, 0, K, T, c⟩) m
  | 0, x, _ => ⟨0, Nat.zero_le _, WExec.cast cap (WExec.skip _) (by simp) le_rfl⟩
  | n + 1, x, hx => by
    obtain ⟨m1, hm1, s1⟩ := divOnce_spec cap b desc q S hS pd K T c x hx
    obtain ⟨m2, hm2, s2⟩ := divs_spec S hS pd K T c n (x / (q + 1)) ((Nat.div_le_self x (q + 1)).trans hx)
    rw [Nat.div_div_eq_div_mul, ← pow_succ'] at s2
    have hmul : (n + 1) * (28 * S + 7) = n * (28 * S + 7) + (28 * S + 7) := by ring
    exact ⟨_, by omega, s1.seq s2⟩

/-! ## The verdict and the check -/

theorem tail_spec (pd x : ℕ) (c : Bool) (hx : x ≤ cap) (hpd : pd ≤ cap) :
    WExec cap tailP (st b desc q ⟨pd, 0, x, 0, 0, 0, c⟩) (st b desc q (dF (decide (x = 0)))) (3 * x + 5 * pd + 6) := by
  have s1 : WExec cap (.ifr rX (.setc false) (.setc true)) (st b desc q ⟨pd, 0, x, 0, 0, 0, c⟩)
      (st b desc q ⟨pd, 0, x, 0, 0, 0, decide (x = 0)⟩) 2 := by
    by_cases h : x = 0
    · exact WExec.ifrF (by rw [st_val]; simpa [D.reg] using h)
        (WExec.cast cap (x_setc cap b desc q _ true) (by simp [h]) le_rfl)
    · exact WExec.ifrT (by rw [st_val]; simpa [D.reg] using h)
        (WExec.cast cap (x_setc cap b desc q _ false) (by simp [h]) le_rfl)
  have s2 : WExec cap (WM.clear rX) (st b desc q ⟨pd, 0, x, 0, 0, 0, decide (x = 0)⟩)
      (st b desc q ⟨pd, 0, 0, 0, 0, 0, decide (x = 0)⟩) (3 * x + 1) :=
    WExec.cast cap (x_clear cap b desc q _ rX (by decide) (by simp [D.reg]; omega)) (by rfin) (by simp [D.reg])
  have s3 : WExec cap (WM.rewind sD rPD) (st b desc q ⟨pd, 0, 0, 0, 0, 0, decide (x = 0)⟩)
      (st b desc q (dF (decide (x = 0)))) (5 * pd + 1) :=
    WExec.cast cap (x_rewD cap b desc q _ (by simp; omega)) (by simp [dF]) le_rfl
  exact WExec.cast cap (s1.seq (s2.seq s3)) rfl (by omega)

/-- The check's time bound at register capacity `cap` and `Dg` divisions. -/
def sizeCost (cap Dg : ℕ) : ℕ := cap * (18 * cap + 16) + Dg * (28 * cap + 7) + 60 * cap + 30

/-- **The check on a decoded oracle**: the cell becomes `decide (c.size ≤ oracleSizeBound G q)`. -/
theorem sizeP_true (G : ℕ) (c : BooleanCircuit q) (hcap1 : c.size + 1 ≤ cap)
    (hcap2 : 2 * natBitLength q + 2 * natBitLength c.size + 2 ≤ cap) :
    ∃ n, n ≤ sizeCost cap (2 ^ RecoveryScheduleEnvelope.oracleDepth G) ∧
      WExec cap (sizeP (2 ^ RecoveryScheduleEnvelope.oracleDepth G)) (st true (PCPPNative.descriptor c) q d0)
        (st true (PCPPNative.descriptor c) q (dF (decide (c.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G q)))) n := by
  set s := c.size with hs
  set Dg := 2 ^ RecoveryScheduleEnvelope.oracleDepth G with hDg
  set k1 := natBitLength q
  set k2 := natBitLength s
  have hv : value (binary k2 s) = s := binary_value k2 s (Round.natBitLength_lt s)
  have hdesc : PCPPNative.descriptor c = (List.replicate k1 true ++ false :: binary k1 q) ++
      ((List.replicate k2 true ++ false :: binary k2 s) ++
        (c.nodes.flatMap PCPPRequestNodeSchema.native ++ natWord c.output.val)) := by
    rw [PCPPNative.descriptor_eq, ← Round.natWord_eq, ← Round.natWord_eq]
    simp only [hs, BooleanCircuit.size, List.append_assoc]
  obtain ⟨n1, hn1, s1⟩ := parse_spec cap true (PCPPNative.descriptor c) q k1 k2 (binary k1 q) (binary k2 s) _
    (binary_length k1 q) (binary_length k2 s) hdesc (by omega) (by rw [hv]; omega) false
  rw [hv] at s1 hn1
  obtain ⟨m, hm, s2⟩ := divs_spec cap true (PCPPNative.descriptor c) q s (by omega) (2 * k1 + 2 + k2) 0 0 false Dg s
    le_rfl
  have hq : s / (q + 1) ^ Dg ≤ s := Nat.div_le_self _ _
  have s3 := tail_spec cap true (PCPPNative.descriptor c) q (2 * k1 + 2 + k2) (s / (q + 1) ^ Dg) false (by omega)
    (by omega)
  have hdec : decide (s / (q + 1) ^ Dg = 0) = decide (s ≤ RecoveryScheduleEnvelope.oracleSizeBound G q) :=
    decide_eq_decide.mpr (by rw [hDg]; exact div_pow_eq_zero_iff G q s)
  rw [hdec] at s3
  have hk2 : k2 * (18 * s + 16) ≤ cap * (18 * cap + 16) := Nat.mul_le_mul (by omega) (by omega)
  have hD : Dg * (28 * s + 7) ≤ Dg * (28 * cap + 7) := Nat.mul_le_mul_left _ (by omega)
  refine ⟨_, ?_, WExec.ifsT (by rw [wbit_F]) (s1.seq (s2.seq s3))⟩
  unfold sizeCost
  omega

/-- **No decoded oracle**: the cell stays `false`. -/
theorem sizeP_false (Dg : ℕ) : WExec cap (sizeP Dg) (st false desc q d0) (st false desc q (dF false)) 2 :=
  WExec.ifsF (by rw [wbit_F]) (WExec.cast cap (x_setc cap false desc q d0 false) rfl le_rfl)


end NearCubicWires.WireExponent3_5.UnionMachine.FrontSize
