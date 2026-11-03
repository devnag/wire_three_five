import Proof.Wire_3_5.UnionMachine.FrontWalkRef
import Proof.Wire_3_5.FinalPass.WordAux
import Proof.Wire_3_5.FinalPass.HashTable

/-! # C6 front, U1a: the walker of the guess's oracle field (P3:3669-3671)

Realizes "The weak machine guesses one size-`q^G` general oracle, a class tag, [...] It rejects malformed
descriptions" (P3:3669-3671) for the guess's first two fields in the codec: the class tag bit and the oracle's
code `natWord c` (`decodeGuess`, `readNat`). A register program (`WM`, C5's word machines) reads the framed witness
`frame w` once and leaves:
* on stream `P`: `frame (payload t)`, the code's bits (low first; `t = w.tail`);
* on stream `R`: `frame (restOf t)`, the rest of the guess (the grid sums, U1b);
* on stream `Tg`: `[tag]`;
* in the result cell: `okOf w`, which is `true` exactly when `w ≠ []` and the reader accepts the field
  (`FrontWalkRef.readNat_isSome`);
every head and register back at `0`, the witness untouched.

The program: the tag; the ones loop (`k`, a missing separator is malformed); the copy loop (`k` payload bits, the last
one kept; a missing bit is malformed); the rest loop; the verdict `¬bad ∧ k ≥ 1 ∧ (k = 1 ∨ last bit)`; the tag; the
rewinds. Main statement: **`walkP_spec`**. Paper quantity: the guess's oracle field and tag, checked. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontOracleField
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef

/-! ## Layout: streams `W P R Tg`; registers `K C T LB BAD F TG PW PP PR` -/

abbrev WS := WState 3 10

local notation "sW" => (0 : Fin 4)
local notation "sP" => (1 : Fin 4)
local notation "sR" => (2 : Fin 4)
local notation "sT" => (3 : Fin 4)
local notation "rK" => (0 : Fin 10)
local notation "rC" => (1 : Fin 10)
local notation "rT" => (2 : Fin 10)
local notation "rLB" => (3 : Fin 10)
local notation "rBAD" => (4 : Fin 10)
local notation "rF" => (5 : Fin 10)
local notation "rTG" => (6 : Fin 10)
local notation "rPW" => (7 : Fin 10)
local notation "rPP" => (8 : Fin 10)
local notation "rPR" => (9 : Fin 10)

/-- The walker's data: the three moving heads (each equal to its counter), the output words, the seven work
registers and the cell. -/
structure D where
  pw : ℕ
  pp : ℕ
  pr : ℕ
  P : List Bool
  R : List Bool
  Tg : List Bool
  K : ℕ
  C : ℕ
  T : ℕ
  LB : ℕ
  BAD : ℕ
  F : ℕ
  TG : ℕ
  cell : Bool

/-- The state of the data, on the witness `frame w`. -/
def st (w : List Bool) (d : D) : WS :=
  ⟨![d.pw, d.pp, d.pr, 0], ![frame w, d.P, d.R, d.Tg], ![d.K, d.C, d.T, d.LB, d.BAD, d.F, d.TG, d.pw, d.pp, d.pr],
    d.cell⟩

/-- The work register `r` of the data. -/
def D.reg (d : D) (r : Fin 10) : ℕ := ![d.K, d.C, d.T, d.LB, d.BAD, d.F, d.TG, d.pw, d.pp, d.pr] r

/-- Setting a work register (`r < 7`). -/
def D.setReg (d : D) (r : Fin 10) (x : ℕ) : D :=
  if r = rK then { d with K := x } else if r = rC then { d with C := x } else if r = rT then { d with T := x }
  else if r = rLB then { d with LB := x } else if r = rBAD then { d with BAD := x } else if r = rF then { d with F := x }
  else if r = rTG then { d with TG := x } else d

variable (cap : ℕ) (w : List Bool)

set_option hygiene false in
/-- Close `st w X = st w Y` for data records `X`, `Y` built from `d`. -/
macro "dfin" : tactic =>
  `(tactic| (congr 1 <;> cases d <;> (try simp_all [D.setReg, D.reg, m0]) <;> omega))

theorem st_val (d : D) (r : Fin 10) : (st w d).val r = d.reg r := rfl

theorem st_setv (d : D) (r : Fin 10) (hr : r.val < 7) (x : ℕ) : (st w d).setv r x = st w (d.setReg r x) := by
  fin_cases r <;> simp at hr <;>
    (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | rfl
        | (funext i; fin_cases i <;> simp [st, D.setReg, Function.update_apply]))

theorem wbit_W (d : D) : wbit (st w d) sW = readTapeBit (frame w) d.pw := rfl

/-! ## One-instruction steps on the data -/

theorem x_inc (d : D) (r : Fin 10) (hr : r.val < 7) (hc : d.reg r < cap) :
    WExec cap (.inc r) (st w d) (st w (d.setReg r (d.reg r + 1))) 3 := by
  have h := WExec.inc (cap := cap) r (st w d) (by rw [st_val]; exact hc)
  rwa [st_val, st_setv w d r hr] at h

theorem x_dec (d : D) (r : Fin 10) (hr : r.val < 7) (hc : d.reg r ≤ cap) :
    WExec cap (.dec r) (st w d) (st w (d.setReg r (d.reg r - 1))) 1 := by
  have h := WExec.dec (cap := cap) r (st w d) (by rw [st_val]; exact hc)
  rwa [st_val, st_setv w d r hr] at h

theorem x_setF (d : D) (r : Fin 10) (hr : r.val < 7) (h1 : d.reg r ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (WM.setF r) (st w d) (st w (d.setReg r 1)) 4 := by
  have h := wsetF_spec cap r (st w d) (by rw [st_val]; exact h1) hcap
  rwa [st_setv w d r hr] at h

theorem x_clear (d : D) (r : Fin 10) (hr : r.val < 7) (hc : d.reg r ≤ cap) :
    WExec cap (WM.clear r) (st w d) (st w (d.setReg r 0)) (3 * d.reg r + 1) := by
  have h := wclear_spec cap r (d.reg r) (st w d) (st_val w d r) (by rw [st_val]; exact hc)
  rwa [st_setv w d r hr] at h

theorem x_fwdW (d : D) (hc : d.pw < cap) :
    WExec cap (WM.fwdC sW rPW) (st w d) (st w { d with pw := d.pw + 1 }) 5 := by
  refine WExec.cast cap (wfwdC_spec cap sW rPW (st w d) hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_emitP (d : D) (b : Bool) (hpp : d.pp = d.P.length) (hc : d.pp < cap) :
    WExec cap (emitC sP rPP b) (st w d) (st w { d with P := d.P ++ [b], pp := d.pp + 1 }) 7 := by
  refine WExec.cast cap (emitC_spec cap sP rPP b (st w d) hpp hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_emitR (d : D) (b : Bool) (hpr : d.pr = d.R.length) (hc : d.pr < cap) :
    WExec cap (emitC sR rPR b) (st w d) (st w { d with R := d.R ++ [b], pr := d.pr + 1 }) 7 := by
  refine WExec.cast cap (emitC_spec cap sR rPR b (st w d) hpr hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_wrP (d : D) (b : Bool) (hpp : d.pp = d.P.length) :
    WExec cap (.wr sP b) (st w d) (st w { d with P := d.P ++ [b] }) 1 := by
  refine WExec.cast cap (WExec.wr sP b (st w d)) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply, hpp, writeTapeBit_end'])

theorem x_wrR (d : D) (b : Bool) (hpr : d.pr = d.R.length) :
    WExec cap (.wr sR b) (st w d) (st w { d with R := d.R ++ [b] }) 1 := by
  refine WExec.cast cap (WExec.wr sR b (st w d)) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply, hpr, writeTapeBit_end'])

theorem x_wrT (d : D) (b : Bool) (hT : d.Tg = []) :
    WExec cap (.wr sT b) (st w d) (st w { d with Tg := [b] }) 1 := by
  refine WExec.cast cap (WExec.wr sT b (st w d)) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply, hT, writeTapeBit])

theorem x_setc (d : D) (b : Bool) : WExec cap (.setc b) (st w d) (st w { d with cell := b }) 1 :=
  WExec.cast cap (WExec.setc b (st w d)) rfl le_rfl

theorem x_rewW (d : D) (hc : d.pw ≤ cap) :
    WExec cap (WM.rewind sW rPW) (st w d) (st w { d with pw := 0 }) (5 * d.pw + 1) := by
  refine WExec.cast cap (wrewind_spec cap sW rPW d.pw (st w d) rfl hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_rewP (d : D) (hc : d.pp ≤ cap) :
    WExec cap (WM.rewind sP rPP) (st w d) (st w { d with pp := 0 }) (5 * d.pp + 1) := by
  refine WExec.cast cap (wrewind_spec cap sP rPP d.pp (st w d) rfl hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_rewR (d : D) (hc : d.pr ≤ cap) :
    WExec cap (WM.rewind sR rPR) (st w d) (st w { d with pr := 0 }) (5 * d.pr + 1) := by
  refine WExec.cast cap (wrewind_spec cap sR rPR d.pr (st w d) rfl hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

/-! ## The program -/

/-- The tag: `TG := w₀`, or `BAD := 1` on the empty witness. -/
def tagP : WM 3 10 :=
  .ifs sW (.seq (WM.fwdC sW rPW) (.seq (.ifs sW (.inc rTG) .skip) (WM.fwdC sW rPW))) (.inc rBAD)

/-- One logical bit of the unary prefix: on `1` count it; on `0` stop past it; at the end stop, malformed. -/
def onesBody : WM 3 10 :=
  .ifs sW (.seq (WM.fwdC sW rPW) (.ifs sW (.seq (.inc rK) (WM.fwdC sW rPW)) (.seq (.dec rF) (WM.fwdC sW rPW))))
    (.seq (.dec rF) (WM.setF rBAD))
def onesP : WM 3 10 := .seq (.inc rF) (.whr rF onesBody)

/-- `C := K`, `K` kept. -/
def dupP : WM 3 10 := .seq (Hash4.wdup rK rC rT) (WM.move rT rK)

/-- One payload bit: copy it framed onto `P`, keeping it in `LB`; at the end stop, malformed. -/
def copyBody : WM 3 10 :=
  .seq (.dec rC) (.ifs sW
    (.seq (WM.fwdC sW rPW) (.seq (emitC sP rPP true) (.seq (.ifs sW (.seq (emitC sP rPP true) (WM.setF rLB))
      (.seq (emitC sP rPP false) (WM.clear rLB))) (WM.fwdC sW rPW))))
    (.seq (WM.setF rBAD) (WM.clear rC)))
def copyP : WM 3 10 := .seq dupP (.seq (.whr rC copyBody) (.wr sP false))

/-- One bit of the rest, copied framed onto `R`. -/
def restBody : WM 3 10 :=
  .seq (WM.fwdC sW rPW) (.seq (emitC sR rPR true) (.seq (.ifs sW (emitC sR rPR true) (emitC sR rPR false))
    (WM.fwdC sW rPW)))
def restP : WM 3 10 := .seq (.whs sW restBody) (.wr sR false)

/-- The verdict: `¬BAD ∧ K ≥ 1 ∧ (K = 1 ∨ LB)`. -/
def verdictP : WM 3 10 :=
  .ifr rBAD (.setc false) (.ifr rK (.seq (.dec rK) (.ifr rK (.ifr rLB (.setc true) (.setc false)) (.setc true)))
    (.setc false))

/-- The tag onto `Tg`. -/
def tagOutP : WM 3 10 := .ifr rTG (.wr sT true) (.wr sT false)

/-- Every head and register back at `0`. -/
def cleanP : WM 3 10 :=
  .seq (WM.rewind sW rPW) (.seq (WM.rewind sP rPP) (.seq (WM.rewind sR rPR) (.seq (WM.clear rK)
    (.seq (WM.clear rLB) (.seq (WM.clear rBAD) (WM.clear rTG))))))

/-- **The oracle-field walker.** -/
def walkP : WM 3 10 :=
  .seq tagP (.seq onesP (.seq copyP (.seq restP (.seq verdictP (.seq tagOutP cleanP)))))

/-! ## Reading the framed witness -/

theorem frame_mark (bs : List Bool) (i : ℕ) : readTapeBit (frame bs) (2 * i) = decide (i < bs.length) := by
  induction bs generalizing i with
  | nil => cases i <;> rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
      show readTapeBit (frame bs) (2 * j) = _
      rw [ih j]
      simp

theorem frame_bit (bs : List Bool) (i : ℕ) : readTapeBit (frame bs) (2 * i + 1) = bs.getD i false := by
  induction bs generalizing i with
  | nil => cases i <;> rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by omega]
      show readTapeBit (frame bs) (2 * j + 1) = _
      rw [ih j]
      simp

/-- The logical start of the tail: `1` past the tag, `0` on the empty witness. -/
def m0 (w : List Bool) : ℕ := if w = [] then 0 else 1

theorem mark_t (j : ℕ) : readTapeBit (frame w) (2 * (m0 w + j)) = decide (j < w.tail.length) := by
  rw [frame_mark]
  cases w with
  | nil => simp [m0]
  | cons b t => simp [m0]; omega

theorem bit_t (j : ℕ) : readTapeBit (frame w) (2 * (m0 w + j) + 1) = w.tail.getD j false := by
  rw [frame_bit]
  cases w with
  | nil => simp [m0]
  | cons b t => simp [m0, Nat.add_comm 1 j]

theorem ones_true (t : List Bool) : ∀ j, j < ones t → t.getD j false = true := by
  induction t with
  | nil => intro j h; simp [ones_nil] at h
  | cons b t ih =>
    cases b with
    | false => intro j h; simp [ones_cons_false] at h
    | true =>
      intro j h
      rw [ones_cons_true] at h
      cases j with
      | zero => rfl
      | succ j => simpa using ih j (by omega)

/-! ## The tag -/

theorem tag_spec (d : D) (hpw : d.pw = 0) (hTG : d.TG = 0) (hBAD : d.BAD = 0) (hcap2 : 2 * w.length + 2 ≤ cap) :
    WExec cap tagP (st w d)
      (st w { d with pw := 2 * m0 w, TG := (w.headD false).toNat, BAD := if w = [] then 1 else 0 }) 17 := by
  cases w with
  | nil =>
    have hb : wbit (st [] d) sW = false := by rw [wbit_W, hpw]; rfl
    have h := x_inc cap [] d rBAD (by decide) (by simp [D.reg, hBAD]; omega)
    refine WExec.cast cap (WExec.ifsF hb h) ?_ (by omega)
    congr 1
    cases d; simp_all [D.setReg, D.reg, m0]
  | cons b t =>
    have hcap : 3 ≤ cap := by simp at hcap2; omega
    have hb : wbit (st (b :: t) d) sW = true := by rw [wbit_W, hpw]; rfl
    have s1 := x_fwdW cap (b :: t) d (by omega)
    set d1 := { d with pw := d.pw + 1 } with hd1
    have hb1 : wbit (st (b :: t) d1) sW = b := by rw [wbit_W, hd1, hpw]; rfl
    have s2 : WExec cap (.ifs sW (.inc rTG) .skip) (st (b :: t) d1) (st (b :: t) { d1 with TG := b.toNat }) 4 := by
      cases b with
      | true =>
        have h := x_inc cap (true :: t) d1 rTG (by decide) (by simp [D.reg, hd1, hTG]; omega)
        refine WExec.cast cap (WExec.ifsT hb1 h) ?_ (by omega)
        dfin
      | false =>
        refine WExec.cast cap (WExec.ifsF hb1 (WExec.skip _)) ?_ (by omega)
        dfin
    have s3 := x_fwdW cap (b :: t) { d1 with TG := b.toNat } (by show d.pw + 1 < cap; omega)
    refine WExec.cast cap (WExec.ifsT hb (s1.seq (s2.seq s3))) ?_ (by omega)
    dfin

/-! ## The ones loop -/

theorem ones_round (d : D) (hm : readTapeBit (frame w) d.pw = true) (hb : readTapeBit (frame w) (d.pw + 1) = true)
    (hc : d.pw + 2 ≤ cap) (hK : d.K + 1 ≤ cap) :
    WExec cap onesBody (st w d) (st w { d with pw := d.pw + 2, K := d.K + 1 }) 17 := by
  have s1 := x_fwdW cap w d (by omega)
  have s2 := x_inc cap w { d with pw := d.pw + 1 } rK (by decide) (by simp [D.reg]; omega)
  have s3 := x_fwdW cap w (({ d with pw := d.pw + 1 } : D).setReg rK (({ d with pw := d.pw + 1 } : D).reg rK + 1))
    (by simp [D.setReg]; omega)
  refine WExec.cast cap (WExec.ifsT (by rw [wbit_W]; exact hm) (s1.seq (WExec.ifsT (by rw [wbit_W]; exact hb)
    (s2.seq s3)))) ?_ (by omega)
  dfin

theorem ones_stop_sep (d : D) (hm : readTapeBit (frame w) d.pw = true)
    (hb : readTapeBit (frame w) (d.pw + 1) = false) (hc : d.pw + 2 ≤ cap) (hF : d.F = 1) :
    WExec cap onesBody (st w d) (st w { d with pw := d.pw + 2, F := 0 }) 15 := by
  have s1 := x_fwdW cap w d (by omega)
  have s2 := x_dec cap w { d with pw := d.pw + 1 } rF (by decide) (by simp [D.reg, hF]; omega)
  have s3 := x_fwdW cap w (({ d with pw := d.pw + 1 } : D).setReg rF (({ d with pw := d.pw + 1 } : D).reg rF - 1))
    (by simp [D.setReg]; omega)
  refine WExec.cast cap (WExec.ifsT (by rw [wbit_W]; exact hm) (s1.seq (WExec.ifsF (by rw [wbit_W]; exact hb)
    (s2.seq s3)))) ?_ (by omega)
  dfin

theorem ones_stop_end (d : D) (hm : readTapeBit (frame w) d.pw = false) (hF : d.F = 1) (hB : d.BAD ≤ 1)
    (hcap : 1 ≤ cap) :
    WExec cap onesBody (st w d) (st w { d with F := 0, BAD := 1 }) 7 := by
  have s1 := x_dec cap w d rF (by decide) (by simp [D.reg, hF]; omega)
  have s2 := x_setF cap w (d.setReg rF (d.reg rF - 1)) rBAD (by decide) (by simp [D.setReg, D.reg]; omega) hcap
  refine WExec.cast cap (WExec.ifsF (by rw [wbit_W]; exact hm) (s1.seq s2)) ?_ (by omega)
  dfin

/-- The ones loop from `j` counted ones (`K = j`, flag up) to its exit. -/
theorem ones_loop (hcap : 2 * w.length + 2 ≤ cap) :
    ∀ (m : ℕ) (d : D) (j : ℕ), j + m = ones w.tail → d.pw = 2 * (m0 w + j) → d.K = j → d.F = 1 → d.BAD ≤ 1 →
      WExec cap (.whr rF onesBody) (st w d)
        (st w (if ones w.tail < w.tail.length then
          { d with pw := 2 * (m0 w + ones w.tail) + 2, K := ones w.tail, F := 0 }
          else { d with pw := 2 * (m0 w + ones w.tail), K := ones w.tail, F := 0, BAD := 1 })) (19 * m + 18) := by
  have hle := ones_le w.tail
  have hm0 : m0 w + w.tail.length ≤ w.length := by cases w <;> simp [m0] <;> omega
  intro m
  induction m with
  | zero =>
    intro d j hj hpw hK hF hB
    have hjk : j = ones w.tail := by omega
    subst hjk
    by_cases hlt : ones w.tail < w.tail.length
    · rw [if_pos hlt]
      have hm : readTapeBit (frame w) d.pw = true := by rw [hpw, mark_t]; simpa using hlt
      have hb : readTapeBit (frame w) (d.pw + 1) = false := by
        rw [hpw, bit_t]
        have := ones_stop w.tail hlt
        rw [List.getD_eq_getElem _ _ hlt] at this ⊢
        exact this
      have r := ones_stop_sep cap w d hm hb (by omega) hF
      have e := WExec.whrF (cap := cap) (r := rF) (P := onesBody) (σ := st w { d with pw := d.pw + 2, F := 0 }) rfl
      refine WExec.cast cap (WExec.whrT (by simp [st, hF]) r e) ?_ (by omega)
      dfin
    · rw [if_neg hlt]
      have hm : readTapeBit (frame w) d.pw = false := by rw [hpw, mark_t]; simpa using hlt
      have r := ones_stop_end cap w d hm hF hB (by omega)
      have e := WExec.whrF (cap := cap) (r := rF) (P := onesBody) (σ := st w { d with F := 0, BAD := 1 }) rfl
      refine WExec.cast cap (WExec.whrT (by simp [st, hF]) r e) ?_ (by omega)
      dfin
  | succ m ih =>
    intro d j hj hpw hK hF hB
    have hjl : j < w.tail.length := by omega
    have hm : readTapeBit (frame w) d.pw = true := by rw [hpw, mark_t]; simpa using hjl
    have hb : readTapeBit (frame w) (d.pw + 1) = true := by
      rw [hpw, bit_t]; exact ones_true w.tail j (by omega)
    have r := ones_round cap w d hm hb (by rw [hpw]; omega) (by rw [hK]; omega)
    have rest := ih { d with pw := d.pw + 2, K := d.K + 1 } (j + 1) (by omega) (by simp [hpw]; ring)
      (by simp [hK]) (by simp [hF]) (by simp [hB])
    have e : ∀ d' : D, d'.pp = d.pp → d'.pr = d.pr → d'.P = d.P → d'.R = d.R → d'.Tg = d.Tg → d'.C = d.C →
        d'.T = d.T → d'.LB = d.LB → d'.BAD = d.BAD → d'.TG = d.TG → d'.cell = d.cell →
        (if ones w.tail < w.tail.length then
          { d' with pw := 2 * (m0 w + ones w.tail) + 2, K := ones w.tail, F := 0 }
          else { d' with pw := 2 * (m0 w + ones w.tail), K := ones w.tail, F := 0, BAD := 1 }) =
        (if ones w.tail < w.tail.length then
          { d with pw := 2 * (m0 w + ones w.tail) + 2, K := ones w.tail, F := 0 }
          else { d with pw := 2 * (m0 w + ones w.tail), K := ones w.tail, F := 0, BAD := 1 }) := by
      intro d' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      cases d; cases d'; simp_all
    rw [e _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl] at rest
    exact WExec.mono (WExec.whrT (by simp [st, hF]) r rest) (by omega)

/-! ## The copy loop -/

theorem dup_spec (d : D) (hC : d.C = 0) (hT : d.T = 0) (hK : d.K ≤ cap) :
    WExec cap dupP (st w d) (st w { d with C := d.K }) (18 * d.K + 3) := by
  have h1 := Hash4.wdup_spec cap rK rC rT (by decide) (by decide) (by decide) d.K (st w d) rfl hK
    (by rw [st_val]; simp [D.reg, hC]; omega) (by rw [st_val]; simp [D.reg, hT]; omega)
  rw [st_val, st_val, st_setv w d rK (by decide), st_setv w _ rC (by decide), st_setv w _ rT (by decide)] at h1
  have h2 := wmove_spec cap rT rK (by decide) d.K
    (st w (((d.setReg rK 0).setReg rC (d.reg rC + d.K)).setReg rT (d.reg rT + d.K)))
    (by rw [st_val]; simp [D.setReg, D.reg, hT]) (by rw [st_val]; simp [D.setReg, D.reg, hT]; omega)
    (by rw [st_val, st_val]; simp [D.setReg, D.reg, hT]; omega)
  rw [st_val, st_val, st_setv w _ rT (by decide), st_setv w _ rK (by decide)] at h2
  refine WExec.cast cap (h1.seq h2) ?_ (by omega)
  dfin

theorem frameP_snoc2 (l : List Bool) (b : Bool) : frameP (l ++ [b]) = frameP l ++ [true] ++ [b] := by
  simp [frameP]

/-- The data after one copied payload bit `b`. -/
def cpNext (d : D) (b : Bool) : D :=
  { d with pw := d.pw + 2, C := d.C - 1, P := d.P ++ [true, b], pp := d.pp + 2, LB := b.toNat }

/-- One payload bit copied (`C ≥ 1`, the bit present). -/
theorem copy_round (d : D) (hC : 1 ≤ d.C) (hCc : d.C ≤ cap) (hm : readTapeBit (frame w) d.pw = true)
    (hpp : d.pp = d.P.length) (hc : d.pw + 2 ≤ cap) (hcp : d.pp + 2 ≤ cap) (hLB : d.LB ≤ 1) :
    WExec cap copyBody (st w d) (st w (cpNext d (readTapeBit (frame w) (d.pw + 1)))) 36 := by
  have s1 := x_dec cap w d rC (by decide) (by simp [D.reg]; omega)
  set d1 := d.setReg rC (d.reg rC - 1) with hd1
  have e1 : d1 = { d with C := d.C - 1 } := by rw [hd1]; cases d; simp [D.setReg, D.reg]
  rw [e1] at s1
  have s2 := x_fwdW cap w { d with C := d.C - 1 } (by simp; omega)
  have s3 := x_emitP cap w { d with C := d.C - 1, pw := d.pw + 1 } true (by simpa using hpp) (by simp; omega)
  set b := readTapeBit (frame w) (d.pw + 1) with hb
  set d3 := ({ ({ d with C := d.C - 1, pw := d.pw + 1 } : D) with P := d.P ++ [true], pp := d.pp + 1 } : D) with hd3
  have s4 : WExec cap (.ifs sW (.seq (emitC sP rPP true) (WM.setF rLB)) (.seq (emitC sP rPP false) (WM.clear rLB)))
      (st w d3) (st w { d3 with P := d3.P ++ [b], pp := d3.pp + 1, LB := b.toNat }) 13 := by
    have hbit : wbit (st w d3) sW = b := by rw [wbit_W]
    cases hbv : b with
    | true =>
      have t1 := x_emitP cap w d3 true (by simp [hd3, hpp]) (by simp [hd3]; omega)
      have t2 := x_setF cap w { d3 with P := d3.P ++ [true], pp := d3.pp + 1 } rLB (by decide)
        (by simp [D.reg, hd3]; omega) (by omega)
      refine WExec.cast cap (WExec.ifsT (by rw [hbit, hbv]) (t1.seq t2)) ?_ (by omega)
      congr 1 <;> simp [D.setReg]
    | false =>
      have t1 := x_emitP cap w d3 false (by simp [hd3, hpp]) (by simp [hd3]; omega)
      have t2 := x_clear cap w { d3 with P := d3.P ++ [false], pp := d3.pp + 1 } rLB (by decide)
        (by simp [D.reg, hd3]; omega)
      refine WExec.cast cap (WExec.ifsF (by rw [hbit, hbv]) (t1.seq t2)) ?_ (by simp [D.reg, hd3]; omega)
      congr 1 <;> simp [D.setReg]
  have s5 := x_fwdW cap w { d3 with P := d3.P ++ [b], pp := d3.pp + 1, LB := b.toNat } (by simp [hd3]; omega)
  refine WExec.cast cap (s1.seq (WExec.ifsT (by rw [wbit_W]; exact hm) (s2.seq (s3.seq (s4.seq s5))))) ?_
    (by omega)
  rw [hd3]
  congr 1
  cases d
  simp [cpNext]

/-- The copy stops at a missing bit (`C ≥ 1`): malformed. -/
theorem copy_miss (d : D) (hC : 1 ≤ d.C) (hCc : d.C ≤ cap) (hm : readTapeBit (frame w) d.pw = false)
    (hB : d.BAD ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap copyBody (st w d) (st w { d with C := 0, BAD := 1 }) (3 * d.C + 9) := by
  have s1 := x_dec cap w d rC (by decide) (by simp [D.reg]; omega)
  have e1 : d.setReg rC (d.reg rC - 1) = { d with C := d.C - 1 } := by cases d; simp [D.setReg, D.reg]
  rw [e1] at s1
  have s2 := x_setF cap w { d with C := d.C - 1 } rBAD (by decide) (by simp [D.reg]; omega) hcap
  have e2 : ({ d with C := d.C - 1 } : D).setReg rBAD 1 = { d with C := d.C - 1, BAD := 1 } := by
    cases d; simp [D.setReg]
  rw [e2] at s2
  have s3 := x_clear cap w { d with C := d.C - 1, BAD := 1 } rC (by decide) (by simp [D.reg]; omega)
  refine WExec.cast cap (s1.seq (WExec.ifsF (by rw [wbit_W]; exact hm) (s2.seq s3))) ?_
    (by simp [D.reg]; omega)
  dfin

/-- The data after `i` copied payload bits. -/
def cpIter (e : D) : ℕ → D
  | 0 => e
  | i + 1 => cpNext (cpIter e i) (readTapeBit (frame w) ((cpIter e i).pw + 1))

/-- The bits read at the payload cells `p + 1, p + 3, …`. -/
def bitsAt (p : ℕ) (i : ℕ) : List Bool := (List.range i).map fun j => readTapeBit (frame w) (p + 2 * j + 1)

theorem bitsAt_succ (p i : ℕ) : bitsAt w p (i + 1) = bitsAt w p i ++ [readTapeBit (frame w) (p + 2 * i + 1)] := by
  simp [bitsAt, List.range_succ]

theorem cpIter_eq (e : D) : ∀ i, cpIter w e i =
    { e with
      pw := e.pw + 2 * i, C := e.C - i, P := e.P ++ frameP (bitsAt w e.pw i), pp := e.pp + 2 * i,
      LB := if i = 0 then e.LB else (readTapeBit (frame w) (e.pw + 2 * (i - 1) + 1)).toNat }
  | 0 => by cases e; simp [cpIter, bitsAt, frameP]
  | i + 1 => by
    rw [cpIter, cpIter_eq e i]
    simp only [cpNext, bitsAt_succ, frameP_snoc2]
    cases e
    simp <;> omega

/-- The data after `i` copied bits of the rest. -/
def rsNext (d : D) (b : Bool) : D := { d with pw := d.pw + 2, R := d.R ++ [true, b], pr := d.pr + 2 }

def rsIter (e : D) : ℕ → D
  | 0 => e
  | i + 1 => rsNext (rsIter e i) (readTapeBit (frame w) ((rsIter e i).pw + 1))

theorem rsIter_eq (e : D) : ∀ i, rsIter w e i =
    { e with pw := e.pw + 2 * i, R := e.R ++ frameP (bitsAt w e.pw i), pr := e.pr + 2 * i }
  | 0 => by cases e; simp [rsIter, bitsAt, frameP]
  | i + 1 => by
    rw [rsIter, rsIter_eq e i]
    simp only [rsNext, bitsAt_succ, frameP_snoc2]
    cases e
    simp <;> omega

theorem frameP_length (l : List Bool) : (frameP l).length = 2 * l.length := by
  simp [frameP]; ring

theorem bitsAt_length (p i : ℕ) : (bitsAt w p i).length = i := by simp [bitsAt]

/-- The payload cells from logical position `p` of the tail are the tail's bits. -/
theorem bitsAt_tail (p i : ℕ) (h : p + i ≤ w.tail.length) :
    bitsAt w (2 * (m0 w + p)) i = (w.tail.drop p).take i := by
  apply List.ext_getElem
  · simp only [bitsAt, List.length_map, List.length_range, List.length_take, List.length_drop]; omega
  · intro j h1 h2
    simp only [bitsAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [show 2 * (m0 w + p) + 2 * j + 1 = 2 * (m0 w + (p + j)) + 1 by ring, bit_t]
    rw [List.getD_eq_getElem _ _ (by simp [bitsAt] at h1; omega)]

/-- **The copy loop** from `i` copied bits to its exit (`c = min k (L − p₁)` copies; short of `k`: malformed). -/
theorem copy_loop (hcap : 2 * w.length + 2 ≤ cap) (e : D) (p1 k c : ℕ) (hp1 : p1 ≤ w.tail.length)
    (hk : k ≤ w.length) (hcdef : c = min k (w.tail.length - p1)) (hpw : e.pw = 2 * (m0 w + p1)) (hC : e.C = k)
    (hP : e.P = []) (hpp : e.pp = 0) (hLB : e.LB ≤ 1) (hB : e.BAD ≤ 1) :
    ∀ m i, i + m = c → WExec cap (.whr rC copyBody) (st w (cpIter w e i))
      (st w (if c < k then { cpIter w e c with C := 0, BAD := 1 } else cpIter w e c)) (38 * m + 3 * k + 12) := by
  have hm0 : m0 w + w.tail.length ≤ w.length := by cases w <;> simp [m0] <;> omega
  intro m
  induction m with
  | zero =>
    intro i hi
    have hic : i = c := by omega
    subst hic
    by_cases hck : i < k
    · rw [if_pos hck]
      have hend : p1 + i = w.tail.length := by omega
      have hm : readTapeBit (frame w) (cpIter w e i).pw = false := by
        rw [cpIter_eq, hpw, show 2 * (m0 w + p1) + 2 * i = 2 * (m0 w + (p1 + i)) by ring, mark_t, hend]; simp
      have r := copy_miss cap w (cpIter w e i) (by rw [cpIter_eq]; simp; omega) (by rw [cpIter_eq]; simp; omega) hm
        (by rw [cpIter_eq]; simpa using hB) (by omega)
      have ex := WExec.whrF (cap := cap) (r := rC) (P := copyBody) (σ := st w { cpIter w e i with C := 0, BAD := 1 })
        rfl
      refine WExec.mono (WExec.whrT (by rw [st_val, cpIter_eq]; simp [D.reg]; omega) r ex) ?_
      rw [cpIter_eq]; simp; omega
    · rw [if_neg hck]
      exact WExec.mono (WExec.whrF (by rw [st_val, cpIter_eq]; simp [D.reg]; omega)) (by omega)
  | succ m ih =>
    intro i hi
    have hilt : p1 + i < w.tail.length := by omega
    have hm : readTapeBit (frame w) (cpIter w e i).pw = true := by
      rw [cpIter_eq, hpw, show 2 * (m0 w + p1) + 2 * i = 2 * (m0 w + (p1 + i)) by ring, mark_t]; simpa using hilt
    have r := copy_round cap w (cpIter w e i) (by rw [cpIter_eq]; simp; omega) (by rw [cpIter_eq]; simp; omega) hm
      (by rw [cpIter_eq]; simp [hP, hpp, frameP_length, bitsAt_length])
      (by rw [cpIter_eq]; simp; omega) (by rw [cpIter_eq]; simp [hpp]; omega)
      (by rw [cpIter_eq]; dsimp only; split_ifs <;> simp [hLB, Bool.toNat_le])
    have rest := ih (i + 1) (by omega)
    refine WExec.mono (WExec.whrT (by rw [st_val, cpIter_eq]; simp [D.reg]; omega) r rest) (by omega)

theorem rest_round (d : D) (hm : readTapeBit (frame w) d.pw = true) (hpr : d.pr = d.R.length)
    (hc : d.pw + 2 ≤ cap) (hcp : d.pr + 2 ≤ cap) :
    WExec cap restBody (st w d) (st w (rsNext d (readTapeBit (frame w) (d.pw + 1)))) 28 := by
  have s1 := x_fwdW cap w d (by omega)
  have s2 := x_emitR cap w { d with pw := d.pw + 1 } true (by simpa using hpr) (by simp; omega)
  set d2 := ({ ({ d with pw := d.pw + 1 } : D) with R := d.R ++ [true], pr := d.pr + 1 } : D) with hd2
  set b := readTapeBit (frame w) (d.pw + 1) with hb
  have s3 : WExec cap (.ifs sW (emitC sR rPR true) (emitC sR rPR false)) (st w d2)
      (st w { d2 with R := d2.R ++ [b], pr := d2.pr + 1 }) 8 := by
    have hbit : wbit (st w d2) sW = b := by rw [wbit_W]
    cases hbv : b with
    | true => exact WExec.ifsT (by rw [hbit, hbv]) (x_emitR cap w d2 true (by simp [hd2, hpr]) (by simp [hd2]; omega))
    | false => exact WExec.ifsF (by rw [hbit, hbv]) (x_emitR cap w d2 false (by simp [hd2, hpr]) (by simp [hd2]; omega))
  have s4 := x_fwdW cap w { d2 with R := d2.R ++ [b], pr := d2.pr + 1 } (by simp [hd2]; omega)
  refine WExec.cast cap (s1.seq (s2.seq (s3.seq s4))) ?_ (by omega)
  rw [hd2]; congr 1; cases d; simp [rsNext]

/-- **The rest loop**: every remaining bit, framed onto `R`. -/
theorem rest_loop (hcap : 2 * w.length + 2 ≤ cap) (e : D) (p2 : ℕ) (hp2 : p2 ≤ w.tail.length)
    (hpw : e.pw = 2 * (m0 w + p2)) (hR : e.R = []) (hpr : e.pr = 0) :
    ∀ m i, i + m = w.tail.length - p2 → WExec cap (.whs sW restBody) (st w (rsIter w e i))
      (st w (rsIter w e (w.tail.length - p2))) (30 * m + 1) := by
  have hm0 : m0 w + w.tail.length ≤ w.length := by cases w <;> simp [m0] <;> omega
  intro m
  induction m with
  | zero =>
    intro i hi
    have hi' : i = w.tail.length - p2 := by omega
    subst hi'
    refine WExec.whsF ?_
    rw [wbit_W, rsIter_eq, hpw, show 2 * (m0 w + p2) + 2 * (w.tail.length - p2) = 2 * (m0 w + w.tail.length) by omega,
      show m0 w + w.tail.length = m0 w + (w.tail.length + 0) by rfl, mark_t]
    simp
  | succ m ih =>
    intro i hi
    have hilt : p2 + i < w.tail.length := by omega
    have hm : readTapeBit (frame w) (rsIter w e i).pw = true := by
      rw [rsIter_eq, hpw, show 2 * (m0 w + p2) + 2 * i = 2 * (m0 w + (p2 + i)) by ring, mark_t]; simpa using hilt
    have r := rest_round cap w (rsIter w e i) hm (by rw [rsIter_eq]; simp [hR, hpr, frameP_length, bitsAt_length])
      (by rw [rsIter_eq]; simp; omega) (by rw [rsIter_eq]; simp [hpr]; omega)
    have rest := ih (i + 1) (by omega)
    exact WExec.mono (WExec.whsT (by rw [wbit_W]; exact hm) r rest) (by omega)

/-! ## The verdict, the tag, the rewinds -/

/-- The verdict of the registers: `¬BAD ∧ K ≥ 1 ∧ (K = 1 ∨ LB)`. -/
def vOf (B K LB : ℕ) : Bool := decide (B = 0) && decide (K ≠ 0) && (decide (K = 1) || decide (LB ≠ 0))

/-- `K` after the verdict. -/
def kOf (B K : ℕ) : ℕ := if B = 0 ∧ K ≠ 0 then K - 1 else K

theorem verdict_spec (d : D) (hK : d.K ≤ cap) :
    WExec cap verdictP (st w d) (st w { d with cell := vOf d.BAD d.K d.LB, K := kOf d.BAD d.K }) 8 := by
  by_cases hB : d.BAD = 0
  · by_cases hK0 : d.K = 0
    · have h := WExec.ifrF (cap := cap) (r := rBAD) (P := .setc false) (by rw [st_val]; simpa [D.reg] using hB)
        (WExec.ifrF (cap := cap) (r := rK) (P := .seq (.dec rK) (.ifr rK (.ifr rLB (.setc true) (.setc false))
          (.setc true))) (by rw [st_val]; simpa [D.reg] using hK0) (x_setc cap w d false))
      refine WExec.cast cap h ?_ (by omega)
      congr 1; cases d; simp_all [vOf, kOf]
    · have s1 := x_dec cap w d rK (by decide) (by simp [D.reg]; omega)
      have e1 : d.setReg rK (d.reg rK - 1) = { d with K := d.K - 1 } := by cases d; simp [D.setReg, D.reg]
      rw [e1] at s1
      by_cases hK1 : d.K - 1 = 0
      · have s2 := WExec.ifrF (cap := cap) (r := rK) (P := .ifr rLB (.setc true) (.setc false))
          (by rw [st_val]; simpa [D.reg] using hK1) (x_setc cap w { d with K := d.K - 1 } true)
        have h := WExec.ifrF (cap := cap) (r := rBAD) (P := .setc false) (by rw [st_val]; simpa [D.reg] using hB)
          (WExec.ifrT (cap := cap) (r := rK) (Q := .setc false) (by rw [st_val]; simpa [D.reg] using hK0)
            (s1.seq s2))
        refine WExec.cast cap h ?_ (by omega)
        congr 1; cases d; simp_all [vOf, kOf]; omega
      · have s3 : WExec cap (.ifr rLB (.setc true) (.setc false)) (st w { d with K := d.K - 1 })
            (st w { d with K := d.K - 1, cell := decide (d.LB ≠ 0) }) 2 := by
          by_cases hL : d.LB = 0
          · refine WExec.cast cap (WExec.ifrF (by rw [st_val]; simpa [D.reg] using hL)
              (x_setc cap w { d with K := d.K - 1 } false)) ?_ le_rfl
            congr 1; cases d; simp_all
          · refine WExec.cast cap (WExec.ifrT (by rw [st_val]; simpa [D.reg] using hL)
              (x_setc cap w { d with K := d.K - 1 } true)) ?_ le_rfl
            congr 1; cases d; simp_all
        have s2 := WExec.ifrT (cap := cap) (r := rK) (Q := .setc true) (by rw [st_val]; simpa [D.reg] using hK1) s3
        have h := WExec.ifrF (cap := cap) (r := rBAD) (P := .setc false) (by rw [st_val]; simpa [D.reg] using hB)
          (WExec.ifrT (cap := cap) (r := rK) (Q := .setc false) (by rw [st_val]; simpa [D.reg] using hK0)
            (s1.seq s2))
        refine WExec.cast cap h ?_ (by omega)
        congr 1; cases d; simp_all [vOf, kOf]; omega
  · have h := WExec.ifrT (cap := cap) (r := rBAD) (Q := .ifr rK (.seq (.dec rK) (.ifr rK (.ifr rLB (.setc true)
      (.setc false)) (.setc true))) (.setc false)) (by rw [st_val]; simpa [D.reg] using hB) (x_setc cap w d false)
    refine WExec.cast cap h ?_ (by omega)
    congr 1; cases d; simp_all [vOf, kOf]

theorem tagOut_spec (d : D) (hT : d.Tg = []) :
    WExec cap tagOutP (st w d) (st w { d with Tg := [decide (d.TG ≠ 0)] }) 2 := by
  by_cases h : d.TG = 0
  · refine WExec.cast cap (WExec.ifrF (by rw [st_val]; simpa [D.reg] using h) (x_wrT cap w d false hT)) ?_ le_rfl
    simp [h]
  · refine WExec.cast cap (WExec.ifrT (by rw [st_val]; simpa [D.reg] using h) (x_wrT cap w d true hT)) ?_ le_rfl
    simp [h]

def cleanCost (d : D) : ℕ :=
  5 * d.pw + 1 + 1 + (5 * d.pp + 1 + 1 + (5 * d.pr + 1 + 1 + (3 * d.K + 1 + 1 + (3 * d.LB + 1 + 1 +
    (3 * d.BAD + 1 + 1 + (3 * d.TG + 1))))))

theorem clean_spec (d : D) (h1 : d.pw ≤ cap) (h2 : d.pp ≤ cap) (h3 : d.pr ≤ cap) (h4 : d.K ≤ cap) (h5 : d.LB ≤ cap)
    (h6 : d.BAD ≤ cap) (h7 : d.TG ≤ cap) :
    WExec cap cleanP (st w d) (st w { d with pw := 0, pp := 0, pr := 0, K := 0, LB := 0, BAD := 0, TG := 0 })
      (cleanCost d) := by
  have s1 := x_rewW cap w d h1
  have s2 := x_rewP cap w { d with pw := 0 } (by simpa using h2)
  have s3 := x_rewR cap w { d with pw := 0, pp := 0 } (by simpa using h3)
  have s4 := x_clear cap w { d with pw := 0, pp := 0, pr := 0 } rK (by decide) (by simpa [D.reg] using h4)
  have e4 : ({ d with pw := 0, pp := 0, pr := 0 } : D).setReg rK 0 = { d with pw := 0, pp := 0, pr := 0, K := 0 } := by
    cases d; simp [D.setReg]
  rw [e4] at s4
  have s5 := x_clear cap w { d with pw := 0, pp := 0, pr := 0, K := 0 } rLB (by decide) (by simpa [D.reg] using h5)
  have e5 : ({ d with pw := 0, pp := 0, pr := 0, K := 0 } : D).setReg rLB 0 =
      { d with pw := 0, pp := 0, pr := 0, K := 0, LB := 0 } := by cases d; simp [D.setReg]
  rw [e5] at s5
  have s6 := x_clear cap w { d with pw := 0, pp := 0, pr := 0, K := 0, LB := 0 } rBAD (by decide)
    (by simpa [D.reg] using h6)
  have e6 : ({ d with pw := 0, pp := 0, pr := 0, K := 0, LB := 0 } : D).setReg rBAD 0 =
      { d with pw := 0, pp := 0, pr := 0, K := 0, LB := 0, BAD := 0 } := by cases d; simp [D.setReg]
  rw [e6] at s6
  have s7 := x_clear cap w { d with pw := 0, pp := 0, pr := 0, K := 0, LB := 0, BAD := 0 } rTG (by decide)
    (by simpa [D.reg] using h7)
  have e7 : ({ d with pw := 0, pp := 0, pr := 0, K := 0, LB := 0, BAD := 0 } : D).setReg rTG 0 =
      { d with pw := 0, pp := 0, pr := 0, K := 0, LB := 0, BAD := 0, TG := 0 } := by cases d; simp [D.setReg]
  rw [e7] at s7
  refine WExec.mono (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))) ?_
  simp [cleanCost, D.reg]

/-! ## The walker -/

/-- The verdict on the witness: the tag is present and the reader accepts the oracle field. -/
def okOf : List Bool → Bool
  | [] => false
  | _ :: t => scanOK t

/-- The logical position after the separator (or the end), and the number of payload bits present. -/
def pos1 (t : List Bool) : ℕ := if ones t < t.length then ones t + 1 else t.length
def ncp (t : List Bool) : ℕ := min (ones t) (t.length - pos1 t)

theorem pos1_le (t : List Bool) : pos1 t ≤ t.length := by unfold pos1; split_ifs <;> omega

theorem payload_eq (t : List Bool) : payload t = (t.drop (pos1 t)).take (ncp t) := by
  unfold payload ncp pos1
  split_ifs with h
  · apply List.ext_getElem
    · simp
    · intro j h1 h2; simp
  · have : t.length ≤ ones t + 1 := by omega
    simp [List.drop_eq_nil_of_le this]

theorem restOf_eq (t : List Bool) : restOf t = t.drop (pos1 t + ncp t) := by
  unfold restOf ncp pos1
  split_ifs with h
  · by_cases h2 : ones t ≤ t.length - (ones t + 1)
    · rw [min_eq_left h2]; congr 1; omega
    · rw [min_eq_right (by omega), List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
  · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]

/-- The verdict of the registers after the scan is T's. -/
theorem verdict_eq (w : List Bool) :
    vOf (if ncp w.tail < ones w.tail then 1 else if ones w.tail < w.tail.length then (if w = [] then 1 else 0) else 1)
      (ones w.tail) (if ncp w.tail = 0 then 0 else (w.tail.getD (pos1 w.tail + ncp w.tail - 1) false).toNat) =
      okOf w := by
  cases w with
  | nil => simp [vOf, okOf, ncp, pos1, ones_nil]
  | cons b t =>
    simp only [List.tail_cons, okOf, reduceCtorEq, if_false]
    unfold scanOK vOf ncp pos1
    by_cases h1 : ones t < t.length
    · rw [if_pos h1]
      by_cases h2 : ones t ≤ t.length - (ones t + 1)
      · rw [min_eq_left h2, if_neg (by omega), if_pos h1]
        by_cases h0 : ones t = 0
        · simp [h0]
        · rw [if_neg h0, show ones t + 1 + ones t - 1 = 2 * ones t by omega]
          cases hb : t.getD (2 * ones t) false <;> simp [h0] <;> omega
      · rw [min_eq_right (by omega), if_pos (by omega)]
        simp; omega
    · rw [if_neg h1]
      simp only [show t.length - t.length = 0 by omega, Nat.min_zero]
      by_cases h0 : ones t = 0
      · simp [h0]
      · rw [if_pos (by omega)]; simp; omega

def walkCost (n : ℕ) : ℕ := 200 * n + 200

/-- The walker's entry data (any cell) and its exit data. -/
def d0 (c0 : Bool) : D := ⟨0, 0, 0, [], [], [], 0, 0, 0, 0, 0, 0, 0, c0⟩
def dF (w : List Bool) : D :=
  ⟨0, 0, 0, frame (payload w.tail), frame (restOf w.tail), [w.headD false], 0, 0, 0, 0, 0, 0, 0, okOf w⟩

/-- **The oracle-field walker**: from the framed witness (blank outputs, zero registers), within `200|w| + 200`
steps, the payload and the rest framed on `P` and `R`, the tag on `Tg`, the verdict in the cell, every head and
register at `0`. -/
theorem walkP_spec (c0 : Bool) (hcap : 2 * w.length + 2 ≤ cap) :
    WExec cap walkP (st w (d0 c0)) (st w (dF w)) (walkCost w.length) := by
  have hlt : w.tail.length = w.length - 1 := List.length_tail
  have hkL : ones w.tail ≤ w.tail.length := ones_le w.tail
  have hm0 : m0 w + w.tail.length ≤ w.length := by cases w <;> simp [m0] <;> omega
  have hp1 := pos1_le w.tail
  have hc1 : ncp w.tail ≤ ones w.tail := by unfold ncp; omega
  have hc2 : pos1 w.tail + ncp w.tail ≤ w.tail.length := by unfold ncp; omega
  -- the tag
  have s1 := tag_spec cap w (d0 c0) rfl rfl rfl hcap
  set B0 := (if w = [] then 1 else 0) with hB0
  have hB0le : B0 ≤ 1 := by rw [hB0]; split_ifs <;> omega
  set e1 : D := { d0 c0 with pw := 2 * m0 w, TG := (w.headD false).toNat, BAD := B0 } with he1
  -- the ones
  have s2 := x_inc cap w e1 rF (by decide) (by simp [D.reg, he1, d0]; omega)
  have e2' : e1.setReg rF (e1.reg rF + 1) = { e1 with F := 1 } := by simp [he1, D.setReg, D.reg, d0]
  rw [e2'] at s2
  have s3 := ones_loop cap w hcap (ones w.tail) { e1 with F := 1 } 0 (by omega) (by simp [he1]) (by simp [he1, d0])
    rfl (by simp [he1, hB0le])
  set BAD2 := (if ones w.tail < w.tail.length then B0 else 1) with hBAD2
  set e2 : D := { e1 with F := 0, pw := 2 * (m0 w + pos1 w.tail), K := ones w.tail, BAD := BAD2 } with he2
  have ee2 : (if ones w.tail < w.tail.length then
      ({ ({ e1 with F := 1 } : D) with pw := 2 * (m0 w + ones w.tail) + 2, K := ones w.tail, F := 0 } : D)
      else { ({ e1 with F := 1 } : D) with pw := 2 * (m0 w + ones w.tail), K := ones w.tail, F := 0, BAD := 1 }) =
      e2 := by
    rw [he2, hBAD2]; unfold pos1
    split_ifs <;> simp [he1] <;> omega
  rw [ee2] at s3
  -- the copy
  have s4 := dup_spec cap w e2 (by simp [he2, he1, d0]) (by simp [he2, he1, d0]) (by simp [he2]; omega)
  set e3 : D := { e2 with C := e2.K } with he3
  have s5 := copy_loop cap w hcap e3 (pos1 w.tail) (ones w.tail) (ncp w.tail) hp1 (by omega) rfl
    (by simp [he3, he2]) (by simp [he3, he2]) (by simp [he3, he2, he1, d0]) (by simp [he3, he2, he1, d0])
    (by simp [he3, he2, he1, d0]) (by simp [he3, he2, hBAD2]; split_ifs <;> omega) (ncp w.tail) 0 (by omega)
  set c := ncp w.tail with hc
  set LBv := (if c = 0 then 0 else (readTapeBit (frame w) (e3.pw + 2 * (c - 1) + 1)).toNat) with hLBv
  set e4 : D :=
    { e3 with
      pw := e3.pw + 2 * c, C := 0, P := frameP (bitsAt w e3.pw c), pp := 2 * c, LB := LBv,
      BAD := if c < ones w.tail then 1 else BAD2 } with he4
  have ee4 : (if c < ones w.tail then ({ cpIter w e3 c with C := 0, BAD := 1 } : D) else cpIter w e3 c) = e4 := by
    rw [he4, cpIter_eq]
    split_ifs with h <;> simp [he3, he2, he1, d0, hLBv] <;> omega
  rw [ee4] at s5
  have s6 := x_wrP cap w e4 false (by simp [he4, frameP_length, bitsAt_length])
  set e5 : D := { e4 with P := e4.P ++ [false] } with he5
  -- the rest
  have s7 := rest_loop cap w hcap e5 (pos1 w.tail + c) hc2 (by simp [he5, he4, he3, he2]; ring)
    (by simp [he5, he4, he3, he2, he1, d0]) (by simp [he5, he4, he3, he2, he1, d0])
    (w.tail.length - (pos1 w.tail + c)) 0 (by omega)
  rw [rsIter_eq w e5 (w.tail.length - (pos1 w.tail + c))] at s7
  set e6 : D :=
    { e5 with
      pw := e5.pw + 2 * (w.tail.length - (pos1 w.tail + c)),
      R := e5.R ++ frameP (bitsAt w e5.pw (w.tail.length - (pos1 w.tail + c))),
      pr := e5.pr + 2 * (w.tail.length - (pos1 w.tail + c)) } with he6
  have s8 := x_wrR cap w e6 false (by simp [he6, he5, he4, he3, he2, he1, d0, frameP_length, bitsAt_length])
  set e7 : D := { e6 with R := e6.R ++ [false] } with he7
  -- the verdict, the tag, the rewinds
  have s9 := verdict_spec cap w e7 (by simp [he7, he6, he5, he4, he3, he2]; omega)
  set e8 : D := { e7 with cell := vOf e7.BAD e7.K e7.LB, K := kOf e7.BAD e7.K } with he8
  have s10 := tagOut_spec cap w e8 (by simp [he8, he7, he6, he5, he4, he3, he2, he1, d0])
  set e9 : D := { e8 with Tg := [decide (e8.TG ≠ 0)] } with he9
  have hTG : e9.TG ≤ 1 := by simp [he9, he8, he7, he6, he5, he4, he3, he2, he1, Bool.toNat_le]
  have hLB : e9.LB ≤ 1 := by
    simp only [he9, he8, he7, he6, he5, he4, hLBv]; split_ifs <;> simp [Bool.toNat_le]
  have hBAD : e9.BAD ≤ 1 := by
    simp only [he9, he8, he7, he6, he5, he4, hBAD2]; split_ifs <;> omega
  have hK9 : e9.K ≤ ones w.tail := by simp only [he9, he8, he7, he6, he5, he4, he3, he2, kOf]; split_ifs <;> omega
  have hpw9 : e9.pw = 2 * (m0 w + w.tail.length) := by
    simp only [he9, he8, he7, he6, he5, he4, he3, he2]; omega
  have hpp9 : e9.pp = 2 * c := by simp [he9, he8, he7, he6, he5, he4]
  have hpr9 : e9.pr = 2 * (w.tail.length - (pos1 w.tail + c)) := by
    simp [he9, he8, he7, he6, he5, he4, he3, he2, he1, d0]
  have s11 := clean_spec cap w e9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hclean : cleanCost e9 ≤ 30 * w.length + 30 := by
    unfold cleanCost; rw [hpw9, hpp9, hpr9]; omega
  -- the exit data
  have hfin : ({ e9 with pw := 0, pp := 0, pr := 0, K := 0, LB := 0, BAD := 0, TG := 0 } : D) = dF w := by
    have hP : e9.P = frame (payload w.tail) := by
      simp only [he9, he8, he7, he6, he5, he4, he3, he2]
      rw [payload_eq, ← bitsAt_tail w (pos1 w.tail) c hc2, frame_eq_frameP]
    have hR : e9.R = frame (restOf w.tail) := by
      simp only [he9, he8, he7, he6, he5, he4, he3, he2, he1, d0, List.nil_append]
      rw [restOf_eq, frame_eq_frameP]
      congr 2
      rw [show 2 * (m0 w + pos1 w.tail) + 2 * c = 2 * (m0 w + (pos1 w.tail + c)) by ring]
      rw [bitsAt_tail w _ _ (by omega), List.take_of_length_le (by simp; omega)]
    have hT : e9.Tg = [w.headD false] := by
      simp only [he9, he8, he7, he6, he5, he4, he3, he2, he1]
      have hb : ∀ b : Bool, [decide (b.toNat ≠ 0)] = [b] := by decide
      exact hb _
    have hcell : e9.cell = okOf w := by
      simp only [he9, he8, he7, he6, he5, he4, he3, he2]
      rw [← verdict_eq w]
      congr 1
      simp only [hLBv, he3, he2]
      split_ifs with h
      · rfl
      · rw [show 2 * (m0 w + pos1 w.tail) + 2 * (c - 1) + 1 = 2 * (m0 w + (pos1 w.tail + c - 1)) + 1 by omega, bit_t]
    have hC : e9.C = 0 := by simp [he9, he8, he7, he6, he5, he4]
    have hT0 : e9.T = 0 := by simp [he9, he8, he7, he6, he5, he4, he3, he2, he1, d0]
    have hF : e9.F = 0 := by simp [he9, he8, he7, he6, he5, he4, he3, he2]
    have key : ∀ x : D, x.P = frame (payload w.tail) → x.R = frame (restOf w.tail) → x.Tg = [w.headD false] →
        x.cell = okOf w → x.C = 0 → x.T = 0 → x.F = 0 →
        ({ x with pw := 0, pp := 0, pr := 0, K := 0, LB := 0, BAD := 0, TG := 0 } : D) = dF w := by
      intro x h1 h2 h3 h4 h5 h6 h7
      cases x
      simp_all [dF]
    exact key e9 hP hR hT hcell hC hT0 hF
  rw [hfin] at s11
  refine WExec.mono (s1.seq ((s2.seq s3).seq ((s4.seq (s5.seq s6)).seq ((s7.seq s8).seq (s9.seq (s10.seq s11))))))
    ?_
  simp only [he2, walkCost]
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontOracleField
