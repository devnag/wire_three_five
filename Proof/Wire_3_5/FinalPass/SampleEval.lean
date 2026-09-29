import Proof.Wire_3_5.FinalPass.SampleRef
import Proof.Wire_3_5.FinalPass.WordMap
import Proof.Wire_3_5.FinalPass.ListEvalCyc

/-! # Final pass, stage 0: the decoder of a sampled half (P3:1188-1193, 1220-1222, 3044-3053)

`dec right : WM 1 12` reads the framed binary word of a half's index `a` (stream `I`, at any offset) and writes the
half's error vector, framed, over the stale frame on stream `O` (from `0`): `decWord b (r/2) tail right (digits)`
(`errorVector_decode`). Per block it reads `s` bits into the digit `D` (weights doubling in `W`), then writes the
one-hot block `[D = i+1]_{i<b}` by counting `D` down; the other positions get zeros. The constants `s, b, r/2, tail`
sit in registers and are restored by every loop that counts them down. At every phase boundary the state is `DSt.w x`
(the counters `X`, `O` equal the heads). **`dec_spec`**: `O` holds `frameP (decWord …)` before the old `false`, is
rewound, and `I` is advanced past the index word. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sample
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-! ## Layout -/

scoped notation "sI" => (0 : Fin 2)
scoped notation "sO" => (1 : Fin 2)

scoped notation "gS" => (0 : Fin 12)
scoped notation "gB" => (1 : Fin 12)
scoped notation "gH" => (2 : Fin 12)
scoped notation "gT" => (3 : Fin 12)
scoped notation "gJ" => (4 : Fin 12)
scoped notation "gI" => (5 : Fin 12)
scoped notation "gD" => (6 : Fin 12)
scoped notation "gW" => (7 : Fin 12)
scoped notation "gY" => (8 : Fin 12)
scoped notation "gX" => (9 : Fin 12)
scoped notation "gO" => (10 : Fin 12)
scoped notation "gK" => (11 : Fin 12)

abbrev DProg := WM 1 12

/-- The decoder's state at a phase boundary. -/
structure DSt where
  iw : List Bool
  ow : List Bool
  ih : ℕ
  oh : ℕ
  s : ℕ
  b : ℕ
  hh : ℕ
  tl : ℕ
  j : ℕ
  i : ℕ
  d : ℕ
  w : ℕ
  y : ℕ
  k : ℕ
  cell : Bool

/-- The word state of a phase record. -/
def DSt.w' (x : DSt) : WState 1 12 :=
  ⟨![x.ih, x.oh], ![x.iw, x.ow], ![x.s, x.b, x.hh, x.tl, x.j, x.i, x.d, x.w, x.y, x.ih, x.oh, x.k], x.cell⟩

/-- Close an equality of word states against phase records. -/
syntax "dst_eq" : tactic
macro_rules
  | `(tactic| dst_eq) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [DSt.w']; done) | (simp [DSt.w'] <;> omega))
        | rfl
        | (simp [DSt.w']; done)))

section Upd
variable (x : DSt)

@[simp] theorem d_valS : x.w'.val gS = x.s := rfl
@[simp] theorem d_valB : x.w'.val gB = x.b := rfl
@[simp] theorem d_valH : x.w'.val gH = x.hh := rfl
@[simp] theorem d_valT : x.w'.val gT = x.tl := rfl
@[simp] theorem d_valJ : x.w'.val gJ = x.j := rfl
@[simp] theorem d_valI : x.w'.val gI = x.i := rfl
@[simp] theorem d_valD : x.w'.val gD = x.d := rfl
@[simp] theorem d_valW : x.w'.val gW = x.w := rfl
@[simp] theorem d_valY : x.w'.val gY = x.y := rfl
@[simp] theorem d_valX : x.w'.val gX = x.ih := rfl
@[simp] theorem d_valO : x.w'.val gO = x.oh := rfl
@[simp] theorem d_valK : x.w'.val gK = x.k := rfl

theorem d_S (n : ℕ) : x.w'.setv gS n = { x with s := n }.w' := by dst_eq
theorem d_B (n : ℕ) : x.w'.setv gB n = { x with b := n }.w' := by dst_eq
theorem d_H (n : ℕ) : x.w'.setv gH n = { x with hh := n }.w' := by dst_eq
theorem d_T (n : ℕ) : x.w'.setv gT n = { x with tl := n }.w' := by dst_eq
theorem d_J (n : ℕ) : x.w'.setv gJ n = { x with j := n }.w' := by dst_eq
theorem d_I (n : ℕ) : x.w'.setv gI n = { x with i := n }.w' := by dst_eq
theorem d_D (n : ℕ) : x.w'.setv gD n = { x with d := n }.w' := by dst_eq
theorem d_W (n : ℕ) : x.w'.setv gW n = { x with w := n }.w' := by dst_eq
theorem d_Y (n : ℕ) : x.w'.setv gY n = { x with y := n }.w' := by dst_eq
theorem d_K (n : ℕ) : x.w'.setv gK n = { x with k := n }.w' := by dst_eq
theorem d_fwdX : (x.w'.seth sI (x.w'.sh sI + 1)).setv gX (x.w'.val gX + 1) = { x with ih := x.ih + 1 }.w' := by
  dst_eq
theorem d_fwdO : (x.w'.seth sO (x.w'.sh sO + 1)).setv gO (x.w'.val gO + 1) = { x with oh := x.oh + 1 }.w' := by
  dst_eq
theorem d_wrO (v : Bool) : x.w'.sets sO (writeTapeBit (x.w'.st sO) (x.w'.sh sO) v) =
    { x with ow := writeTapeBit x.ow x.oh v }.w' := by
  dst_eq
theorem d_rewO (n : ℕ) (hn : x.oh = n) : (x.w'.setv gO 0).seth sO (x.w'.sh sO - n) = { x with oh := 0 }.w' := by
  dst_eq

end Upd

variable (cap : ℕ)

/-! ## Registers -/

theorem d_move (a b : Fin 12) (hab : a ≠ b) (x : DSt) (ha : x.w'.val a ≤ cap) (hb : x.w'.val b + x.w'.val a ≤ cap) :
    WExec cap (WM.move a b) x.w' ((x.w'.setv a 0).setv b (x.w'.val b + x.w'.val a)) (7 * x.w'.val a + 1) :=
  wmove_spec cap a b hab (x.w'.val a) x.w' rfl ha hb

/-! ## The output -/

/-- Append one framed bit `v` to the output. -/
def emitC (v : Bool) : DProg := .seq (.wr sO true) (.seq (WM.fwdC sO gO) (.seq (.wr sO v) (WM.fwdC sO gO)))

theorem frameP_app' (l l' : List Bool) : frameP (l ++ l') = frameP l ++ frameP l' := by
  simp [frameP, List.flatMap_append]

theorem emitC_spec' (v : Bool) (x : DSt) (dd r : List Bool) (o0 o1 : Bool) (hout : x.ow = frameP dd ++ o0 :: o1 :: r)
    (hoh : x.oh = 2 * dd.length) (hc : x.oh + 2 ≤ cap) :
    WExec cap (emitC v) x.w' { x with ow := frameP (dd ++ [v]) ++ r, oh := x.oh + 2 }.w' 15 := by
  have hlen : (frameP dd).length = x.oh := by simp [hoh]
  have s1 := WExec.wr (cap := cap) sO true x.w'
  rw [d_wrO] at s1
  have e1 : writeTapeBit x.ow x.oh true = frameP dd ++ true :: o1 :: r := by
    rw [hout, ← hlen]; exact writeTapeBit_mid' _ _ _ _
  rw [e1] at s1
  have s2 := wfwdC_spec cap sO gO { x with ow := frameP dd ++ true :: o1 :: r }.w' (by simp; omega)
  rw [d_fwdO] at s2
  have s3 := WExec.wr (cap := cap) sO v { { x with ow := frameP dd ++ true :: o1 :: r } with oh := x.oh + 1 }.w'
  rw [d_wrO] at s3
  have e3 : writeTapeBit (frameP dd ++ true :: o1 :: r) (x.oh + 1) v = frameP (dd ++ [v]) ++ r := by
    have := writeTapeBit_mid' (frameP dd ++ [true]) r o1 v
    rw [show frameP dd ++ true :: o1 :: r = frameP dd ++ [true] ++ o1 :: r by simp,
      show x.oh + 1 = (frameP dd ++ [true]).length by simp [hlen]]
    rw [this, frameP_app']
    simp
  simp only [] at s3
  rw [e3] at s3
  obtain ⟨z3, hz3⟩ : ∃ z, z = { { { x with ow := frameP dd ++ true :: o1 :: r } with oh := x.oh + 1 } with ow := frameP (dd ++ [v]) ++ r } :=
    ⟨_, rfl⟩
  rw [← hz3] at s3
  have s4 := wfwdC_spec cap sO gO z3.w' (by rw [hz3]; simp; omega)
  rw [d_fwdO] at s4
  exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by rw [hz3]) (by omega)

/-- Fill `B` false positions, restoring `B` through `Y`. -/
def fillBL : DProg := .whr gB (.seq (.dec gB) (.seq (.inc gY) (emitC false)))
def fillB : DProg := .seq fillBL (WM.move gY gB)

theorem fillBL_spec : ∀ (c : ℕ) (x : DSt) (dd r : List Bool), x.b = c → x.ow = frameP dd ++ r →
    x.oh = 2 * dd.length → 2 * c ≤ r.length → x.y + c ≤ cap → x.oh + 2 * c ≤ cap → c ≤ cap →
    WExec cap fillBL x.w'
      { x with b := 0, y := x.y + c, ow := frameP (dd ++ List.replicate c false) ++ r.drop (2 * c),
               oh := x.oh + 2 * c }.w' (23 * c + 1)
  | 0, x, dd, r, hb, hout, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hb])) ?_ le_rfl
    congr 1; cases x; simp_all
  | c + 1, x, dd, r, hb, hout, hoh, hr, hy, ho, hc => by
    obtain ⟨o0, o1, r', rfl⟩ : ∃ o0 o1 r', r = o0 :: o1 :: r' := by
      rcases r with _ | ⟨o0, _ | ⟨o1, r'⟩⟩ <;> simp at hr <;> try omega
      exact ⟨o0, o1, r', rfl⟩
    have d1 := WExec.dec (cap := cap) gB x.w' (by simp; omega)
    rw [d_valB, d_B, hb, Nat.add_sub_cancel] at d1
    have d2 := WExec.inc (cap := cap) gY { x with b := c }.w' (by simp; omega)
    rw [d_valY, d_Y] at d2
    have d3 := emitC_spec' cap false { { x with b := c } with y := x.y + 1 } dd r' o0 o1 hout hoh (by simp; omega)
    obtain ⟨z, hz⟩ : ∃ z, z = { { { x with b := c } with y := x.y + 1 } with ow := frameP (dd ++ [false]) ++ r', oh := x.oh + 2 } :=
      ⟨_, rfl⟩
    rw [← hz] at d3
    have hr' : 2 * c ≤ r'.length := by simp only [List.length_cons] at hr; omega
    have ih := fillBL_spec c z (dd ++ [false]) r' (by rw [hz]) (by rw [hz]) (by rw [hz]; simp [hoh]; omega)
      hr' (by rw [hz]; simp only []; omega) (by rw [hz]; simp only []; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by simp [hb]) (WExec.seq d1 (WExec.seq d2 d3)) ih) ?_ (by omega)
    rw [hz]
    congr 1
    simp only [List.append_assoc, List.singleton_append]
    congr 1 <;> omega

theorem fillB_spec (c : ℕ) (x : DSt) (dd r : List Bool) (hb : x.b = c) (hout : x.ow = frameP dd ++ r)
    (hoh : x.oh = 2 * dd.length) (hr : 2 * c ≤ r.length) (hy : x.y = 0) (hc : c ≤ cap) (ho : x.oh + 2 * c ≤ cap) :
    WExec cap fillB x.w' { x with ow := frameP (dd ++ List.replicate c false) ++ r.drop (2 * c),
                                  oh := x.oh + 2 * c }.w' (30 * c + 3) := by
  have s1 := fillBL_spec cap c x dd r hb hout hoh hr (by omega) ho hc
  obtain ⟨z, hz⟩ : ∃ z, z = { x with b := 0, y := x.y + c, ow := frameP (dd ++ List.replicate c false) ++ r.drop (2 * c), oh := x.oh + 2 * c } :=
    ⟨_, rfl⟩
  rw [← hz] at s1
  have s2 := d_move cap gY gB (by decide) z (by rw [hz]; simp; omega) (by rw [hz]; simp; omega)
  rw [d_valB, d_valY, d_Y, d_B] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [hz]; simp [hy]; omega)
  rw [hz]; congr 1; cases x; simp_all

/-- Fill `T` false positions, restoring `T` through `Y`. -/
def fillTL : DProg := .whr gT (.seq (.dec gT) (.seq (.inc gY) (emitC false)))
def fillT : DProg := .seq fillTL (WM.move gY gT)

theorem fillTL_spec : ∀ (c : ℕ) (x : DSt) (dd r : List Bool), x.tl = c → x.ow = frameP dd ++ r →
    x.oh = 2 * dd.length → 2 * c ≤ r.length → x.y + c ≤ cap → x.oh + 2 * c ≤ cap → c ≤ cap →
    WExec cap fillTL x.w'
      { x with tl := 0, y := x.y + c, ow := frameP (dd ++ List.replicate c false) ++ r.drop (2 * c),
               oh := x.oh + 2 * c }.w' (23 * c + 1)
  | 0, x, dd, r, hb, hout, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hb])) ?_ le_rfl
    congr 1; cases x; simp_all
  | c + 1, x, dd, r, hb, hout, hoh, hr, hy, ho, hc => by
    obtain ⟨o0, o1, r', rfl⟩ : ∃ o0 o1 r', r = o0 :: o1 :: r' := by
      rcases r with _ | ⟨o0, _ | ⟨o1, r'⟩⟩ <;> simp at hr <;> try omega
      exact ⟨o0, o1, r', rfl⟩
    have d1 := WExec.dec (cap := cap) gT x.w' (by simp; omega)
    rw [d_valT, d_T, hb, Nat.add_sub_cancel] at d1
    have d2 := WExec.inc (cap := cap) gY { x with tl := c }.w' (by simp; omega)
    rw [d_valY, d_Y] at d2
    have d3 := emitC_spec' cap false { { x with tl := c } with y := x.y + 1 } dd r' o0 o1 hout hoh (by simp; omega)
    obtain ⟨z, hz⟩ : ∃ z, z = { { { x with tl := c } with y := x.y + 1 } with ow := frameP (dd ++ [false]) ++ r', oh := x.oh + 2 } :=
      ⟨_, rfl⟩
    rw [← hz] at d3
    have hr' : 2 * c ≤ r'.length := by simp only [List.length_cons] at hr; omega
    have ih := fillTL_spec c z (dd ++ [false]) r' (by rw [hz]) (by rw [hz]) (by rw [hz]; simp [hoh]; omega)
      hr' (by rw [hz]; simp only []; omega) (by rw [hz]; simp only []; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by simp [hb]) (WExec.seq d1 (WExec.seq d2 d3)) ih) ?_ (by omega)
    rw [hz]
    congr 1
    simp only [List.append_assoc, List.singleton_append]
    congr 1 <;> omega

theorem fillT_spec (c : ℕ) (x : DSt) (dd r : List Bool) (hb : x.tl = c) (hout : x.ow = frameP dd ++ r)
    (hoh : x.oh = 2 * dd.length) (hr : 2 * c ≤ r.length) (hy : x.y = 0) (hc : c ≤ cap) (ho : x.oh + 2 * c ≤ cap) :
    WExec cap fillT x.w' { x with ow := frameP (dd ++ List.replicate c false) ++ r.drop (2 * c),
                                  oh := x.oh + 2 * c }.w' (30 * c + 3) := by
  have s1 := fillTL_spec cap c x dd r hb hout hoh hr (by omega) ho hc
  obtain ⟨z, hz⟩ : ∃ z, z = { x with tl := 0, y := x.y + c, ow := frameP (dd ++ List.replicate c false) ++ r.drop (2 * c), oh := x.oh + 2 * c } :=
    ⟨_, rfl⟩
  rw [← hz] at s1
  have s2 := d_move cap gY gT (by decide) z (by rw [hz]; simp; omega) (by rw [hz]; simp; omega)
  rw [d_valT, d_valY, d_Y, d_T] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [hz]; simp [hy]; omega)
  rw [hz]; congr 1; cases x; simp_all

/-- Fill `H·B` false positions: `H` blocks of `B`, restoring `H` through `J`. -/
def fillHL : DProg := .whr gH (.seq (.dec gH) (.seq (.inc gJ) fillB))
def fillHB : DProg := .seq fillHL (WM.move gJ gH)

theorem fillHL_spec (bb : ℕ) : ∀ (c : ℕ) (x : DSt) (dd r : List Bool), x.hh = c → x.b = bb → x.y = 0 →
    x.ow = frameP dd ++ r → x.oh = 2 * dd.length → 2 * (c * bb) ≤ r.length → x.j + c ≤ cap →
    x.oh + 2 * (c * bb) ≤ cap → c ≤ cap → bb ≤ cap →
    WExec cap fillHL x.w'
      { x with hh := 0, j := x.j + c, ow := frameP (dd ++ List.replicate (c * bb) false) ++ r.drop (2 * (c * bb)),
               oh := x.oh + 2 * (c * bb) }.w' (c * (30 * bb + 11) + 1)
  | 0, x, dd, r, hh, _, _, hout, _, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hh])) ?_ (by simp)
    congr 1; cases x; simp_all
  | c + 1, x, dd, r, hh, hb, hy, hout, hoh, hr, hj, ho, hc, hbc => by
    have hcb : (c + 1) * bb = bb + c * bb := by ring
    rw [hcb] at hr ho
    have d1 := WExec.dec (cap := cap) gH x.w' (by simp; omega)
    rw [d_valH, d_H, hh, Nat.add_sub_cancel] at d1
    have d2 := WExec.inc (cap := cap) gJ { x with hh := c }.w' (by simp; omega)
    rw [d_valJ, d_J] at d2
    have d3 := fillB_spec cap bb { { x with hh := c } with j := x.j + 1 } dd r hb hout hoh (by omega) hy hbc
      (by simp only []; omega)
    obtain ⟨z, hz⟩ : ∃ z, z = { { { x with hh := c } with j := x.j + 1 } with ow := frameP (dd ++ List.replicate bb false) ++ r.drop (2 * bb), oh := x.oh + 2 * bb } :=
      ⟨_, rfl⟩
    rw [← hz] at d3
    have ih := fillHL_spec bb c z (dd ++ List.replicate bb false) (r.drop (2 * bb)) (by rw [hz]) (by rw [hz]; exact hb)
      (by rw [hz]; exact hy) (by rw [hz]) (by rw [hz]; simp [hoh]; omega) (by simp; omega) (by rw [hz]; simp only []; omega)
      (by rw [hz]; simp only []; omega) (by omega) hbc
    refine WExec.cast cap (WExec.whrT (by simp [hh]) (WExec.seq d1 (WExec.seq d2 d3)) ih) ?_ (by nlinarith)
    rw [hz]
    congr 1
    simp only [List.append_assoc, List.drop_drop, ← List.replicate_add]
    rw [hcb]
    congr 1 <;> first | omega | (congr 2; omega)

theorem fillHB_spec (bb c : ℕ) (x : DSt) (dd r : List Bool) (hh : x.hh = c) (hb : x.b = bb) (hy : x.y = 0)
    (hj : x.j = 0) (hout : x.ow = frameP dd ++ r) (hoh : x.oh = 2 * dd.length) (hr : 2 * (c * bb) ≤ r.length)
    (ho : x.oh + 2 * (c * bb) ≤ cap) (hc : c ≤ cap) (hbc : bb ≤ cap) :
    WExec cap fillHB x.w' { x with ow := frameP (dd ++ List.replicate (c * bb) false) ++ r.drop (2 * (c * bb)),
                                   oh := x.oh + 2 * (c * bb) }.w' (c * (30 * bb + 11) + 7 * c + 3) := by
  have s1 := fillHL_spec cap bb c x dd r hh hb hy hout hoh hr (by omega) ho hc hbc
  obtain ⟨z, hz⟩ : ∃ z, z = { x with hh := 0, j := x.j + c, ow := frameP (dd ++ List.replicate (c * bb) false) ++ r.drop (2 * (c * bb)), oh := x.oh + 2 * (c * bb) } :=
    ⟨_, rfl⟩
  rw [← hz] at s1
  have s2 := d_move cap gJ gH (by decide) z (by rw [hz]; simp; omega) (by rw [hz]; simp; omega)
  rw [d_valH, d_valJ, d_J, d_H] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [hz]; simp [hj]; omega)
  rw [hz]; congr 1; cases x; simp_all

/-! ## One digit -/

/-- Forward the index word, counting in `X`. -/
def fwdX : DProg := WM.fwdC sI gX

theorem fwdX_spec (x : DSt) (hx : x.ih < cap) : WExec cap fwdX x.w' { x with ih := x.ih + 1 }.w' 5 := by
  have h := wfwdC_spec cap sI gX x.w' hx
  rwa [d_fwdX] at h

/-- `D += W` through `K`. -/
def addWL : DProg := .whr gW (.seq (.dec gW) (.seq (.inc gK) (.inc gD)))
def addW : DProg := .seq addWL (WM.move gK gW)

theorem addWL_spec : ∀ (c : ℕ) (x : DSt), x.w = c → x.k + c ≤ cap → x.d + c ≤ cap → c ≤ cap →
    WExec cap addWL x.w' { x with w := 0, k := x.k + c, d := x.d + c }.w' (11 * c + 1)
  | 0, x, hw, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hw])) ?_ le_rfl
    congr 1; cases x; simp_all
  | c + 1, x, hw, hk, hd, hc => by
    have d1 := WExec.dec (cap := cap) gW x.w' (by simp; omega)
    rw [d_valW, d_W, hw, Nat.add_sub_cancel] at d1
    have d2 := WExec.inc (cap := cap) gK { x with w := c }.w' (by simp; omega)
    rw [d_valK, d_K] at d2
    have d3 := WExec.inc (cap := cap) gD { { x with w := c } with k := x.k + 1 }.w' (by simp; omega)
    rw [d_valD, d_D] at d3
    have ih := addWL_spec c { { { x with w := c } with k := x.k + 1 } with d := x.d + 1 } rfl (by simp only []; omega)
      (by simp only []; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by simp [hw]) (WExec.seq d1 (WExec.seq d2 d3)) ih) ?_ (by omega)
    congr 1; simp only []; congr 1 <;> omega

theorem addW_spec (x : DSt) (hk : x.k = 0) (hd : x.d + x.w ≤ cap) (hc : x.w ≤ cap) :
    WExec cap addW x.w' { x with d := x.d + x.w }.w' (18 * x.w + 3) := by
  have s1 := addWL_spec cap x.w x rfl (by omega) hd hc
  obtain ⟨z, hz⟩ : ∃ z, z = { x with w := 0, k := x.k + x.w, d := x.d + x.w } := ⟨_, rfl⟩
  rw [← hz] at s1
  have s2 := d_move cap gK gW (by decide) z (by rw [hz]; simp; omega) (by rw [hz]; simp; omega)
  rw [d_valW, d_valK, d_K, d_W] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [hz]; simp [hk]; omega)
  rw [hz]; congr 1; cases x; simp_all

/-- `W := 2W` through `K`. -/
def dblWL : DProg := .whr gW (.seq (.dec gW) (.seq (.inc gK) (.inc gK)))
def dblW : DProg := .seq dblWL (WM.move gK gW)

theorem dblWL_spec : ∀ (c : ℕ) (x : DSt), x.w = c → x.k + 2 * c ≤ cap → c ≤ cap →
    WExec cap dblWL x.w' { x with w := 0, k := x.k + 2 * c }.w' (11 * c + 1)
  | 0, x, hw, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hw])) ?_ le_rfl
    congr 1; cases x; simp_all
  | c + 1, x, hw, hk, hc => by
    have d1 := WExec.dec (cap := cap) gW x.w' (by simp; omega)
    rw [d_valW, d_W, hw, Nat.add_sub_cancel] at d1
    have d2 := WExec.inc (cap := cap) gK { x with w := c }.w' (by simp; omega)
    rw [d_valK, d_K] at d2
    have d3 := WExec.inc (cap := cap) gK { { x with w := c } with k := x.k + 1 }.w' (by simp; omega)
    rw [d_valK, d_K] at d3
    have ih := dblWL_spec c { { { x with w := c } with k := x.k + 1 } with k := x.k + 1 + 1 } rfl
      (by simp only []; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by simp [hw]) (WExec.seq d1 (WExec.seq d2 d3)) ih) ?_ (by omega)
    congr 1; simp only []; congr 1; omega

theorem dblW_spec (x : DSt) (hk : x.k = 0) (hc : 2 * x.w ≤ cap) :
    WExec cap dblW x.w' { x with w := 2 * x.w }.w' (25 * x.w + 3) := by
  have s1 := dblWL_spec cap x.w x rfl (by omega) (by omega)
  obtain ⟨z, hz⟩ : ∃ z, z = { x with w := 0, k := x.k + 2 * x.w } := ⟨_, rfl⟩
  rw [← hz] at s1
  have s2 := d_move cap gK gW (by decide) z (by rw [hz]; simp; omega) (by rw [hz]; simp; omega)
  rw [d_valW, d_valK, d_K, d_W] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [hz]; simp [hk]; omega)
  rw [hz]; congr 1; cases x; simp_all

/-- One bit of a digit: `D += [bit]·W`, `W := 2W`. -/
def digBody : DProg := .seq (.dec gS) (.seq (.inc gI) (.seq fwdX (.seq (.ifs sI addW .skip) (.seq dblW fwdX))))
def digL : DProg := .whr gS digBody

theorem chunkVal_lt : ∀ (l : List Bool), chunkVal l < 2 ^ l.length
  | [] => by simp [chunkVal]
  | x :: xs => by
    have := chunkVal_lt xs
    simp only [chunkVal, List.length_cons, pow_succ]
    cases x <;> (simp; omega)

theorem digL_spec (rest : List Bool) (S : ℕ) : ∀ (bits : List Bool) (x : DSt) (m : ℕ), x.s = bits.length →
    x.w = 2 ^ m → x.k = 0 → x.iw.drop x.ih = frameP bits ++ rest → m + bits.length ≤ S →
    x.d + 2 ^ m * chunkVal bits ≤ cap → 2 * 2 ^ S ≤ cap → x.i + bits.length ≤ cap → x.ih + 2 * bits.length ≤ cap →
    WExec cap digL x.w'
      { x with s := 0, i := x.i + bits.length, d := x.d + 2 ^ m * chunkVal bits, w := 2 ^ (m + bits.length),
               ih := x.ih + 2 * bits.length }.w' (bits.length * (43 * 2 ^ S + 30) + 1)
  | [], x, m, hs, hw, _, _, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hs])) ?_ (by simp)
    congr 1; cases x; simp_all [chunkVal]
  | bit :: bits, x, m, hs, hw, hk, hI, hS, hd, hcap, hi, hih => by
    simp only [List.length_cons] at hs hS hi hih
    have hmS : 2 ^ m ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm1 : 2 ^ (m + 1) ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcv := chunkVal_lt bits
    have hcv' : chunkVal (bit :: bits) = bit.toNat + 2 * chunkVal bits := rfl
    have hI0 : x.iw.drop x.ih = true :: bit :: (frameP bits ++ rest) := by simpa using hI
    have d1 := WExec.dec (cap := cap) gS x.w' (by simp; omega)
    rw [d_valS, d_S, hs, Nat.add_sub_cancel] at d1
    have d2 := WExec.inc (cap := cap) gI { x with s := bits.length }.w' (by simp; omega)
    rw [d_valI, d_I] at d2
    have d3 := fwdX_spec cap { { x with s := bits.length } with i := x.i + 1 } (by simp only []; omega)
    obtain ⟨y1, hy1⟩ : ∃ y, y = { { { x with s := bits.length } with i := x.i + 1 } with ih := x.ih + 1 } := ⟨_, rfl⟩
    rw [← hy1] at d3
    have hbit : wbit y1.w' sI = bit := by
      rw [hy1]; show readTapeBit x.iw (x.ih + 1) = bit
      exact ListEval.read_of_cons (ListEval.drop_succ_of_cons hI0)
    obtain ⟨y2, hy2, d4⟩ : ∃ y2 : DSt, y2 = { y1 with d := y1.d + bit.toNat * 2 ^ m } ∧
        WExec cap (.ifs sI addW .skip) y1.w' y2.w' (18 * 2 ^ m + 4) := by
      refine ⟨_, rfl, ?_⟩
      cases bit
      · refine WExec.cast cap (WExec.ifsF hbit (WExec.skip _)) ?_ (by omega)
        congr 1; cases y1; simp
      · have a := addW_spec cap y1 (by rw [hy1]; exact hk) (by rw [hy1]; simp only []; rw [hw]; simp at hd hcv'; nlinarith)
          (by rw [hy1]; simp only []; rw [hw]; omega)
        refine WExec.cast cap (WExec.ifsT hbit a) ?_ (by rw [hy1]; simp only []; rw [hw])
        congr 1; rw [hy1]; simp only []; rw [hw]; simp
    have d5 := dblW_spec cap y2 (by rw [hy2, hy1]; exact hk) (by rw [hy2, hy1]; simp only []; rw [hw]; omega)
    have d6 := fwdX_spec cap { y2 with w := 2 * y2.w } (by rw [hy2, hy1]; simp only []; omega)
    obtain ⟨y3, hy3⟩ : ∃ y, y = { { y2 with w := 2 * y2.w } with ih := y2.ih + 1 } := ⟨_, rfl⟩
    rw [← hy3] at d6
    have hI3 : y3.iw.drop y3.ih = frameP bits ++ rest := by
      rw [hy3, hy2, hy1]; simp only []
      exact ListEval.drop_succ_of_cons (ListEval.drop_succ_of_cons hI0)
    have ih := digL_spec rest S bits y3 (m + 1) (by rw [hy3, hy2, hy1]) (by rw [hy3, hy2, hy1]; simp only []; rw [hw]; ring)
      (by rw [hy3, hy2, hy1]; exact hk) hI3 (by omega)
      (by rw [hy3, hy2, hy1]; simp only []; rw [hcv'] at hd; rw [pow_succ]; cases bit <;> simp at hd ⊢ <;> nlinarith)
      hcap (by rw [hy3, hy2, hy1]; simp only []; omega) (by rw [hy3, hy2, hy1]; simp only []; omega)
    refine WExec.cast cap (WExec.whrT (by simp [hs]) (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4
      (WExec.seq d5 d6))))) ih) ?_ ?_
    · have hd_eq : x.d + bit.toNat * 2 ^ m + 2 ^ (m + 1) * chunkVal bits =
          x.d + 2 ^ m * (bit.toNat + 2 * chunkVal bits) := by rw [pow_succ]; ring
      rw [hy3, hy2, hy1]
      simp only [List.length_cons]
      rw [hd_eq, hcv', show m + 1 + bits.length = m + (bits.length + 1) by omega]
      congr 1; congr 1 <;> omega
    · rw [hy2, hy1]; simp only [List.length_cons]; rw [hw]; nlinarith

/-- **Read one digit**: `D := ` the value of the next `s` bits of the index word. -/
def readDigit : DProg := .seq (.inc gW) (.seq digL (.seq (WM.move gI gS) (WM.clear gW)))

theorem readDigit_spec (rest bits : List Bool) (x : DSt) (hs : x.s = bits.length) (hw : x.w = 0) (hk : x.k = 0)
    (hi : x.i = 0) (hd : x.d = 0) (hI : x.iw.drop x.ih = frameP bits ++ rest) (hcap : 2 * 2 ^ bits.length ≤ cap)
    (hbl : bits.length ≤ cap) (hih : x.ih + 2 * bits.length ≤ cap) :
    WExec cap readDigit x.w' { x with d := chunkVal bits, ih := x.ih + 2 * bits.length }.w'
      (bits.length * (43 * 2 ^ bits.length + 30) + 3 * 2 ^ bits.length + 7 * bits.length + 10) := by
  have hcv := chunkVal_lt bits
  have h1 : 1 ≤ 2 ^ bits.length := Nat.one_le_two_pow
  have s1 := WExec.inc (cap := cap) gW x.w' (by simp; omega)
  rw [d_valW, d_W, hw] at s1
  have s2 := digL_spec cap rest bits.length bits { x with w := 0 + 1 } 0 hs (by simp) hk hI (by omega)
    (by simp [hd]; omega) hcap (by simp [hi]; omega) (by simp only []; omega)
  obtain ⟨z, hz⟩ : ∃ z, z = { { x with w := 0 + 1 } with s := 0, i := x.i + bits.length, d := x.d + 2 ^ 0 * chunkVal bits, w := 2 ^ (0 + bits.length), ih := x.ih + 2 * bits.length } :=
    ⟨_, rfl⟩
  rw [← hz] at s2
  have s3 := d_move cap gI gS (by decide) z (by rw [hz]; simp [hi]; omega) (by rw [hz]; simp [hi]; omega)
  rw [d_valS, d_valI, d_I, d_S] at s3
  have s4 := wclear_spec cap gW (2 ^ bits.length) { { z with i := 0 } with s := z.s + z.i }.w'
    (by rw [hz]; simp) (by rw [hz]; simp; omega)
  rw [d_W] at s4
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · rw [hz]; congr 1; cases x; simp_all
  · rw [hz]; simp [hi]; omega

/-! ## One block -/

/-- The bit `[D = 1]`, counting `D` down. -/
def hotBit : DProg := .ifr gD (.seq (.dec gD) (.ifr gD (.wr sO false) (.wr sO true))) (.wr sO false)

/-- One position of a one-hot block. -/
def ohBody : DProg :=
  .seq (.dec gB) (.seq (.inc gY) (.seq (.wr sO true) (.seq (WM.fwdC sO gO) (.seq hotBit (WM.fwdC sO gO)))))
def ohL : DProg := .whr gB ohBody
/-- **The one-hot block** `[D = i+1]_{i<B}`, restoring `B` through `Y`. -/
def oneHotP : DProg := .seq ohL (WM.move gY gB)

theorem hotStep_spec (x : DSt) (dd r : List Bool) (o0 o1 : Bool) (hout : x.ow = frameP dd ++ o0 :: o1 :: r)
    (hoh : x.oh = 2 * dd.length) (hc : x.oh + 2 ≤ cap) (hd : x.d ≤ cap) :
    WExec cap (.seq (.wr sO true) (.seq (WM.fwdC sO gO) (.seq hotBit (WM.fwdC sO gO)))) x.w'
      { x with ow := frameP (dd ++ [decide (x.d = 1)]) ++ r, oh := x.oh + 2, d := x.d - 1 }.w' 19 := by
  have hlen : (frameP dd).length = x.oh := by simp [hoh]
  have s1 := WExec.wr (cap := cap) sO true x.w'
  rw [d_wrO] at s1
  have e1 : writeTapeBit x.ow x.oh true = frameP dd ++ true :: o1 :: r := by
    rw [hout, ← hlen]; exact writeTapeBit_mid' _ _ _ _
  rw [e1] at s1
  have s2 := wfwdC_spec cap sO gO { x with ow := frameP dd ++ true :: o1 :: r }.w' (by simp; omega)
  rw [d_fwdO] at s2
  obtain ⟨y1, hy1⟩ : ∃ y, y = { { x with ow := frameP dd ++ true :: o1 :: r } with oh := x.oh + 1 } := ⟨_, rfl⟩
  rw [← hy1] at s2
  have e3 : ∀ v : Bool, writeTapeBit (frameP dd ++ true :: o1 :: r) (x.oh + 1) v = frameP (dd ++ [v]) ++ r := by
    intro v
    have := writeTapeBit_mid' (frameP dd ++ [true]) r o1 v
    rw [show frameP dd ++ true :: o1 :: r = frameP dd ++ [true] ++ o1 :: r by simp,
      show x.oh + 1 = (frameP dd ++ [true]).length by simp [hlen]]
    rw [this, frameP_app']
    simp
  obtain ⟨y2, hy2, s3⟩ : ∃ y2 : DSt, y2 = { y1 with ow := frameP (dd ++ [decide (x.d = 1)]) ++ r, d := x.d - 1 } ∧
      WExec cap hotBit y1.w' y2.w' 5 := by
    refine ⟨_, rfl, ?_⟩
    have ew : ∀ v : Bool, writeTapeBit y1.ow y1.oh v = frameP (dd ++ [v]) ++ r := by
      intro v; rw [hy1]; exact e3 v
    have hy1d : y1.d = x.d := by rw [hy1]
    rcases Nat.eq_zero_or_pos x.d with h0 | h0
    · have w := WExec.wr (cap := cap) sO false y1.w'
      rw [d_wrO, ew] at w
      refine WExec.cast cap (WExec.ifrF (by simp [hy1d, h0]) w) ?_ (by omega)
      congr 1; rw [hy1]; simp [h0]
    · have dd1 := WExec.dec (cap := cap) gD y1.w' (by simp [hy1d]; omega)
      rw [d_valD, d_D] at dd1
      by_cases h1 : x.d = 1
      · have w := WExec.wr (cap := cap) sO true { y1 with d := y1.d - 1 }.w'
        rw [d_wrO] at w
        simp only [] at w
        rw [ew] at w
        refine WExec.cast cap (WExec.ifrT (by simp [hy1d]; omega) (WExec.seq dd1
          (WExec.ifrF (by simp [hy1d]; omega) w))) ?_ (by omega)
        rw [hy1]; congr 1; simp [h1]
      · have w := WExec.wr (cap := cap) sO false { y1 with d := y1.d - 1 }.w'
        rw [d_wrO] at w
        simp only [] at w
        rw [ew] at w
        refine WExec.cast cap (WExec.ifrT (by simp [hy1d]; omega) (WExec.seq dd1
          (WExec.ifrT (by simp [hy1d]; omega) w))) ?_ (by omega)
        rw [hy1]; congr 1; simp [h1]
  have s4 := wfwdC_spec cap sO gO y2.w' (by rw [hy2, hy1]; simp; omega)
  rw [d_fwdO] at s4
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (by omega)
  rw [hy2, hy1]

theorem ofFn_hot (δ c : ℕ) : List.ofFn (fun i : Fin (c + 1) => decide (δ = i.val + 1)) =
    decide (δ = 1) :: List.ofFn (fun i : Fin c => decide (δ - 1 = i.val + 1)) := by
  rw [List.ofFn_succ]
  congr 1
  congr 1
  funext i
  simp only [Fin.val_succ]
  apply decide_eq_decide.mpr
  omega

theorem ohL_spec : ∀ (c : ℕ) (x : DSt) (dd r : List Bool), x.b = c → x.ow = frameP dd ++ r →
    x.oh = 2 * dd.length → 2 * c ≤ r.length → x.y + c ≤ cap → x.oh + 2 * c ≤ cap → c ≤ cap → x.d ≤ cap →
    WExec cap ohL x.w'
      { x with b := 0, y := x.y + c, d := x.d - c,
               ow := frameP (dd ++ List.ofFn (fun i : Fin c => decide (x.d = i.val + 1))) ++ r.drop (2 * c),
               oh := x.oh + 2 * c }.w' (27 * c + 1)
  | 0, x, dd, r, hb, hout, _, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hb])) ?_ le_rfl
    congr 1; cases x; simp_all
  | c + 1, x, dd, r, hb, hout, hoh, hr, hy, ho, hc, hd => by
    obtain ⟨o0, o1, r', rfl⟩ : ∃ o0 o1 r', r = o0 :: o1 :: r' := by
      rcases r with _ | ⟨o0, _ | ⟨o1, r'⟩⟩ <;> simp at hr <;> try omega
      exact ⟨o0, o1, r', rfl⟩
    have d1 := WExec.dec (cap := cap) gB x.w' (by simp; omega)
    rw [d_valB, d_B, hb, Nat.add_sub_cancel] at d1
    have d2 := WExec.inc (cap := cap) gY { x with b := c }.w' (by simp; omega)
    rw [d_valY, d_Y] at d2
    have d3 := hotStep_spec cap { { x with b := c } with y := x.y + 1 } dd r' o0 o1 hout hoh (by simp only []; omega)
      (by simp only []; omega)
    obtain ⟨z, hz⟩ : ∃ z, z = { { { x with b := c } with y := x.y + 1 } with ow := frameP (dd ++ [decide (x.d = 1)]) ++ r', oh := x.oh + 2, d := x.d - 1 } :=
      ⟨_, rfl⟩
    rw [← hz] at d3
    have hr' : 2 * c ≤ r'.length := by simp only [List.length_cons] at hr; omega
    have ih := ohL_spec c z (dd ++ [decide (x.d = 1)]) r' (by rw [hz]) (by rw [hz]) (by rw [hz]; simp [hoh]; omega)
      hr' (by rw [hz]; simp only []; omega) (by rw [hz]; simp only []; omega) (by omega) (by rw [hz]; simp only []; omega)
    refine WExec.cast cap (WExec.whrT (by simp [hb]) (WExec.seq d1 (WExec.seq d2 d3)) ih) ?_ (by omega)
    rw [hz]
    simp only [List.append_assoc, List.singleton_append, ofFn_hot]
    congr 1; congr 1 <;> omega

theorem oneHotP_spec (bb : ℕ) (x : DSt) (dd r : List Bool) (hb : x.b = bb) (hout : x.ow = frameP dd ++ r)
    (hoh : x.oh = 2 * dd.length) (hr : 2 * bb ≤ r.length) (hy : x.y = 0) (hdb : x.d ≤ bb) (hc : bb ≤ cap)
    (ho : x.oh + 2 * bb ≤ cap) :
    WExec cap oneHotP x.w' { x with d := 0, ow := frameP (dd ++ oneHot bb x.d) ++ r.drop (2 * bb),
                                    oh := x.oh + 2 * bb }.w' (34 * bb + 3) := by
  have s1 := ohL_spec cap bb x dd r hb hout hoh hr (by omega) ho hc (by omega)
  obtain ⟨z, hz⟩ : ∃ z, z = { x with b := 0, y := x.y + bb, d := x.d - bb, ow := frameP (dd ++ List.ofFn (fun i : Fin bb => decide (x.d = i.val + 1))) ++ r.drop (2 * bb), oh := x.oh + 2 * bb } :=
    ⟨_, rfl⟩
  rw [← hz] at s1
  have s2 := d_move cap gY gB (by decide) z (by rw [hz]; simp; omega) (by rw [hz]; simp; omega)
  rw [d_valB, d_valY, d_Y, d_B] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [hz]; simp [hy]; omega)
  rw [hz]; congr 1; cases x; simp_all [oneHot]

/-! ## All blocks -/

def blkBody : DProg := .seq (.dec gH) (.seq (.inc gJ) (.seq readDigit oneHotP))
def blkL : DProg := .whr gH blkBody
/-- **All `H` one-hot blocks** from the digits of the index word, restoring `H` through `J`. -/
def blocks : DProg := .seq blkL (WM.move gJ gH)

/-- The cost of one block. -/
def blkCost (s bb : ℕ) : ℕ := s * (43 * 2 ^ s + 30) + 3 * 2 ^ s + 7 * s + 34 * bb + 22

theorem blkL_spec (rest : List Bool) (s bb : ℕ) (hbs : bb + 1 = 2 ^ s) : ∀ (c : ℕ) (w : List Bool) (x : DSt)
    (dd r : List Bool), x.hh = c → w.length = s * c → x.s = s → x.b = bb → x.d = 0 → x.w = 0 → x.i = 0 → x.k = 0 →
    x.y = 0 → x.iw.drop x.ih = frameP w ++ rest → x.ow = frameP dd ++ r → x.oh = 2 * dd.length →
    2 * (c * bb) ≤ r.length → 2 * 2 ^ s ≤ cap → s ≤ cap → x.ih + 2 * (s * c) ≤ cap → x.oh + 2 * (c * bb) ≤ cap →
    bb ≤ cap → x.j + c ≤ cap → c ≤ cap →
    WExec cap blkL x.w'
      { x with hh := 0, j := x.j + c, ih := x.ih + 2 * (s * c),
               ow := frameP (dd ++ (digitsOf s c w).flatMap (oneHot bb)) ++ r.drop (2 * (c * bb)),
               oh := x.oh + 2 * (c * bb) }.w' (c * blkCost s bb + 1)
  | 0, w, x, dd, r, hh, _, _, _, _, _, _, _, _, _, hout, _, _, _, _, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hh])) ?_ (by simp)
    congr 1; cases x; simp_all [digitsOf]
  | c + 1, w, x, dd, r, hh, hw, hs, hb, hd, hW, hi, hk, hy, hI, hout, hoh, hr, hcap, hsc, hih, ho, hbc, hj, hc => by
    have hcb : (c + 1) * bb = bb + c * bb := by ring
    have hsc' : s * (c + 1) = s + s * c := by ring
    rw [hcb] at hr ho
    rw [hsc'] at hw hih
    have d1 := WExec.dec (cap := cap) gH x.w' (by simp; omega)
    rw [d_valH, d_H, hh, Nat.add_sub_cancel] at d1
    have d2 := WExec.inc (cap := cap) gJ { x with hh := c }.w' (by simp; omega)
    rw [d_valJ, d_J] at d2
    have hwt : (w.take s).length = s := by rw [List.length_take]; omega
    have hI' : x.iw.drop x.ih = frameP (w.take s) ++ (frameP (w.drop s) ++ rest) := by
      rw [hI, ← List.append_assoc, ← frameP_app', List.take_append_drop]
    have d3 := readDigit_spec cap (frameP (w.drop s) ++ rest) (w.take s) { { x with hh := c } with j := x.j + 1 }
      (by simp only []; rw [hwt]; exact hs) hW hk hi hd hI' (by rw [hwt]; exact hcap) (by rw [hwt]; exact hsc)
      (by simp only []; rw [hwt]; omega)
    rw [hwt] at d3
    obtain ⟨y1, hy1⟩ : ∃ y, y = { { { x with hh := c } with j := x.j + 1 } with d := chunkVal (w.take s), ih := x.ih + 2 * s } :=
      ⟨_, rfl⟩
    rw [← hy1] at d3
    have hcv : chunkVal (w.take s) ≤ bb := by have := chunkVal_lt (w.take s); rw [hwt] at this; omega
    have d4 := oneHotP_spec cap bb y1 dd r (by rw [hy1]; exact hb) (by rw [hy1]; exact hout) (by rw [hy1]; exact hoh)
      (by omega) (by rw [hy1]; exact hy) (by rw [hy1]; exact hcv) hbc (by rw [hy1]; simp only []; omega)
    obtain ⟨y2, hy2⟩ : ∃ y, y = { y1 with d := 0, ow := frameP (dd ++ oneHot bb y1.d) ++ r.drop (2 * bb), oh := y1.oh + 2 * bb } :=
      ⟨_, rfl⟩
    rw [← hy2] at d4
    have hI2 : y2.iw.drop y2.ih = frameP (w.drop s) ++ rest := by
      rw [hy2, hy1]; simp only []
      have := ListEval.drop_add_of_append hI'
      rwa [frameP_length, hwt] at this
    have ih := blkL_spec rest s bb hbs c (w.drop s) y2 (dd ++ oneHot bb y1.d) (r.drop (2 * bb))
      (by rw [hy2, hy1]) (by rw [List.length_drop]; omega) (by rw [hy2, hy1]; exact hs) (by rw [hy2, hy1]; exact hb)
      (by rw [hy2]) (by rw [hy2, hy1]; exact hW) (by rw [hy2, hy1]; exact hi) (by rw [hy2, hy1]; exact hk)
      (by rw [hy2, hy1]; exact hy) hI2 (by rw [hy2]) (by rw [hy2, hy1]; simp [hoh, oneHot]; omega)
      (by rw [List.length_drop]; omega) hcap hsc (by rw [hy2, hy1]; simp only []; omega)
      (by rw [hy2, hy1]; simp only []; omega) hbc (by rw [hy2, hy1]; simp only []; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by simp [hh]) (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) ih) ?_ ?_
    · rw [hy2, hy1]
      simp only [digitsOf, List.flatMap_cons, List.append_assoc, List.drop_drop]
      congr 1; congr 1 <;> first | omega | (congr 2; omega)
    · unfold blkCost; nlinarith

theorem blocks_spec (rest : List Bool) (s bb c : ℕ) (hbs : bb + 1 = 2 ^ s) (w : List Bool) (x : DSt) (dd r : List Bool)
    (hh : x.hh = c) (hw : w.length = s * c) (hs : x.s = s) (hb : x.b = bb) (hd : x.d = 0) (hW : x.w = 0) (hi : x.i = 0)
    (hk : x.k = 0) (hy : x.y = 0) (hj : x.j = 0) (hI : x.iw.drop x.ih = frameP w ++ rest)
    (hout : x.ow = frameP dd ++ r) (hoh : x.oh = 2 * dd.length) (hr : 2 * (c * bb) ≤ r.length)
    (hcap : 2 * 2 ^ s ≤ cap) (hsc : s ≤ cap) (hih : x.ih + 2 * (s * c) ≤ cap) (ho : x.oh + 2 * (c * bb) ≤ cap)
    (hbc : bb ≤ cap) (hc : c ≤ cap) :
    WExec cap blocks x.w'
      { x with ih := x.ih + 2 * (s * c),
               ow := frameP (dd ++ (digitsOf s c w).flatMap (oneHot bb)) ++ r.drop (2 * (c * bb)),
               oh := x.oh + 2 * (c * bb) }.w' (c * blkCost s bb + 7 * c + 3) := by
  have s1 := blkL_spec cap rest s bb hbs c w x dd r hh hw hs hb hd hW hi hk hy hI hout hoh hr hcap hsc hih ho hbc
    (by omega) hc
  obtain ⟨z, hz⟩ : ∃ z, z = { x with hh := 0, j := x.j + c, ih := x.ih + 2 * (s * c), ow := frameP (dd ++ (digitsOf s c w).flatMap (oneHot bb)) ++ r.drop (2 * (c * bb)), oh := x.oh + 2 * (c * bb) } :=
    ⟨_, rfl⟩
  rw [← hz] at s1
  have s2 := d_move cap gJ gH (by decide) z (by rw [hz]; simp; omega) (by rw [hz]; simp; omega)
  rw [d_valH, d_valJ, d_J, d_H] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [hz]; simp [hj]; omega)
  rw [hz]; congr 1; cases x; simp_all

/-! ## The decoder -/

/-- The left half: its blocks, then zeros. -/
def decL : DProg := .seq blocks (.seq fillHB (.seq fillT (.seq (WM.rewind sO gO) fwdX)))
/-- The right half: zeros, its blocks, zeros. -/
def decR : DProg := .seq fillHB (.seq blocks (.seq fillT (.seq (WM.rewind sO gO) fwdX)))
/-- **The decoder of a half.** -/
def dec (right : Bool) : DProg := if right then decR else decL

/-- The decoder's cost. -/
def decCost (s bb h tl : ℕ) : ℕ :=
  h * blkCost s bb + h * (30 * bb + 11) + 14 * h + 30 * tl + 10 * (2 * (h * bb) + tl) + 30

theorem digitsOf_length (s : ℕ) : ∀ (h : ℕ) (w : List Bool), (digitsOf s h w).length = h
  | 0, _ => rfl
  | h + 1, w => by simp [digitsOf, digitsOf_length s h]

theorem flat_length (s bb h : ℕ) (w : List Bool) : ((digitsOf s h w).flatMap (oneHot bb)).length = h * bb := by
  rw [length_flatMap_oneHot, digitsOf_length]

/-- **Stage 0, a sampled half from its index**: from the framed binary word of the index `k` (stream `I` at any
offset) and a stale frame of `2·h·b + tail` positions before a `false` on `O` (from `0`), with the constants
`s, b, h, tail` in their registers (`b + 1 = 2^s`) and the other registers `0`, the output becomes
`frameP (decWord b h tail right (digits of k))` before that `false`; `O` is rewound and `I` is past the index word. -/
theorem dec_spec (right : Bool) (x : DSt) (s bb h tl : ℕ) (hbs : bb + 1 = 2 ^ s) (k : ℕ)
    (Y restO restI : List Bool) (hs : x.s = s) (hb : x.b = bb) (hh : x.hh = h) (ht : x.tl = tl) (hj : x.j = 0)
    (hd : x.d = 0) (hW : x.w = 0) (hi : x.i = 0) (hk : x.k = 0) (hy : x.y = 0) (hoh : x.oh = 0)
    (hI : x.iw.drop x.ih = frameP (binary (s * h) k) ++ false :: restI)
    (hout : x.ow = frameP Y ++ false :: restO) (hY : Y.length = h * bb + h * bb + tl)
    (hcap : 2 * 2 ^ s ≤ cap) (hsc : s ≤ cap) (hih : x.ih + 2 * (s * h) + 1 ≤ cap) (hYc : 2 * Y.length ≤ cap)
    (hbc : bb ≤ cap) (hc : h ≤ cap) (htc : tl ≤ cap) :
    WExec cap (dec right) x.w'
      { x with ow := frameP (decWord bb h tl right (digitsOf s h (binary (s * h) k))) ++ false :: restO,
               ih := x.ih + 2 * (s * h) + 1 }.w' (decCost s bb h tl) := by
  have hwl : (binary (s * h) k).length = s * h := binary_length'' _ _
  have hfl := flat_length s bb h (binary (s * h) k)
  have hr0 : (frameP Y ++ false :: restO).length = 2 * (h * bb + h * bb + tl) + 1 + restO.length := by
    simp [hY]; ring
  have hdrop : (frameP Y ++ false :: restO).drop (2 * (h * bb) + 2 * (h * bb) + 2 * tl) = false :: restO := by
    rw [List.drop_left' (by simp [hY]; ring)]
  cases right
  · -- the left half
    have s1 := blocks_spec cap (false :: restI) s bb h hbs (binary (s * h) k) x [] (frameP Y ++ false :: restO) hh hwl
      hs hb hd hW hi hk hy hj hI (by simpa using hout) (by simp [hoh]) (by rw [hr0]; omega) hcap hsc (by omega)
      (by omega) hbc hc
    obtain ⟨z1, hz1⟩ : ∃ z, z = { x with ih := x.ih + 2 * (s * h), ow := frameP ([] ++ (digitsOf s h (binary (s * h) k)).flatMap (oneHot bb)) ++ (frameP Y ++ false :: restO).drop (2 * (h * bb)), oh := x.oh + 2 * (h * bb) } :=
      ⟨_, rfl⟩
    rw [← hz1] at s1
    have s2 := fillHB_spec cap bb h z1 ([] ++ (digitsOf s h (binary (s * h) k)).flatMap (oneHot bb))
      ((frameP Y ++ false :: restO).drop (2 * (h * bb))) (by rw [hz1]; exact hh) (by rw [hz1]; exact hb)
      (by rw [hz1]; exact hy) (by rw [hz1]; exact hj) (by rw [hz1]) (by rw [hz1]; simp [hoh, hfl])
      (by rw [List.length_drop, hr0]; omega) (by rw [hz1]; simp only []; omega) hc hbc
    obtain ⟨z2, hz2⟩ : ∃ z, z = { z1 with ow := frameP ([] ++ (digitsOf s h (binary (s * h) k)).flatMap (oneHot bb) ++ List.replicate (h * bb) false) ++ ((frameP Y ++ false :: restO).drop (2 * (h * bb))).drop (2 * (h * bb)), oh := z1.oh + 2 * (h * bb) } :=
      ⟨_, rfl⟩
    rw [← hz2] at s2
    have s3 := fillT_spec cap tl z2 ([] ++ (digitsOf s h (binary (s * h) k)).flatMap (oneHot bb) ++
      List.replicate (h * bb) false) (((frameP Y ++ false :: restO).drop (2 * (h * bb))).drop (2 * (h * bb)))
      (by rw [hz2, hz1]; exact ht) (by rw [hz2]) (by rw [hz2, hz1]; simp [hoh, hfl]; ring)
      (by simp only [List.length_drop]; rw [hr0]; omega) (by rw [hz2, hz1]; exact hy) htc
      (by rw [hz2, hz1]; simp only []; omega)
    obtain ⟨z3, hz3⟩ : ∃ z, z = { z2 with ow := frameP ([] ++ (digitsOf s h (binary (s * h) k)).flatMap (oneHot bb) ++ List.replicate (h * bb) false ++ List.replicate tl false) ++ (((frameP Y ++ false :: restO).drop (2 * (h * bb))).drop (2 * (h * bb))).drop (2 * tl), oh := z2.oh + 2 * tl } :=
      ⟨_, rfl⟩
    rw [← hz3] at s3
    have s4 := wrewind_spec cap sO gO z3.oh z3.w' (by simp) (by rw [d_valO, hz3, hz2, hz1]; simp only []; omega)
    rw [d_rewO z3 z3.oh rfl] at s4
    have s5 := fwdX_spec cap { z3 with oh := 0 } (by rw [hz3, hz2, hz1]; simp only []; omega)
    refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
    · rw [hz3, hz2, hz1]
      simp only [List.drop_drop, List.nil_append]
      rw [hdrop]
      simp only [decWord, Bool.false_eq_true, if_false, List.replicate_add, List.append_assoc]
      congr 1; cases x; simp_all
    · rw [hz3, hz2, hz1]; unfold decCost; simp only [hoh]; nlinarith
  · -- the right half
    have s1 := fillHB_spec cap bb h x [] (frameP Y ++ false :: restO) hh hb hy hj (by simpa using hout)
      (by simp [hoh]) (by rw [hr0]; omega) (by omega) hc hbc
    obtain ⟨z1, hz1⟩ : ∃ z, z = { x with ow := frameP ([] ++ List.replicate (h * bb) false) ++ (frameP Y ++ false :: restO).drop (2 * (h * bb)), oh := x.oh + 2 * (h * bb) } :=
      ⟨_, rfl⟩
    rw [← hz1] at s1
    have s2 := blocks_spec cap (false :: restI) s bb h hbs (binary (s * h) k) z1 ([] ++ List.replicate (h * bb) false)
      ((frameP Y ++ false :: restO).drop (2 * (h * bb))) (by rw [hz1]; exact hh) hwl (by rw [hz1]; exact hs)
      (by rw [hz1]; exact hb) (by rw [hz1]; exact hd) (by rw [hz1]; exact hW) (by rw [hz1]; exact hi)
      (by rw [hz1]; exact hk) (by rw [hz1]; exact hy) (by rw [hz1]; exact hj) (by rw [hz1]; exact hI) (by rw [hz1])
      (by rw [hz1]; simp [hoh]) (by rw [List.length_drop, hr0]; omega) hcap hsc (by rw [hz1]; simp only []; omega)
      (by rw [hz1]; simp only []; omega) hbc hc
    obtain ⟨z2, hz2⟩ : ∃ z, z = { z1 with ih := z1.ih + 2 * (s * h), ow := frameP ([] ++ List.replicate (h * bb) false ++ (digitsOf s h (binary (s * h) k)).flatMap (oneHot bb)) ++ ((frameP Y ++ false :: restO).drop (2 * (h * bb))).drop (2 * (h * bb)), oh := z1.oh + 2 * (h * bb) } :=
      ⟨_, rfl⟩
    rw [← hz2] at s2
    have s3 := fillT_spec cap tl z2 ([] ++ List.replicate (h * bb) false ++ (digitsOf s h (binary (s * h) k)).flatMap
      (oneHot bb)) (((frameP Y ++ false :: restO).drop (2 * (h * bb))).drop (2 * (h * bb)))
      (by rw [hz2, hz1]; exact ht) (by rw [hz2]) (by rw [hz2, hz1]; simp [hoh, hfl]; ring)
      (by simp only [List.length_drop]; rw [hr0]; omega) (by rw [hz2, hz1]; exact hy) htc
      (by rw [hz2, hz1]; simp only []; omega)
    obtain ⟨z3, hz3⟩ : ∃ z, z = { z2 with ow := frameP ([] ++ List.replicate (h * bb) false ++ (digitsOf s h (binary (s * h) k)).flatMap (oneHot bb) ++ List.replicate tl false) ++ (((frameP Y ++ false :: restO).drop (2 * (h * bb))).drop (2 * (h * bb))).drop (2 * tl), oh := z2.oh + 2 * tl } :=
      ⟨_, rfl⟩
    rw [← hz3] at s3
    have s4 := wrewind_spec cap sO gO z3.oh z3.w' (by simp) (by rw [d_valO, hz3, hz2, hz1]; simp only []; omega)
    rw [d_rewO z3 z3.oh rfl] at s4
    have s5 := fwdX_spec cap { z3 with oh := 0 } (by rw [hz3, hz2, hz1]; simp only []; omega)
    refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
    · rw [hz3, hz2, hz1]
      simp only [List.drop_drop, List.nil_append]
      rw [hdrop]
      simp only [decWord, if_true, List.append_assoc]
      congr 1; cases x; simp_all
    · rw [hz3, hz2, hz1]; unfold decCost; simp only [hoh]; nlinarith

end NearCubicWires.WireExponent3_5.FinalPass.Sample
