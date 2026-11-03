import Proof.Wire_3_5.UnionMachine.FrontEntriesRef
import Proof.Wire_3_5.UnionMachine.FrontOracleField
import Proof.MachineModel.OrdinaryZeroPadding

/-! # C6 front, U1b: one guessed atom's code onto v8's decoder tape (P3:3670)

For "It rejects malformed descriptions, oversized atoms" (P3:3670) the front decodes every grid atom with v8's
canonical circuit decoder (`CloseoutRowsCircuit{Threshold,Symmetric}Run`, run padded: base `CloseoutRowsCircuitPadding`),
whose raw input tape holds `pad P (frame bits)` for the atom's code bits `bits` (`value bits` = the code). This register
program (C5's `WM`) takes one entry of the validated guess rest `frame r` (the codec: the grid word `b 1 0 x`, then
the code's field `1^k 0 p` with `|p| = k`, `FrontEntriesRef.entStep`) and writes `pad P (frame p)` over the blank tape
`replicate P false`; the rest's head moves from the entry to the next one, the decoder tape's head returns to `0`.
Main statement: **`copyAtom_spec`**. Paper quantity: the code of one guessed atom, as the decoder reads it. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Layout: streams `G` (the rest, framed) and `T` (the decoder's raw tape); registers `PG PT K` -/

abbrev CS := WState 1 3

local notation "sG" => (0 : Fin 2)
local notation "sT" => (1 : Fin 2)
local notation "rPG" => (0 : Fin 3)
local notation "rPT" => (1 : Fin 3)
local notation "rK" => (2 : Fin 3)

/-- The copy's data: the two heads (each equal to its counter), the count, the decoder tape, the cell. -/
structure D where
  pg : ℕ
  pt : ℕ
  K : ℕ
  t : List Bool
  cell : Bool

/-- The state on the rest `frame r`. -/
def st (r : List Bool) (d : D) : CS := ⟨![d.pg, d.pt], ![frame r, d.t], ![d.pg, d.pt, d.K], d.cell⟩

variable (cap : ℕ) (r : List Bool)

theorem st_val (d : D) (i : Fin 3) : (st r d).val i = ![d.pg, d.pt, d.K] i := rfl

/-- Close `st r X = st r Y` for explicit data records. -/
macro "cfin" : tactic => `(tactic| (congr 1 <;> simp <;> omega))

theorem wbit_G (d : D) : wbit (st r d) sG = readTapeBit (frame r) d.pg := rfl

/-! ## One-instruction steps -/

theorem x_fwdG (d : D) (hc : d.pg < cap) :
    WExec cap (WM.fwdC sG rPG) (st r d) (st r { d with pg := d.pg + 1 }) 5 := by
  refine WExec.cast cap (wfwdC_spec cap sG rPG (st r d) hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

theorem x_fwdT (d : D) (hc : d.pt < cap) :
    WExec cap (WM.fwdC sT rPT) (st r d) (st r { d with pt := d.pt + 1 }) 5 := by
  refine WExec.cast cap (wfwdC_spec cap sT rPT (st r d) hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

/-- One step back on the rest, the counter down. -/
def bwdG : WM 1 3 := .seq (.bwd sG) (.dec rPG)

theorem x_bwdG (d : D) (hc : d.pg ≤ cap) :
    WExec cap bwdG (st r d) (st r { d with pg := d.pg - 1 }) 3 := by
  have h1 := WExec.bwd (cap := cap) sG (st r d)
  have h2 := WExec.dec (cap := cap) rPG ((st r d).seth sG ((st r d).sh sG - 1)) (by
    simpa [st, WState.seth] using hc)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, WState.seth, WState.setv, Function.update_apply])

theorem x_incK (d : D) (hc : d.K < cap) :
    WExec cap (.inc rK) (st r d) (st r { d with K := d.K + 1 }) 3 := by
  refine WExec.cast cap (WExec.inc (cap := cap) rK (st r d) (by rw [st_val]; simpa using hc)) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, WState.setv, Function.update_apply])

theorem x_decK (d : D) (hc : d.K ≤ cap) :
    WExec cap (.dec rK) (st r d) (st r { d with K := d.K - 1 }) 1 := by
  refine WExec.cast cap (WExec.dec (cap := cap) rK (st r d) (by rw [st_val]; simpa using hc)) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, WState.setv, Function.update_apply])

theorem x_wrT (d : D) (b : Bool) :
    WExec cap (.wr sT b) (st r d) (st r { d with t := writeTapeBit d.t d.pt b }) 1 := by
  refine WExec.cast cap (WExec.wr (cap := cap) sT b (st r d)) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, WState.sets, Function.update_apply])

theorem x_rewT (d : D) (hc : d.pt ≤ cap) :
    WExec cap (WM.rewind sT rPT) (st r d) (st r { d with pt := 0 }) (5 * d.pt + 1) := by
  refine WExec.cast cap (wrewind_spec cap sT rPT d.pt (st r d) rfl hc) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, Function.update_apply])

/-! ## The program -/

/-- `n` steps forward on the rest. -/
def fwdGn : ℕ → WM 1 3
  | 0 => .skip
  | n + 1 => .seq (WM.fwdC sG rPG) (fwdGn n)

/-- The code field's ones, counted in `K` (the head on a bit cell of the frame). -/
def onesLoop : WM 1 3 := .whs sG (.seq (.inc rK) (fwdGn 2))
/-- One payload bit `b` onto the decoder tape as `1 b`. -/
def cpBit : WM 1 3 :=
  .seq (.wr sT true) (.seq (WM.fwdC sT rPT) (.seq (.ifs sG (.wr sT true) (.wr sT false)) (WM.fwdC sT rPT)))
/-- The `K` payload bits. -/
def copyLoop : WM 1 3 := .whr rK (.seq (.dec rK) (.seq cpBit (fwdGn 2)))

/-- **One atom's code onto the decoder tape**: past the grid word, count the field's ones, copy its payload framed,
back to the next entry's mark, the decoder tape rewound. -/
def copyAtom : WM 1 3 := .seq (fwdGn 9) (.seq onesLoop (.seq (fwdGn 2) (.seq copyLoop (.seq bwdG (WM.rewind sT rPT)))))

/-! ## Specs -/

theorem fwdGn_spec : ∀ (n : ℕ) (d : D), d.pg + n ≤ cap →
    WExec cap (fwdGn n) (st r d) (st r { d with pg := d.pg + n }) (6 * n)
  | 0, d, _ => WExec.cast cap (WExec.skip _) (by cfin) (by omega)
  | n + 1, d, hc => by
    have s1 := x_fwdG cap r d (by omega)
    have s2 := fwdGn_spec n { d with pg := d.pg + 1 } (by simp; omega)
    exact WExec.cast cap (s1.seq s2) (by cfin) (by omega)

/-- The frame's bit cells of a word `pre ++ 1^k 0 tail` read `1` on the ones and `0` on the separator. -/
theorem ones_spec (u : List Bool) (P0 k : ℕ) (hu : ∀ i, i < k → u.getD (P0 + i) false = true)
    (hs : u.getD (P0 + k) false = false) (hlen : P0 + k < u.length) :
    ∀ j (d : D), j ≤ k → d.pg = 2 * (P0 + j) + 1 → d.K = j → 2 * (P0 + k) + 2 ≤ cap → k ≤ cap →
      WExec cap onesLoop (st u d) (st u { d with pg := 2 * (P0 + k) + 1, K := k }) (20 * (k - j) + 1) := by
  intro j
  induction h : k - j generalizing j with
  | zero =>
    intro d hj hpg hK _ _
    have hjk : j = k := by omega
    subst hjk
    refine WExec.cast cap (WExec.whsF (by rw [wbit_G, hpg, FrontOracleField.frame_bit]; exact hs)) ?_ (by omega)
    cases d; simp_all
  | succ m ih =>
    intro d hj hpg hK hc hk
    have hbit : readTapeBit (frame u) d.pg = true := by
      rw [hpg, FrontOracleField.frame_bit]; exact hu j (by omega)
    have s1 := x_incK cap u d (by omega)
    have s2 := fwdGn_spec cap u 2 { d with K := d.K + 1 } (by simp; omega)
    have s3 := ih (j + 1) (by omega) { { d with K := d.K + 1 } with pg := { d with K := d.K + 1 }.pg + 2 }
      (by omega) (by simp; omega) (by simp; omega) hc hk
    refine WExec.cast cap (WExec.whsT (by rw [wbit_G]; exact hbit) (s1.seq s2) s3) ?_ (by omega)
    cases d; simp_all

/-- The decoder tape after `j` copied payload bits. -/
def tpref (p : List Bool) (j P : ℕ) : List Bool := (p.take j).flatMap (fun b => [true, b]) ++ List.replicate (P - 2 * j) false

theorem wmid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simpa [writeTapeBit] using congrArg (List.cons a) ih

theorem flat_len (l : List Bool) : (l.flatMap (fun b => [true, b])).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]; omega

theorem tpref_step (p : List Bool) (j P : ℕ) (hj : j < p.length) (hP : 2 * j + 2 ≤ P) :
    writeTapeBit (writeTapeBit (tpref p j P) (2 * j) true) (2 * j + 1) (p.getD j false) = tpref p (j + 1) P := by
  set A := (p.take j).flatMap (fun b => [true, b]) with hA
  have hl : A.length = 2 * j := by rw [hA, flat_len, List.length_take]; omega
  have e0 : tpref p j P = A ++ false :: false :: List.replicate (P - 2 * j - 2) false := by
    obtain ⟨m, hm⟩ : ∃ m, P - 2 * j = m + 2 := ⟨P - 2 * j - 2, by omega⟩
    unfold tpref
    rw [← hA, show P - 2 * j - 2 = m by omega, hm, List.replicate_succ, List.replicate_succ]
  have e1 : writeTapeBit (A ++ false :: false :: List.replicate (P - 2 * j - 2) false) (2 * j) true =
      A ++ true :: false :: List.replicate (P - 2 * j - 2) false := by rw [← hl]; exact wmid _ _ _ _
  have e2 : writeTapeBit (A ++ true :: false :: List.replicate (P - 2 * j - 2) false) (2 * j + 1) (p.getD j false) =
      (A ++ [true]) ++ p.getD j false :: List.replicate (P - 2 * j - 2) false := by
    have := wmid (A ++ [true]) (List.replicate (P - 2 * j - 2) false) false (p.getD j false)
    simp only [List.length_append, List.length_singleton, hl, List.append_assoc, List.singleton_append] at this
    simpa [List.append_assoc] using this
  rw [e0, e1, e2]
  unfold tpref
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append, ← hA,
    show P - 2 * (j + 1) = P - 2 * j - 2 by omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem cpBit_spec (u p : List Bool) (P : ℕ) (j : ℕ) (hj : j < p.length) (hP : 2 * j + 2 ≤ P) (d : D)
    (ht : d.t = tpref p j P) (hpt : d.pt = 2 * j) (hbit : readTapeBit (frame u) d.pg = p.getD j false)
    (hc : 2 * j + 2 ≤ cap) :
    WExec cap cpBit (st u d) (st u { d with t := tpref p (j + 1) P, pt := 2 * j + 2 }) 16 := by
  have s1 := x_wrT cap u d true
  have s2 := x_fwdT cap u { d with t := writeTapeBit d.t d.pt true } (by simp; omega)
  set d2 : D := { { d with t := writeTapeBit d.t d.pt true } with pt := { d with t := writeTapeBit d.t d.pt true }.pt + 1 }
    with hd2
  have hb2 : wbit (st u d2) sG = p.getD j false := by rw [wbit_G]; simpa [hd2] using hbit
  have s3 : WExec cap (.ifs sG (.wr sT true) (.wr sT false)) (st u d2)
      (st u { d2 with t := writeTapeBit d2.t d2.pt (p.getD j false) }) 2 := by
    cases hpj : p.getD j false with
    | true => exact WExec.ifsT (by rw [hb2, hpj]) (x_wrT cap u d2 true)
    | false => exact WExec.ifsF (by rw [hb2, hpj]) (x_wrT cap u d2 false)
  have s4 := x_fwdT cap u { d2 with t := writeTapeBit d2.t d2.pt (p.getD j false) } (by show d.pt + 1 < cap; omega)
  refine WExec.cast cap (s1.seq (s2.seq (s3.seq s4))) ?_ (by omega)
  have e : writeTapeBit (writeTapeBit d.t d.pt true) (d.pt + 1) (p.getD j false) = tpref p (j + 1) P := by
    rw [ht, hpt]; exact tpref_step p j P hj hP
  cases d; simp_all [hd2]

/-- The payload loop: `k` bits copied (`K` counting down), the rest's head two cells per bit. -/
theorem copyLoop_spec (u p : List Bool) (P Q : ℕ) (hbits : ∀ i, i < p.length → u.getD (Q + i) false = p.getD i false)
    (hP : 2 * p.length + 1 ≤ P) :
    ∀ j (d : D), j ≤ p.length → d.K = p.length - j → d.t = tpref p j P → d.pt = 2 * j → d.pg = 2 * (Q + j) + 1 →
      2 * (Q + p.length) + 2 ≤ cap → 2 * p.length + 2 ≤ cap →
      WExec cap copyLoop (st u d)
        (st u { d with K := 0, t := tpref p p.length P, pt := 2 * p.length, pg := 2 * (Q + p.length) + 1 })
        (33 * (p.length - j) + 1) := by
  intro j
  induction h : p.length - j generalizing j with
  | zero =>
    intro d hj hK ht hpt hpg _ _
    have hjk : j = p.length := by omega
    subst hjk
    refine WExec.cast cap (WExec.whrF (by rw [st_val]; simpa using hK)) ?_ (by omega)
    cases d; simp_all
  | succ m ih =>
    intro d hj hK ht hpt hpg hc1 hc2
    have s1 := x_decK cap u d (by omega)
    have s2 := cpBit_spec cap u p P j (by omega) (by omega) { d with K := d.K - 1 } ht hpt
      (by simp only; rw [hpg, FrontOracleField.frame_bit]; exact hbits j (by omega)) (by omega)
    have s3 := fwdGn_spec cap u 2 { { d with K := d.K - 1 } with t := tpref p (j + 1) P, pt := 2 * j + 2 }
      (by simp; omega)
    have s4 := ih (j + 1) (by omega)
      { { { d with K := d.K - 1 } with t := tpref p (j + 1) P, pt := 2 * j + 2 } with
        pg := { { d with K := d.K - 1 } with t := tpref p (j + 1) P, pt := 2 * j + 2 }.pg + 2 }
      (by omega) (by simp; omega) (by simp) (by simp; omega) (by simp; omega) hc1 hc2
    refine WExec.cast cap (WExec.whrT (by rw [st_val]; show d.K ≠ 0; omega) (s1.seq (s2.seq s3)) s4) ?_ (by omega)
    cases d; simp_all

theorem frame_flat : ∀ p : List Bool, frame p = p.flatMap (fun b => [true, b]) ++ [false]
  | [] => rfl
  | a :: p => by rw [show frame (a :: p) = true :: a :: frame p from rfl, frame_flat p]; simp

theorem tpref_full (p : List Bool) (P : ℕ) (hP : 2 * p.length + 1 ≤ P) :
    tpref p p.length P = ZeroPadding.pad P (frame p) := by
  have hf := frame_flat p
  unfold tpref ZeroPadding.pad
  rw [hf, List.take_length]
  simp only [List.length_append, flat_len, List.length_singleton, List.append_assoc, List.singleton_append]
  rw [show P - 2 * p.length = (P - (2 * p.length + 1)) + 1 by omega, List.replicate_succ]

theorem getD_four (a b c d : Bool) (L : List Bool) (i : ℕ) :
    ([a, b, c, d] ++ L).getD (4 + i) false = L.getD i false := by
  rw [show 4 + i = i + 1 + 1 + 1 + 1 by omega]; rfl

theorem rep_lt (k i : ℕ) (M : List Bool) (hi : i < k) : (List.replicate k true ++ M).getD i false = true := by
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]

theorem rep_ge (k j : ℕ) (M : List Bool) : (List.replicate k true ++ M).getD (k + j) false = M.getD j false := by
  have := List.getD_append_right (List.replicate k true) M false (k + j) (by simp)
  rw [this]; simp

/-- **One atom's code**: from the entry at `P0` of the rest (`r.drop P0 = b 1 0 x ++ 1^k 0 p ++ rest`, `|p| = k ≥ 1`),
the decoder tape `replicate P false` becomes `pad P (frame p)`; the rest's head moves to the next entry. -/
theorem copyAtom_spec (P0 : ℕ) (b x : Bool) (p rest : List Bool) (P : ℕ)
    (hr : r.drop P0 = FrontEntriesRef.gridWord b x ++ (List.replicate p.length true ++ false :: p) ++ rest)
    (hk : 1 ≤ p.length) (hP : 2 * p.length + 1 ≤ P) (hcap : 2 * (P0 + 2 * p.length + 5) + 2 ≤ cap)
    (hcap2 : 2 * p.length + 2 ≤ cap) (c : Bool) :
    ∃ n, n ≤ 70 * (p.length + 2) ∧
      WExec cap copyAtom (st r ⟨2 * P0, 0, 0, List.replicate P false, c⟩)
        (st r ⟨2 * (P0 + 2 * p.length + 5), 0, 0, ZeroPadding.pad P (frame p), c⟩) n := by
  set k := p.length with hkd
  have hget : ∀ i, r.getD (P0 + i) false = (FrontEntriesRef.gridWord b x ++
      (List.replicate k true ++ false :: p) ++ rest).getD i false := by
    intro i; rw [← hr]; simp [List.getD_eq_getElem?_getD]
  have hlen : P0 + (2 * k + 5) ≤ r.length := by
    have := congrArg List.length hr
    simp [FrontEntriesRef.gridWord] at this; omega
  have hshape : FrontEntriesRef.gridWord b x ++ (List.replicate k true ++ false :: p) ++ rest =
      [b, true, false, x] ++ (List.replicate k true ++ (false :: (p ++ rest))) := by
    simp [FrontEntriesRef.gridWord]
  have hones : ∀ i, i < k → r.getD (P0 + 4 + i) false = true := by
    intro i hi
    rw [show P0 + 4 + i = P0 + (4 + i) by omega, hget, hshape, getD_four, rep_lt _ _ _ hi]
  have hsep : r.getD (P0 + 4 + k) false = false := by
    rw [show P0 + 4 + k = P0 + (4 + (k + 0)) by omega, hget, hshape, getD_four, rep_ge]; rfl
  have hpay : ∀ i, i < k → r.getD (P0 + 5 + k + i) false = p.getD i false := by
    intro i hi
    rw [show P0 + 5 + k + i = P0 + (4 + (k + (i + 1))) by omega, hget, hshape, getD_four, rep_ge]
    show (p ++ rest).getD i false = p.getD i false
    rw [List.getD_append _ _ _ _ (by omega)]
  -- 1. past the grid word, onto the first ones cell
  have s1 := fwdGn_spec cap r 9 ⟨2 * P0, 0, 0, List.replicate P false, c⟩ (by simp; omega)
  -- 2. the ones
  have s2 := ones_spec cap r (P0 + 4) k hones hsep (by omega) 0
    { (⟨2 * P0, 0, 0, List.replicate P false, c⟩ : D) with pg := 2 * P0 + 9 } (by omega) (by simp; omega) rfl
    (by omega) (by omega)
  -- 3. onto the first payload bit cell
  have s3 := fwdGn_spec cap r 2
    { { (⟨2 * P0, 0, 0, List.replicate P false, c⟩ : D) with pg := 2 * P0 + 9 } with
      pg := 2 * (P0 + 4 + k) + 1, K := k } (by simp; omega)
  -- 4. the payload
  have s4 := copyLoop_spec cap r p P (P0 + 5 + k) hpay hP 0
    { { { (⟨2 * P0, 0, 0, List.replicate P false, c⟩ : D) with pg := 2 * P0 + 9 } with
      pg := 2 * (P0 + 4 + k) + 1, K := k } with pg := 2 * (P0 + 4 + k) + 1 + 2 }
    (by omega) (by simp [hkd]) (by simp [tpref]) (by simp) (by simp; omega) (by omega) hcap2
  -- 5. back to the next entry's mark, the decoder tape rewound
  have s5 := x_bwdG cap r
    ⟨2 * (P0 + 5 + k + k) + 1, 2 * k, 0, tpref p k P, c⟩ (by show 2 * (P0 + 5 + k + k) + 1 ≤ cap; omega)
  have s6 : WExec cap (WM.rewind sT rPT) (st r ⟨2 * (P0 + 5 + k + k) + 1 - 1, 2 * k, 0, tpref p k P, c⟩)
      (st r ⟨2 * (P0 + 5 + k + k) + 1 - 1, 0, 0, tpref p k P, c⟩) (5 * (2 * k) + 1) :=
    x_rewT cap r ⟨2 * (P0 + 5 + k + k) + 1 - 1, 2 * k, 0, tpref p k P, c⟩ (by show 2 * k ≤ cap; omega)
  have s4' : WExec cap copyLoop (st r ⟨2 * (P0 + 4 + k) + 1 + 2, 0, k, List.replicate P false, c⟩)
      (st r ⟨2 * (P0 + 5 + k + k) + 1, 2 * k, 0, tpref p k P, c⟩) (33 * (k - 0) + 1) :=
    WExec.cast cap s4 (by cfin) le_rfl
  have s1' : WExec cap (fwdGn 9) (st r ⟨2 * P0, 0, 0, List.replicate P false, c⟩)
      (st r ⟨2 * P0 + 9, 0, 0, List.replicate P false, c⟩) (6 * 9) := WExec.cast cap s1 (by cfin) le_rfl
  have s2' : WExec cap onesLoop (st r ⟨2 * P0 + 9, 0, 0, List.replicate P false, c⟩)
      (st r ⟨2 * (P0 + 4 + k) + 1, 0, k, List.replicate P false, c⟩) (20 * (k - 0) + 1) :=
    WExec.cast cap s2 (by cfin) le_rfl
  have s3' : WExec cap (fwdGn 2) (st r ⟨2 * (P0 + 4 + k) + 1, 0, k, List.replicate P false, c⟩)
      (st r ⟨2 * (P0 + 4 + k) + 1 + 2, 0, k, List.replicate P false, c⟩) (6 * 2) := WExec.cast cap s3 (by cfin) le_rfl
  refine ⟨_, ?_, WExec.cast cap (s1'.seq (s2'.seq (s3'.seq (s4'.seq (s5.seq s6))))) ?_ le_rfl⟩
  · omega
  · rw [← tpref_full p P hP, ← hkd]; cfin

end NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomCopy
