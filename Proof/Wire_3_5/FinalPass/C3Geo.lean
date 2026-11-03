import Proof.Wire_3_5.FinalPass.SymFr3Base

/-! # The compiler request's geometry clauses (mode-generic)

"Assign `r/2` whole blocks to each side [...] Split the remaining `n−rb` coordinates as evenly as possible"
(P3:1213-1215) and the printer's instance (P3:1195-1196, `dRow` left center bits): at a call's star `P` and
translation `σ`, the pool request `C4Geo.poolReq P σ gates h Q ψ` (every mode's) meets `PoolReq.Pre` (sides and flips
of length `n`, both sides within the width), and the printer's fields meet `C3Req.Pre`'s geometry clauses
(`width ≤ 2·dRow`, `dRow` columns of `width` bits).
* `ofFn_filter_length`, **`nLeft_side`** (`= width`), **`nRight_side`** (`= n − width`), **`poolReq_pre`**;
* **`width_le_dRow`** (`2s ≤ b` for `s ≥ 3`; `s = 2` through `n − 3r ≥ r`), **`cols_lt`**.
Paper quantities of the main types: the halves of the star and the printer's rows and columns. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.C3Geo
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo NearCubicWires.WireExponent3_5.CompilerMachine

/-- The trues of `ofFn f` are the count `cnt` of `f` below `n`. -/
theorem ofFn_filter_length {n : ℕ} (f : Fin n → Bool) (x : ℕ) (hx : x ≤ n) :
    (((List.ofFn f).take x).filter id).length =
      PrimT.C4Geo.cnt (fun y => if h : y < n then f ⟨y, h⟩ else false) x := by
  induction x with
  | zero => simp [PrimT.C4Geo.cnt]
  | succ x ih =>
    rw [List.take_add_one, List.filter_append, List.length_append, ih (by omega)]
    have hx' : x < (List.ofFn f).length := by simp; omega
    rw [List.getElem?_eq_getElem hx']
    have hd : (if h : x < n then f ⟨x, h⟩ else false) = f ⟨x, by omega⟩ := dif_pos (by omega)
    simp only [PrimT.C4Geo.cnt, List.getElem_ofFn, Option.toList_some, List.filter_cons, List.filter_nil, hd]
    cases f ⟨x, by omega⟩ <;> simp

variable (P : StarParams)

theorem side_ofFn : (List.ofFn fun i : Fin P.n => (side P).getD i false) = List.ofFn P.centerSide := by
  congr 1; funext i; exact side_getD P i i.isLt

/-- **The left half has `width` coordinates.** -/
theorem nLeft_side : Pool.nLeft (side P) P.n = width P := by
  unfold Pool.nLeft
  rw [side_ofFn]
  have h := ofFn_filter_length P.centerSide P.n le_rfl
  rw [List.take_of_length_le (by simp)] at h
  rw [h, cnt_side]
  have h1 := rb_eq P
  have h2 := hL_le P
  unfold cntL width
  omega

theorem filter_not_length (l : List Bool) : (l.filter fun b => !b).length = l.length - (l.filter id).length := by
  have h := List.length_eq_length_filter_add (l := l) id
  simp only [id] at h ⊢
  omega

/-- **The right half has `n − width` coordinates.** -/
theorem nRight_side : Pool.nRight (side P) P.n = P.n - width P := by
  unfold Pool.nRight
  rw [filter_not_length, ← nLeft_side P]
  unfold Pool.nLeft
  simp

/-- **The pool request of every mode is admissible** (`PoolReq.Pre`). -/
theorem poolReq_pre (σ : P.Translation) (gates : List (NormalizedThresholdGate P.n)) (h Q psi : ℕ) :
    (poolReq P σ gates h Q psi).Pre := by
  refine ⟨by simp [poolReq, side], ?_, ?_, ?_⟩
  · intro f hf
    simp only [poolReq, flips, List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    simp only [List.length_ofFn]
    rfl
  · show Pool.nLeft (side P) P.n ≤ width P
    rw [nLeft_side]
  · show Pool.nRight (side P) P.n ≤ width P
    rw [nRight_side]
    have h1 := rb_eq P
    have h2 := hL_le P
    unfold width hL at *
    omega

theorem two_s_le (t : ℕ) (ht : 3 ≤ t) : 2 * t + 1 ≤ 2 ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge t 3 with h | h
    · interval_cases t <;> simp_all
    · have := ih h; rw [pow_succ]; omega

/-- **`width ≤ 2·dRow`** (the printer's instance). -/
theorem width_le_dRow : width P ≤ 2 * dRow P := by
  have hs2 := two_le_s P
  have hb := P.b_succ
  have h4 := P.four_r_le_n
  have hrb := P.r_mul_b_le
  have h1 := rb_eq P
  have hR : P.r = 2 * (P.r / 2) := by have := P.r_half_add; omega
  show P.r / 2 * P.b + hL P ≤ 2 * (P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2)
  unfold hL
  obtain ⟨R, hRd⟩ : ∃ R, R = P.r / 2 := ⟨_, rfl⟩
  rw [← hRd] at h1 hR ⊢
  rcases Nat.lt_or_ge P.s 3 with hs | hs
  · have hs' : P.s = 2 := by omega
    rw [hs'] at hb ⊢
    have hb3 : P.b = 3 := by norm_num at hb; omega
    rw [hb3] at h1 hrb ⊢
    omega
  · have hk := two_s_le P.s hs
    have hsb : 2 * P.s ≤ P.b := by omega
    have e1 : R * (P.b - P.s) + R * P.s = R * P.b := by rw [← Nat.mul_add]; congr 1; omega
    have e2 : 2 * (R * P.s) ≤ R * P.b := by
      calc 2 * (R * P.s) = R * (2 * P.s) := by ring
        _ ≤ R * P.b := Nat.mul_le_mul_left _ hsb
    omega

/-- **Every column fits the width.** -/
theorem cols_lt : ∀ c ∈ cols P, c < 2 ^ width P := by
  intro c hc
  simp only [cols, List.mem_map, List.mem_range] at hc
  obtain ⟨j, _, rfl⟩ := hc
  have h := PrimAsm.ParseNat.bitsValue_lt (colBits P j)
  rwa [show (colBits P j).length = width P by simp [colBits]] at h

end NearCubicWires.WireExponent3_5.FinalPass.C3Geo

