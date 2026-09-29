import Proof.Wire_3_5.Primitive.SeedFix.C4KWi

/-! # C4KW, part 10: stage B1's data (the rulers, the emission table) and its checks

B1 writes the 90 kept words `oB1 j` (every kept word but `3, 4, 5, 71`) on a streams-only layout of 115 streams:
the outputs `0 … 89`, the inputs `90 … 97` (`1^ℓ₀, 1^t, 1^J, 1^G, 1^N, 1^{nE}, 1^{cap}, 1^{|pops|}`), the rulers
`98 … 114`: the eight input counts, then `2t`, `2t·ℓ₀`, `L = 2t + 2t·ℓ₀`, `0`, `N`, `N²`, `2ℓ₀ + 1`,
`2t·ℓ₀(2ℓ₀ + 1)` (the elimination's register word) and that plus `cap` (**`rvB`**, **`stpB`**, **`stpB_ok`**).
The emission table **`emsB`** has one emission per output; **`emsB_word`**: its word is the kept word
`kw D cap (oB1 j)`, the Hb printer's static word before cell `0` (the word state's streams and registers, the log,
the elimination's own tapes at `R0`). **`rvB_le`**: every ruler value is at most `6(kwT + 1)³ + cap`.

Paper quantity of the main type: the Hb printer's static words (P3:2253-2290) as functions of the call's numbers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B1
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4KW

noncomputable section

/-- **B1's ruler values** (streams `98 … 114`). -/
def rvB (D : HashData) (cap : ℕ) (i : Fin 115) : ℕ :=
  match i.val with
  | 98 => D.MP.ell0
  | 99 => D.MP.t
  | 100 => D.MP.J
  | 101 => D.G
  | 102 => D.N
  | 103 => D.nE
  | 104 => cap
  | 105 => D.pops.length
  | 106 => 2 * D.MP.t
  | 107 => 2 * D.MP.t * D.MP.ell0
  | 108 => 2 * D.MP.t + 2 * D.MP.t * D.MP.ell0
  | 109 => 0
  | 110 => D.N
  | 111 => D.N ^ 2
  | 112 => 2 * D.MP.ell0 + 1
  | 113 => 2 * D.MP.t * (D.MP.ell0 * (2 * D.MP.ell0 + 1))
  | 114 => 2 * D.MP.t * (D.MP.ell0 * (2 * D.MP.ell0 + 1)) + cap
  | _ => 0

/-- **B1's ruler steps.** -/
def stpB (k : ℕ) : RS 114 :=
  match k with
  | 0 => .mkI 90
  | 1 => .mkI 91
  | 2 => .mkI 92
  | 3 => .mkI 93
  | 4 => .mkI 94
  | 5 => .mkI 95
  | 6 => .mkI 96
  | 7 => .mkI 97
  | 8 => .ap 99 99 0
  | 9 => .mul 106 98
  | 10 => .ap 106 107 0
  | 11 => .zero
  | 12 => .ap 102 109 0
  | 13 => .mul 102 110
  | 14 => .ap 98 98 1
  | 15 => .mul 107 112
  | 16 => .ap 113 104 0
  | _ => .zero

/-- **B1's emission table** (output `j` holds kept word `oB1 j`). -/
def emsL : List (Em 114) :=
  [.c [],
   .c [false],
   .c [],
   .u 108 false [false] [],
   .u 100 false [false] [],
   .u 105 true [false] [],
   .u 103 true [false] [],
   .u 111 true [false] [],
   .c [],
   .c [false],
   .c [],
   .c [false],
   .dec 105 103 102,
   .u 106 false [true] [],
   .u 98 false [true] [],
   .u 100 false [true] [],
   .u 101 false [true] [],
   .u 111 true [true] [],
   .u 103 true [true] [],
   .u 105 true [true] [],
   .u 108 false [true] [],
   .c [],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [false],
   .u 104 false [false] [],
   .u 106 false [true] [false],
   .u 98 false [true] [false],
   .u 98 false [true, false] [false],
   .u 98 false [true, false] [false],
   .u 114 false [false] [],
   .c [],
   .u 98 false [true, false] [false],
   .u 98 false [true, false] [false],
   .c [false],
   .u 104 false [false] [],
   .u 104 false [false] [],
   .u 104 false [false] [],
   .u 104 false [false] [],
   .c [false],
   .u 98 false [true, false] [false],
   .c [],
   .c [false],
   .c [false],
   .c [],
   .bin 98,
   .u 104 false [false] [],
   .u 104 false [false] [],
   .u 104 false [false] [],
   .c [],
   .c [],
   .u 104 false [false] [],
   .pad 107 104]

def emsB (j : ℕ) : Em 114 := emsL.getD j (.c [])

theorem emsB_ok : ∀ j, j < 90 → (emsB j).okb 98 = true := by decide

theorem hbn_eq (D : HashData) (cap : ℕ) :
    (hbX D (FinalPass.HashFr.capsOf cap) 0 0).n = 2 ^ (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) * (D.MP.J + 1) * D.pops.length * D.nE * D.N ^ 2 := rfl

theorem dec_eq (D : HashData) (cap : ℕ) :
    [decide (D.pops.length ≠ 0 ∧ D.nE ≠ 0 ∧ D.N ≠ 0)] = [decide (0 < (hbX D (FinalPass.HashFr.capsOf cap) 0 0).n)] := by
  rw [hbn_eq]
  have e : (D.pops.length ≠ 0 ∧ D.nE ≠ 0 ∧ D.N ≠ 0) ↔
      0 < 2 ^ (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) * (D.MP.J + 1) * D.pops.length * D.nE * D.N ^ 2 := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.succ_pos _))
        (Nat.pos_of_ne_zero h1)) (Nat.pos_of_ne_zero h2)) (pow_pos (Nat.pos_of_ne_zero h3) 2)
    · intro h
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> rw [e] at h <;> simp at h
  exact congrArg (fun b => [b]) (decide_eq_decide.mpr e)

/-- **The emission table writes the kept words.** -/
theorem emsB_word (D : HashData) (cap : ℕ) : ∀ j : Fin 90, (emsB j.val).word (rvB D cap) = kw D cap (oB1 j) := by
  intro j
  fin_cases j
  · rfl
  · rfl
  · rfl
  · show repW (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0 - 0) [false] ++ [] = SignedSortKey.binary (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) 0
    simp [repW_single, binary_zero_rep]
  · show repW (D.MP.J - 0) [false] ++ [] = HbM.unary 0 (D.MP.J + 1)
    simp [repW_single, HbM.unary]
  · show repW (D.pops.length - 1) [false] ++ [] = HbM.unary 0 D.pops.length
    simp [repW_single, HbM.unary]
  · show repW (D.nE - 1) [false] ++ [] = HbM.unary 0 D.nE
    simp [repW_single, HbM.unary]
  · show repW (D.N ^ 2 - 1) [false] ++ [] = HbM.unary 0 (D.N ^ 2)
    simp [repW_single, HbM.unary]
  · rfl
  · rfl
  · rfl
  · rfl
  · show [decide (D.pops.length ≠ 0 ∧ D.nE ≠ 0 ∧ D.N ≠ 0)] = [decide (0 < (hbX D (FinalPass.HashFr.capsOf cap) 0 0).n)]
    exact dec_eq D cap
  · show repW (2 * D.MP.t - 0) [true] ++ [] = List.replicate (2 * D.MP.t) true
    simp [repW_single]
  · show repW (D.MP.ell0 - 0) [true] ++ [] = List.replicate D.MP.ell0 true
    simp [repW_single]
  · show repW (D.MP.J - 0) [true] ++ [] = List.replicate D.MP.J true
    simp [repW_single]
  · show repW (D.G - 0) [true] ++ [] = List.replicate D.G true
    simp [repW_single]
  · show repW (D.N ^ 2 - 1) [true] ++ [] = List.replicate (D.N ^ 2 - 1) true
    simp [repW_single]
  · show repW (D.nE - 1) [true] ++ [] = List.replicate (D.nE - 1) true
    simp [repW_single]
  · show repW (D.pops.length - 1) [true] ++ [] = List.replicate (D.pops.length - 1) true
    simp [repW_single]
  · show repW (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0 - 0) [true] ++ [] = List.replicate (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) true
    simp [repW_single]
  · rfl
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [false] = FinalPass.Tm.regTape cap 0
    simp [repW_single, FinalPass.Tm.regTape, List.replicate_succ]
  · show repW (cap - 0) [false] ++ [] = List.replicate cap false
    simp [repW_single]
  · show repW (2 * D.MP.t - 0) [true] ++ [false] = List.replicate (2 * D.MP.t) true ++ [false]
    simp [repW_single]
  · show repW (D.MP.ell0 - 0) [true] ++ [false] = List.replicate D.MP.ell0 true ++ [false]
    simp [repW_single]
  · show repW (D.MP.ell0 - 0) [true, false] ++ [false] = frame (SignedSortKey.binary D.MP.ell0 0)
    simp [binary_zero_rep, frame_rep_false]
  · show repW (D.MP.ell0 - 0) [true, false] ++ [false] = frame (SignedSortKey.binary D.MP.ell0 0)
    simp [binary_zero_rep, frame_rep_false]
  · show repW (2 * D.MP.t * (D.MP.ell0 * (2 * D.MP.ell0 + 1)) + cap - 0) [false] ++ [] = List.replicate (2 * D.MP.t * (D.MP.ell0 * (2 * D.MP.ell0 + 1))) false ++ List.replicate cap false
    rw [Nat.sub_zero, List.append_nil, repW_single, List.replicate_add]
  · rfl
  · show repW (D.MP.ell0 - 0) [true, false] ++ [false] = frame (SignedSortKey.binary D.MP.ell0 0)
    simp [binary_zero_rep, frame_rep_false]
  · show repW (D.MP.ell0 - 0) [true, false] ++ [false] = frame (SignedSortKey.binary D.MP.ell0 0)
    simp [binary_zero_rep, frame_rep_false]
  · rfl
  · show repW (cap - 0) [false] ++ [] = List.replicate cap false
    simp [repW_single]
  · show repW (cap - 0) [false] ++ [] = List.replicate cap false
    simp [repW_single]
  · show repW (cap - 0) [false] ++ [] = List.replicate cap false
    simp [repW_single]
  · show repW (cap - 0) [false] ++ [] = List.replicate cap false
    simp [repW_single]
  · rfl
  · show repW (D.MP.ell0 - 0) [true, false] ++ [false] = frame (SignedSortKey.binary D.MP.ell0 0)
    simp [binary_zero_rep, frame_rep_false]
  · rfl
  · rfl
  · rfl
  · rfl
  · show bin1W D.MP.ell0 = frame (SignedSortKey.binary D.MP.ell0 1)
    exact bin1W_eq _
  · show repW (cap - 0) [false] ++ [] = List.replicate cap false
    simp [repW_single]
  · show repW (cap - 0) [false] ++ [] = List.replicate cap false
    simp [repW_single]
  · show repW (cap - 0) [false] ++ [] = List.replicate cap false
    simp [repW_single]
  · rfl
  · rfl
  · show repW (cap - 0) [false] ++ [] = ZeroPadding.pad cap []
    simp [repW_single, ZeroPadding.pad]
  · show padW (2 * D.MP.t * D.MP.ell0) cap = ZeroPadding.pad cap (List.replicate (2 * D.MP.t * D.MP.ell0 - 0) true)
    exact padW_eq _ _

/-- **B1's ruler steps are well formed** (their operands done, their values the ruler values). -/
theorem stpB_ok (D : HashData) (cap : ℕ) :
    ∀ k, k < 17 → (stpB k).ok 90 98 (stIn (no := 90) iB1 D cap) (rvB D cap) stpB k := by
  intro k hk
  interval_cases k
  · dsimp only [stpB, RS.ok]; exact ⟨by decide, by decide, by decide, rfl⟩
  · dsimp only [stpB, RS.ok]; exact ⟨by decide, by decide, by decide, rfl⟩
  · dsimp only [stpB, RS.ok]; exact ⟨by decide, by decide, by decide, rfl⟩
  · dsimp only [stpB, RS.ok]; exact ⟨by decide, by decide, by decide, rfl⟩
  · dsimp only [stpB, RS.ok]; exact ⟨by decide, by decide, by decide, rfl⟩
  · dsimp only [stpB, RS.ok]; exact ⟨by decide, by decide, by decide, rfl⟩
  · dsimp only [stpB, RS.ok]; exact ⟨by decide, by decide, by decide, rfl⟩
  · dsimp only [stpB, RS.ok]; exact ⟨by decide, by decide, by decide, rfl⟩
  · dsimp only [stpB, RS.ok]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    show 2 * D.MP.t = D.MP.t + D.MP.t + 0
    omega
  · dsimp only [stpB, RS.ok]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    show 2 * D.MP.t * D.MP.ell0 = 2 * D.MP.t * D.MP.ell0
    rfl
  · dsimp only [stpB, RS.ok]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    show 2 * D.MP.t + 2 * D.MP.t * D.MP.ell0 = 2 * D.MP.t + 2 * D.MP.t * D.MP.ell0 + 0
    rfl
  · dsimp only [stpB, RS.ok]; rfl
  · dsimp only [stpB, RS.ok]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    show D.N = D.N + 0 + 0
    rfl
  · dsimp only [stpB, RS.ok]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    show D.N ^ 2 = D.N * D.N
    exact sq _
  · dsimp only [stpB, RS.ok]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    show 2 * D.MP.ell0 + 1 = D.MP.ell0 + D.MP.ell0 + 1
    omega
  · dsimp only [stpB, RS.ok]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    show 2 * D.MP.t * (D.MP.ell0 * (2 * D.MP.ell0 + 1)) = 2 * D.MP.t * D.MP.ell0 * (2 * D.MP.ell0 + 1)
    ring
  · dsimp only [stpB, RS.ok]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    show 2 * D.MP.t * (D.MP.ell0 * (2 * D.MP.ell0 + 1)) + cap = 2 * D.MP.t * (D.MP.ell0 * (2 * D.MP.ell0 + 1)) + cap + 0
    rfl

/-- **Every ruler value is at most `6(kwT + 1)³ + cap`.** -/
theorem rvB_le (D : HashData) (cap : ℕ) : ∀ i, rvB D cap i ≤ 6 * (kwT D + 1) ^ 3 + cap := by
  intro i
  set T := kwT D with hT
  have hl : D.MP.ell0 ≤ T := by rw [hT]; unfold kwT; omega
  have ht : D.MP.t ≤ T := by rw [hT]; unfold kwT; omega
  have hJ : D.MP.J ≤ T := by rw [hT]; unfold kwT; omega
  have hG : D.G ≤ T := by rw [hT]; unfold kwT; omega
  have hN : D.N ≤ T := by rw [hT]; unfold kwT; omega
  have hE : D.nE ≤ T := by rw [hT]; unfold kwT; omega
  have hP : D.pops.length ≤ T := by rw [hT]; unfold kwT; omega
  have a1 : T + 1 ≤ (T + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have a2 : (T + 1) ^ 2 ≤ (T + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hsq : D.N ^ 2 ≤ (T + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have htl : 2 * D.MP.t * D.MP.ell0 ≤ 2 * (T + 1) ^ 2 := by
    have := Nat.mul_le_mul ht hl; nlinarith
  have hR : 2 * D.MP.t * (D.MP.ell0 * (2 * D.MP.ell0 + 1)) ≤ 6 * (T + 1) ^ 3 := by
    have h1 := Nat.mul_le_mul hl (show 2 * D.MP.ell0 + 1 ≤ 3 * (T + 1) by omega)
    have h2 := Nat.mul_le_mul (show 2 * D.MP.t ≤ 2 * (T + 1) by omega) h1
    nlinarith
  unfold rvB
  split <;> omega

end

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B1
