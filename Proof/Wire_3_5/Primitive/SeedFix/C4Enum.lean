import Proof.Wire_3_5.Primitive.SeedFix.C4Arm

/-! # SEEDFIX C4.L, the enumeration's context and its entry bank (samp:printable P3:2977-3055)

The enumeration of a child prefix `p'` (`SeedFix.JLink.sampEnum_run`, "print the conditional objective [...] of the
prefix", P3:2910-2923) runs in the context **`jX P ents TWd Cap p'`**: the sampler's parameters `P`, the prefix as
`plen = |p'|`, `pfx = listNum p'`, one capacity `Cap` for every scratch area, `cK = cC = 8ℓ`, the batch's entries.
From the minimal state **`S0`** its entry bank is **`jInit`**: framed zero words, unary rulers and blank areas, the
child prefix `frame p'` and `1^{8ℓ−|p'|} 0^{|p'|}` (**`jt_init`**). The arm (`C4Arm.armW_spec`) writes exactly the
words that are neither blank nor per-call constants.

Paper quantity of the main types: the enumeration's context of the child prefix `p'` (`plen`, `pfx = listNum p'`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Enum
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.SeedFix (JBody.JCtx JBody.JState Regs)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec (reps)

/-- **The enumeration's context of the child prefix `p'`.** -/
def jX (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap : ℕ) (p' : List Bool) : JBody.JCtx where
  P := P
  plen := p'.length
  pfx := SeedFix.listNum p'
  m := Cap
  c0 := Cap
  c1 := Cap
  c2 := Cap
  c3 := Cap
  c4 := Cap
  c5 := Cap
  c6 := Cap
  c7 := Cap
  cK := 8 * P.ell
  cC := 8 * P.ell
  TWd := TWd
  t := 0
  ents := ents
  tailB := []
  OB := []

/-- **The minimal state**: every register and area empty, the table register `T` blank of its width. -/
def S0 (P : SeedParams) : JBody.JState :=
  ⟨[], ⟨0, 0, 0, 0, 0, [], false, [], List.replicate (8 * (P.ell * (2 * P.ell + 1))) false⟩, [], [], [], false, [],
    false, [], [], [], [], 0, false⟩

theorem S0_ok (P : SeedParams) : (S0 P).R.Ok P.ell 8 := by
  refine ⟨by simp [S0], by simp [S0], by simp [S0]⟩

theorem binary_zero (k : ℕ) : binary k 0 = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [SignedSortKey.binary, ih, List.replicate_succ]

theorem binary_listNum : ∀ p : List Bool, binary p.length (SeedFix.listNum p) = p
  | [] => rfl
  | b :: p => by
    show (Nat.bit b (SeedFix.listNum p) % 2 == 1) :: binary p.length (Nat.bit b (SeedFix.listNum p) / 2) = b :: p
    rw [Nat.bit_div_two, binary_listNum p]
    cases b <;> simp [Nat.bit]

theorem fields8_zero (r : ℕ) : SeedFix.Split.fields8 r 0 = List.replicate 8 (List.replicate r false) := by
  simp [SeedFix.Split.fields8, binary_zero, List.map_const', List.length_range]

theorem flatMap_rep_frame (n : ℕ) (w : List Bool) :
    (List.replicate n w).flatMap frame = reps n (frame w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatMap_cons, ih]; simp [reps, List.replicate_succ]

/-! ## The counter's fields at `0` -/

section Fields
variable (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap : ℕ) (p' : List Bool)

theorem asJ_zero : (jX P ents TWd Cap p').asJ 0 = List.replicate 8 (List.replicate P.ell false) := by
  simp [JBody.JCtx.asJ, SeedFix.Split.alphasOf, fields8_zero, jX]

theorem alW_zero : (jX P ents TWd Cap p').alW 0 = reps 8 (frame (List.replicate P.ell false)) ++ [false] := by
  rw [JBody.JCtx.alW, asJ_zero, flatMap_rep_frame]

theorem digs_zero : SeedFix.Split.digsOf P.ell P.kh 0 = List.replicate 8 (List.replicate P.kh false) := by
  simp [SeedFix.Split.digsOf, fields8_zero]

theorem dgW_zero : (jX P ents TWd Cap p').dgW 0 = reps 8 (frame (List.replicate P.kh false)) ++ [false] := by
  simp only [JBody.JCtx.dgW, jX, digs_zero, flatMap_rep_frame]

theorem dnW_zero : (jX P ents TWd Cap p').dnW 0 = reps 8 (frame (List.replicate P.kh false)) ++ [false] := by
  simp only [JBody.JCtx.dnW, jX, digs_zero]
  rw [show (List.replicate 8 (List.replicate P.kh false)).tail ++
      [(List.replicate 8 (List.replicate P.kh false)).headD []] = List.replicate 8 (List.replicate P.kh false) by
    simp [List.replicate_succ]]
  rw [flatMap_rep_frame]

theorem cellW_zero (k : Fin 8) : SeedFix.Cells.cellW P 0 k = List.replicate (2 * P.kh) false := by
  unfold SeedFix.Cells.cellW
  have h : SeedFix.cellNumC (Shared.cellOf (by norm_num) (SeedFix.wOf P 0) k) = 0 := by
    have hw : ∀ i, (SeedFix.wOf P 0 i).val = 0 := fun i => by simp [SeedFix.wOf]
    unfold Shared.cellOf SeedFix.cellNumC
    split_ifs <;> simp [hw]
  rw [h, binary_zero]

theorem clW_zero : (jX P ents TWd Cap p').clW 0 = reps 8 (frame (List.replicate (2 * P.kh) false)) ++ [false] := by
  have h : (jX P ents TWd Cap p').csJ 0 = List.replicate 8 (List.replicate (2 * P.kh) false) := by
    simp only [JBody.JCtx.csJ, jX]
    rw [show (List.finRange 8).map (SeedFix.Cells.cellW P 0) = (List.finRange 8).map (fun _ =>
      List.replicate (2 * P.kh) false) from List.map_congr_left (fun k _ => cellW_zero P k)]
    simp
  rw [JBody.JCtx.clW, h, flatMap_rep_frame]

theorem cmpQ_zero (hQ : 1 ≤ P.Q) :
    SeedFix.Valid.cmpQ ((jX P ents TWd Cap p').q) (List.replicate P.ell false) = true := by
  have h := SeedFix.Valid.cmpQ_binary P.ell P.Q 0 hQ P.Q_le
  rw [binary_zero] at h
  simp only [JBody.JCtx.q, jX]
  rw [h]
  simp; omega

theorem validJ_zero (hQ : 1 ≤ P.Q) : (jX P ents TWd Cap p').validJ 0 = true := by
  simp only [JBody.JCtx.validJ, asJ_zero, List.all_replicate]
  rw [cmpQ_zero P ents TWd Cap p' hQ]
  simp

end Fields

/-! ## The entry bank -/

section Init
variable (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap : ℕ) (p' : List Bool)

/-- The zero word of width `k`. -/
abbrev zs (k : ℕ) : List Bool := List.replicate k false

/-- **The enumeration's entry bank** of the child prefix `p'` (the 60 words of `JT.toList`). -/
def jInit : List (List Bool) :=
  [frame (zs 8), reps 8 (frame (zs P.ell)) ++ [false], reps 8 (frame (zs P.kh)) ++ [false],
   reps 8 (frame (zs P.kh)) ++ [false], reps 8 (frame (zs (2 * P.kh))) ++ [false], frame (zs P.ell),
   frame (binary P.ell (P.Q - 1)), [true], [true], [true], [], frame (List.replicate 8 true), [false], [], [], [], [],
   SeedFix.blockWord ents ++ [], frame (zs (2 * P.kh + TWd)), frame (zs (2 * P.kh + TWd)), [false], frame (zs TWd),
   [false], List.replicate 8 true ++ [false], List.replicate P.ell true ++ [false],
   List.replicate P.kh true ++ [false], List.replicate 1 true ++ [false], List.replicate 7 true ++ [false],
   List.replicate (2 * P.kh) true ++ [false], frame (zs P.ell), frame (zs P.ell),
   zs (8 * (P.ell * (2 * P.ell + 1))) ++ zs Cap, frame (binary P.ell P.modulus), [], frame (zs P.ell),
   frame (zs P.ell), [false], frame p', frame (zs P.ell), [], [false], [false], [], frame (binary P.ell 1), [], [],
   zs (8 * P.ell), List.replicate (8 * P.ell - p'.length) true ++ zs p'.length, [false], [],
   zs Cap, zs Cap, zs Cap, zs Cap, zs Cap, zs Cap, zs Cap, zs Cap,
   zs (8 + 8 * P.ell + 8 * P.kh + 1), zs (8 + 8 * P.ell + 8 * P.kh + 1)]

theorem at_zero : SeedFix.SplitT.at_ (jX P ents TWd Cap p') (SeedFix.SplitT.tOf (jX P ents TWd Cap p') 0) =
    jX P ents TWd Cap p' := by
  simp [SeedFix.SplitT.at_, SeedFix.SplitT.tOf, jX]

/-- **The entry bank of the child's enumeration** is `jInit`. -/
theorem jt_init (hp : p'.length ≤ 8 * P.ell) (hQ : 1 ≤ P.Q) :
    ((SeedFix.SplitT.at_ (jX P ents TWd Cap p') (SeedFix.SplitT.tOf (jX P ents TWd Cap p') 0)).jt 0 (S0 P) [] 0).toList =
      jInit P ents TWd Cap p' := by
  rw [at_zero]
  simp only [JBody.JCtx.jt, SeedFix.JBank.JT.toList, alW_zero, dgW_zero, dnW_zero, clW_zero, asJ_zero,
    validJ_zero P ents TWd Cap p' hQ]
  have hlab : (List.replicate 8 (List.replicate P.ell false)).getD 7 [] = List.replicate P.ell false := by simp
  rw [hlab, cmpQ_zero P ents TWd Cap p' hQ]
  simp only [jInit, jX, S0, binary_zero, binary_listNum, RepairOrdinary.ZeroPadding.pad, List.length_replicate,
    List.length_nil, Nat.sub_zero, List.nil_append, JBody.JCtx.q, JBody.JCtx.Wt, JBody.JCtx.w]
  have hcc : 8 * P.ell - (8 * P.ell - p'.length) = p'.length := by omega
  rw [hcc]
  simp [StablePartition.Workspace.overlay, ListMachine.Rec.exprWord]
  all_goals rfl

end Init

end NearCubicWires.WireExponent3_5.PrimT.C4Enum
