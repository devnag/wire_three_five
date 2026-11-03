import Proof.SourceAssembly.SourceFactorSelMetaOps

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.MetaPipe
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
noncomputable section

/-- The pipeline's fixed constants: six `(exponent, coefficient)` pairs. -/
structure MC where
  mE : ℕ
  mC : ℕ
  hE : ℕ
  hC : ℕ
  tE : ℕ
  tC : ℕ
  sE : ℕ
  sC : ℕ
  vE : ℕ
  vC : ℕ
  rE : ℕ
  rC : ℕ

/-! ## 1. The registers -/

/-- Register 0: `q`. -/
def r0 (c : MC) (q K2 : ℕ) : ℕ := q
/-- Register 1: `K2 = 2K`. -/
def r1 (c : MC) (q K2 : ℕ) : ℕ := K2
def r2 (c : MC) (q K2 : ℕ) : ℕ := (r1 c q K2) / 2
def r3 (c : MC) (q K2 : ℕ) : ℕ := (r0 c q K2) / 2
def r4 (c : MC) (q K2 : ℕ) : ℕ := (r3 c q K2) / 2
def r5 (c : MC) (q K2 : ℕ) : ℕ := (r0 c q K2) - (r2 c q K2)
def r6 (c : MC) (q K2 : ℕ) : ℕ := NearCubicWires.BlockPlatform.UnaryCalc.value 0 200 (r0 c q K2)
def r7 (c : MC) (q K2 : ℕ) : ℕ := (r5 c q K2) / (r6 c q K2)
def r8 (c : MC) (q K2 : ℕ) : ℕ := (r7 c q K2) - (r2 c q K2)
def r9 (c : MC) (q K2 : ℕ) : ℕ := (r2 c q K2) + 2
def r10 (c : MC) (q K2 : ℕ) : ℕ := (r8 c q K2) / (r9 c q K2)
def r11 (c : MC) (q K2 : ℕ) : ℕ := (r0 c q K2) / (r6 c q K2)
def r12 (c : MC) (q K2 : ℕ) : ℕ := (r11 c q K2) / (r9 c q K2)
def r13 (c : MC) (q K2 : ℕ) : ℕ := NearCubicWires.BlockPlatform.UnaryCalc.value c.mE c.mC (r0 c q K2)
def r14 (c : MC) (q K2 : ℕ) : ℕ := Nat.clog 2 ((r13 c q K2) + 1)
def r15 (c : MC) (q K2 : ℕ) : ℕ := (r14 c q K2) + (r4 c q K2)
def r16 (c : MC) (q K2 : ℕ) : ℕ := NearCubicWires.BlockPlatform.UnaryCalc.value c.hE c.hC (r0 c q K2)
def r17 (c : MC) (q K2 : ℕ) : ℕ := Nat.clog 2 ((r16 c q K2) + 1)
def r18 (c : MC) (q K2 : ℕ) : ℕ := (r17 c q K2) + (r4 c q K2)
def r19 (c : MC) (q K2 : ℕ) : ℕ := NearCubicWires.BlockPlatform.UnaryCalc.value c.tE c.tC (r0 c q K2)
def r20 (c : MC) (q K2 : ℕ) : ℕ := Nat.clog 2 ((r19 c q K2) + 1)
def r21 (c : MC) (q K2 : ℕ) : ℕ := (r20 c q K2) + (r5 c q K2)
def r22 (c : MC) (q K2 : ℕ) : ℕ := NearCubicWires.BlockPlatform.UnaryCalc.value c.sE c.sC (r0 c q K2)
def r23 (c : MC) (q K2 : ℕ) : ℕ := Nat.clog 2 ((r22 c q K2) + 1)
def r24 (c : MC) (q K2 : ℕ) : ℕ := (r23 c q K2) + (r4 c q K2)
def r25 (c : MC) (q K2 : ℕ) : ℕ := max (r21 c q K2) (r24 c q K2)
def r26 (c : MC) (q K2 : ℕ) : ℕ := (r25 c q K2) + 1
def r27 (c : MC) (q K2 : ℕ) : ℕ := NearCubicWires.BlockPlatform.UnaryCalc.value c.vE c.vC (r0 c q K2)
def r28 (c : MC) (q K2 : ℕ) : ℕ := Nat.clog 2 ((r27 c q K2) + 1)
def r29 (c : MC) (q K2 : ℕ) : ℕ := (r28 c q K2) + (r5 c q K2)
def r30 (c : MC) (q K2 : ℕ) : ℕ := NearCubicWires.BlockPlatform.UnaryCalc.value c.rE c.rC (r0 c q K2)
def r31 (c : MC) (q K2 : ℕ) : ℕ := Nat.clog 2 ((r30 c q K2) + 1)
def r32 (c : MC) (q K2 : ℕ) : ℕ := (r31 c q K2) + (r4 c q K2)

/-- **All registers.** -/
def regs (c : MC) (q K2 : ℕ) : List ℕ :=
  [r0 c q K2, r1 c q K2, r2 c q K2, r3 c q K2, r4 c q K2, r5 c q K2, r6 c q K2, r7 c q K2, r8 c q K2, r9 c q K2, r10 c q K2, r11 c q K2, r12 c q K2, r13 c q K2, r14 c q K2, r15 c q K2, r16 c q K2, r17 c q K2, r18 c q K2, r19 c q K2, r20 c q K2, r21 c q K2, r22 c q K2, r23 c q K2, r24 c q K2, r25 c q K2, r26 c q K2, r27 c q K2, r28 c q K2, r29 c q K2, r30 c q K2, r31 c q K2, r32 c q K2]

/-! ## 2. The layout -/

/-- Stage `k`'s local tape count. -/
def nOf (c : MC) : ℕ → ℕ
  | 0 => halfOp.n
  | 1 => halfOp.n
  | 2 => halfOp.n
  | 3 => subOp.n
  | 4 => (polyOp 0 200).n
  | 5 => divOp.n
  | 6 => subOp.n
  | 7 => (plusOp 2).n
  | 8 => divOp.n
  | 9 => divOp.n
  | 10 => divOp.n
  | 11 => (polyOp c.mE c.mC).n
  | 12 => clog1Op.n
  | 13 => sumOp.n
  | 14 => (polyOp c.hE c.hC).n
  | 15 => clog1Op.n
  | 16 => sumOp.n
  | 17 => (polyOp c.tE c.tC).n
  | 18 => clog1Op.n
  | 19 => sumOp.n
  | 20 => (polyOp c.sE c.sC).n
  | 21 => clog1Op.n
  | 22 => sumOp.n
  | 23 => maxOp.n
  | 24 => (plusOp 1).n
  | 25 => (polyOp c.vE c.vC).n
  | 26 => clog1Op.n
  | 27 => sumOp.n
  | 28 => (polyOp c.rE c.rC).n
  | 29 => clog1Op.n
  | 30 => sumOp.n
  | _ => 0

/-- Stage `k`'s scratch block starts at `Sof c k`. -/
def Sof (c : MC) : ℕ → ℕ
  | 0 => 33
  | k + 1 => Sof c k + nOf c k

/-- **The universe.** -/
def NL (c : MC) : ℕ := Sof c 31

theorem Sof_mono (c : MC) (k : ℕ) : ∀ j, k ≤ j → Sof c k ≤ Sof c j := by
  intro j hj
  induction j with
  | zero =>
    rw [Nat.le_zero.mp hj]
  | succ j ih =>
    rcases Nat.lt_or_ge k (j + 1) with h | h
    · exact le_trans (ih (Nat.lt_succ_iff.mp h)) (Nat.le_add_right _ _)
    · rw [Nat.le_antisymm hj h]

theorem Sof_ge (c : MC) (k : ℕ) : 33 ≤ Sof c k := Sof_mono c 0 k (Nat.zero_le _)

theorem lt_NL (c : MC) (i : ℕ) (h : i < 33) : i < NL c := lt_of_lt_of_le h (Sof_ge c 31)

theorem hsOf (c : MC) (k : ℕ) (h : k < 31) : Sof c k + nOf c k ≤ NL c := Sof_mono c (k + 1) 31 h

/-! ## 3. The machine and its cost -/

/-- Stage 0's docked machine. -/
def mS0 (c : MC) := uM (NL := NL c) halfOp 1 2 (Sof c 0) (lt_NL c 1 (by decide)) (lt_NL c 2 (by decide)) (hsOf c 0 (by decide))
/-- Stage 1's docked machine. -/
def mS1 (c : MC) := uM (NL := NL c) halfOp 0 3 (Sof c 1) (lt_NL c 0 (by decide)) (lt_NL c 3 (by decide)) (hsOf c 1 (by decide))
/-- Stage 2's docked machine. -/
def mS2 (c : MC) := uM (NL := NL c) halfOp 3 4 (Sof c 2) (lt_NL c 3 (by decide)) (lt_NL c 4 (by decide)) (hsOf c 2 (by decide))
/-- Stage 3's docked machine. -/
def mS3 (c : MC) := bM (NL := NL c) subOp 0 2 5 (Sof c 3) (lt_NL c 0 (by decide)) (lt_NL c 2 (by decide)) (lt_NL c 5 (by decide)) (hsOf c 3 (by decide))
/-- Stage 4's docked machine. -/
def mS4 (c : MC) := uM (NL := NL c) (polyOp 0 200) 0 6 (Sof c 4) (lt_NL c 0 (by decide)) (lt_NL c 6 (by decide)) (hsOf c 4 (by decide))
/-- Stage 5's docked machine. -/
def mS5 (c : MC) := bM (NL := NL c) divOp 5 6 7 (Sof c 5) (lt_NL c 5 (by decide)) (lt_NL c 6 (by decide)) (lt_NL c 7 (by decide)) (hsOf c 5 (by decide))
/-- Stage 6's docked machine. -/
def mS6 (c : MC) := bM (NL := NL c) subOp 7 2 8 (Sof c 6) (lt_NL c 7 (by decide)) (lt_NL c 2 (by decide)) (lt_NL c 8 (by decide)) (hsOf c 6 (by decide))
/-- Stage 7's docked machine. -/
def mS7 (c : MC) := uM (NL := NL c) (plusOp 2) 2 9 (Sof c 7) (lt_NL c 2 (by decide)) (lt_NL c 9 (by decide)) (hsOf c 7 (by decide))
/-- Stage 8's docked machine. -/
def mS8 (c : MC) := bM (NL := NL c) divOp 8 9 10 (Sof c 8) (lt_NL c 8 (by decide)) (lt_NL c 9 (by decide)) (lt_NL c 10 (by decide)) (hsOf c 8 (by decide))
/-- Stage 9's docked machine. -/
def mS9 (c : MC) := bM (NL := NL c) divOp 0 6 11 (Sof c 9) (lt_NL c 0 (by decide)) (lt_NL c 6 (by decide)) (lt_NL c 11 (by decide)) (hsOf c 9 (by decide))
/-- Stage 10's docked machine. -/
def mS10 (c : MC) := bM (NL := NL c) divOp 11 9 12 (Sof c 10) (lt_NL c 11 (by decide)) (lt_NL c 9 (by decide)) (lt_NL c 12 (by decide)) (hsOf c 10 (by decide))
/-- Stage 11's docked machine. -/
def mS11 (c : MC) := uM (NL := NL c) (polyOp c.mE c.mC) 0 13 (Sof c 11) (lt_NL c 0 (by decide)) (lt_NL c 13 (by decide)) (hsOf c 11 (by decide))
/-- Stage 12's docked machine. -/
def mS12 (c : MC) := uM (NL := NL c) clog1Op 13 14 (Sof c 12) (lt_NL c 13 (by decide)) (lt_NL c 14 (by decide)) (hsOf c 12 (by decide))
/-- Stage 13's docked machine. -/
def mS13 (c : MC) := bM (NL := NL c) sumOp 14 4 15 (Sof c 13) (lt_NL c 14 (by decide)) (lt_NL c 4 (by decide)) (lt_NL c 15 (by decide)) (hsOf c 13 (by decide))
/-- Stage 14's docked machine. -/
def mS14 (c : MC) := uM (NL := NL c) (polyOp c.hE c.hC) 0 16 (Sof c 14) (lt_NL c 0 (by decide)) (lt_NL c 16 (by decide)) (hsOf c 14 (by decide))
/-- Stage 15's docked machine. -/
def mS15 (c : MC) := uM (NL := NL c) clog1Op 16 17 (Sof c 15) (lt_NL c 16 (by decide)) (lt_NL c 17 (by decide)) (hsOf c 15 (by decide))
/-- Stage 16's docked machine. -/
def mS16 (c : MC) := bM (NL := NL c) sumOp 17 4 18 (Sof c 16) (lt_NL c 17 (by decide)) (lt_NL c 4 (by decide)) (lt_NL c 18 (by decide)) (hsOf c 16 (by decide))
/-- Stage 17's docked machine. -/
def mS17 (c : MC) := uM (NL := NL c) (polyOp c.tE c.tC) 0 19 (Sof c 17) (lt_NL c 0 (by decide)) (lt_NL c 19 (by decide)) (hsOf c 17 (by decide))
/-- Stage 18's docked machine. -/
def mS18 (c : MC) := uM (NL := NL c) clog1Op 19 20 (Sof c 18) (lt_NL c 19 (by decide)) (lt_NL c 20 (by decide)) (hsOf c 18 (by decide))
/-- Stage 19's docked machine. -/
def mS19 (c : MC) := bM (NL := NL c) sumOp 20 5 21 (Sof c 19) (lt_NL c 20 (by decide)) (lt_NL c 5 (by decide)) (lt_NL c 21 (by decide)) (hsOf c 19 (by decide))
/-- Stage 20's docked machine. -/
def mS20 (c : MC) := uM (NL := NL c) (polyOp c.sE c.sC) 0 22 (Sof c 20) (lt_NL c 0 (by decide)) (lt_NL c 22 (by decide)) (hsOf c 20 (by decide))
/-- Stage 21's docked machine. -/
def mS21 (c : MC) := uM (NL := NL c) clog1Op 22 23 (Sof c 21) (lt_NL c 22 (by decide)) (lt_NL c 23 (by decide)) (hsOf c 21 (by decide))
/-- Stage 22's docked machine. -/
def mS22 (c : MC) := bM (NL := NL c) sumOp 23 4 24 (Sof c 22) (lt_NL c 23 (by decide)) (lt_NL c 4 (by decide)) (lt_NL c 24 (by decide)) (hsOf c 22 (by decide))
/-- Stage 23's docked machine. -/
def mS23 (c : MC) := bM (NL := NL c) maxOp 21 24 25 (Sof c 23) (lt_NL c 21 (by decide)) (lt_NL c 24 (by decide)) (lt_NL c 25 (by decide)) (hsOf c 23 (by decide))
/-- Stage 24's docked machine. -/
def mS24 (c : MC) := uM (NL := NL c) (plusOp 1) 25 26 (Sof c 24) (lt_NL c 25 (by decide)) (lt_NL c 26 (by decide)) (hsOf c 24 (by decide))
/-- Stage 25's docked machine. -/
def mS25 (c : MC) := uM (NL := NL c) (polyOp c.vE c.vC) 0 27 (Sof c 25) (lt_NL c 0 (by decide)) (lt_NL c 27 (by decide)) (hsOf c 25 (by decide))
/-- Stage 26's docked machine. -/
def mS26 (c : MC) := uM (NL := NL c) clog1Op 27 28 (Sof c 26) (lt_NL c 27 (by decide)) (lt_NL c 28 (by decide)) (hsOf c 26 (by decide))
/-- Stage 27's docked machine. -/
def mS27 (c : MC) := bM (NL := NL c) sumOp 28 5 29 (Sof c 27) (lt_NL c 28 (by decide)) (lt_NL c 5 (by decide)) (lt_NL c 29 (by decide)) (hsOf c 27 (by decide))
/-- Stage 28's docked machine. -/
def mS28 (c : MC) := uM (NL := NL c) (polyOp c.rE c.rC) 0 30 (Sof c 28) (lt_NL c 0 (by decide)) (lt_NL c 30 (by decide)) (hsOf c 28 (by decide))
/-- Stage 29's docked machine. -/
def mS29 (c : MC) := uM (NL := NL c) clog1Op 30 31 (Sof c 29) (lt_NL c 30 (by decide)) (lt_NL c 31 (by decide)) (hsOf c 29 (by decide))
/-- Stage 30's docked machine. -/
def mS30 (c : MC) := bM (NL := NL c) sumOp 31 4 32 (Sof c 30) (lt_NL c 31 (by decide)) (lt_NL c 4 (by decide)) (lt_NL c 32 (by decide)) (hsOf c 30 (by decide))

/-- **THE meta pipeline machine** (fixed per `c`). -/
def metaM (c : MC) :=
  Composition.machine (mS0 c) (Composition.machine (mS1 c) (Composition.machine (mS2 c) (Composition.machine (mS3 c) (Composition.machine (mS4 c) (Composition.machine (mS5 c) (Composition.machine (mS6 c) (Composition.machine (mS7 c) (Composition.machine (mS8 c) (Composition.machine (mS9 c) (Composition.machine (mS10 c) (Composition.machine (mS11 c) (Composition.machine (mS12 c) (Composition.machine (mS13 c) (Composition.machine (mS14 c) (Composition.machine (mS15 c) (Composition.machine (mS16 c) (Composition.machine (mS17 c) (Composition.machine (mS18 c) (Composition.machine (mS19 c) (Composition.machine (mS20 c) (Composition.machine (mS21 c) (Composition.machine (mS22 c) (Composition.machine (mS23 c) (Composition.machine (mS24 c) (Composition.machine (mS25 c) (Composition.machine (mS26 c) (Composition.machine (mS27 c) (Composition.machine (mS28 c) (Composition.machine (mS29 c) (mS30 c))))))))))))))))))))))))))))))

/-- **Its cost** at `q`, `K2`. -/
def metaCost (c : MC) (q K2 : ℕ) : ℕ :=
  halfOp.cost (r1 c q K2) + 1 + (halfOp.cost (r0 c q K2) + 1 + (halfOp.cost (r3 c q K2) + 1 + (subOp.cost (r0 c q K2) (r2 c q K2) + 1 + ((polyOp 0 200).cost (r0 c q K2) + 1 + (divOp.cost (r5 c q K2) (r6 c q K2) + 1 + (subOp.cost (r7 c q K2) (r2 c q K2) + 1 + ((plusOp 2).cost (r2 c q K2) + 1 + (divOp.cost (r8 c q K2) (r9 c q K2) + 1 + (divOp.cost (r0 c q K2) (r6 c q K2) + 1 + (divOp.cost (r11 c q K2) (r9 c q K2) + 1 + ((polyOp c.mE c.mC).cost (r0 c q K2) + 1 + (clog1Op.cost (r13 c q K2) + 1 + (sumOp.cost (r14 c q K2) (r4 c q K2) + 1 + ((polyOp c.hE c.hC).cost (r0 c q K2) + 1 + (clog1Op.cost (r16 c q K2) + 1 + (sumOp.cost (r17 c q K2) (r4 c q K2) + 1 + ((polyOp c.tE c.tC).cost (r0 c q K2) + 1 + (clog1Op.cost (r19 c q K2) + 1 + (sumOp.cost (r20 c q K2) (r5 c q K2) + 1 + ((polyOp c.sE c.sC).cost (r0 c q K2) + 1 + (clog1Op.cost (r22 c q K2) + 1 + (sumOp.cost (r23 c q K2) (r4 c q K2) + 1 + (maxOp.cost (r21 c q K2) (r24 c q K2) + 1 + ((plusOp 1).cost (r25 c q K2) + 1 + ((polyOp c.vE c.vC).cost (r0 c q K2) + 1 + (clog1Op.cost (r27 c q K2) + 1 + (sumOp.cost (r28 c q K2) (r5 c q K2) + 1 + ((polyOp c.rE c.rC).cost (r0 c q K2) + 1 + (clog1Op.cost (r30 c q K2) + 1 + (sumOp.cost (r31 c q K2) (r4 c q K2)))))))))))))))))))))))))))))))

theorem value_pos (D C x : ℕ) (hC : 0 < C) : 0 < NearCubicWires.BlockPlatform.UnaryCalc.value D C x :=
  Nat.mul_pos hC (Nat.pow_pos (Nat.succ_pos x))

/-! ## 4. The run -/

/-- **The meta pipeline run.** -/
theorem meta_run (c : MC) (R q K2 : ℕ) (E : Fin (NL c) → List Bool)
    (h0 : Inv R 33 ((regs c q K2).take 2) (Sof c 0) E) :
    ∃ E', Step (metaM c) (metaCost c q K2) (fun _ => 0) E (fun _ => 0) E' ∧
      Inv R 33 ((regs c q K2).take 33) (Sof c 31) E' := by
  obtain ⟨E1, s0, g1⟩ := ustage halfOp h0 1 2 (r1 c q K2) ((regs c q K2).take 3) rfl (by decide) rfl rfl (by decide) (Sof_ge c 0) (lt_NL c 1 (by decide)) (lt_NL c 2 (by decide)) (hsOf c 0 (by decide))
  have h1 : Inv R 33 ((regs c q K2).take 3) (Sof c 1) E1 := g1
  obtain ⟨E2, s1, g2⟩ := ustage halfOp h1 0 3 (r0 c q K2) ((regs c q K2).take 4) rfl (by decide) rfl rfl (by decide) (Sof_ge c 1) (lt_NL c 0 (by decide)) (lt_NL c 3 (by decide)) (hsOf c 1 (by decide))
  have h2 : Inv R 33 ((regs c q K2).take 4) (Sof c 2) E2 := g2
  obtain ⟨E3, s2, g3⟩ := ustage halfOp h2 3 4 (r3 c q K2) ((regs c q K2).take 5) rfl (by decide) rfl rfl (by decide) (Sof_ge c 2) (lt_NL c 3 (by decide)) (lt_NL c 4 (by decide)) (hsOf c 2 (by decide))
  have h3 : Inv R 33 ((regs c q K2).take 5) (Sof c 3) E3 := g3
  obtain ⟨E4, s3, g4⟩ := bstage subOp h3 0 2 5 (r0 c q K2) (r2 c q K2) ((regs c q K2).take 6) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 3) (lt_NL c 0 (by decide)) (lt_NL c 2 (by decide)) (lt_NL c 5 (by decide)) (hsOf c 3 (by decide))
  have h4 : Inv R 33 ((regs c q K2).take 6) (Sof c 4) E4 := g4
  obtain ⟨E5, s4, g5⟩ := ustage (polyOp 0 200) h4 0 6 (r0 c q K2) ((regs c q K2).take 7) rfl (by decide) rfl rfl (by decide) (Sof_ge c 4) (lt_NL c 0 (by decide)) (lt_NL c 6 (by decide)) (hsOf c 4 (by decide))
  have h5 : Inv R 33 ((regs c q K2).take 7) (Sof c 5) E5 := g5
  obtain ⟨E6, s5, g6⟩ := bstage divOp h5 5 6 7 (r5 c q K2) (r6 c q K2) ((regs c q K2).take 8) rfl (by decide) (by decide) (by decide) rfl rfl (value_pos 0 200 _ (by decide)) rfl (by decide) (Sof_ge c 5) (lt_NL c 5 (by decide)) (lt_NL c 6 (by decide)) (lt_NL c 7 (by decide)) (hsOf c 5 (by decide))
  have h6 : Inv R 33 ((regs c q K2).take 8) (Sof c 6) E6 := g6
  obtain ⟨E7, s6, g7⟩ := bstage subOp h6 7 2 8 (r7 c q K2) (r2 c q K2) ((regs c q K2).take 9) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 6) (lt_NL c 7 (by decide)) (lt_NL c 2 (by decide)) (lt_NL c 8 (by decide)) (hsOf c 6 (by decide))
  have h7 : Inv R 33 ((regs c q K2).take 9) (Sof c 7) E7 := g7
  obtain ⟨E8, s7, g8⟩ := ustage (plusOp 2) h7 2 9 (r2 c q K2) ((regs c q K2).take 10) rfl (by decide) rfl rfl (by decide) (Sof_ge c 7) (lt_NL c 2 (by decide)) (lt_NL c 9 (by decide)) (hsOf c 7 (by decide))
  have h8 : Inv R 33 ((regs c q K2).take 10) (Sof c 8) E8 := g8
  obtain ⟨E9, s8, g9⟩ := bstage divOp h8 8 9 10 (r8 c q K2) (r9 c q K2) ((regs c q K2).take 11) rfl (by decide) (by decide) (by decide) rfl rfl (Nat.succ_pos _) rfl (by decide) (Sof_ge c 8) (lt_NL c 8 (by decide)) (lt_NL c 9 (by decide)) (lt_NL c 10 (by decide)) (hsOf c 8 (by decide))
  have h9 : Inv R 33 ((regs c q K2).take 11) (Sof c 9) E9 := g9
  obtain ⟨E10, s9, g10⟩ := bstage divOp h9 0 6 11 (r0 c q K2) (r6 c q K2) ((regs c q K2).take 12) rfl (by decide) (by decide) (by decide) rfl rfl (value_pos 0 200 _ (by decide)) rfl (by decide) (Sof_ge c 9) (lt_NL c 0 (by decide)) (lt_NL c 6 (by decide)) (lt_NL c 11 (by decide)) (hsOf c 9 (by decide))
  have h10 : Inv R 33 ((regs c q K2).take 12) (Sof c 10) E10 := g10
  obtain ⟨E11, s10, g11⟩ := bstage divOp h10 11 9 12 (r11 c q K2) (r9 c q K2) ((regs c q K2).take 13) rfl (by decide) (by decide) (by decide) rfl rfl (Nat.succ_pos _) rfl (by decide) (Sof_ge c 10) (lt_NL c 11 (by decide)) (lt_NL c 9 (by decide)) (lt_NL c 12 (by decide)) (hsOf c 10 (by decide))
  have h11 : Inv R 33 ((regs c q K2).take 13) (Sof c 11) E11 := g11
  obtain ⟨E12, s11, g12⟩ := ustage (polyOp c.mE c.mC) h11 0 13 (r0 c q K2) ((regs c q K2).take 14) rfl (by decide) rfl rfl (by decide) (Sof_ge c 11) (lt_NL c 0 (by decide)) (lt_NL c 13 (by decide)) (hsOf c 11 (by decide))
  have h12 : Inv R 33 ((regs c q K2).take 14) (Sof c 12) E12 := g12
  obtain ⟨E13, s12, g13⟩ := ustage clog1Op h12 13 14 (r13 c q K2) ((regs c q K2).take 15) rfl (by decide) rfl rfl (by decide) (Sof_ge c 12) (lt_NL c 13 (by decide)) (lt_NL c 14 (by decide)) (hsOf c 12 (by decide))
  have h13 : Inv R 33 ((regs c q K2).take 15) (Sof c 13) E13 := g13
  obtain ⟨E14, s13, g14⟩ := bstage sumOp h13 14 4 15 (r14 c q K2) (r4 c q K2) ((regs c q K2).take 16) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 13) (lt_NL c 14 (by decide)) (lt_NL c 4 (by decide)) (lt_NL c 15 (by decide)) (hsOf c 13 (by decide))
  have h14 : Inv R 33 ((regs c q K2).take 16) (Sof c 14) E14 := g14
  obtain ⟨E15, s14, g15⟩ := ustage (polyOp c.hE c.hC) h14 0 16 (r0 c q K2) ((regs c q K2).take 17) rfl (by decide) rfl rfl (by decide) (Sof_ge c 14) (lt_NL c 0 (by decide)) (lt_NL c 16 (by decide)) (hsOf c 14 (by decide))
  have h15 : Inv R 33 ((regs c q K2).take 17) (Sof c 15) E15 := g15
  obtain ⟨E16, s15, g16⟩ := ustage clog1Op h15 16 17 (r16 c q K2) ((regs c q K2).take 18) rfl (by decide) rfl rfl (by decide) (Sof_ge c 15) (lt_NL c 16 (by decide)) (lt_NL c 17 (by decide)) (hsOf c 15 (by decide))
  have h16 : Inv R 33 ((regs c q K2).take 18) (Sof c 16) E16 := g16
  obtain ⟨E17, s16, g17⟩ := bstage sumOp h16 17 4 18 (r17 c q K2) (r4 c q K2) ((regs c q K2).take 19) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 16) (lt_NL c 17 (by decide)) (lt_NL c 4 (by decide)) (lt_NL c 18 (by decide)) (hsOf c 16 (by decide))
  have h17 : Inv R 33 ((regs c q K2).take 19) (Sof c 17) E17 := g17
  obtain ⟨E18, s17, g18⟩ := ustage (polyOp c.tE c.tC) h17 0 19 (r0 c q K2) ((regs c q K2).take 20) rfl (by decide) rfl rfl (by decide) (Sof_ge c 17) (lt_NL c 0 (by decide)) (lt_NL c 19 (by decide)) (hsOf c 17 (by decide))
  have h18 : Inv R 33 ((regs c q K2).take 20) (Sof c 18) E18 := g18
  obtain ⟨E19, s18, g19⟩ := ustage clog1Op h18 19 20 (r19 c q K2) ((regs c q K2).take 21) rfl (by decide) rfl rfl (by decide) (Sof_ge c 18) (lt_NL c 19 (by decide)) (lt_NL c 20 (by decide)) (hsOf c 18 (by decide))
  have h19 : Inv R 33 ((regs c q K2).take 21) (Sof c 19) E19 := g19
  obtain ⟨E20, s19, g20⟩ := bstage sumOp h19 20 5 21 (r20 c q K2) (r5 c q K2) ((regs c q K2).take 22) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 19) (lt_NL c 20 (by decide)) (lt_NL c 5 (by decide)) (lt_NL c 21 (by decide)) (hsOf c 19 (by decide))
  have h20 : Inv R 33 ((regs c q K2).take 22) (Sof c 20) E20 := g20
  obtain ⟨E21, s20, g21⟩ := ustage (polyOp c.sE c.sC) h20 0 22 (r0 c q K2) ((regs c q K2).take 23) rfl (by decide) rfl rfl (by decide) (Sof_ge c 20) (lt_NL c 0 (by decide)) (lt_NL c 22 (by decide)) (hsOf c 20 (by decide))
  have h21 : Inv R 33 ((regs c q K2).take 23) (Sof c 21) E21 := g21
  obtain ⟨E22, s21, g22⟩ := ustage clog1Op h21 22 23 (r22 c q K2) ((regs c q K2).take 24) rfl (by decide) rfl rfl (by decide) (Sof_ge c 21) (lt_NL c 22 (by decide)) (lt_NL c 23 (by decide)) (hsOf c 21 (by decide))
  have h22 : Inv R 33 ((regs c q K2).take 24) (Sof c 22) E22 := g22
  obtain ⟨E23, s22, g23⟩ := bstage sumOp h22 23 4 24 (r23 c q K2) (r4 c q K2) ((regs c q K2).take 25) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 22) (lt_NL c 23 (by decide)) (lt_NL c 4 (by decide)) (lt_NL c 24 (by decide)) (hsOf c 22 (by decide))
  have h23 : Inv R 33 ((regs c q K2).take 25) (Sof c 23) E23 := g23
  obtain ⟨E24, s23, g24⟩ := bstage maxOp h23 21 24 25 (r21 c q K2) (r24 c q K2) ((regs c q K2).take 26) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 23) (lt_NL c 21 (by decide)) (lt_NL c 24 (by decide)) (lt_NL c 25 (by decide)) (hsOf c 23 (by decide))
  have h24 : Inv R 33 ((regs c q K2).take 26) (Sof c 24) E24 := g24
  obtain ⟨E25, s24, g25⟩ := ustage (plusOp 1) h24 25 26 (r25 c q K2) ((regs c q K2).take 27) rfl (by decide) rfl rfl (by decide) (Sof_ge c 24) (lt_NL c 25 (by decide)) (lt_NL c 26 (by decide)) (hsOf c 24 (by decide))
  have h25 : Inv R 33 ((regs c q K2).take 27) (Sof c 25) E25 := g25
  obtain ⟨E26, s25, g26⟩ := ustage (polyOp c.vE c.vC) h25 0 27 (r0 c q K2) ((regs c q K2).take 28) rfl (by decide) rfl rfl (by decide) (Sof_ge c 25) (lt_NL c 0 (by decide)) (lt_NL c 27 (by decide)) (hsOf c 25 (by decide))
  have h26 : Inv R 33 ((regs c q K2).take 28) (Sof c 26) E26 := g26
  obtain ⟨E27, s26, g27⟩ := ustage clog1Op h26 27 28 (r27 c q K2) ((regs c q K2).take 29) rfl (by decide) rfl rfl (by decide) (Sof_ge c 26) (lt_NL c 27 (by decide)) (lt_NL c 28 (by decide)) (hsOf c 26 (by decide))
  have h27 : Inv R 33 ((regs c q K2).take 29) (Sof c 27) E27 := g27
  obtain ⟨E28, s27, g28⟩ := bstage sumOp h27 28 5 29 (r28 c q K2) (r5 c q K2) ((regs c q K2).take 30) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 27) (lt_NL c 28 (by decide)) (lt_NL c 5 (by decide)) (lt_NL c 29 (by decide)) (hsOf c 27 (by decide))
  have h28 : Inv R 33 ((regs c q K2).take 30) (Sof c 28) E28 := g28
  obtain ⟨E29, s28, g29⟩ := ustage (polyOp c.rE c.rC) h28 0 30 (r0 c q K2) ((regs c q K2).take 31) rfl (by decide) rfl rfl (by decide) (Sof_ge c 28) (lt_NL c 0 (by decide)) (lt_NL c 30 (by decide)) (hsOf c 28 (by decide))
  have h29 : Inv R 33 ((regs c q K2).take 31) (Sof c 29) E29 := g29
  obtain ⟨E30, s29, g30⟩ := ustage clog1Op h29 30 31 (r30 c q K2) ((regs c q K2).take 32) rfl (by decide) rfl rfl (by decide) (Sof_ge c 29) (lt_NL c 30 (by decide)) (lt_NL c 31 (by decide)) (hsOf c 29 (by decide))
  have h30 : Inv R 33 ((regs c q K2).take 32) (Sof c 30) E30 := g30
  obtain ⟨E31, s30, g31⟩ := bstage sumOp h30 31 4 32 (r31 c q K2) (r4 c q K2) ((regs c q K2).take 33) rfl (by decide) (by decide) (by decide) rfl rfl trivial rfl (by decide) (Sof_ge c 30) (lt_NL c 31 (by decide)) (lt_NL c 4 (by decide)) (lt_NL c 32 (by decide)) (hsOf c 30 (by decide))
  have h31 : Inv R 33 ((regs c q K2).take 33) (Sof c 31) E31 := g31
  exact ⟨E31, s0.seq (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq (s18.seq (s19.seq (s20.seq (s21.seq (s22.seq (s23.seq (s24.seq (s25.seq (s26.seq (s27.seq (s28.seq (s29.seq (s30)))))))))))))))))))))))))))))), h31⟩

end
end NearCubicWires.SourceFactorSel.MetaPipe

