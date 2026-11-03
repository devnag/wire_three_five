import Proof.Packets.SrcStartStages
import Proof.SourceAssembly.SourceFactorSelItem4Bank

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Bank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. The layout -/

/-- The tail size (a closed function of `a`; here a constant). -/
def kOf (_a : DecompositionAlgorithm) : ℕ := 194

theorem kOf_eq (a : DecompositionAlgorithm) : kOf a = 194 := rfl

theorem base_eq (a : DecompositionAlgorithm) : Cold.Base a = SB a + 14 := rfl

theorem tapes_ge (a : DecompositionAlgorithm) : SB a + 28 ≤ Cold.tapes a := by
  simp only [Cold.tapes, Cold.Base, Cold.Power, CT, T, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]
  omega

/-- A tail tape. -/
def tl (a : DecompositionAlgorithm) (o : ℕ) (h : o < 194) : Fin (132 + Cold.tapes a + kOf a) :=
  ⟨132 + Cold.tapes a + o, by rw [kOf_eq]; omega⟩

/-- A bank tape. -/
def bk (a : DecompositionAlgorithm) (i : ℕ) (h : i < 132 + Cold.tapes a) : Fin (132 + Cold.tapes a + kOf a) :=
  ⟨i, by rw [kOf_eq]; omega⟩

@[simp] theorem tl_val (a : DecompositionAlgorithm) (o : ℕ) (h : o < 194) : (tl a o h).val = 132 + Cold.tapes a + o := rfl
@[simp] theorem bk_val (a : DecompositionAlgorithm) (i : ℕ) (h : i < 132 + Cold.tapes a) : (bk a i h).val = i := rfl

/-- The template tape (Cold `SB + 10`) and the capacity tape (Cold `Base`) of the bank. -/
def tT (a : DecompositionAlgorithm) : Fin (132 + Cold.tapes a + kOf a) := bk a (132 + SB a + 10) (by have := tapes_ge a; omega)
def tP (a : DecompositionAlgorithm) : Fin (132 + Cold.tapes a + kOf a) := bk a (132 + Cold.Base a) (by rw [base_eq]; have := tapes_ge a; omega)

@[simp] theorem tT_val (a : DecompositionAlgorithm) : (tT a).val = 132 + SB a + 10 := rfl
@[simp] theorem tP_val (a : DecompositionAlgorithm) : (tP a).val = 132 + SB a + 14 := rfl

/-- The input ports (agreed: `inPort j = ⟨j, _⟩`). -/
def inPortB (a : DecompositionAlgorithm) (j : Fin 5) : Fin (kOf a) := ⟨j.val, by rw [kOf_eq]; omega⟩

theorem inPortB_val (a : DecompositionAlgorithm) (j : Fin 5) : (inPortB a j).val = j.val := rfl

theorem inPortB_inj (a : DecompositionAlgorithm) : Function.Injective (inPortB a) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa only [inPortB_val] using hv

theorem natAdd_in (a : DecompositionAlgorithm) (j : Fin 5) :
    Fin.natAdd (132 + Cold.tapes a) (inPortB a j) = tl a j.val (by omega) := Fin.ext rfl

/-! ## 2. The slot maps of the many-tape stages -/

/-- The stream extractor (54 tapes + its log): tape `0` is the frame copy (5), tape `1` the stream (the producer's tape 64, at 160),
the rest fresh (`8..60`). -/
def sST (a : DecompositionAlgorithm) (j : Fin 55) : Fin (132 + Cold.tapes a + kOf a) :=
  if j.val = 0 then tl a 5 (by omega) else if j.val = 1 then tl a 160 (by omega) else tl a (6 + j.val) (by omega)

theorem sST_val (a : DecompositionAlgorithm) (j : Fin 55) :
    (sST a j).val = if j.val = 0 then 132 + Cold.tapes a + 5 else if j.val = 1 then 132 + Cold.tapes a + 160
      else 132 + Cold.tapes a + (6 + j.val) := by
  unfold sST; split_ifs <;> rfl

theorem sST_spec (a : DecompositionAlgorithm) (j : Fin 55) :
    (j.val = 0 ∧ (sST a j).val = 132 + Cold.tapes a + 5) ∨ (j.val = 1 ∧ (sST a j).val = 132 + Cold.tapes a + 160) ∨
      (j.val ≠ 0 ∧ j.val ≠ 1 ∧ (sST a j).val = 132 + Cold.tapes a + (6 + j.val)) := by
  rw [sST_val]
  by_cases h0 : j.val = 0
  · exact Or.inl ⟨h0, by rw [if_pos h0]⟩
  · by_cases h1 : j.val = 1
    · exact Or.inr (Or.inl ⟨h1, by rw [if_neg h0, if_pos h1]⟩)
    · exact Or.inr (Or.inr ⟨h0, h1, by rw [if_neg h0, if_neg h1]⟩)

theorem sST_inj (a : DecompositionAlgorithm) : Function.Injective (sST a) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := sST_spec a i
  have hj := sST_spec a j
  apply Fin.ext
  omega

/-- The sum stage (4 tapes): `1^B` (97), `1^q` (61), the sum (74), its log (75). -/
def sZ (a : DecompositionAlgorithm) : Fin 4 → Fin (132 + Cold.tapes a + kOf a) :=
  ![tl a 97 (by omega), tl a 61 (by omega), tl a 74 (by omega), tl a 75 (by omega)]

theorem sZ_inj (a : DecompositionAlgorithm) : Function.Injective (sZ a) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [sZ] at hv ⊢

theorem sZ_spec (a : DecompositionAlgorithm) (j : Fin 4) :
    (sZ a j).val = 132 + Cold.tapes a + 97 ∨ (sZ a j).val = 132 + Cold.tapes a + 61 ∨
      (sZ a j).val = 132 + Cold.tapes a + 74 ∨ (sZ a j).val = 132 + Cold.tapes a + 75 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- The polynomial stage (`DimensionPolynomial.tapes 3 = 20` tapes): input `1^(B+q)` (74), output the bank capacity tape, the rest
fresh from `76`. -/
def sPC (a : DecompositionAlgorithm) (j : Fin (RepairSource.ProjectionNormalization.DimensionPolynomial.tapes 3)) :
    Fin (132 + Cold.tapes a + kOf a) :=
  if j.val = 0 then tl a 74 (by omega) else if j.val = (BlockPlatform.UnaryCalc.outputTape 3).val then tP a
  else tl a (76 + j.val) (by have := j.isLt; simp only [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this; omega)

theorem sPC_val (a : DecompositionAlgorithm) (j : Fin (RepairSource.ProjectionNormalization.DimensionPolynomial.tapes 3)) :
    (sPC a j).val = if j.val = 0 then 132 + Cold.tapes a + 74 else if j.val = (BlockPlatform.UnaryCalc.outputTape 3).val then
      132 + SB a + 14 else 132 + Cold.tapes a + (76 + j.val) := by
  unfold sPC; split_ifs <;> rfl

theorem sPC_spec (a : DecompositionAlgorithm) (j : Fin (RepairSource.ProjectionNormalization.DimensionPolynomial.tapes 3)) :
    (j.val = 0 ∧ (sPC a j).val = 132 + Cold.tapes a + 74) ∨
      (j.val ≠ 0 ∧ j.val = (BlockPlatform.UnaryCalc.outputTape 3).val ∧ (sPC a j).val = 132 + SB a + 14) ∨
      (j.val ≠ 0 ∧ j.val ≠ (BlockPlatform.UnaryCalc.outputTape 3).val ∧ (sPC a j).val = 132 + Cold.tapes a + (76 + j.val)) := by
  rw [sPC_val]
  by_cases h0 : j.val = 0
  · exact Or.inl ⟨h0, by rw [if_pos h0]⟩
  · by_cases h1 : j.val = (BlockPlatform.UnaryCalc.outputTape 3).val
    · exact Or.inr (Or.inl ⟨h0, h1, by rw [if_neg h0, if_pos h1]⟩)
    · exact Or.inr (Or.inr ⟨h0, h1, by rw [if_neg h0, if_neg h1]⟩)

theorem sPC_inj (a : DecompositionAlgorithm) : Function.Injective (sPC a) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := sPC_spec a i
  have hj := sPC_spec a j
  have := tapes_ge a
  apply Fin.ext
  omega

/-- The producer stage (229 tapes + its log) on the block `96 + p` (its inputs `word q`, `1^B`, `word N`, the mask, the stream were
written at `96, 97, 158, 159, 160` by the earlier stages); the 132 worker slots `93..224` onto the bank's writer tapes; `225..229` at
`189..193`. -/
def sPR (a : DecompositionAlgorithm) (p : Fin 230) : Fin (132 + Cold.tapes a + kOf a) :=
  if h : p.val < 93 then tl a (96 + p.val) (by omega)
  else if h' : p.val < 225 then bk a (p.val - 93) (by omega)
  else tl a (p.val - 36) (by have := p.isLt; omega)

theorem sPR_val (a : DecompositionAlgorithm) (p : Fin 230) :
    (sPR a p).val = if p.val < 93 then 132 + Cold.tapes a + (96 + p.val) else if p.val < 225 then p.val - 93
      else 132 + Cold.tapes a + (p.val - 36) := by
  unfold sPR; split_ifs <;> rfl

theorem sPR_spec (a : DecompositionAlgorithm) (p : Fin 230) :
    (p.val < 93 ∧ (sPR a p).val = 132 + Cold.tapes a + (96 + p.val)) ∨
      (93 ≤ p.val ∧ p.val < 225 ∧ (sPR a p).val = p.val - 93) ∨
      (225 ≤ p.val ∧ (sPR a p).val = 132 + Cold.tapes a + (p.val - 36)) := by
  rw [sPR_val]
  by_cases h0 : p.val < 93
  · exact Or.inl ⟨h0, by rw [if_pos h0]⟩
  · by_cases h1 : p.val < 225
    · exact Or.inr (Or.inl ⟨Nat.le_of_not_lt h0, h1, by rw [if_neg h0, if_pos h1]⟩)
    · exact Or.inr (Or.inr ⟨Nat.le_of_not_lt h1, by rw [if_neg h0, if_neg h1]⟩)

theorem sPR_inj (a : DecompositionAlgorithm) : Function.Injective (sPR a) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := sPR_spec a i
  have hj := sPR_spec a j
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  omega

/-- The producer's reset selection: every tape but the worker slots. -/
def selPR (p : Fin 229) : Bool := !(93 ≤ p.val && p.val < 225)

/-- The final head move: the template tape's head to `1`. -/
def dirMV (a : DecompositionAlgorithm) (i : Fin (132 + Cold.tapes a + kOf a)) : HeadMove :=
  if i.val = 132 + SB a + 10 then HeadMove.right else HeadMove.stay

/-! ## 3. The stage machines and the composite -/

section machines
variable (a : DecompositionAlgorithm)

abbrev T3 := Fin (132 + Cold.tapes a + kOf a)

def mXN := RecoveryFocus.machine (![tl a 0 (by omega), tl a 5 (by omega), tl a 6 (by omega)] : Fin 3 → T3 a)
  (MaskedReset.machine RepairSource.ProjectionNormalization.Field.machine (fun _ => true))
def mST := RecoveryFocus.machine (sST a) (MaskedReset.machine NearCubicWires.SourceStart.Stream.xM (fun _ => true))
def mQ1 := RecoveryFocus.machine (![tl a 2 (by omega), tl a 61 (by omega), tl a 62 (by omega)] : Fin 3 → T3 a)
  (MaskedReset.machine GeneratedAmplifier.Copy.machine (fun _ => true))
def mWQ := RecoveryFocus.machine (![tl a 61 (by omega), tl a 96 (by omega), tl a 64 (by omega)] : Fin 3 → T3 a)
  (MaskedReset.machine PacketsGlue.CmpWord.machine (fun _ => true))
def mWT := RecoveryFocus.machine (![tl a 61 (by omega), tT a, tl a 65 (by omega)] : Fin 3 → T3 a)
  (MaskedReset.machine PacketsGlue.CmpWord.machine (fun _ => true))
def mB1 := RecoveryFocus.machine (![tl a 3 (by omega), tl a 97 (by omega), tl a 67 (by omega)] : Fin 3 → T3 a)
  (MaskedReset.machine (PacketsGlue.RequestMeta.CopyPlus.machine 0) (fun _ => true))
def mN1 := RecoveryFocus.machine (![tl a 1 (by omega), tl a 68 (by omega), tl a 69 (by omega)] : Fin 3 → T3 a)
  (MaskedReset.machine PacketsGlue.CountFrames.machine (fun _ => true))
def mWN := RecoveryFocus.machine (![tl a 68 (by omega), tl a 158 (by omega), tl a 71 (by omega)] : Fin 3 → T3 a)
  (MaskedReset.machine PacketsGlue.CmpWord.machine (fun _ => true))
def mMK := RecoveryFocus.machine (![tl a 4 (by omega), tl a 159 (by omega), tl a 73 (by omega)] : Fin 3 → T3 a)
  (MaskedReset.machine GeneratedAmplifier.Copy.machine (fun _ => true))
def mZ := RecoveryFocus.machine (sZ a) ClockUnarySum.machine
def mPC := RecoveryFocus.machine (sPC a) (PCPSerializerCapacity.Power.machine 3 16777216)
def mPR := RecoveryFocus.machine (sPR a) (MaskedReset.machine PCJ6e421fabe2aa4155_SourcePoolProduced.machine selPR)
def mMV := DecompositionCountPosition.move (dirMV a)

/-- The word stages (frame copy, stream, `1^q`, `word q`, template, `1^B`, `1^N`, `word N`, mask). -/
def wordsM :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine (mXN a) (mST a)) (mQ1 a)) (mWQ a)) (mWT a)) (mB1 a))
    (mN1 a)) (mWN a)) (mMK a)

/-- **The start-bank machine** (one fixed machine per `a`): the words ; `1^(B+q)` ; `1^Pc` ; the producer ; the template head. -/
def bankM :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (wordsM a) (mZ a)) (mPC a)) (mPR a)) (mMV a)

end machines

end
end NearCubicWires.SourceStart.Bank

