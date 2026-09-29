import Proof.Wire_3_5.UnionMachine.CWIface

/-! # C6 front, U5: the constant atom's code writer (v2 interface)

"Constants, complemented atoms, and the systematic encoding parity are permitted at the same fixed description
envelope" (P3:3092-3094): every call may name the constant atom, so the union front writes its canonical code
`natWord (m.code (unionConstAtom m q))` for each class mode.

The constant atom has no bottoms and a top over zero inputs, so its code does not depend on the length `q`
(**`constCode_eq`**). The writer is base's fixed-word printer (`HierarchyFixedWord`) docked on the output tape and one
scratch tape; the input `1^q` is never read. **`constWriter m : ConstWriterJ m`** (constant time `2L + 2`, `L` the
framed code's length).

Paper quantity of the main type: the code of the setup's constant atom. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWConst
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters NearCubicWires.WireExponent3_5.UnionMachine.CWIface
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairRepresentation (natWord)

/-- The constant atom's code (at length `0`; it is the same at every length). -/
def constCode (m : Mode) : ℕ := m.code (unionConstAtom m 0)

/-- **The constant atom's code does not depend on the length.** -/
theorem constCode_eq (m : Mode) (q : ℕ) : m.code (unionConstAtom m q) = constCode m := by
  cases m <;> rfl

/-- The framed word the writer prints. -/
def constWord (m : Mode) : List Bool := frame (natWord (constCode m))

/-- The printer's slots: the output tape `1` and the scratch tape `2`. -/
def slots : Fin 2 → Fin 3 := ![1, 2]

theorem slots_inj : Function.Injective slots := by decide

/-- The writer: the fixed-word printer of `constWord m`, docked. -/
noncomputable def machine (m : Mode) := RecoveryFocus.machine slots (HierarchyFixedWord.machine (constWord m))

/-- The writer's word stage: input tape `0`, output tape `1`, time `2L + 2` (degree `1`, so at least `2L + 2`). -/
noncomputable def stage (m : Mode) : WordStage where
  t := 3
  s := (constWord m).length + 1 + 2
  M := machine m
  inS := 0
  outS := 1
  hio := by decide
  K := 2 * (constWord m).length + 2
  d := 1

/-- The printer's run, docked on the input bank. -/
theorem machine_ready (m : Mode) (u : List Bool) :
    ClockJoin.ReadyRun (machine m) (2 * (constWord m).length + 2) (inBank (0 : Fin 3) u)
      (install slots (inBank (0 : Fin 3) u) ![constWord m, List.replicate (constWord m).length false]) := by
  obtain ⟨r, hr, ht, hh, hs⟩ := HierarchyFixedWord.word_ready (constWord m)
  exact CompetitorRationalProducts.bounded_focus slots slots_inj _ _ _ ⟨r, hr, ht, hh, hs.le⟩ _
    (by intro j; fin_cases j <;> rfl)

theorem out_eq (m : Mode) (u : List Bool) :
    install slots (inBank (0 : Fin 3) u) ![constWord m, List.replicate (constWord m).length false] =
      outBankJ 0 1 u (natWord (constCode m))
        (install slots (inBank (0 : Fin 3) u) ![constWord m, List.replicate (constWord m).length false]) := by
  funext j
  by_cases h0 : j = 0
  · subst h0
    rw [outBankJ_in, install_other slots _ _ 0 (by intro k; fin_cases k <;> decide)]
    simp [inBank]
  by_cases h1 : j = 1
  · subst h1
    rw [outBankJ_out 0 1 (by decide), show (1 : Fin 3) = slots 0 from rfl, install_slot slots slots_inj]; rfl
  · rw [outBankJ_other 0 1 j h0 h1]

/-- The residue's lengths: the input, the printed word and the printer's counter are within the time bound. -/
theorem res_len (m : Mode) (q : ℕ) (j : Fin 3) :
    (install slots (inBank (0 : Fin 3) (List.replicate q true))
      ![constWord m, List.replicate (constWord m).length false] j).length ≤
      (2 * (constWord m).length + 2) * ((List.replicate q true).length + q + 1) ^ 1 := by
  have hK : 2 * (constWord m).length + 2 ≤ (2 * (constWord m).length + 2) * ((List.replicate q true).length + q + 1) ^ 1 :=
    Nat.le_mul_of_pos_right _ (by simp)
  have hL : (constWord m).length ≤ (2 * (constWord m).length + 2) * ((List.replicate q true).length + q + 1) ^ 1 :=
    le_trans (by omega) hK
  by_cases h0 : j = 0
  · subst h0
    rw [install_other slots _ _ 0 (by intro k; fin_cases k <;> decide)]
    simp only [inBank, if_true, frame_length, List.length_replicate, pow_one]
    nlinarith
  by_cases h1 : j = 1
  · subst h1
    rw [show (1 : Fin 3) = slots 0 from rfl, install_slot slots slots_inj]
    exact hL
  have h2 : j = 2 := by omega
  subst h2
  rw [show (2 : Fin 3) = slots 1 from rfl, install_slot slots slots_inj]
  simpa using hL

/-- **The constant-code writer** of mode `m`. -/
noncomputable def constWriter (m : Mode) : ConstWriterJ m where
  toWordStage := stage m
  const_ready := by
    intro q
    have hr := machine_ready m (List.replicate q true)
    rw [out_eq m (List.replicate q true)] at hr
    set J := install slots (inBank (0 : Fin 3) (List.replicate q true))
      ![constWord m, List.replicate (constWord m).length false] with hJ
    have hK : 2 * (constWord m).length + 2 ≤ (2 * (constWord m).length + 2) * ((List.replicate q true).length + q + 1) ^ 1 :=
      Nat.le_mul_of_pos_right _ (by simp)
    refine ⟨J, fun j => res_len m q j, ?_⟩
    rw [constCode_eq]
    exact ClockJoin.enlarge _ _ _ _ _ hr hK

end NearCubicWires.WireExponent3_5.UnionMachine.CWConst
