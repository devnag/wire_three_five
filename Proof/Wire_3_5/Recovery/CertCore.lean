import Proof.Wire_3_5.Recovery.CertSetup

/-! # The core length test `2m_a ≤ n` (P3:3738-3741; D1.6, the prefix stage)

Realizes the test of the prefix's scan: "Choose the largest `a` such that `m_a ≤ n/2`" (P3:3740) at one candidate `a`
with width `q = q(2^a)` and schedule `t = t(q)`: `m_a = (t+1)·(q + ⌈d_G log₂(q+2)⌉ + 1)` (`coreLen`), and
`m_a ≤ n/2` iff `2m_a ≤ n`. The machine: base's `Clause` (the clause width `⌈log₂((q+2)^{d_G})⌉` and `q + 1`),
`UWalkUnary`, the unary sum (`q + 1 + cw`), `DimensionTemplate` (the word of `t + 1`), the unary product (`m_a`),
the product with `2`, and base's `RawCompare` with `n`.

Paper quantity: `m_a`; **`coreMachine D`** on `Clause.tapes D + 18` tapes and **`coreMachine_ready`**: from `1^q`, the
counter `1^t` (padded to `total`) and `1^n` it writes `[2(t+1)(q + 1 + cw) ≤ n]`, `cw = clauseWidth D q`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes Clause.machine Clause.clause_run Clause.input
  Clause.qSlot Clause.widthSlot)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

section Core
variable (D : ℕ)

/-- The clause machine's tapes, then 18 more. -/
def cl (i : Fin (Clause.tapes D)) : Fin (Clause.tapes D + 18) := i.castAdd 18
def tl (j : Fin 18) : Fin (Clause.tapes D + 18) := j.natAdd (Clause.tapes D)

theorem cl_val (i : Fin (Clause.tapes D)) : (cl D i).val = i.val := rfl
theorem tl_val (j : Fin 18) : (tl D j).val = Clause.tapes D + j.val := rfl
theorem width_val : (Clause.widthSlot D).val = 24 + 2 * D := by
  simp [Clause.widthSlot, RepairSource.CloseoutSchedule.Clause.clogSlots]; omega
theorem tapes_eq : Clause.tapes D = 26 + 2 * D := rfl

def slotsCU : Fin 3 → Fin (Clause.tapes D + 18) := ![cl D (Clause.widthSlot D), tl D 2, tl D 3]
def slotsCS : Fin 4 → Fin (Clause.tapes D + 18) := ![cl D (Clause.qSlot D), tl D 2, tl D 4, tl D 5]
def slotsCT : Fin 3 → Fin (Clause.tapes D + 18) := ![tl D 0, tl D 6, tl D 7]
def slotsCP : Fin 4 → Fin (Clause.tapes D + 18) := ![tl D 4, tl D 6, tl D 8, tl D 9]
def slotsCW : Fin 2 → Fin (Clause.tapes D + 18) := ![tl D 10, tl D 11]
def slotsCD : Fin 4 → Fin (Clause.tapes D + 18) := ![tl D 8, tl D 10, tl D 12, tl D 13]
def slotsCC : Fin 6 → Fin (Clause.tapes D + 18) := ![tl D 12, tl D 1, tl D 14, tl D 15, tl D 16, tl D 17]

/-- Injectivity and disjointness of these maps reduce to their values. -/
theorem slots_inj {m : ℕ} (s : Fin m → Fin (Clause.tapes D + 18)) (h : ∀ a b, (s a).val = (s b).val → a = b) :
    Function.Injective s := fun a b hab => h a b (congrArg Fin.val hab)

/-- **The core length machine**. -/
noncomputable def coreMachine :=
  Composition.machine (RecoveryFocus.machine (cl D) (Clause.machine D))
  (Composition.machine (RecoveryFocus.machine (slotsCU D) (UWalkUnary.machine false false))
  (Composition.machine (RecoveryFocus.machine (slotsCS D) ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine (slotsCT D) (RepairSource.ProjectionNormalization.DimensionTemplate.machine true))
  (Composition.machine (RecoveryFocus.machine (slotsCP D) ClockUnaryProduct.machine)
  (Composition.machine (RecoveryFocus.machine (slotsCW D) (HierarchyFixedWord.machine (CompareMachine.word 2)))
  (Composition.machine (RecoveryFocus.machine (slotsCD D) ClockUnaryProduct.machine)
    (RecoveryFocus.machine (slotsCC D) RepairSource.CloseoutSchedule.RawCompare.machine)))))))

/-- The input: `1^q` on the clause machine's tape 0, the counter `1^t` padded to `total` and `1^n` on the tail. -/
def coreInput (q t n total : ℕ) : Fin (Clause.tapes D + 18) → List Bool := fun i =>
  if i.val = 0 then List.replicate q true
  else if i.val = Clause.tapes D then ZeroPadding.pad total (List.replicate t true)
  else if i.val = Clause.tapes D + 1 then List.replicate n true else []

theorem fin_ne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- Close `∀ j, s j ≠ k` and injectivity goals for the core layout by their values. -/
macro "core_off" : tactic => `(tactic| (intro j; fin_cases j <;> (apply fin_ne; simp [slotsCU, slotsCS, slotsCT,
  slotsCP, slotsCW, slotsCD, slotsCC, cl, tl, width_val, Clause.qSlot, tapes_eq]; try omega)))
macro "core_inj" : tactic => `(tactic| (apply slots_inj; intro a b h; fin_cases a <;> fin_cases b <;>
  simp [slotsCU, slotsCS, slotsCT, slotsCP, slotsCW, slotsCD, slotsCC, cl, tl, width_val, Clause.qSlot,
    tapes_eq] at h ⊢ <;> omega))

theorem cl_injective : Function.Injective (cl D) := fun _ _ h => Fin.castAdd_injective _ _ h

end Core

end NearCubicWires.WireExponent3_5.Transfer
