import Lean
import Proof.Wire_3_5.UnionMachine.UnionSchedule
import Proof.Wire_3_5.UnionMachine.UnionCodec
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCodecBase


noncomputable section


/-! # The union machine's exact acceptance function (P3:3669-3691, 3485-3489)

Realizes the union weak machine of `tr:machine` (P3:3669-3691) as one executable function of its witness and the
primitive's answers: "The weak machine guesses one size-`q^G` general oracle, a class tag, and one sparse grid sum
for each distinct PCPP variable. It rejects malformed descriptions, oversized atoms, and coefficients outside the
fixed grid. Systematic parities are constructed from the PCPP output. It then selects the common star translation,
constructs the shared coordinate filters, and performs (tr:tests)", accepting by `tr:thresholds` (P3:3485-3489):
"accept only if `V̂ ≤ 2v₀`, `Q̂ ≤ 1+v₀`, and `μ̂` is at least the threshold".

Paper quantity: the acceptance of the union machine on a guess, `UnionAccepts S P z g`, computed from the printed
values `P.value` at the call schedule.

* `UnionGuess.checkData g tr`: the guess as `UnionCheckData` at the translation `tr`; at `tr = g.translation` its
  calls ARE the guess's calls (`checkData_vCall`, `checkData_muCall`, by `rfl`), its rational polynomials cast to the
  guess's (`polyVAt_eq`, …), and its rational estimates cast to `V̂, Q̂, μ̂` (`Vhat_eq`, `Qhat_eq`, `μhat_eq`).
* **`unionCheck S z g tr callOk val`**: oracle size `≤ q^G`, the word bound `⌊N/16⌋`, grid signs, every scheduled
  call admissible (by the Boolean `callOk`), and `tr:thresholds` in exact rationals at the answers `val`.
* **`unionCheck_iff`**: `unionCheck S z g g.translation callOk P.value = true ↔ UnionAccepts S P z g` whenever
  `callOk` decides `I.Call` on the scheduled requests (only there: `GatesIn` holds on every nonzero-coefficient call
  by construction of the carriers, the `gates_sublist_of_allowed`, so `callOk` may be the numeric conjuncts).
* **`unionRun S z tr callOk val w`**: decode the witness `w` (`decodeGuess`), then `unionCheck`.
  `unionRun_sound`: an accepting run yields an accepting guess (the `SoundFor` direction);
  `unionRun_complete`: every accepting guess is accepted on every witness length `W ≥ ⌊N/16⌋` (the `CompleteFor`
  direction). The C6 machine's remaining obligations are: compute `decodeGuess`, the translation (`selectCodes`),
  `callOk`, issue `schedule` to the estimator, compute `unionCheck`, within `tr:time`.
* `length_schedule_le`: the schedule has at most `24·K·(1 + 2K(s+1))⁴` calls for
  `K = c·(size(H)+1)^d` (the PCPP algorithm's constants, `size(H)` the substituted circuit's size, which
  `PCPPSubstitution.sourceRequest_call_budget` bounds polynomially in the oracle size and the outer PCP's sizes). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.WireExponent3_5.Shared (uMean)

section Check
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

namespace UnionGuess
variable {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z)

/-- The guess as the check reads it, at the translation `tr`. -/
def checkData (tr : List ℕ) : UnionCheckData :=
  ⟨g.mode, g.q, (S.request z g.pair).circuit, g.pcpp, g.s, g.sign, g.atom, S.constAtom g.mode g.q,
    S.parityAtom g.mode g.q, S.gridMass g.q, tr⟩

theorem checkData_circ (tr : List ℕ) : (g.checkData tr).circ = g.circ := by
  funext x
  rcases x with _ | ⟨X, a⟩ | X <;> rfl

theorem checkData_vCall (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (t : Fin 4 → g.AtomIx) :
    (g.checkData g.translation).vCall pos t = g.vCall pos t := by
  unfold UnionCheckData.vCall UnionGuess.vCall
  rw [checkData_circ]
  rfl

theorem checkData_muCall (i : Fin (2 ^ g.pcpp.clauseBits)) (t : Fin 4 → g.AtomIx) :
    (g.checkData g.translation).muCall i t = g.muCall i t := by
  unfold UnionCheckData.muCall UnionGuess.muCall
  rw [checkData_circ]
  rfl

theorem castF_wS (tr : List ℕ) (X : PcppVar g.pcpp) : castF ((g.checkData tr).wS X) = g.wS X := by
  funext y
  rcases y with _ | ⟨Y, a⟩ | Y
  · simp [castF, UnionCheckData.wS, UnionGuess.wS]
  · simp only [castF, UnionCheckData.wS, UnionGuess.wS]
    split_ifs with h1 h2 h2 <;>
      first | exact absurd h1 h2 | exact absurd h2 h1 | (push_cast; rfl)
  · simp [castF, UnionCheckData.wS, UnionGuess.wS]

theorem castF_wOne (tr : List ℕ) : castF (g.checkData tr).wOne = g.wOne := by
  funext y
  rcases y with _ | ⟨Y, a⟩ | Y <;> simp [castF, UnionCheckData.wOne, UnionGuess.wOne]

theorem castF_wE (tr : List ℕ) (X : PcppVar g.pcpp) : castF ((g.checkData tr).wE X) = g.wE X := by
  funext y
  rcases y with _ | ⟨Y, a⟩ | Y
  · simp [castF, UnionCheckData.wE, UnionGuess.wE]
  · simp [castF, UnionCheckData.wE, UnionGuess.wE]
  · simp only [castF, UnionCheckData.wE, UnionGuess.wE]
    split_ifs with h1 h2 h2 <;> first | exact absurd h1 h2 | exact absurd h2 h1 | simp

theorem polyVAt_eq (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) :
    g.polyVAt pos = ((g.checkData tr).polyVAt pos).toReal := by
  rw [UnionCheckData.polyVAt, polyVQ_toReal, castF_wS, castF_wOne, castF_wE]
  rfl

theorem polyQAt_eq (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) :
    g.polyQAt pos = ((g.checkData tr).polyQAt pos).toReal := by
  rw [UnionCheckData.polyQAt, polyQQ_toReal, castF_wS, castF_wOne]
  rfl

theorem polyMuAt_eq (tr : List ℕ) (i : Fin (2 ^ g.pcpp.clauseBits)) :
    g.polyMuAt i = ((g.checkData tr).polyMuAt i).toReal := by
  rw [UnionCheckData.polyMuAt, polyMuQ_toReal, castF_wS, castF_wS, castF_wOne]
  rfl

theorem coeffV_eq (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (j : Fin 4) (t : Fin 4 → g.AtomIx) :
    (g.polyVAt pos).coeff j t = (((g.checkData tr).polyVAt pos).coeff j t : ℝ) := by
  rw [g.polyVAt_eq tr pos]
  exact Poly4Q.coeff_toReal _ _ _

theorem coeffQ_eq (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (j : Fin 4) (t : Fin 4 → g.AtomIx) :
    (g.polyQAt pos).coeff j t = (((g.checkData tr).polyQAt pos).coeff j t : ℝ) := by
  rw [g.polyQAt_eq tr pos]
  exact Poly4Q.coeff_toReal _ _ _

theorem coeffMu_eq (tr : List ℕ) (i : Fin (2 ^ g.pcpp.clauseBits)) (j : Fin 4) (t : Fin 4 → g.AtomIx) :
    (g.polyMuAt i).coeff j t = (((g.checkData tr).polyMuAt i).coeff j t : ℝ) := by
  rw [g.polyMuAt_eq tr i]
  exact Poly4Q.coeff_toReal _ _ _

theorem coeffV_ne_zero (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (j : Fin 4)
    (t : Fin 4 → g.AtomIx) : (g.polyVAt pos).coeff j t ≠ 0 ↔ ((g.checkData tr).polyVAt pos).coeff j t ≠ 0 := by
  rw [g.coeffV_eq tr pos j t]
  exact Rat.cast_ne_zero

theorem coeffQ_ne_zero (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (j : Fin 4)
    (t : Fin 4 → g.AtomIx) : (g.polyQAt pos).coeff j t ≠ 0 ↔ ((g.checkData tr).polyQAt pos).coeff j t ≠ 0 := by
  rw [g.coeffQ_eq tr pos j t]
  exact Rat.cast_ne_zero

theorem coeffMu_ne_zero (tr : List ℕ) (i : Fin (2 ^ g.pcpp.clauseBits)) (j : Fin 4) (t : Fin 4 → g.AtomIx) :
    (g.polyMuAt i).coeff j t ≠ 0 ↔ ((g.checkData tr).polyMuAt i).coeff j t ≠ 0 := by
  rw [g.coeffMu_eq tr i j t]
  exact Rat.cast_ne_zero

end UnionGuess

instance (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : Decidable (NearCubicGates.Close.Outer.SrcFits G ν B) := by
  unfold NearCubicGates.Close.Outer.SrcFits; infer_instance

instance (ν : ℕ) {N : ℕ} (z : BitInput N) {m : ℕ} (B : BooleanCircuit m) :
    Decidable (NearCubicGates.Close.Outer.CheckAt ν z B) := by
  unfold NearCubicGates.Close.Outer.CheckAt; infer_instance

/-- The outer step's guards on a pair `Γ` (Lemma H.7; the machine's order): live setup, `N = 2^a` past the onset, both
circuits of size `≤ q^G`, the description-length guard and the source check. -/
def PairGuards (S : UnionSetup I) {N : ℕ} (z : BitInput N) (Γ : NearCubicGates.Close.Outer.OuterGuess (S.width N)) :
    Prop :=
  S.live = true ∧ N = 2 ^ Nat.log 2 N ∧ S.onset ≤ Nat.log 2 N ∧
  Γ.src.size ≤ oracleSizeBound S.G (S.width N) ∧ Γ.pf.size ≤ oracleSizeBound S.G (S.width N) ∧
  NearCubicGates.Close.Outer.SrcFits S.lenG (Nat.log 2 N) Γ.src ∧
  NearCubicGates.Close.Outer.CheckAt (Nat.log 2 N) z Γ.src

instance (S : UnionSetup I) {N : ℕ} (z : BitInput N) (Γ : NearCubicGates.Close.Outer.OuterGuess (S.width N)) :
    Decidable (PairGuards S z Γ) := by
  unfold PairGuards; infer_instance

/-- The guards of `UnionAccepts` on a guess: those of its pair. -/
def UnionGuards (S : UnionSetup I) {N : ℕ} (z : BitInput N) (g : UnionGuess S z) : Prop := PairGuards S z g.pair

instance (S : UnionSetup I) {N : ℕ} (z : BitInput N) (g : UnionGuess S z) : Decidable (UnionGuards S z g) := by
  unfold UnionGuards; infer_instance

/-- `UnionAccepts` is the pair's guards followed by the old tail. -/
theorem unionAccepts_iff (P : FusedPrimitive I) {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z) :
    UnionAccepts S P z g ↔ PairGuards S z g.pair ∧
      ((∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) ∧ g.word.length ≤ N / 16 ∧
      (∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
      (∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
      (∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t)) ∧
      g.Vhat P ≤ 2 * (S.params.v0 : ℝ) ∧ g.Qhat P ≤ 1 + (S.params.v0 : ℝ) ∧ (S.params.threshold : ℝ) ≤ g.μhat P) := by
  unfold UnionAccepts PairGuards
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, rest⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, rest⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, rest⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, rest⟩

variable {S : UnionSetup I} {N : ℕ} {z : BitInput N}

/-- **The schedule's length is polynomial**: at most `24·K·(1 + 2K(s+1))⁴` for `K = c·(size(H)+1)^d`. -/
theorem length_schedule_le (g : UnionGuess S z) (tr : List ℕ) :
    (g.checkData tr).schedule.length ≤
      24 * (S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ S.pcppAlg.degree) *
        (1 + 2 * (S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ S.pcppAlg.degree) *
          (g.s + 1)) ^ 4 := by
  set K := S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ S.pcppAlg.degree with hK
  have hM : 2 ^ (g.checkData tr).pcpp.clauseBits ≤ K := S.pcppAlg.clauseCountBound (S.request z g.pair)
  have hsys : (g.checkData tr).pcpp.systematicBits ≤ K := by
    refine (S.pcppAlg.systematicBound (S.request z g.pair)).trans (Nat.mul_le_mul_left _ ?_)
    exact Nat.pow_le_pow_left (by have := (S.request z g.pair).sizeLarge; omega) _
  have haux : (g.checkData tr).pcpp.auxiliaryBits ≤ K := S.pcppAlg.auxiliaryBound (S.request z g.pair)
  have hA : (g.checkData tr).atomCount ≤ 1 + 2 * K * (g.s + 1) := by
    unfold UnionCheckData.atomCount UnionCheckData.nvars
    have hs : (g.checkData tr).s = g.s := rfl
    rw [hs]
    have hnv : (g.checkData tr).pcpp.systematicBits + (g.checkData tr).pcpp.auxiliaryBits ≤ 2 * K := by omega
    nlinarith [Nat.mul_le_mul_right (g.s + 1) hnv]
  calc (g.checkData tr).schedule.length
      ≤ 3 * (2 ^ (g.checkData tr).pcpp.clauseBits * 2) * (4 * (g.checkData tr).atomCount ^ 4) :=
        (g.checkData tr).length_schedule
    _ ≤ 3 * (K * 2) * (4 * (1 + 2 * K * (g.s + 1)) ^ 4) := by gcongr
    _ = 24 * K * (1 + 2 * K * (g.s + 1)) ^ 4 := by ring

end Check

end NearCubicWires.WireExponent3_5.Transfer

end
