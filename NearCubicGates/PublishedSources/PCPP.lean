import Statement

set_option autoImplicit false

namespace NearCubicGates.PublishedSources.PCPP

open NearCubicWires
open NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Lemma311

noncomputable def relativeHamming {n : ℕ} (x y : BitInput n) : ℝ :=
  ((Finset.univ.filter fun i => x i ≠ y i).card : ℝ) / n

structure LinearCodeFamily where
  length : ℕ → ℕ
  support : (n : ℕ) → Fin (length n) → Finset (Fin n)
  decoder : (n : ℕ) → BitInput (length n) → BitInput n

noncomputable def LinearCodeFamily.enc (E : LinearCodeFamily)
    (n : ℕ) (x : BitInput n) : BitInput (E.length n) :=
  fun i => parityOn (E.support n i) x

abbrev MessageRequest := Σ n : ℕ, {_x : BitInput n // 2 ≤ n}

def messageWord (p : MessageRequest) : List Bool :=
  RepairOrdinary.frame p.1.bits ++ RepairOrdinary.frame (List.ofFn p.2.val)

abbrev CodewordRequest (E : LinearCodeFamily) :=
  Σ n : ℕ, {_y : BitInput (E.length n) // 2 ≤ n}

def codewordWord (E : LinearCodeFamily) (p : CodewordRequest E) : List Bool :=
  RepairOrdinary.frame p.1.bits ++ RepairOrdinary.frame (List.ofFn p.2.val)

/-- CW19 Lemma 27's constant-rate linear code, in explicit support form.
The n/2 support claim is stated for n ≥ 2. -/
def EfficientLinearCodeLiteral : Prop :=
  ∃ E : LinearCodeFamily, ∃ distance radius : ℝ,
    0 < radius ∧ radius < distance ∧ distance < 1 ∧
    (∃ K : ℕ, ∀ n, 2 ≤ n → E.length n ≤ K * (n + 1)) ∧
    (∀ n, 2 ≤ n → ∀ i, (E.support n i).card ≤ n / 2) ∧
    (∀ n, 2 ≤ n → ∀ x y : BitInput n, x ≠ y →
      distance ≤ relativeHamming (E.enc n x) (E.enc n y)) ∧
    (∀ n, 2 ≤ n → ∀ x : BitInput n, ∀ y : BitInput (E.length n),
      relativeHamming (E.enc n x) y ≤ radius → E.decoder n y = x) ∧
    Nonempty (Turing.TM2ComputableInPolyTime messageWord
      (fun word : List Bool => word) (fun p => List.ofFn (E.enc p.1 p.2.val))) ∧
    Nonempty (Turing.TM2ComputableInPolyTime (codewordWord E)
      (fun word : List Bool => word) (fun p => List.ofFn (E.decoder p.1 p.2.val)))

structure RawThreeQueryPCPP (n : ℕ) where
  proofBits : ℕ
  randomBits : ℕ
  clause : Fin (2 ^ randomBits) → Fin 3 → Literal (n + proofBits)

def RawThreeQueryPCPP.accepts {n : ℕ} (P : RawThreeQueryPCPP n)
    (input : BitInput n) (proof : BitInput P.proofBits)
    (coins : Fin (2 ^ P.randomBits)) : Bool :=
  (List.ofFn fun i : Fin 3 => (P.clause coins i).eval (Fin.addCases input proof)).any id

noncomputable def RawThreeQueryPCPP.fraction {n : ℕ} (P : RawThreeQueryPCPP n)
    (input : BitInput n) (proof : BitInput P.proofBits) : ℝ :=
  ((Finset.univ.filter fun coins => P.accepts input proof coins = true).card : ℝ) /
    (2 ^ P.randomBits : ℝ)

def RawThreeQueryPCPP.word {n : ℕ} (P : RawThreeQueryPCPP n) : List Bool :=
  RepairOrdinary.frame P.proofBits.bits ++ RepairOrdinary.frame P.randomBits.bits ++
    (List.ofFn fun coins : Fin (2 ^ P.randomBits) =>
      (List.ofFn fun i : Fin 3 =>
        RepairOrdinary.frame (literalCode (P.clause coins i)).bits).flatten).flatten

def ProximityFar (delta : ℝ) (C : Circuit) (input : BitInput C.n) : Prop :=
  ∀ accepted : BitInput C.n, C.D.eval accepted = true →
    delta ≤ relativeHamming input accepted

abbrev AcceptedCircuitInput := Σ C : Circuit, {x : BitInput C.n // C.D.eval x = true}

def acceptedCircuitInputWord (p : AcceptedCircuitInput) : List Bool :=
  p.1.word ++ List.ofFn p.2.val

/-- CW19 Lemma 24: three queries, OR predicates, proximity soundness,
perfect completeness, and a uniform honest-proof procedure on YES inputs. -/
def PerfectThreeQueryProximityLiteral : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    ∃ output : (C : Circuit) → RawThreeQueryPCPP C.n,
      Nonempty (Turing.TM2ComputableInPolyTime (fun C : Circuit => C.word)
        (fun word : List Bool => word) (fun C => (output C).word)) ∧
      (∃ K e : ℕ, ∀ C,
        (output C).proofBits ≤ K * (C.m + 1) ^ e ∧
        2 ^ (output C).randomBits ≤ K * (C.m + 1) ^ e) ∧
      (∀ C input, ProximityFar delta C input →
        ∀ proof, (output C).fraction input proof ≤ s) ∧
      ∃ honest : (p : AcceptedCircuitInput) → BitInput (output p.1).proofBits,
        (∀ p coins, (output p.1).accepts p.2.val (honest p) coins = true) ∧
        Nonempty (Turing.TM2ComputableInPolyTime acceptedCircuitInputWord
          (fun word : List Bool => word) (fun p => List.ofFn (honest p)))

/-- Input 9: CW19 Lemmas 24 and 27 together. The pointwise form the paper uses is proved from them. -/
def ThreeQuerySourceGroup : Prop :=
  PerfectThreeQueryProximityLiteral ∧ EfficientLinearCodeLiteral

end NearCubicGates.PublishedSources.PCPP
