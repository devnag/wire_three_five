import Proof.SourceAssembly.SourcePoolIndexReady
import Proof.SourceAssembly.SourceCacheReady

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Item4
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-- P's five input words (agreed 04:5x). -/
def inWord (a : DecompositionAlgorithm) (r : Request) : Fin 5 → List Bool :=
  ![RepairOrdinary.frame r.nativeWord, RepairOrdinary.frame (r.supportWord a), RepairOrdinary.frame (List.replicate r.q true),
    List.replicate r.nativeWord.length true,
    RepairOrdinary.frame (CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a)))]

/-- **P's start-bank contract** (the typed hole): one fixed machine on `Fin (132 + Cold.tapes a + k)` (bank first, then P's tail with
the five inputs on `inPort`), writing the ACCEPTED runs' common entry bank for EVERY request, at request functions `B w Pc` meeting
`request_run`'s side conditions. -/
structure StartBank (a : DecompositionAlgorithm) (k : Nat) where
  states : Nat
  machine : Machine (132 + Cold.tapes a + k) states
  cost : Request → Nat
  need : Request → Nat
  B : Request → Nat
  w : Request → Nat
  Pc : Request → Nat
  inPort : Fin 5 → Fin k
  inPort_inj : Function.Injective inPort
  hw : ∀ r, 0 < w r
  hqw : ∀ r : Request, r.q ≤ w r
  hb : ∀ (r : Request), ∀ g ∈ (r.family a).occurrences, (CloseoutRowsCircuitBottom.nativeWord g).length ≤ B r
  hm : ∀ (r : Request), ∀ g ∈ (r.family a).occurrences,
    (g.gate.threshold - 1).natAbs + (∑ i, (g.gate.weight i).natAbs) < 2 ^ (w r)
  hqP : ∀ r : Request, r.q ≤ Pc r
  hi : ∀ r : Request, (segment (CloseoutRowsUniversal.pool (Packets.live (r.family a)) (r.family a).occurrences)
    []).length ≤ 1000 * (Pc r + 2) ^ 2
  run : ∀ (r : Request) (R : Nat) (E : Fin (132 + Cold.tapes a + k) → List Bool), need r ≤ R →
    (∀ j, E (Fin.natAdd (132 + Cold.tapes a) (inPort j)) = ZeroPadding.pad R (inWord a r j)) →
    (∀ x, (∀ j, Fin.natAdd (132 + Cold.tapes a) (inPort j) ≠ x) → E x = List.replicate R false) →
    ∃ E' : Fin (132 + Cold.tapes a + k) → List Bool,
      Step machine (cost r) (fun _ => 0) E
        (Fin.addCases (Fin.addCases (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences (B r) (w r) []).heads
          (PoolCold.coldHeads a)) (fun _ : Fin k => 0)) E' ∧
      (∀ i : Fin (132 + Cold.tapes a), E' (Fin.castAdd k i) = ZeroPadding.pad R
        (Fin.addCases (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences (B r) (w r) []).tapes
          (PoolCold.coldData a (Pc r) r.q) i)) ∧
      (∀ j, E' (Fin.natAdd (132 + Cold.tapes a) (inPort j)) = E (Fin.natAdd (132 + Cold.tapes a) (inPort j)))

/-! ## The index block -/

section index
variable {a : DecompositionAlgorithm} {k : Nat}

/-- P's machine docked on the index block: bank in place, tail after the six extra tapes. -/
def sbI (a : DecompositionAlgorithm) (k : Nat) (x : Fin ((132 + Cold.tapes a) + k)) : Fin ((132 + Cold.tapes a) + (6 + k)) :=
  if h : x.val < (132 + Cold.tapes a) then ⟨x.val, by omega⟩ else ⟨x.val + 6, by have := x.isLt; omega⟩

/-- The index run docked on the index block: the identity on the bank and its six extra tapes. -/
def ixI (a : DecompositionAlgorithm) (k : Nat) (x : Fin ((132 + Cold.tapes a) + 6)) : Fin ((132 + Cold.tapes a) + (6 + k)) := ⟨x.val, by omega⟩

/-- The index block. -/
def idxBlock (SB : StartBank a k) :=
  Composition.machine (RecoveryFocus.machine (sbI a k) SB.machine)
    (RecoveryFocus.machine (ixI a k) (PCJ6e421fabe2aa4155_SourcePoolIndex.machine a))

/-- Its per-request cost. -/
def idxCost (SB : StartBank a k) (r : Request) : Nat :=
  SB.cost r + 1 + PCJ6e421fabe2aa4155_SourcePoolIndex.budget a (Packets.live (r.family a)) (r.family a).occurrences
    (SB.B r) (SB.w r) (SB.Pc r)


end index

/-! ## The pool block -/

section pool
variable {a : DecompositionAlgorithm} {k : Nat}

/-- P's machine docked on the pool block: bank in place, tail after the 373 extra tapes. -/
def sbP (a : DecompositionAlgorithm) (k : Nat) (x : Fin ((132 + Cold.tapes a) + k)) : Fin ((132 + Cold.tapes a) + (373 + k)) :=
  if h : x.val < (132 + Cold.tapes a) then ⟨x.val, by omega⟩ else ⟨x.val + 373, by have := x.isLt; omega⟩

/-- The cache run docked on the pool block: the identity on the bank and its 373 extra tapes. -/
def plI (a : DecompositionAlgorithm) (k : Nat) (x : Fin ((132 + Cold.tapes a) + 373)) :
    Fin ((132 + Cold.tapes a) + (373 + k)) := ⟨x.val, by omega⟩

/-- The pool block. -/
def poolBlock (SB : StartBank a k) :=
  Composition.machine (RecoveryFocus.machine (sbP a k) SB.machine)
    (RecoveryFocus.machine (plI a k) (PCJ6e421fabe2aa4155_SourceCache.machine a))

/-- Its per-request cost. -/
def poolCost (SB : StartBank a k) (r : Request) : Nat :=
  SB.cost r + 1 + PCJ6e421fabe2aa4155_SourceCache.budget a (r.family a).occurrences (SB.B r) (SB.w r) (SB.Pc r)

def plOut (a : DecompositionAlgorithm) (k : Nat) (j : Fin 373) : Fin ((132 + Cold.tapes a) + (373 + k)) :=
  plI a k (PCJ6e421fabe2aa4155_SourceCache.poolSlots a j)

end pool

end
end NearCubicWires.SourceFactorSel.Item4

