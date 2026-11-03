import Proof.Wire_3_5.UnionMachine.FrontSemEntBase
import Proof.Wire_3_5.UnionMachine.FrontEnd
import Proof.Wire_3_5.UnionMachine.FrontFoldSem
import Proof.Wire_3_5.UnionMachine.FrontCallOkBase
import Proof.Wire_3_5.UnionMachine.CWConst
import Proof.Wire_3_5.UnionMachine.FrontRest

/-! # C6 front, the semantic core (3): the table writer's data at a guess (P3:3672-3691)

At a decoded guess `g` (check data `D = g.checkData g.translation`) the chain leaves the table writer's ten sources:
the PCPP output word, the entries, the head `natWord q ++ [mode] ++ natWord 4`, the translation, the constant's code,
the fold's parity and carrier codes and envelope bits, and the all-ones flag strings. **`twD g deg`** is that data;
**`twRel`** (the sources hold `D`), **`twFlags`** (the flag strings are the envelope bits `fDI`, `fEI`: the atom test
passed, the parities and the constant are small), **`twHolds`** (the sources sit on the streams).

Paper quantity of the main types: the guess's check data as the table writer reads it. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)

/-- `frame` on a concatenation. -/
theorem frame_app (u v : List Bool) : RepairOrdinary.frame (u ++ v) = PrimAsm.ParseNat.enc true u ++ RepairOrdinary.frame v := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    show true :: b :: RepairOrdinary.frame (u ++ v) = _
    rw [ih]
    simp [PrimAsm.ParseNat.enc, RepairOrdinary.Streaming.marks]

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N} 

variable {g}

theorem getD_rep (n i : ℕ) (hi : i < n) : (List.replicate n true).getD i false = true := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp

end Guess

/-! ## The table writer on every guess (both verdicts) -/

section Sem2
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge (entryOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- The call table's entry words in the passes' order (no admissibility needed). -/
def twWords (D : UnionCheckData) : List Bool :=
  (myV D).flatMap (fun t => Entry.entryWord (entryOf 0 D.s t)) ++
    (myQ D).flatMap (fun t => Entry.entryWord (entryOf 1 D.s t)) ++
      (myMu D).flatMap (fun t => Entry.entryWord (entryOf 2 D.s t))

/-- **The table writer on any guess**: the entry words, then `OK = [schedule.all okR]` (twSem without the calls'
admissibility, for the rejecting verdict too). -/
theorem twSem2 (cap : ℕ) (src : Fin 11 → List Bool) (cl : Bool) (D : UnionCheckData) (d : TWData) (hr : TWRel D d)
    (fD : D.mode.Circuit D.q → Bool) (fE : Stars.Carrier D.q → Bool) (hf : TWFlags D d fD fE)
    (hd : d.Holds src) (Bn : ℕ) (hB : d.Bnd Bn) (v0 : Fin NR → ℕ) (hc : ClauseRegs cap d Bn v0) (hv : RdOK v0)
    (hC : decide (v0 rCDF ≠ 0) = fD D.const) (hSS : v0 rSS = D.s) (hSYS : v0 rSYS = D.pcpp.systematicBits)
    (Λ : ℕ) (hm : D.mass = Λ) (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true) (hmr : MagRegs D Λ v0)
    (hPO : POLayout cap src v0 (litsD D) (2 ^ D.pcpp.clauseBits)) (hl : LitsOK cap d v0 (litsD D) (2 ^ D.pcpp.clauseBits))
    (cV cQ cM Rb : ℕ)
    (hcV : ∀ i < 2 ^ D.pcpp.clauseBits, 7 * litA (litsD D) i + 1 + 1 + (110 * (litA (litsD D) i * v0 rSS) +
      110 * litA (litsD D) i + 110 * v0 rSS + 30 * v0 rSYS + costV Bn (posRegs (Function.update (Function.update v0 rL1
        (litB (litsD D) i)) rLIT (litA (litsD D) i))) + 120) + 1 + (7 * litB (litsD D) i + 1 + 1 +
          (110 * (litB (litsD D) i * v0 rSS) + 110 * litB (litsD D) i + 110 * v0 rSS + 30 * v0 rSYS +
            costV Bn (posRegs (Function.update v0 rLIT (litB (litsD D) i))) + 120)) ≤ cV)
    (hcQ : ∀ i < 2 ^ D.pcpp.clauseBits, 7 * litA (litsD D) i + 1 + 1 + (110 * (litA (litsD D) i * v0 rSS) +
      110 * litA (litsD D) i + 110 * v0 rSS + 30 * v0 rSYS + mbCost Bn (posRegs (Function.update (Function.update v0 rL1
        (litB (litsD D) i)) rLIT (litA (litsD D) i))) rMb (patQ 0) + 120) + 1 + (7 * litB (litsD D) i + 1 + 1 +
          (110 * (litB (litsD D) i * v0 rSS) + 110 * litB (litsD D) i + 110 * v0 rSS + 30 * v0 rSYS +
            mbCost Bn (posRegs (Function.update v0 rLIT (litB (litsD D) i))) rMb (patQ 0) + 120)) ≤ cQ)
    (hcM : ∀ i < 2 ^ D.pcpp.clauseBits, 100 * (litA (litsD D) i + 1) * (v0 rSS + 1) +
      100 * (litB (litsD D) i + 1) * (v0 rSS + 1) + costMu Bn (FrontTW.muRegs v0 (litA (litsD D) i) (litB (litsD D) i)) +
        100 ≤ cM)
    (hrd : ∀ x ∈ litsD D, rdCost x ≤ Rb ∧ 2 ^ (natBitLength x + 1) ≤ cap) (hT : v0 rT = 0) (hBc : v0 rBIG ≤ cap)
    (hMc : 2 ^ D.pcpp.clauseBits + 1 ≤ cap)
    (okR : PrimRequest → Bool)
    (hokV : ∀ (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (pat : Fin 4 → FrontTableRef.FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ FrontTableRef.cand D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (pat k)) →
      okR (D.vCall pos t) = okT D fD fE (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) false t)
    (hokM : ∀ (i : Fin (2 ^ D.pcpp.clauseBits)) (pat : Fin 4 → FrontTableRef.FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ FrontTableRef.cand D (posVar D.pcpp i 0) (posVar D.pcpp i 1) (pat k)) →
      okR (D.muCall i t) = okT D fD fE (posVar D.pcpp i 0) (posVar D.pcpp i 1) true t)
    (hlen : (twWords D).length + 30 * Bn + 41 ≤ cap) :
    WExec cap twP (ts src 0 [] (regsOf v0 Z4 Z4 Z4 1) cl)
      (ts src 0 (twWords D ++ [false]) (regsOf v0 Z4 Z4 Z4 (if D.schedule.all okR then 1 else 0)) cl)
      (3 * (60 * v0 rBIG + 250 + 18 * 2 ^ D.pcpp.clauseBits + 2 ^ D.pcpp.clauseBits * (2 * Rb + cV + cQ + cM + 8)) + 10) := by
  have hmass : D.mass ≠ 0 := by rw [hm]; exact_mod_cast (show Λ ≠ 0 by omega)
  have eV := accW_V_eq D d hr v0 Λ hm hΛ hs hsg hSS hSYS hmr
  have eQ := accW_Q_eq D d hr v0 Λ hm hΛ hs hsg hSS hSYS hmr
  have eM := accW_Mu_eq D d hr v0 Λ hm hΛ hs hsg hSS hmr
  have bV := accB_V_eq D d hr fD fE hf v0 hC hSS okR Λ hmr hSYS hokV
  have bQ := accB_Q_eq D d hr fD fE hf v0 hC hSS okR Λ hmr hSYS hokV
  have bM := accB_Mu_eq D d hr fD fE hf v0 hC hSS okR hokM
  have tw := twT cap src cl v0 hv hT hBc (litsD D) (2 ^ D.pcpp.clauseBits) hPO (WVof d v0) (WQof d v0) (WMof d v0)
    (bVof d v0) (bQof d v0) (bMof d v0) (30 * Bn + 40) cV cQ cM Rb
    (bodyV_ok cap src cl d hd Bn hB v0 hc (litsD D) _ hl cV hcV) (bodyQ_ok cap src cl d hd Bn hB v0 hc (litsD D) _ hl cQ hcQ)
    (bodyMu_ok cap src cl d hd Bn hB v0 hc (litsD D) _ hl cM hcM) hrd hMc
    (by rw [eV, eQ, eM]; unfold twWords at hlen; simp only [List.length_append] at hlen; omega)
  rw [eV, eQ, eM, bV, bQ, bM, ok_eq D hmass hs okR] at tw
  exact tw

end Sem2

/-! ## The sources, the registers, the layout at a guess -/

section Src
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The writer's streams from the ten sources (stream `0` the empty output). -/
def srcF (v : Fin 10 → List Bool) (j : Fin 11) : List Bool :=
  if h : j.val = 0 then [] else v ⟨j.val - 1, by have := j.isLt; omega⟩

theorem srcF_succ (v : Fin 10 → List Bool) (i : Fin 10) : srcF v i.succ = v i := by
  unfold srcF; simp

end Src

section Regs
open NearCubicWires.WireExponent3_5.FinalPass.Tm
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

theorem numCap_ge (s Λ q sys aux cb : ℕ) :
    s * s * s * s + 1 ≤ numCap s Λ q sys aux cb ∧ Λ * Λ * (s * s) + 1 ≤ numCap s Λ q sys aux cb ∧
    Λ * (s * s * s) + Λ * (s * s * s) + 1 ≤ numCap s Λ q sys aux cb ∧
    Λ * Λ * Λ * s + Λ * Λ * Λ * s + 1 ≤ numCap s Λ q sys aux cb ∧ Λ * Λ * Λ * Λ + 1 ≤ numCap s Λ q sys aux cb ∧
    Λ * (s * s * s) + 1 ≤ numCap s Λ q sys aux cb ∧ s + 1 ≤ numCap s Λ q sys aux cb := by
  unfold numCap
  generalize 2 ^ (cb + 1) = p2
  generalize s * s * s * s = a1
  generalize Λ * Λ * (s * s) = a2
  generalize Λ * (s * s * s) = a3
  generalize Λ * Λ * Λ * s = a4
  generalize Λ * Λ * Λ * Λ = a5
  omega

end Regs

/-! ## The PCPP stream's layout and the clauses' variables -/

section Layout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

theorem litIdx_lt {n : ℕ} (l : SourceInterfaces.Literal n) : RepairRepresentation.literalIndex l < 2 * n := by
  cases l with
  | positive i => have := i.isLt; show 2 * i.val < 2 * n; omega
  | negative i => have := i.isLt; show 2 * i.val + 1 < 2 * n; omega

end Layout

/-! ## The writer's run at a guess -/

section Run
open NearCubicWires.WireExponent3_5.FinalPass.Tm
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- A clause's cost in the first pass. -/
def cVf (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (i : ℕ) : ℕ :=
  7 * litA lits i + 1 + 1 + (110 * (litA lits i * v0 rSS) + 110 * litA lits i + 110 * v0 rSS + 30 * v0 rSYS +
    costV Bn (posRegs (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i))) + 120) + 1 +
      (7 * litB lits i + 1 + 1 + (110 * (litB lits i * v0 rSS) + 110 * litB lits i + 110 * v0 rSS + 30 * v0 rSYS +
        costV Bn (posRegs (Function.update v0 rLIT (litB lits i))) + 120))

/-- A clause's cost in the second pass. -/
def cQf (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (i : ℕ) : ℕ :=
  7 * litA lits i + 1 + 1 + (110 * (litA lits i * v0 rSS) + 110 * litA lits i + 110 * v0 rSS + 30 * v0 rSYS +
    mbCost Bn (posRegs (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i))) rMb
      (FrontTableRef.patQ 0) + 120) + 1 + (7 * litB lits i + 1 + 1 + (110 * (litB lits i * v0 rSS) +
        110 * litB lits i + 110 * v0 rSS + 30 * v0 rSYS +
          mbCost Bn (posRegs (Function.update v0 rLIT (litB lits i))) rMb (FrontTableRef.patQ 0) + 120))

/-- A clause's cost in the third pass. -/
def cMf (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (i : ℕ) : ℕ :=
  100 * (litA lits i + 1) * (v0 rSS + 1) + 100 * (litB lits i + 1) * (v0 rSS + 1) +
    costMu Bn (FrontTW.muRegs v0 (litA lits i) (litB lits i)) + 100

/-- The largest value of `f` below `M`. -/
def supR (f : ℕ → ℕ) (M : ℕ) : ℕ := ((List.range M).map f).foldr max 0

theorem le_supR (f : ℕ → ℕ) (M i : ℕ) (hi : i < M) : f i ≤ supR f M :=
  FrontOutRef.le_foldr_max _ _ (List.mem_map_of_mem (List.mem_range.2 hi))

/-- The table writer's cost at a guess. -/
def twCost (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (cb : ℕ) : ℕ :=
  3 * (60 * v0 rBIG + 250 + 18 * 2 ^ cb + 2 ^ cb * (2 * ((lits.map rdCost).foldr max 0) + supR (cVf Bn v0 lits) (2 ^ cb) +
    supR (cQf Bn v0 lits) (2 ^ cb) + supR (cMf Bn v0 lits) (2 ^ cb) + 8)) + 10

end Run

/-! ## The front's end at a guess -/

section End
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- The end's cost (the valid branch's; the rejecting one is below it). -/
def endCost (W nT crT KT AT q L : ℕ) : ℕ :=
  (11 * W + 20) + 1 + (1 + 1 + (2 * (nT + 1 + (1 + 1)) + 2)) + 1 +
    ((11 * W + 20) + 1 + (1 + 1 + (nT + FrontTail.tailCost crT KT AT q L (2 * W + 2))) + 1 +
      (2 * FrontTail.rOf crT KT AT q + 4) + 1)

end End

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW
