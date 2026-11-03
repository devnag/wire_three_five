import Proof.Wire_3_5.Stage35.Bundle
import Proof.Wire_3_5.Stage35.AfterSpec
import Proof.Wire_3_5.Stage35.Prefix
import Proof.CaseAnalysis.CommonPrefixSelected
import Proof.Hierarchy.HierarchyFixedWord
import Proof.CaseAnalysis.CommonPortBank

-- Port of W3 Recovery3/CommonLayout.lean: the prefix is this proof's scan prefix (Stage35.Cert), the parameters Stage35.WQ.

/-!
# The common SAT-oracle program of the recovery: layout

The near-cubic-gates paper's uniform recovery: "The fixed-machine refuter runs in poly(T_clk(N_ν)) = 2^{O(q)} time with SAT access. The choices of
sec:gadget-transfer are recovered in three stages …; Since q = O(n), the final functions belong to E^NP." One ordinary
SAT-oracle program on every final length `n`, three pieces on one tape bank:
* piece 0, the refuter prefix (GR's `CloseoutCommonPrefix.program` at `toEight s g`): the schedule selects `ν`, the
  live flag is `onset ≤ N_ν`, the hierarchy slot holds `frame z ++ post` for the refuter's output `z`, tape 0 the
  framed final address, the query tape a run of zeros;
* piece 1, the after-prefix program `AfterRun` (`Recovery.AfterSpec`), its ports `zPort`, `pointPort`, query and output
  banked onto the hierarchy slot, the address, the query tape and the output tape, every other tape fresh;
* piece 2, the fixed word `false` on the output tape (no live source index).
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.Common

open Stage35 _root_.NearCubicGates.Close

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-- The constants of the recovery program: the prefix's (`Stage35.Cert.exists_selected_prefix`: capacity exponents,
onset, preparation capacity, refuter), the XOR schedule's `ζ = u/v`, and the after-prefix program. -/
structure Params (s : WS35) (P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm) (g : WQ) where
  u : ℕ
  v : ℕ
  e1 : ℕ
  e2 : ℕ
  e3 : ℕ
  onset : ℕ
  Aw : ℕ
  Bw : ℕ
  refuter : OrdinaryOracleProgram
  ar : AfterRun s P g

variable {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ}

noncomputable section

/-- The prefix's guarded workspace. -/
noncomputable def work (g : WQ) : ℕ := NearCubicWires.WireExponent3_5.Transfer.CertPrefixPrep.prefixTapes g.clauseDegree

/-- Piece 0's program: the scan prefix with the refuter at `N = 2^{a(n)}`, then the preparation. -/
noncomputable def prefixProgram (p : Params s P g) : OrdinaryOracleProgram :=
  Stage35.Cert.prefixProgram s.k (Outer.apad s.mw s.SV) p.u p.v g.clauseDegree p.e1 p.e2 p.e3 p.onset p.Aw p.Bw
    s.HR p.refuter

/-- The prefix's tape count. -/
noncomputable abbrev pt (p : Params s P g) : ℕ := (prefixProgram p).base.tapeCount

/-- The prefix bank and the output tape. -/
noncomputable abbrev n0 (p : Params s P g) : ℕ := pt p + 1
noncomputable abbrev ta (p : Params s P g) : ℕ := p.ar.prog.base.tapeCount
noncomputable abbrev tapes (p : Params s P g) : ℕ := n0 p + ta p + 2

/-! ## The prefix's ports, in its own bank -/

/-- The framed final address (tape 0). -/
noncomputable def addressP (p : Params s P g) : Fin (pt p) :=
  NearCubicWires.RepairSource.CloseoutCommonPrefix.firstSlots (work g) p.refuter s.k
    (NearCubicWires.RepairSource.CloseoutCommonPrefix.address (work g) p.refuter)

/-- The hierarchy slot `frame z ++ post`. -/
noncomputable def wordP (p : Params s P g) : Fin (pt p) :=
  NearCubicWires.RepairSource.CloseoutCommonPrefix.prepareSlots (work g) p.refuter s.k
    (CloseoutCommonPrepare.hierarchySlot s.k)

/-- The live flag `[decide (onset ≤ N)]`. -/
noncomputable def flagP (p : Params s P g) : Fin (pt p) :=
  NearCubicWires.RepairSource.CloseoutCommonPrefix.firstSlots (work g) p.refuter s.k
    (CloseoutRetainedRefuter.old p.refuter
      (NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix.flagPort (work g)))

theorem addressP_val (p : Params s P g) : (addressP p).val = 0 := by
  unfold addressP
  rw [NearCubicWires.RepairSource.CloseoutCommonPrefix.first_address]
  rfl

theorem queryP_pos (p : Params s P g) : (prefixProgram p).queryTape.val ≠ 0 := (prefixProgram p).queryFresh

theorem queryP_lt (p : Params s P g) :
    (prefixProgram p).queryTape.val < 1 + NearCubicWires.RepairSource.CloseoutCommonPrefix.base (work g) p.refuter :=
  NearCubicWires.RepairSource.CloseoutCommonPrefix.first_bound (work g) p.refuter s.k
    (NearCubicWires.RepairSource.CloseoutCommonPrefix.query (work g) p.refuter)

theorem wordP_ge (p : Params s P g) :
    1 + NearCubicWires.RepairSource.CloseoutCommonPrefix.base (work g) p.refuter ≤ (wordP p).val := by
  have hb := HierarchyFromInput.tapes_lower (s.k + 2)
  have hf : (CloseoutHierarchyRequest.fresh s.k 0).val ≠ 2 := by
    change CloseoutHierarchyClock.Input.tapes (s.k + 2) + 0 ≠ 2
    unfold CloseoutHierarchyClock.Input.tapes
    omega
  have hw : (CloseoutCommonPrepare.hierarchySlot s.k).val = 27 + (CloseoutHierarchyRequest.fresh s.k 0).val := by
    simp only [CloseoutCommonPrepare.hierarchySlot, CloseoutCommonPrepare.requestSlots,
      CloseoutHierarchyRequest.Shared.bank, if_neg hf, Fin.val_natAdd]
  have h0 : (CloseoutCommonPrepare.hierarchySlot s.k).val ≠ 0 := by omega
  have h1 : (CloseoutCommonPrepare.hierarchySlot s.k).val ≠ 1 := by omega
  unfold wordP
  simp only [NearCubicWires.RepairSource.CloseoutCommonPrefix.prepareSlots, if_neg h0, if_neg h1]
  omega

/-! ## The common bank -/

def lift0 (p : Params s P g) (i : Fin (n0 p)) : Fin (tapes p) := (i.castAdd (ta p)).castAdd 2
def prefixSlot (p : Params s P g) (i : Fin (pt p)) : Fin (tapes p) := lift0 p (i.castAdd 1)
def output0 (p : Params s P g) : Fin (n0 p) := (0 : Fin 1).natAdd (pt p)

/-- The after-prefix program's four shared ports. -/
def afterLocal (p : Params s P g) : Fin 4 → Fin (ta p) :=
  ![p.ar.zPort, p.ar.pointPort, p.ar.prog.queryTape, p.ar.prog.base.outputTape]
def afterShared (p : Params s P g) : Fin 4 → Fin (n0 p) :=
  ![(wordP p).castAdd 1, (addressP p).castAdd 1, (prefixProgram p).queryTape.castAdd 1, output0 p]
def afterSlot (p : Params s P g) (i : Fin (ta p)) : Fin (tapes p) :=
  (CloseoutCommonPortBank.slot (afterLocal p) (afterShared p) i).castAdd 2

def falseLocal : Fin 1 → Fin 2 := fun _ => 0
def falseShared (p : Params s P g) : Fin 1 → Fin (n0 p + ta p) := fun _ => (output0 p).castAdd (ta p)
def falseSlot (p : Params s P g) : Fin 2 → Fin (tapes p) := CloseoutCommonPortBank.slot falseLocal (falseShared p)

def liveFlag (p : Params s P g) : Fin (tapes p) := prefixSlot p (flagP p)

/-- The three pieces. -/
noncomputable def pieces (p : Params s P g) : Fin 3 → Piece (tapes p) :=
  ![focused (prefixProgram p) (prefixSlot p),
    focused p.ar.prog (afterSlot p),
    ordinary (RecoveryFocus.machine (falseSlot p) (HierarchyFixedWord.machine [false]))]

/-- After the prefix: the after-prefix program on a live flag, else `false`; then stop. -/
def next (p : Params s P g) (j : Fin 3) (_ : Fin (pieces p j).states) (read : Fin (tapes p) → Bool) : Option (Fin 3) :=
  if j.val = 0 then some (if read (liveFlag p) then 1 else 2) else none

theorem output0_ne_zero (p : Params s P g) : (lift0 p (output0 p)).val ≠ 0 := by
  have h := (prefixProgram p).base.twoTapes
  change pt p + 0 ≠ 0
  unfold pt
  omega

noncomputable def ports (p : Params s P g) : Ports (tapes p) where
  twoTapes := by unfold tapes; omega
  outputTape := lift0 p (output0 p)
  outputFresh := output0_ne_zero p
  queryTape := lift0 p ((prefixProgram p).queryTape.castAdd 1)
  queryFresh := (prefixProgram p).queryFresh

/-- **The common program.** -/
noncomputable def program (p : Params s P g) : OrdinaryOracleProgram := (ports p).program (graph (pieces p) 0 (next p))

/-- The initial bank: the framed final address on tape 0. -/
def input (p : Params s P g) (bits : List Bool) (i : Fin (tapes p)) : List Bool := if i.val = 0 then RepairOrdinary.frame bits else []

theorem ordinary_input (p : Params s P g) (bits : List Bool) : (program p).base.inputTapes bits = input p bits := rfl

/-! ## Injectivity -/

theorem lift0_injective (p : Params s P g) : Function.Injective (lift0 p) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [lift0] using this

theorem prefix_injective (p : Params s P g) : Function.Injective (prefixSlot p) :=
  (lift0_injective p).comp (Fin.castAdd_injective _ _)

theorem afterLocal_injective (p : Params s P g) : Function.Injective (afterLocal p) := by
  have h1 := p.ar.zPoint
  have h2 := p.ar.zQuery
  have h3 := p.ar.zOutput
  have h4 := p.ar.pointQuery
  have h5 := p.ar.pointOutput
  have h6 := p.ar.queryOutput
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [afterLocal]

theorem afterShared_injective (p : Params s P g) : Function.Injective (afterShared p) := by
  have ha := addressP_val p
  have hq0 := queryP_pos p
  have hq1 := queryP_lt p
  have hw := wordP_ge p
  have hwb := (wordP p).isLt
  have hqb := (prefixProgram p).queryTape.isLt
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [afterShared, output0] at hv ⊢ <;> unfold pt at * <;> omega

theorem after_injective (p : Params s P g) : Function.Injective (afterSlot p) :=
  (Fin.castAdd_injective _ _).comp (CloseoutCommonPortBank.injective _ _ (afterShared_injective p))

theorem false_injective (p : Params s P g) : Function.Injective (falseSlot p) :=
  CloseoutCommonPortBank.injective _ _ (fun i j _ => Subsingleton.elim i j)

end

end NearCubicGates.Close.Recovery3.Common

