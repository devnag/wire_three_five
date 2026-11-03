import TabMachine.Decode
import Proof.Hierarchy.CompetitorCountTableBounds
import Proof.Supplier.EquationRowProducer

/-! # K5 back end: proof 1's request writer and printer, then the decoder (M5, M6)

The near-cubic-gates paper lem:print: "Apply lem:signed-printer on the full cube of `m` variables. If a dummy variable
was added, its two slices are identical; keep one slice." Proof 1 has both machines:
* `EquationRowFramed.machine` (`producer_run`): from `frame (EquationRowRaw.source r)` (the exact cuts of an
  `EquationRow.Input r`: `d`, `p`, cut count, `odd`, the cut words) it writes the printer's request
  `physicalInput (EquationRow.request r)` (two weak cuts per exact cut, lem:signed-printer;
* `CompetitorCountTable.machine a` (`cold_run`, lem:signed-printer): from that request, `1^q` and `[odd]` it prints
  the table's residues modulo `2^q`, row-major, the odd slice cropped (`CompetitorFinalTable.word q odd f`).
Both run through `WMX.mach` (no re-implementation). `TabMachine.Decode.decode` turns the residues into the exact
signed values (two's complement, M6). **`back_spec`**: from the framed source of `r`, the output stream holds the
record stream of the printer's weighted-dominance table of `EquationRow.request r` in the printer's order
(`pvals`), each entry an exact integer in the sign-magnitude format of width `q = d + 2p + 5`; cost
`backCost a r` (the producer's `uniformBudget`, the printer's `budget`, the decoder's `2^s (100q + 100)`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Platform
open NearCubicWires.RepairRepresentation (WilliamsAlgorithm)
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (physicalInput leftScore rightScore weight)
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)

variable {ns nr : ℕ}

/-! ## Writing `1^n` -/

/-- `X := 1^n` (`n` in register `K`, kept). -/
def writeOnes (X : Fin (ns + 1)) (K K2 : Fin nr) : WMX ns nr :=
  .seq (repK K K2 (.seq (WMX.wr X true) (WMX.fwd X))) (repK K K2 (WMX.bwd X))

theorem writeOnes_spec (cap : ℕ) {X : Fin (ns + 1)} {K K2 : Fin nr} (hK : K ≠ K2) (σ : WState ns nr) (n : ℕ)
    (hX : σ.st X = []) (hXh : σ.sh X = 0) (hKv : σ.val K = n) (hK2 : σ.val K2 = 0) (hcap : 2 * n ≤ cap) :
    WXExec cap (writeOnes X K K2) σ (σ.sets X (List.replicate n true)) (34 * n + 7) := by
  have h1 := Runs.repE (cap := cap) (body := .seq (WMX.wr X true) (WMX.fwd X)) hK 3 n
    (fun k => (σ.sets X (List.replicate k true)).seth X k) hcap (fun k => by simp) (fun k => by simp)
    (fun k _ v1 v2 => by
      have e1 := WXExec.wr cap X true (((σ.sets X (List.replicate k true)).seth X k).setv K v1 |>.setv K2 v2)
      have e2 := WXExec.fwd cap X ((((σ.sets X (List.replicate k true)).seth X k).setv K v1 |>.setv K2 v2).sets X
        (writeTapeBit ((((σ.sets X (List.replicate k true)).seth X k).setv K v1 |>.setv K2 v2).st X)
          ((((σ.sets X (List.replicate k true)).seth X k).setv K v1 |>.setv K2 v2).sh X) true))
      refine (WXExec.seq e1 e2).cast cap ?_ (by omega)
      have hw : writeTapeBit (List.replicate k true) k true = List.replicate (k + 1) true := by
        have := writeTapeBit_end' (List.replicate k true) true
        rw [List.length_replicate] at this; rw [this, List.replicate_succ']
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      · funext i; by_cases hi : i = X
        · subst hi; simp [hw]
        · simp [Function.update_of_ne hi]
      · rfl
      · rfl) (by simp [hKv]) (by simp [hK2])
  have e0 : (σ.sets X (List.replicate 0 true)).seth X 0 = σ := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hXh]
      · simp [Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [hX]
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
  rw [e0] at h1
  have h2 := Runs.repE (cap := cap) (body := WMX.bwd X) hK 1 n
    (fun k => (σ.sets X (List.replicate n true)).seth X (n - k)) hcap (fun k => by simp) (fun k => by simp)
    (fun k hk v1 v2 => by
      refine (WXExec.bwd cap X _).cast cap ?_ le_rfl
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp; omega
        · simp [Function.update_of_ne hi]
      · rfl
      · rfl
      · rfl) (by simp [hKv]) (by simp [hK2])
  have e1 : (σ.sets X (List.replicate n true)).seth X (n - 0) = (σ.sets X (List.replicate n true)).seth X n := by simp
  have e2 : (σ.sets X (List.replicate n true)).seth X (n - n) = σ.sets X (List.replicate n true) := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hXh]
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
    · rfl
  rw [e1, e2] at h2
  exact (WXExec.seq h1 h2).mono (by ring_nf; omega)

/-! ## The printer's entry bank and its table -/


/-! ## Residues -/

/-! ## The back end -/

end NearCubicGates.Close.TabMachine
