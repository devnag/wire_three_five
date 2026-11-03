import Proof.Wire_3_5.MachineModel.BlockCost
import Proof.MachineModel.OrdinaryStreamController

/-! # Block v3 (S5): the stream loop (`while` the source tape's scanned bit is set)

Paper: the primitive's programs run over lists whose length is data.
- The rows of a linear system (P3:2950-2957).
- The occurrences of the printer (P3:1733-1738: "For each occurrence …").
- The records of a sorted stream (P3:1743-1749).
Each record is framed, so the list ends at a `false` marker.

The paper quantity of the main type is the iteration sequence: `WhileBody` gives the banks `(H j, A j)`
before the `j`-th pass, for `j ≤ bound`, and one uniform body with a `Step` from each bank to the next.
The loop continues while the source tape reads `true` and stops at `false`.
`WhileBody.run` is the whole loop as ONE `Step` of the Theorem 2.5 `StreamController` machine. It
costs `Σ_{j<bound} (cost j + 2) + 1` (the test and return transfers of each pass, then the final test).
`WhileBody.within` bounds that in a class. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecordController (code test stop)

/-- A data-dependent loop over a stream: `bound` passes of one body. -/
structure WhileBody (t s : ℕ) where
  body : Machine t s
  tape : Fin t
  bound : ℕ
  H : ℕ → Fin t → ℕ
  A : ℕ → Fin t → List Bool
  cost : ℕ → ℕ
  step : ∀ j, j < bound → Step body (cost j) (H j) (A j) (H (j + 1)) (A (j + 1))
  cont : ∀ j, j < bound → readTapeBit (A j tape) (H j tape) = true
  halt : readTapeBit (A bound tape) (H bound tape) = false

namespace WhileBody
variable {t s : ℕ}

/-- The total cost of the passes from `j` on. -/
def rest (W : WhileBody t s) (j : ℕ) : ℕ :=
  ((List.range (W.bound - j)).map (fun i => W.cost (j + i) + 2)).sum + 1

/-- The loop's test configuration at bank `j`. -/
def testConfig (W : WhileBody t s) (j : ℕ) : Configuration t (s + 2) := ⟨test s, W.H j, W.A j⟩

theorem rest_succ (W : WhileBody t s) (j : ℕ) (hj : j < W.bound) :
    W.rest j = W.cost j + 2 + W.rest (j + 1) := by
  unfold rest
  have e : W.bound - j = (W.bound - (j + 1)) + 1 := by omega
  rw [e, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  simp only [Nat.add_zero, Function.comp_def]
  have e2 : ∀ i, W.cost (j + (i + 1)) = W.cost (j + 1 + i) := by intro i; congr 1; omega
  simp only [e2]
  omega

theorem rest_bound (W : WhileBody t s) : W.rest W.bound = 1 := by
  simp [rest]

/-- The configuration the loop stops in. -/
def stopConfig (W : WhileBody t s) : Configuration t (s + 2) := ⟨stop s, W.H W.bound, W.A W.bound⟩

/-- The passes from bank `j` to the end, as a timed trace of the loop machine, within `rest j`. -/
theorem timed_from (W : WhileBody t s) (j : ℕ) (hj : j ≤ W.bound) :
    ∃ n, n ≤ W.rest j ∧
      RecoveryExecution.Timed (StreamController.machine W.body W.tape) n (W.testConfig j) W.stopConfig := by
  induction h : W.bound - j generalizing j with
  | zero =>
    have hjb : j = W.bound := by omega
    subst hjb
    refine ⟨1, by rw [rest_bound], ?_⟩
    have hs := StreamController.stop_step W.body W.tape ⟨W.body.start, W.H W.bound, W.A W.bound⟩ W.halt
    exact RecoveryExecution.Timed.single (StreamController.test_halted W.body W.tape) hs
  | succ n ih =>
    have hjb : j < W.bound := by omega
    obtain ⟨r, hr, hh, ht, hs⟩ := W.step j hjb
    have henter := StreamController.enter_step W.body W.tape ⟨W.body.start, W.H j, W.A j⟩ (W.cont j hjb)
    obtain ⟨hp, hhalt⟩ := StreamController.body_prefix W.body W.tape _ _ r hr
    have hret := StreamController.return_step W.body W.tape r.final hhalt
    have t1 := RecoveryExecution.Timed.single (StreamController.test_halted W.body W.tape) henter
    have t2 : RecoveryExecution.Timed (StreamController.machine W.body W.tape) r.steps
        (controlConfig code ⟨W.body.start, W.H j, W.A j⟩) (controlConfig code r.final) := ⟨_, hp⟩
    have t3 := RecoveryExecution.Timed.single (StreamController.body_halted W.body W.tape r.final.control) hret
    have e3 : controlConfig (fun _ => test s) r.final = W.testConfig (j + 1) := by
      apply configuration_ext
      · rfl
      · exact hh
      · exact ht
    rw [e3] at t3
    obtain ⟨m, hm, tail⟩ := ih (j + 1) (by omega) (by omega)
    refine ⟨1 + r.steps + 1 + m, ?_, ((t1.trans t2).trans t3).trans tail⟩
    rw [rest_succ W j hjb]
    omega

/-- **The whole stream loop as one `Step`.** -/
theorem run (W : WhileBody t s) :
    Step (StreamController.machine W.body W.tape) (W.rest 0) (W.H 0) (W.A 0) (W.H W.bound) (W.A W.bound) := by
  obtain ⟨n, hn, htimed⟩ := W.timed_from 0 (Nat.zero_le _)
  obtain ⟨r, hr, hf, hs⟩ := htimed.run (StreamController.stop_halted W.body W.tape)
  have more := runFrom_moreFuel (StreamController.machine W.body W.tape) n (W.rest 0 - n) _ r hr
  rw [Nat.add_sub_of_le hn] at more
  refine ⟨r, more, ?_, ?_, by omega⟩
  · rw [hf]; rfl
  · rw [hf]; rfl

/-- With a constant pass cost the loop costs `bound·(c+2)+1` (executable check of `rest`). -/
theorem rest_const (W : WhileBody t s) (c : ℕ) (hc : ∀ j, W.cost j = c) : W.rest 0 = W.bound * (c + 2) + 1 := by
  simp [rest, hc, List.sum_replicate]

end WhileBody


end NearCubicWires.WireExponent3_5.Block
