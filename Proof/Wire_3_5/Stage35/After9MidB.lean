import Proof.Wire_3_5.Stage35.After9MidA
import Proof.Wire_3_5.Stage35.Bundle

-- Port of W3 Recovery3/After9MidB.lean with the copies schedule (Stage35.WQ).

/-!
# The recovery after the refuter: the middle segment, piece 22

The near-cubic-gates paper's uniform recovery (sec:all-lengths): "a formula with one variable per oracle address and the constraints
`C^O_{⟨B*_src⟩_ν}(R) = 0` for all `2^{ℓ_out}` inputs `R` … finds the first oracle `O*`" and "If no oracle `O*` exists at
an exceptional initial source length, the second stage detects that case". Piece 22 is stage 2 (`ENP.TStage`), clocked
(every head back at `0`) and focused on its bank: its input word on MW1 (`18`), its query on the shared query tape (`3`,
zero padded to the clear's length), its flag and table in its own block; its flag branches to piece 24 (`O*` exists)
or piece 23 (`false`).
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.After

open Stage35 _root_.NearCubicGates.Close _root_.NearCubicGates.Close.Recovery3 _root_.NearCubicGates.Close.Recovery3.After

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget NearCubicWires.Bindings.MW20

section

variable {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ} (K : Kit s P g) (c : Cfg)

/-- Stage 2's padding: the clear's length `cap` on the shared query tape, nothing elsewhere. -/
noncomputable def caps22 (cap : ℕ) (j : Fin (pT K).base.tapeCount) : ℕ :=
  if j = (pT K).queryTape then cap else 0

/-- Stage 2's input bank (`ENP.TStage.run` with `post = []`). -/
def in22 (o : OracleOutput) : Fin K.ts.program.base.tapeCount → List Bool :=
  fun i => if i = K.ts.inPort then o.word ++ [] else []

theorem tBank_mem_query : (cslot _ K.ts.program.queryTape, sh K 3) ∈ (tBank K).l := by
  simp [tBank, mkBank]

/-- **Piece 22** (stage 2, the near-cubic-gates paper's uniform recovery): on the word of `C_{⟨B⟩_ν}` (MW1) with the cleared query `0^cap`, stage 2 runs
within its cost `cst` (plus the clocked rewind); the query is then `max cap cst` long at most; the table tape holds
the first honest table; the flag sends the program to piece 24 when an honest oracle exists, to piece 23 otherwise. -/
theorem piece22 (A : Fin (T K) → List Bool) (cap : ℕ) (o : OracleOutput)
    (h3 : A (sh K 3) = List.replicate cap false) (h18 : A (sh K 18) = o.word)
    (hb : ∀ x : Fin (T K), off K 22 ≤ x.val → A x = []) :
    ∃ cst k : ℕ, cst ≤ K.ts.K * (2 ^ o.ell + o.word.length + 1) ^ K.ts.e ∧ k ≤ cst ∧
      ∃ out : Fin (pT K).base.tapeCount → List Bool,
        (out (cslot _ K.ts.program.queryTape)).length ≤ max cap cst ∧
        (∀ first : Transfer.FirstTable o.circuit,
          out (cslot _ K.ts.tablePort) = RepairOrdinary.frame (List.ofFn first.table)) ∧
        ((∃ t, Transfer.HonestTable o.circuit t) →
          OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) (cst + (k + 2) + 1) (start K c 22 A)
            (start K c 24 (install (tBank K).slot A out))) ∧
        ((¬ ∃ t, Transfer.HonestTable o.circuit t) →
          OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) (cst + (k + 2) + 1) (start K c 22 A)
            (start K c 23 (install (tBank K).slot A out))) := by
  obtain ⟨cst, hcst, final, htr, hh, hflag, htab, -, -, hq, -⟩ := K.ts.run o []
  rw [List.append_nil] at hcst
  obtain ⟨k, hk, hready, -⟩ := clocked_ready htr hh
  have hiq : K.ts.inPort ≠ K.ts.program.queryTape := K.ts.inQuery
  have hcapq : caps22 K cap (cslot _ K.ts.program.queryTape) = cap := by
    unfold caps22; rw [if_pos (cslot_query _)]
  have hcap0 : ∀ j, j ≠ cslot _ K.ts.program.queryTape → caps22 K cap j = 0 := by
    intro j hj; unfold caps22; rw [if_neg (by rw [← cslot_query]; exact hj)]
  have hcq : cslot _ K.ts.inPort ≠ cslot _ K.ts.program.queryTape :=
    fun e => hiq (cslot_injective _ e)
  have hin := (tBank K).input A (fun j => ZeroPadding.pad (caps22 K cap j) (clockIn _ (in22 K o) j)) (by
      intro q hq'
      simp only [tBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · show A (sh K 3) = ZeroPadding.pad (caps22 K cap (cslot _ K.ts.program.queryTape))
          (clockIn _ (in22 K o) (cslot _ K.ts.program.queryTape))
        rw [h3, hcapq, clockIn_src]
        simp [in22, Ne.symm hiq, ZeroPadding.pad]
      · show A (sh K 18) = ZeroPadding.pad (caps22 K cap (cslot _ K.ts.inPort))
          (clockIn _ (in22 K o) (cslot _ K.ts.inPort))
        rw [h18, hcap0 _ hcq, ZeroPadding.pad_zero, clockIn_src]
        simp [in22])
    (by
      intro j hj
      simp only [tBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hj
      show ZeroPadding.pad (caps22 K cap j) (clockIn _ (in22 K o) j) = []
      rw [hcap0 j (Ne.symm hj.1), ZeroPadding.pad_zero]
      rcases clocked_cases K.ts.program j with ⟨i, rfl⟩ | rfl | rfl
      · rw [clockIn_src]
        have hi : i ≠ K.ts.inPort := fun e => hj.2 (by rw [e])
        simp [in22, hi]
      · exact clockIn_clock _ _
      · exact clockIn_reset _ _)
    (fun x hx _ => hb x hx)
  have hpr := piece_oracle (ports K) hready (caps22 K cap) (tBank K).slot (tBank K).injective
    ((tBank K).slot_port (tBank_mem_query K)) A hin
  refine ⟨cst, k, hcst, hk, fun j => ZeroPadding.pad (caps22 K cap j) (clockOut _ final.tapes k j), ?_, ?_, ?_, ?_⟩
  · show (ZeroPadding.pad (caps22 K cap (cslot _ K.ts.program.queryTape))
      (clockOut _ final.tapes k (cslot _ K.ts.program.queryTape))).length ≤ max cap cst
    rw [hcapq, clockOut_src, ZeroPadding.pad_length]
    omega
  · intro first
    have hne : cslot _ K.ts.tablePort ≠ cslot _ K.ts.program.queryTape :=
      fun e => K.ts.tableQuery (cslot_injective _ e)
    show ZeroPadding.pad (caps22 K cap (cslot _ K.ts.tablePort)) (clockOut _ final.tapes k (cslot _ K.ts.tablePort)) = _
    rw [hcap0 _ hne, ZeroPadding.pad_zero, clockOut_src]
    exact htab first
  · intro hex
    refine step_call K c (k := 22) (l := 24) hpr (fun q => ?_)
    rw [next_22]
    have hf : readTapeBit (install (tBank K).slot A
        (fun j => ZeroPadding.pad (caps22 K cap j) (clockOut _ final.tapes k j)) (flag2 K)) 0 = true := by
      unfold flag2
      rw [install_slot _ (tBank K).injective, ZeroPadding.read_pad, clockOut_src]
      exact hflag.mpr hex
    rw [hf, if_pos rfl]
  · intro hex
    refine step_call K c (k := 22) (l := 23) hpr (fun q => ?_)
    rw [next_22]
    have hf : readTapeBit (install (tBank K).slot A
        (fun j => ZeroPadding.pad (caps22 K cap j) (clockOut _ final.tapes k j)) (flag2 K)) 0 = false := by
      unfold flag2
      rw [install_slot _ (tBank K).injective, ZeroPadding.read_pad, clockOut_src]
      cases h : readTapeBit (final.tapes K.ts.flagPort) 0
      · rfl
      · exact absurd (hflag.mp h) hex
    rw [hf]
    rfl

end

end NearCubicGates.Close.Recovery3.After

