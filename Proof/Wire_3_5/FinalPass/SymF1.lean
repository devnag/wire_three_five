import Proof.Wire_3_5.Primitive.Writers.UnitReady

/-! # SWf (the SYM words writer's flat tables), part 1: a list seed's flat table from a table-ready state

The flat tables writer builds, per unit, the flat table `flatTable Pl e L` of one list seed `e` at one population
length `L` (`tablesJ`, list:flatten P3:1508-1520). The first two stages of PA's POP pipeline run as black boxes,
composed exactly as in `PopPipe.popPipe`: the walk (`walkStage`) and C5's builder (`buildStage`). Their entry is
**`TabReady`**: exactly the fields of the POP-ready state (`UnitReady.PopReady`) those two stages read (the walk
bank's inputs at the seed, C5's builder entry state, the rank facts, two capacity facts). `PopReady` itself also
carries the POP row's capacities (`(8L+2)^{3·lbP+1} ≤ cap`, super-polynomial in the final pass's input), which the
flat tables never need.

* `TabReady`; `tabPrePM`, `tabPrePCost`; **`tabPreP`**: the flat table on stream `6` with its head at `0`, the
  streams `0 … 4` (request, output, counter, record, data) kept, every register from `19` on kept.

Paper quantity of the main type: the list seed's flat table `flatTable Pl e L` (P3:1508-1520). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierWalk Theorem25Completion
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.FinalPass.Flat
open NearCubicWires.WireExponent3_5.PrimAsm.PopRecW NearCubicWires.WireExponent3_5.PrimAsm.PopLink

variable (cap : ℕ) (W : WalkBankProducer)

/-- **A table-ready cell state**: the fields of `UnitReady.PopReady` the walk and table stages read. -/
structure TabReady (σ : WState (LNS W.x) LNR) (Pl : FlatListParams) (e : Pl.FlatSeed) (L RW LW : ℕ) : Prop where
  hRW : 2 * sideB Pl.base.rank + 1 ≤ RW
  hLW : 2 * sideB Pl.base.rank + 1 ≤ LW
  hpad : padB Pl.base.rank ≤ 1
  hps : padB Pl.base.rank ≤ sideB Pl.base.rank
  hsd : 2 * Pl.base.rank - 1 + Pl.base.rank ≤ 2 * sideB Pl.base.rank - padB Pl.base.rank
  hlb : 1 ≤ Pl.base.rank
  hnJ : Pl.base.J + 1 ≤ Pl.base.rank + 1
  hcapC : 8 * sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ cap
  hO : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < cap
  hin : ∀ j : Fin 14, σ.st (sk W.x (portT j)) = inPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW
    (seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e) j
  hh : ∀ j : Fin 14, σ.sh (sk W.x (portT j)) = 0
  hsc : ∀ k : Fin W.x, σ.st (sT W.x k) = []
  hsh : ∀ k : Fin W.x, σ.sh (sT W.x k) = 0
  hC5 : ∀ i : Fin 12, i.val ≠ 0 → i.val ≠ 2 → σ.st (fsC W.x i) = (yC Pl e L RW LW).st i ∧ σ.sh (fsC W.x i) = 0
  hC5r : ∀ r, σ.val (frC r) = (yC Pl e L RW LW).val r
  hcell : σ.cell = (yC Pl e L RW LW).cell

/-- The table stages' machine: the walk, then C5's builder (`popPipeM`'s first two stages). -/
noncomputable def tabPrePM := Composition.machine (walkM W) (buildM W.x)

/-- The table stages' cost. -/
def tabPrePCost (Pl : FlatListParams) (L RW LW : ℕ) : ℕ :=
  walkBankCost (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW + 1 +
    ((2 * (Pl.errExp / 4)) * (bodyCostL (sideB Pl.base.rank) Pl.base.rank L (Pl.base.J + 1) RW + 3) + 3 + 1 +
      lastCostL (sideB Pl.base.rank) Pl.base.rank L (Pl.base.J + 1) (2 * (Pl.errExp / 4)))

/-- **A list seed's flat table from a table-ready state**: on stream `6`, head `0`; streams `0 … 4` and the
registers from `19` on kept. -/
theorem tabPreP (σ : WState (LNS W.x) LNR) (Pl : FlatListParams) (e : Pl.FlatSeed) (L RW LW : ℕ)
    (h : TabReady cap W σ Pl e L RW LW) :
    ∃ σC : WState (LNS W.x) LNR, Step (tabPrePM W) (tabPrePCost Pl L RW LW) (wenc cap σ).H (wenc cap σ).A
        (wenc cap σC).H (wenc cap σC).A ∧
      σC.st (sk W.x 6) = FinalPass.Flat.flatTable Pl e L ∧ σC.sh (sk W.x 6) = 0 ∧
      (∀ k : Fin 161, k.val < 5 → σC.st (sk W.x k) = σ.st (sk W.x k) ∧ σC.sh (sk W.x k) = σ.sh (sk W.x k)) ∧
      (∀ r : Fin LNR, 19 ≤ r.val → σC.val r = σ.val r) := by
  -- the walk stage
  obtain ⟨J, -, sB⟩ := walkStage cap W σ (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW e h.hRW h.hLW h.hin h.hh
    h.hsc h.hsh
  obtain ⟨σB, hσB⟩ : ∃ τ, τ = updS (tmapT W.x) σ (Fin.addCases (motive := fun _ => ℕ)
      (outHeads (2 * (Pl.errExp / 4))) (fun _ => 0)) (Fin.addCases (motive := fun _ => List Bool)
      (outPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW e) J) := ⟨_, rfl⟩
  have sB' : Step (walkM W) (walkBankCost (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW)
      (wenc cap σ).H (wenc cap σ).A (wenc cap σB).H (wenc cap σB).A := by
    rw [hσB]
    exact sB
  have hB_other : ∀ k : Fin 161, (∀ j : Fin 14, portT j ≠ k) →
      σB.st (sk W.x k) = σ.st (sk W.x k) ∧ σB.sh (sk W.x k) = σ.sh (sk W.x k) := fun k hk => by
    rw [hσB]
    exact ⟨updT_st_other σ _ _ k hk, updT_sh_other σ _ _ k hk⟩
  have hB_pst : ∀ j : Fin 14, σB.st (sk W.x (portT j)) = outPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW e j :=
    fun j => by rw [hσB, updT_st_port, Fin.addCases_left]
  have hB_psh : ∀ j : Fin 14, σB.sh (sk W.x (portT j)) = outHeads (2 * (Pl.errExp / 4)) j :=
    fun j => by rw [hσB, updT_sh_port, Fin.addCases_left]
  have hB_val : σB.val = σ.val := by rw [hσB]; rfl
  have hB_cell : σB.cell = σ.cell := by rw [hσB]; rfl
  -- the table stage
  have hshC : ∀ i, σB.sh (fsC W.x i) = (yC Pl e L RW LW).sh i := by
    intro i
    rw [yC_sh]
    by_cases h0 : i.val = 0
    · have : i = 0 := Fin.ext h0
      subst this
      rw [fsC0, hB_psh]
      rfl
    · by_cases h2 : i.val = 2
      · have : i = 2 := Fin.ext h2
        subst this
        rw [fsC2, hB_psh]
        rfl
      · exact (hB_other _ (fun j hj => portT_ne_fs i h0 h2 j (congrArg Fin.val hj))).2.trans (h.hC5 i h0 h2).2
  have hstC : ∀ i, σB.st (fsC W.x i) = (yC Pl e L RW LW).st i := by
    intro i
    by_cases h0 : i.val = 0
    · have : i = 0 := Fin.ext h0
      subst this
      rw [fsC0, hB_pst, yC_st0]
      rfl
    · by_cases h2 : i.val = 2
      · have : i = 2 := Fin.ext h2
        subst this
        rw [fsC2, hB_pst, yC_st2]
        rfl
      · exact (hB_other _ (fun j hj => portT_ne_fs i h0 h2 j (congrArg Fin.val hj))).1.trans (h.hC5 i h0 h2).1
  have sC := buildStage cap W.x σB (sideB Pl.base.rank) Pl.base.rank L (padB Pl.base.rank) (Pl.base.J + 1)
    (n := 2 * (Pl.errExp / 4)) RW LW e h.hRW h.hLW h.hpad h.hps h.hsd h.hlb h.hnJ h.hcapC h.hO hshC hstC
    (fun r => (congrFun hB_val _).trans (h.hC5r r)) (hB_cell.trans h.hcell)
    (fun k => by rw [emC_port, hB_psh, outHeads_bank]) (fun k => by rw [emC_port, hB_pst, outPorts_bank])
  obtain ⟨σC, hσC⟩ : ∃ τ, τ = updW (fsC W.x) frC (emC W.x) σB (yF Pl e L RW LW)
      (Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ)
        (fun k => WalkTimeLoop.H (2 * (Pl.errExp / 4)) (2 * (Pl.errExp / 4)) k.succ.succ) (fun _ => 1))
      (Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool)
        (fun k => WalkTimeLoop.A (r := sideB Pl.base.rank) (n := 2 * (Pl.errExp / 4)) RW LW e []
          (2 * (Pl.errExp / 4)) k.succ.succ)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word (2 * (Pl.errExp / 4)))) := ⟨_, rfl⟩
  have sC' : Step (buildM W.x) ((2 * (Pl.errExp / 4)) * (bodyCostL (sideB Pl.base.rank) Pl.base.rank L
      (Pl.base.J + 1) RW + 3) + 3 + 1 + lastCostL (sideB Pl.base.rank) Pl.base.rank L (Pl.base.J + 1)
      (2 * (Pl.errExp / 4))) (wenc cap σB).H (wenc cap σB).A (wenc cap σC).H (wenc cap σC).A := by
    rw [hσC]
    exact sC
  have hC_other : ∀ k : Fin 161, (k.val < 5 ∨ 23 < k.val) →
      σC.st (sk W.x k) = σB.st (sk W.x k) ∧ σC.sh (sk W.x k) = σB.sh (sk W.x k) := fun k hk => by
    rw [hσC]
    exact ⟨updC_st_other σB _ _ _ k hk, updC_sh_other σB _ _ _ k hk⟩
  have hC_tab : σC.st (sk W.x 6) = tableW Pl.walkLen Pl.base.J (rowKP Pl e L) ++ [false] ∧ σC.sh (sk W.x 6) = 0 := by
    rw [hσC, ← fsC1, updC_st_fs, updC_sh_fs, yF_st1 Pl e L RW LW h.hlb, yF_sh1]
    exact ⟨rfl, rfl⟩
  have hC_val : ∀ r : Fin LNR, 19 ≤ r.val → σC.val r = σ.val r := fun r hr => by
    rw [hσC]
    exact (updC_val_other σB _ _ _ r hr).trans (congrFun hB_val r)
  refine ⟨σC, Step.seq sB' sC', by rw [flatTable_eq]; exact hC_tab.1, hC_tab.2, fun k hk => ?_, hC_val⟩
  have hp : ∀ j : Fin 14, portT j ≠ k := fun j hj => by
    have := portT_ge j
    rw [hj] at this
    omega
  obtain ⟨c1, c2⟩ := hC_other k (Or.inl hk)
  obtain ⟨b1, b2⟩ := hB_other k hp
  exact ⟨c1.trans b1, c2.trans b2⟩

end NearCubicWires.WireExponent3_5.FinalPass.SymF
