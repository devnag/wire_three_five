import Proof.Wire_3_5.Primitive.SeedFix.TabSym

/-! # SW parts: the SYM table machine, with its scan tape exposed (P3:3049-3050, 3170-3178)

The SYM words writer's top tables (`symWords` word `4·1 + j`, the framed top table `frame (ofFn C.top)` of
circuit `j`, P3:3170-3178) are not in the request verbatim: the circuit's code is one Cantor-paired number
(`encodeNormalizedSymmetricThresholdCircuit`), and the top table appears only after base's SYM decoder chain, inside
the table machine `symTableM`. Its scan stage keeps its input: after the whole run the tape `scanSl 0`
(`= 1694`, outside the table stage's slots) holds the decoder's native word
`symWord C = natWord C.bottomCount ++ (frame (ofFn C.top) ++ tabSeg (symGates C))` (`PrimT.symWord_eq`).

* **`symTable_stepW`**: `symTable_step` (the same machine, fuel, entry and six exits), plus
  `tout (scanSl 0) = natWord C.bottomCount ++ (frame (List.ofFn C.top) ++ tabSeg (symGates C))`.

The proof is `symTable_step`'s (`PrimTTabSym`), cloned with the one extra exit (the statement).

Paper quantity of the main type: circuit `C`'s framed top table `frame (ofFn C.top)` (with the bottom count before it
and the gate segment after it) on the machine's scan tape. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymParts.TabSymW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimT.SymTab

open PCJd4d1d9d7d1fa4313_Production in
/-- **The SYM gate table with the scan tape**: `symTable_step`'s run and exits, and the decoder's native word
(the bottom count, the framed top table, the gate segment) on the tape `scanSl 0`. -/
theorem symTable_stepW {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L)
    (h2 : 2 ≤ n + L) :
    ∃ tout : Fin 1789 → List Bool,
      Step symTableM (symTableCost C L) (fun _ => 0) (symIn (encodeNormalizedSymmetricThresholdCircuit C) n L)
        (fun _ => 0) tout ∧
      tout 0 = frame (natWord (encodeNormalizedSymmetricThresholdCircuit C)) ∧ tout 1 = List.replicate n true ∧
      tout 2 = List.replicate L true ∧ tout 3 = gatesW (tabH (Stars.symGates C)) (Stars.symGates C) ∧
      tout 4 = List.replicate (tabH (Stars.symGates C)) true ∧
      tout 5 = List.replicate (Stars.symGates C).length true ∧
      tout (scanSl 0) = natWord C.bottomCount ++ (frame (List.ofFn C.top) ++ tabSeg (Stars.symGates C)) := by
  set code := encodeNormalizedSymmetricThresholdCircuit C with hcode
  set k := natBitLength code with hk
  set G := Stars.symGates C with hG
  set h := tabH G with hh
  set P := cC * (k + 1 + 1) ^ 26 with hP
  have zH : ∀ {t : ℕ} (sl : Fin t → Fin 1789), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => dockH_existing sl _ _ (fun _ => rfl)
  -- 1: the cell
  have d1 := cell_step.dock cellSl cellSl_inj (fun _ => 0) (symIn code n L) (fun _ => rfl) (entry_cell code n L)
  rw [zH] at d1
  -- 2: the preparation
  obtain ⟨o2, s2, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := prepStage code n L
  have d2 := s2.dock prepSl prepSl_inj (fun _ => 0) (A1 code n L) (fun _ => rfl) (entry_prep code n L)
  rw [zH] at d2
  -- 3: the capacity
  obtain ⟨o3, s3, q0, q55⟩ := BlockPlatform.UnaryCalc.poly_step 26 cC (k + 1)
  have d3 := s3.dock polySl polySl_inj (fun _ => 0) (A2 code n L o2) (fun _ => rfl) (entry_poly code n L k o2 p5)
  rw [zH] at d3
  -- 4: the decoder chain
  obtain ⟨o4, s4, -, r1688⟩ := symChain_run C P L L (binary k code) (by rw [binary_length, capacity_eq])
    (symBits_decode C) ((sym_wire_le_desc C).trans hL) hL
  have d4 := s4.dock chainSl chainSl_inj (fun _ => 0) (A3 code n L o2 o3) (fun _ => rfl)
    (entry_chain code n L P (binary k code) o2 o3 p4 p6 p7 p8 q55)
  rw [zH] at d4
  -- 5: the scan
  obtain ⟨o5, s5, t0, t1, t2, t3, t4, t5, t6, t7⟩ := scanStage (n + L) C.bottomCount (List.ofFn C.top) G (symWord C)
    (symWord_eq C) (symScan_le C L hL)
  have d5 := s5.dock scanSl scanSl_inj (fun _ => 0) (A4 code n L o2 o3 o4) (fun _ => rfl)
    (entry_scan code n L (n + L) (symWord C) o2 o3 o4 p1 (by rw [p9]) r1688)
  rw [zH] at d5
  -- 6: the unary width and the table
  obtain ⟨o6, s6, u3, u5, u6⟩ := tabStage (n + L) h G (symGateOk C L hL h2)
  have d6 := s6.dock tabSl tabSl_inj (fun _ => 0) (A5 code n L o2 o3 o4 o5) (fun _ => rfl)
    (entry_tab code n L (n + L) h (tabSeg G) o2 o3 o4 o5 p2 (by rw [p10]) (by rw [p11]) t1 t2 t3 t4 t6 t7)
  rw [zH] at d6
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq d6))))
  have run' : Step symTableM _ (fun _ => 0) (symIn code n L) (fun _ => 0) (A6 code n L o2 o3 o4 o5 o6) := run
  refine ⟨A6 code n L o2 o3 o4 o5 o6, run'.enlarge (by unfold symTableCost; exact le_refl _), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · unfold A6; rw [miss_tab _ (by decide)]; unfold A5; rw [miss_scan _ (by decide)]; unfold A4
    rw [miss_chain _ (by decide)]; unfold A3; rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [show (0 : Fin 1789) = prepSl 0 from rfl, hit_prep, p0]
  · unfold A6; rw [show (1 : Fin 1789) = tabSl 3 from rfl, hit_tab, u3]
  · unfold A6; rw [miss_tab _ (by decide)]; unfold A5; rw [miss_scan _ (by decide)]; unfold A4
    rw [miss_chain _ (by decide)]; unfold A3; rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [show (2 : Fin 1789) = prepSl 3 from rfl, hit_prep, p3]
  · unfold A6; rw [show (3 : Fin 1789) = tabSl 5 from rfl, hit_tab, u5]
  · unfold A6; rw [show (4 : Fin 1789) = tabSl 6 from rfl, hit_tab, u6]
  · unfold A6; rw [miss_tab _ (by decide)]; unfold A5; rw [show (5 : Fin 1789) = scanSl 5 from rfl, hit_scan, t5]
  · unfold A6; rw [miss_tab _ (by decide)]; unfold A5; rw [hit_scan, t0, symWord_eq]

end NearCubicWires.WireExponent3_5.FinalPass.SymParts.TabSymW
