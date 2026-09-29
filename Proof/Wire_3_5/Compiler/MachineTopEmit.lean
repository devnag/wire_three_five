import Proof.Wire_3_5.Compiler.MachineTopSubsets

/-! # C3 v2 top level, T4 as a stage: the emit machine on the compiler stages' output (P3:1929-1936, 1728-1731)

Paper: "Each resulting conjunction contains at most `Q'd` equation atoms, so Lemma alg:stack turns it into one separated
equation" (P3:1934-1936), printed as "the two successor cuts" (P3:1728-1731). MC8's `emit_run` walks the groups
`groupsRef Q' (shapeOf D) m V` and writes the request's cut words; as a stage of the top-level machine it runs on the
tapes the earlier stages leave: the groups and their terminator, C3a's pool stream (T1), the zero field, the empty
stack stream and the unary widths (T2); its registers start from whatever the compiler stages left (the emit machine
reads none of them before writing). **`emit_stage`**: the emit loop, then the output's terminator, every head back at
cell 0: the output tape holds `(c3v2Ref a R).flatMap (cutWord (p+1)) ++ [false]` and the count tape one mark per
stacked occurrence. The paper quantity is the printer request's cut words. Main declarations: `e2`, `emitStageM`,
**`emit_stage`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (cutWord)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def e2 : Fin 1 → Fin (29 + 1) := ![2]

theorem e2_inj : Function.Injective e2 := by decide

theorem install_e2 (A : Fin (29 + 1) → List Bool) (v : Fin 1 → List Bool) :
    install e2 A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29] := by
  funext i
  fin_cases i
  · exact install_other e2 A v 0 (by decide)
  · exact install_other e2 A v 1 (by decide)
  · exact install_slot e2 e2_inj A v 0
  · exact install_other e2 A v 3 (by decide)
  · exact install_other e2 A v 4 (by decide)
  · exact install_other e2 A v 5 (by decide)
  · exact install_other e2 A v 6 (by decide)
  · exact install_other e2 A v 7 (by decide)
  · exact install_other e2 A v 8 (by decide)
  · exact install_other e2 A v 9 (by decide)
  · exact install_other e2 A v 10 (by decide)
  · exact install_other e2 A v 11 (by decide)
  · exact install_other e2 A v 12 (by decide)
  · exact install_other e2 A v 13 (by decide)
  · exact install_other e2 A v 14 (by decide)
  · exact install_other e2 A v 15 (by decide)
  · exact install_other e2 A v 16 (by decide)
  · exact install_other e2 A v 17 (by decide)
  · exact install_other e2 A v 18 (by decide)
  · exact install_other e2 A v 19 (by decide)
  · exact install_other e2 A v 20 (by decide)
  · exact install_other e2 A v 21 (by decide)
  · exact install_other e2 A v 22 (by decide)
  · exact install_other e2 A v 23 (by decide)
  · exact install_other e2 A v 24 (by decide)
  · exact install_other e2 A v 25 (by decide)
  · exact install_other e2 A v 26 (by decide)
  · exact install_other e2 A v 27 (by decide)
  · exact install_other e2 A v 28 (by decide)
  · exact install_other e2 A v 29 (by decide)

theorem dockH_e2 (H : Fin (29 + 1) → ℕ) (v : Fin 1 → ℕ) :
    dockH e2 H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29] := by
  funext i
  fin_cases i
  · exact dockH_other e2 H v 0 (by decide)
  · exact dockH_other e2 H v 1 (by decide)
  · exact dockH_slot e2 e2_inj H v 0
  · exact dockH_other e2 H v 3 (by decide)
  · exact dockH_other e2 H v 4 (by decide)
  · exact dockH_other e2 H v 5 (by decide)
  · exact dockH_other e2 H v 6 (by decide)
  · exact dockH_other e2 H v 7 (by decide)
  · exact dockH_other e2 H v 8 (by decide)
  · exact dockH_other e2 H v 9 (by decide)
  · exact dockH_other e2 H v 10 (by decide)
  · exact dockH_other e2 H v 11 (by decide)
  · exact dockH_other e2 H v 12 (by decide)
  · exact dockH_other e2 H v 13 (by decide)
  · exact dockH_other e2 H v 14 (by decide)
  · exact dockH_other e2 H v 15 (by decide)
  · exact dockH_other e2 H v 16 (by decide)
  · exact dockH_other e2 H v 17 (by decide)
  · exact dockH_other e2 H v 18 (by decide)
  · exact dockH_other e2 H v 19 (by decide)
  · exact dockH_other e2 H v 20 (by decide)
  · exact dockH_other e2 H v 21 (by decide)
  · exact dockH_other e2 H v 22 (by decide)
  · exact dockH_other e2 H v 23 (by decide)
  · exact dockH_other e2 H v 24 (by decide)
  · exact dockH_other e2 H v 25 (by decide)
  · exact dockH_other e2 H v 26 (by decide)
  · exact dockH_other e2 H v 27 (by decide)
  · exact dockH_other e2 H v 28 (by decide)
  · exact dockH_other e2 H v 29 (by decide)

/-- The terminator put on the output tape (index 2) of the emit layout. -/
theorem dockPut2 (H : Fin (29 + 1) → ℕ) (A : Fin (29 + 1) → List Bool) (w : List Bool) (hA : A 2 = w)
    (hH : H 2 = w.length) :
    Step (RecoveryFocus.machine e2 (putM false)) 1 H A (dockH e2 H ![w.length + 1]) (install e2 A ![w ++ [false]]) := by
  have e := putStep false (overlay w []) w.length
  rw [overlay_write, overlay_nil_right, overlay_nil_right] at e
  exact dockRun e e2 e2_inj H A (by intro j; fin_cases j; exact hH) (by intro j; fin_cases j; exact hA)

/-- The emit loop then the output's terminator, every head back at cell 0. -/
noncomputable def emitStageM :=
  MaskedReset.machine (Composition.machine (StreamController.machine groupBodyM 0) (RecoveryFocus.machine e2 (putM false)))
    (fun _ => true)

variable (a : DecompositionAlgorithm)

/-- The emit loop's cost at the request's parameters. -/
def emitCostR (R : C3Req) : ℕ :=
  emitCost (2 ^ R.m * R.V.length) (R.P.Q * ((poolChildren a R.P.gates R.P.flips).length + 1) ^ (R.P.Q * R.d)) R.p R.P.Q
    (R.p + 1) (poolChildren a R.P.gates R.P.flips).length R.P.h R.P.width (R.P.h * R.P.Q * R.d)

/-- **The emit stage** (T4 in the top-level machine): from the groups, the pool stream and the constants, the output
tape holds the request's cut words and a terminator, the count tape one mark per stacked occurrence; every head is
back at cell 0. -/
theorem emit_stage (R : C3Req) (hR : R.Pre a) (g0 : Emit.GSt) (hg0o : g0.en.out = []) (hg0c : g0.en.cnt = 0)
    (cap capA capC capCut capCoef capEnt capL : ℕ)
    (hcap1 : 2 * (R.p + 1) + 1 ≤ cap) (hcapL : 2 * (R.P.h * R.P.Q * R.d) + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hcapE : 2 * (R.P.Q + (poolChildren a R.P.gates R.P.flips).length + 1) + 1 ≤ cap)
    (hcapS : appendCost 0 (2 * (R.P.width + R.P.width + 1)) 1 ≤ cap)
    (hA1 : mergeAllCost (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h ≤ capA)
    (hA2 : skipCost (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h ≤ capA)
    (hC : appendCost 0 (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h + R.P.h) ≤ capC)
    (hcut0 : cut0Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width) ≤ capCut)
    (hcut1 : cut1Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width) ≤ capCut)
    (hcoef : coefRawCost R.P.Q (R.p + 1) R.p ≤ capCoef)
    (hent : entryCost R.P.Q (R.p + 1) (poolChildren a R.P.gates R.P.flips).length R.P.h R.P.width (R.P.h * R.P.Q * R.d) R.p ≤ capEnt)
    (hL : emitCostR a R + 1 + 1 ≤ capL) :
    ∃ gf : Emit.GSt, Step emitStageM (2 * (emitCostR a R + 1 + 1) + 2) (fun _ => 0)
      (Fin.addCases (![Poly.groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ [false], ((poolChildren a R.P.gates R.P.flips).flatMap (labRecs R.P.h R.P.side R.P.width)).flatMap frame, [], frame (List.replicate (R.p + 1) false), Kit.streamTape (List.replicate (2 * (R.P.width + R.P.width + 1)) [true]) [], List.replicate R.P.Q true, List.replicate (R.P.width + R.P.width) true, g0.rcb, [g0.rpar], g0.en.re, g0.en.s1, g0.en.s2, g0.en.rp, g0.en.rn, g0.en.rd, [false], g0.en.rp1, g0.en.rc, [g0.en.pk], [g0.en.sc], [g0.en.nz], [g0.en.sv], [g0.en.snv], [], List.replicate cap false, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false, List.replicate capEnt false] : Fin (29 + 1) → List Bool)
        (fun _ : Fin 1 => List.replicate capL false))
      (fun _ => 0)
      (Fin.addCases (![Poly.groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ [false], ((poolChildren a R.P.gates R.P.flips).flatMap (labRecs R.P.h R.P.side R.P.width)).flatMap frame, (c3v2Ref a R).flatMap (cutWord (R.p + 1)) ++ [false], frame (List.replicate (R.p + 1) false), Kit.streamTape (List.replicate (2 * (R.P.width + R.P.width + 1)) [true]) [], List.replicate R.P.Q true, List.replicate (R.P.width + R.P.width) true, gf.rcb, [gf.rpar], gf.en.re, gf.en.s1, gf.en.s2, gf.en.rp, gf.en.rn, gf.en.rd, [false], gf.en.rp1, gf.en.rc, [gf.en.pk], [gf.en.sc], [gf.en.nz], [gf.en.sv], [gf.en.snv], List.replicate (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length true, List.replicate cap false, List.replicate capA false, List.replicate capC false, List.replicate capCut false, List.replicate capCoef false, List.replicate capEnt false] : Fin (29 + 1) → List Bool)
        (fun _ : Fin 1 => List.replicate capL false)) := by
  obtain ⟨gf, hout, hcnt, st⟩ := emit_run a R hR [] [] [] [] [] [] [] [] [] g0 cap capA capC capCut capCoef capEnt rfl rfl
    hcap1 hcapL hcapE hcapS hA1 hA2 hC hcut0 hcut1 hcoef hent
  refine ⟨gf, ?_⟩
  rw [enBH_vec, enBH_vec, enBA_vec, enBA_vec, hout, hcnt, hg0o, hg0c] at st
  simp only [List.nil_append, List.append_nil, overlay_nil_right, List.length_nil, Nat.zero_add, stackRecs_nil,
    List.replicate_zero] at st
  have j := st.seq (dockPut2 _ _ _ rfl rfl)
  rw [install_e2, dockH_e2] at j
  have m := j.mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hL
  exact (m.congr_in (addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (mask_heads_zero _) rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Top
