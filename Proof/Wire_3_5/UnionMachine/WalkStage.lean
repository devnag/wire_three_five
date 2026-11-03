import Proof.Wire_3_5.UnionMachine.WalkRun
import Proof.Wire_3_5.UnionMachine.TailAsm

/-! # C6 tail, item 3: the walk-bank producer, the `WalkBankProducer`

"The walk starts uniformly [...] the seed consists of the initial base seed and `O(t)` edge-label bits" (P3:2083-2087,
2098-2100): from a walk sample's index word, the entry bank of base's `WalkTimeLoop.run`. One machine on `14 + 4`
tapes (the producer's ports `0 … 13`; scratch `14` the cell, `15` the bank program's register, `16`, `17` the logs):
1. the cell; the register-free writer of the register tape `0^{R+n+LW+1}` (`reg0_spec`, docked by `sl0`);
2. the bank program (`WalkRun.bank_spec`, docked by `sl1`): the bank, the counter word, the inputs kept;
3. one step moving the heads of ports `5` and `8` to `1` (`WalkTimeLoop.run`'s entry heads);
within `walkBankCost`, the residues on the scratch tapes (the cell, the register, the two logs `0^k`) bounded by it
(**`walk_run`**, **`walkBank`**).

Paper quantity of the main type: the walk sample's start vertex and edge labels, as the bank `WalkTimeLoop.A`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.WalkStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW)
open NearCubicWires.WireExponent3_5.UnionMachine.TailAsm (cell_dock zeroH)

/-! ## The register tape of the bank program -/

theorem emitRun_spec (cap : ℕ) {ns nr : ℕ} (S D : Fin (ns + 1)) (hSD : S ≠ D) : ∀ (j h : ℕ) (σ : WState ns nr),
    σ.st S = List.replicate (h + j) true → σ.sh S = h → σ.sh D = (σ.st D).length →
    ∃ τ, WExec cap (.whs S (.seq (emitW D false) (.fwd S))) σ τ (j * 7 + 1) ∧
      τ.st D = σ.st D ++ List.replicate j false ∧ τ.sh D = (τ.st D).length ∧ τ.st S = σ.st S ∧
      (∀ i, i ≠ D → i ≠ S → Same σ τ i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, h, σ, hS, hh, hD => by
    have hz : wbit σ S = false := by unfold wbit; rw [hS, hh, Nat.add_zero]; exact SampKit.rd_rep_end h
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hD, rfl, fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | j + 1, h, σ, hS, hh, hD => by
    have hw : wbit σ S = true := by unfold wbit; rw [hS, hh]; exact SampKit.rd_rep (h + (j + 1)) h (by omega)
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap D false σ hD
    obtain ⟨σ2, s2, f2, f2h, o2, v2, c2⟩ := fwd_facts cap S σ1
    obtain ⟨τ, s3, e3, e3h, f3, o3, v3, c3⟩ := emitRun_spec cap S D hSD j (h + 1) σ2
      (by rw [f2, (o1 S hSD).1, hS]; congr 1; omega) (by rw [f2h, (o1 S hSD).2, hh])
      (by rw [(o2 D (Ne.symm hSD)).1, (o2 D (Ne.symm hSD)).2]; exact e1h)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) (by omega), ?_, e3h, ?_, fun i hiD hiS => ?_, ?_, ?_⟩
    · rw [e3, (o2 D (Ne.symm hSD)).1, e1, List.replicate_succ, List.append_assoc]; rfl
    · rw [f3, f2, (o1 S hSD).1]
    · exact ((o1 i hiD).trans' (o2 i hiS)).trans' (o3 i hiD hiS)
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

/-- The register tape's writer: a zero per cell of the rulers `1^R`, `1^n`, `1^{LW}`, then one more. -/
def regW0 : WM 3 0 :=
  .seq (.whs 1 (.seq (emitW 0 false) (.fwd 1))) (.seq (.whs 2 (.seq (emitW 0 false) (.fwd 2)))
    (.seq (.whs 3 (.seq (emitW 0 false) (.fwd 3))) (emitW 0 false)))

/-- The register tape writer's entry state. -/
def σ0 (n R LW : ℕ) : WState 3 0 :=
  ⟨fun _ => 0, fun i => if i.val = 1 then List.replicate R true else if i.val = 2 then List.replicate n true
    else if i.val = 3 then List.replicate LW true else [], fun r => r.elim0, false⟩

def reg0Cost (n R LW : ℕ) : ℕ := R * 7 + 1 + 1 + (n * 7 + 1 + 1 + (LW * 7 + 1 + 1 + 3))

theorem reg0_spec (n R LW : ℕ) : ∃ τ, WExec 0 regW0 (σ0 n R LW) τ (reg0Cost n R LW) ∧
    τ.st 0 = List.replicate (R + n + LW + 1) false ∧ τ.st 1 = List.replicate R true ∧
    τ.st 2 = List.replicate n true ∧ τ.st 3 = List.replicate LW true ∧ τ.cell = false := by
  obtain ⟨τ1, s1, e1, eh1, f1, o1, -, c1⟩ := emitRun_spec 0 (1 : Fin 4) 0 (by decide) R 0 (σ0 n R LW)
    (by simp [σ0]) rfl rfl
  obtain ⟨τ2, s2, e2, eh2, f2, o2, -, c2⟩ := emitRun_spec 0 (2 : Fin 4) 0 (by decide) n 0 τ1
    (by rw [(o1 2 (by decide) (by decide)).1]; simp [σ0]) (by rw [(o1 2 (by decide) (by decide)).2]; rfl) eh1
  obtain ⟨τ3, s3, e3, eh3, f3, o3, -, c3⟩ := emitRun_spec 0 (3 : Fin 4) 0 (by decide) LW 0 τ2
    (by rw [(o2 3 (by decide) (by decide)).1, (o1 3 (by decide) (by decide)).1]; simp [σ0])
    (by rw [(o2 3 (by decide) (by decide)).2, (o1 3 (by decide) (by decide)).2]; rfl) eh2
  obtain ⟨τ, s4, e4, -, o4, -, c4⟩ := emit_facts 0 (0 : Fin 4) false τ3 eh3
  refine ⟨τ, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [e4, e3, e2, e1, List.replicate_succ', ← List.replicate_append_replicate,
      ← List.replicate_append_replicate]
    simp [σ0]
  · rw [(o4 1 (by decide)).1, (o3 1 (by decide) (by decide)).1, (o2 1 (by decide) (by decide)).1, f1]; rfl
  · rw [(o4 2 (by decide)).1, (o3 2 (by decide) (by decide)).1, f2, (o1 2 (by decide) (by decide)).1]; rfl
  · rw [(o4 3 (by decide)).1, f3, (o2 3 (by decide) (by decide)).1, (o1 3 (by decide) (by decide)).1]; rfl
  · rw [c4, c3, c2, c1]; rfl

/-! ## The layout and the machine -/

/-- The register tape writer's tapes: its target (the bank program's register) at `15`, its cell at `14`, its rulers
`R`, `n`, `LW` at `12`, `11`, `13`, its log at `16`. -/
def sl0 : Fin 6 → Fin 18 := ![15, 14, 12, 11, 13, 16]

theorem sl0_inj : Function.Injective sl0 := by decide

/-- The bank program's tapes: its streams at the ports, its cell at `14`, its register at `15`, its log at `17`. -/
def sl1 (j : Fin 17) : Fin 18 :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then 14 else if j.val ≤ 14 then j.val - 1 else if j.val = 15 then 15 else 17,
    by split_ifs <;> omega⟩

theorem sl1_inj : Function.Injective sl1 := by decide

/-- One step: the heads of ports `5` and `8` one cell on. -/
def nudgeP : Prog 18 := .act (fun _ => none) (fun i => if i.val = 5 ∨ i.val = 8 then HeadMove.right else HeadMove.stay)

theorem nudge_step (A : Fin 18 → List Bool) :
    Step nudgeP.compile 1 (fun _ => 0) A (fun i => if i.val = 5 ∨ i.val = 8 then 1 else 0) A := by
  have hs := Exec.step (Exec.act (⟨fun _ => 0, A⟩ : Bank 18) (fun _ => none)
    (fun i => if i.val = 5 ∨ i.val = 8 then HeadMove.right else HeadMove.stay))
  have hH : ((⟨fun _ => 0, A⟩ : Bank 18).act (fun _ => none)
      (fun i => if i.val = 5 ∨ i.val = 8 then HeadMove.right else HeadMove.stay)).H =
      fun i => if i.val = 5 ∨ i.val = 8 then 1 else 0 := by
    funext i; simp only [Bank.act]; split_ifs <;> rfl
  have hA : ((⟨fun _ => 0, A⟩ : Bank 18).act (fun _ => none)
      (fun i => if i.val = 5 ∨ i.val = 8 then HeadMove.right else HeadMove.stay)).A = A := by
    funext i; rfl
  rw [hH, hA] at hs
  exact hs

/-- **The walk-bank producer's machine.** -/
noncomputable def walkM :=
  Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (14 : Fin 18)) NearCubicWires.WireExponent3_5.PrimT.cellM)
    (Composition.machine (RecoveryFocus.machine sl0 (Rewind.machine regW0.toProg.compile))
      (Composition.machine (RecoveryFocus.machine sl1 (Rewind.machine WalkRun.bankW.toProg.compile))
        nudgeP.compile))

theorem inst1 (c : Fin 18) (B : Fin 18 → List Bool) (v : List Bool) (i : Fin 18) :
    install (fun _ : Fin 1 => c) B (fun _ => v) i = if i = c then v else B i := by
  by_cases h : i = c
  · subst h; rw [if_pos rfl]
    exact install_slot (fun _ : Fin 1 => i) (fun a b _ => Subsingleton.elim a b) B (fun _ => v) 0
  · rw [if_neg h]; exact install_other _ _ _ i (fun _ e => h e.symm)

/-! ## The cost -/

theorem total_le (r n R LW : ℕ) :
    1 + 1 + (2 * reg0Cost n R LW + 2 + 1 + (2 * WalkRun.bankCost r n R LW + 2 + 1 + 1)) ≤
      PrimT.WalkBank.walkBankCost r n R LW ∧ reg0Cost n R LW ≤ PrimT.WalkBank.walkBankCost r n R LW ∧
      WalkRun.bankCost r n R LW ≤ PrimT.WalkBank.walkBankCost r n R LW ∧
      R + n + LW + 1 ≤ PrimT.WalkBank.walkBankCost r n R LW := by
  unfold reg0Cost WalkRun.bankCost WalkRun.padCost WalkRun.tapesCost PrimT.WalkBank.walkBankCost
  obtain ⟨S, hS⟩ : ∃ S, S = 160 * n + 2 * r + R + LW + 2 := ⟨_, rfl⟩
  rw [← hS]
  have h2 : 2000 * S ≤ 1000 * S ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ## The run -/

/-- **The walk-bank producer's run** (the `WalkBankProducer.run`). -/
theorem walk_run (r n R LW : ℕ) (sample : SupplierWalk.MargulisWalkSample (2 ^ r) (n + 1)) (hR : 2 * r + 1 ≤ R)
    (hLW : 2 * r + 1 ≤ LW) :
    ∃ J : Fin 4 → List Bool, (∀ j, (J j).length ≤ PrimT.WalkBank.walkBankCost r n R LW) ∧
      Step walkM (PrimT.WalkBank.walkBankCost r n R LW) (fun _ => 0)
        (Fin.addCases (m := 14) (n := 4) (motive := fun _ => List Bool)
          (PrimT.WalkBank.inPorts r n R LW (PrimT.WalkBank.seedIndexWord r n sample)) (fun _ => []))
        (Fin.addCases (m := 14) (n := 4) (motive := fun _ => ℕ) (PrimT.WalkBank.outHeads n) (fun _ => 0))
        (Fin.addCases (m := 14) (n := 4) (motive := fun _ => List Bool) (PrimT.WalkBank.outPorts r n R LW sample)
          J) := by
  obtain ⟨hT, hT0, hT1, hTc⟩ := total_le r n R LW
  -- the cell and the register tape
  have d1 := cell_dock (14 : Fin 18) (Fin.addCases (m := 14) (n := 4) (motive := fun _ => List Bool)
    (PrimT.WalkBank.inPorts r n R LW (PrimT.WalkBank.seedIndexWord r n sample)) (fun _ => [])) rfl
  obtain ⟨τ0, s0, e00, e01, e02, e03, cl0⟩ := reg0_spec n R LW
  obtain ⟨out0, k0, st0, ho0, hl0, hk0⟩ := WalkKit.wm_stepJ 0 regW0 (σ0 n R LW) τ0 _ s0
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  have hA0 : ∀ j : Fin 6, install (fun _ : Fin 1 => (14 : Fin 18)) (Fin.addCases (m := 14) (n := 4)
      (motive := fun _ => List Bool) (PrimT.WalkBank.inPorts r n R LW (PrimT.WalkBank.seedIndexWord r n sample))
      (fun _ => [])) (fun _ => [false]) (sl0 j) =
      Fin.addCases (m := 3 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σ0 n R LW)).A (fun _ => []) j := by
    intro j; rw [inst1]; fin_cases j <;> rfl
  have d2 := st0.dock sl0 sl0_inj (fun _ => 0) _ (fun _ => rfl) hA0
  rw [zeroH] at d2
  -- the bank program
  obtain ⟨τ1, s1, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, bv, bc⟩ :=
    WalkRun.bank_spec (R + n + LW) r n R LW sample hR (by omega) (by omega) (by omega)
  obtain ⟨out1, k1, st1, ho1, hl1, hk1⟩ := WalkKit.wm_stepJ (R + n + LW) WalkRun.bankW
    (WalkRun.σB r n R LW (PrimT.WalkBank.seedIndexWord r n sample)) τ1 _ s1
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero _ _ (fun _ => rfl) (fun _ => rfl))
  set B2 := install sl0 (install (fun _ : Fin 1 => (14 : Fin 18)) (Fin.addCases (m := 14) (n := 4)
      (motive := fun _ => List Bool) (PrimT.WalkBank.inPorts r n R LW (PrimT.WalkBank.seedIndexWord r n sample))
      (fun _ => [])) (fun _ => [false])) out0 with hB2
  have hA1 : ∀ j : Fin 17, B2 (sl1 j) = Fin.addCases (m := 13 + 2 + 1) (n := 1) (motive := fun _ => List Bool)
      (wenc (R + n + LW) (WalkRun.σB r n R LW (PrimT.WalkBank.seedIndexWord r n sample))).A (fun _ => []) j := by
    intro j
    fin_cases j
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · show install sl0 _ out0 (sl0 1) = _
      rw [install_slot sl0 sl0_inj, show (1 : Fin 6) = Fin.castAdd 1 (1 : Fin 5) from rfl, ho0]
      show [τ0.cell] = [false]; rw [cl0]
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
    · show install sl0 _ out0 (sl0 3) = _
      rw [install_slot sl0 sl0_inj, show (3 : Fin 6) = Fin.castAdd 1 (3 : Fin 5) from rfl, ho0]
      show τ0.st 2 = _; rw [e02]; rfl
    · show install sl0 _ out0 (sl0 2) = _
      rw [install_slot sl0 sl0_inj, show (2 : Fin 6) = Fin.castAdd 1 (2 : Fin 5) from rfl, ho0]
      show τ0.st 1 = _; rw [e01]; rfl
    · show install sl0 _ out0 (sl0 4) = _
      rw [install_slot sl0 sl0_inj, show (4 : Fin 6) = Fin.castAdd 1 (4 : Fin 5) from rfl, ho0]
      show τ0.st 3 = _; rw [e03]; rfl
    · show install sl0 _ out0 (sl0 0) = _
      rw [install_slot sl0 sl0_inj, show (0 : Fin 6) = Fin.castAdd 1 (0 : Fin 5) from rfl, ho0]
      show τ0.st 0 = regTape (R + n + LW) 0; rw [e00, regTape_zero]
    · rw [hB2, install_other sl0 _ out0 _ (by decide), inst1]; rfl
  have d3 := st1.dock sl1 sl1_inj (fun _ => 0) B2 (fun _ => rfl) hA1
  rw [zeroH] at d3
  have d4 := nudge_step (install sl1 B2 out1)
  -- the exit bank
  have eH : (fun i : Fin 18 => if i.val = 5 ∨ i.val = 8 then 1 else 0) =
      Fin.addCases (m := 14) (n := 4) (motive := fun _ => ℕ) (PrimT.WalkBank.outHeads n) (fun _ => 0) := by
    funext i; fin_cases i <;> rfl
  have eA : install sl1 B2 out1 = Fin.addCases (m := 14) (n := 4) (motive := fun _ => List Bool)
      (PrimT.WalkBank.outPorts r n R LW sample) (fun q => install sl1 B2 out1 (Fin.natAdd 14 q)) := by
    funext i
    fin_cases i
    · show install sl1 B2 out1 (sl1 ⟨0, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨0, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨0, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (0 : Fin 14) = _
      rw [b0]
      show _ = Theorem25Completion.WalkTimeLoop.A R LW sample [] 0 0
      rw [WalkMath.bank_eq]; rfl
    · show install sl1 B2 out1 (sl1 ⟨2, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨2, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨2, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (1 : Fin 14) = _
      rw [b1]
      show _ = Theorem25Completion.WalkTimeLoop.A R LW sample [] 0 1
      rw [WalkMath.bank_eq]; rfl
    · show install sl1 B2 out1 (sl1 ⟨3, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨3, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨3, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (2 : Fin 14) = _
      rw [b2]
      show _ = Theorem25Completion.WalkTimeLoop.A R LW sample [] 0 2
      rw [WalkMath.bank_eq]; rfl
    · show install sl1 B2 out1 (sl1 ⟨4, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨4, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨4, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (3 : Fin 14) = _
      rw [b3]
      show _ = Theorem25Completion.WalkTimeLoop.A R LW sample [] 0 3
      rw [WalkMath.bank_eq]; rfl
    · show install sl1 B2 out1 (sl1 ⟨5, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨5, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨5, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (4 : Fin 14) = _
      rw [b4]
      show _ = Theorem25Completion.WalkTimeLoop.A R LW sample [] 0 4
      rw [WalkMath.bank_eq]; rfl
    · show install sl1 B2 out1 (sl1 ⟨6, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨6, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨6, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (5 : Fin 14) = _
      rw [b5]
      show _ = Theorem25Completion.WalkTimeLoop.A R LW sample [] 0 5
      rw [WalkMath.bank_eq]; rfl
    · show install sl1 B2 out1 (sl1 ⟨7, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨7, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨7, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (6 : Fin 14) = _
      rw [b6]
      show _ = Theorem25Completion.WalkTimeLoop.A R LW sample [] 0 6
      rw [WalkMath.bank_eq]; rfl
    · show install sl1 B2 out1 (sl1 ⟨8, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨8, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨8, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (7 : Fin 14) = _
      rw [b7]
      show _ = Theorem25Completion.WalkTimeLoop.A R LW sample [] 0 7
      rw [WalkMath.bank_eq]; rfl
    · show install sl1 B2 out1 (sl1 ⟨9, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨9, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨9, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (8 : Fin 14) = _
      rw [b8]
      rfl
    · show install sl1 B2 out1 (sl1 ⟨10, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨10, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨10, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (9 : Fin 14) = _
      rw [b9]
      rfl
    · show install sl1 B2 out1 (sl1 ⟨11, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨11, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨11, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (10 : Fin 14) = _
      rw [b10]
      rfl
    · show install sl1 B2 out1 (sl1 ⟨12, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨12, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨12, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (11 : Fin 14) = _
      rw [b11]
      rfl
    · show install sl1 B2 out1 (sl1 ⟨13, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨13, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨13, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (12 : Fin 14) = _
      rw [b12]
      rfl
    · show install sl1 B2 out1 (sl1 ⟨14, by decide⟩) = _
      rw [install_slot sl1 sl1_inj, show (⟨14, by decide⟩ : Fin 17) = Fin.castAdd 1 (⟨14, by decide⟩ : Fin 16)
        from rfl, ho1]
      show τ1.st (13 : Fin 14) = _
      rw [b13]
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
  refine ⟨fun q => install sl1 B2 out1 (Fin.natAdd 14 q), fun q => ?_, ?_⟩
  · fin_cases q
    · show (install sl1 B2 out1 (sl1 1)).length ≤ _
      rw [install_slot sl1 sl1_inj, show (1 : Fin 17) = Fin.castAdd 1 (1 : Fin 16) from rfl, ho1]
      show [τ1.cell].length ≤ _; simp; omega
    · show (install sl1 B2 out1 (sl1 15)).length ≤ _
      rw [install_slot sl1 sl1_inj, show (15 : Fin 17) = Fin.castAdd 1 (15 : Fin 16) from rfl, ho1]
      show (regTape (R + n + LW) (τ1.val 0)).length ≤ _
      rw [bv, regTape_zero, List.length_replicate]; omega
    · show (install sl1 B2 out1 16).length ≤ _
      rw [install_other sl1 B2 out1 16 (by decide), hB2]
      show (install sl0 _ out0 (sl0 5)).length ≤ _
      rw [install_slot sl0 sl0_inj]
      rw [show (5 : Fin 6) = Fin.natAdd (3 + 2 + 0) (0 : Fin 1) from rfl, hl0, List.length_replicate]; omega
    · show (install sl1 B2 out1 (sl1 16)).length ≤ _
      rw [install_slot sl1 sl1_inj, show (16 : Fin 17) = Fin.natAdd (13 + 2 + 1) (0 : Fin 1) from rfl, hl1,
        List.length_replicate]; omega
  · rw [← eH, ← eA]
    exact (d1.seq (d2.seq (d3.seq d4))).enlarge hT

/-- **The walk-bank producer** (the interface), built. -/
noncomputable def walkBank : PrimT.WalkBank.WalkBankProducer where
  x := 4
  s := _
  M := walkM
  run := fun r n R LW sample hR hLW => walk_run r n R LW sample hR hLW

end NearCubicWires.WireExponent3_5.UnionMachine.WalkStage
