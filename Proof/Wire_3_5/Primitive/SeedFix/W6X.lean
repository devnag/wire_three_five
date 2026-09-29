import Proof.Wire_3_5.Primitive.SeedFix.W6W

/-! # W6, part 24: the word phase and proof 1's two programs, chained

P3:2543-2558 (row:threshold-rows: `|𝒢|` and the family's magnitude exponent, from the circuits' payloads): from the
fill's state (`σ1`), the word phase (`p1_spec2`), then proof 1's program with the `|𝒢|` tail (`progC_dock2`) and with the
exponent tail (`progE_dock2`), at the THR request (`tw_payOf`, `Cv_thr`, `E_thr`):
* `payF_cat` (the four payloads are the top word), `pcC`/`pcE` (the two programs' counts), `body1M`,
  **`body1_run`**: `1^{|𝒢|}` on block C's tape `1`, `1^E` on block E's tape `1` (`E` the magnitude exponent), `rN … rCap`
  = `n, a', M, ncar, cap_T`, every other register `0`, every stream off the two blocks as the fill left it.

Paper quantities of the main type: `|𝒢|`, the magnitude exponent, `M = |thrOccs|`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.PacketsMeta NearCubicWires.PacketsMeta.Lev NearCubicWires.PacketsMeta.Setup
open NearCubicWires.PacketsMeta.Tail NearCubicWires.PacketsMeta.Prog NearCubicWires.PacketsMeta.Spec
open NearCubicWires.PacketsMeta.Bounds
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

variable (alg : DecompositionAlgorithm)

theorem payF_cat (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (ha : a' ≤ 4) :
    payF alg Cs 0 ++ payF alg Cs 1 ++ payF alg Cs 2 ++ payF alg Cs 3 = twOf (dsOf alg (Primitive.thrRequest P Cs)) := by
  rw [PrimThrW.W6Meta.tw_payOf alg P Cs ha]
  unfold payF
  interval_cases a' <;> simp [List.ofFn_succ]

/-- Proof 1's program with the `|𝒢|` tail: its count at the THR request. -/
noncomputable def pcC (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) : ℕ :=
  2 * PrimThrW.W6Meta.progCost (twOf (dsOf alg (Primitive.thrRequest P Cs))) (dsOf alg (Primitive.thrRequest P Cs))
    (PrimThrW.W6Meta.costC (PrimThrW.W6Meta.metaW (twOf (dsOf alg (Primitive.thrRequest P Cs)))) (Cv (dsOf alg (Primitive.thrRequest P Cs)))) + 2

/-- Proof 1's program with the exponent tail: its count at the THR request. -/
noncomputable def pcE (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) : ℕ :=
  2 * PrimThrW.W6Meta.progCost (twOf (dsOf alg (Primitive.thrRequest P Cs))) (dsOf alg (Primitive.thrRequest P Cs))
    (PrimThrW.W6Meta.costE (PrimThrW.W6Meta.metaW (twOf (dsOf alg (Primitive.thrRequest P Cs)))) (Fv (dsOf alg (Primitive.thrRequest P Cs)))) + 2

/-- **The word phase and the two programs.** -/
noncomputable def body1M :=
  Composition.machine (Composition.machine p1W.toProg.compile
    (RecoveryFocus.machine (fun j => sTape (nr := 80) (bC j))
      (MaskedReset.machine (PacketsMeta.Prog.prog PacketsMeta.Tail.selTailM) (fun _ => true))))
    (RecoveryFocus.machine (fun j => sTape (nr := 80) (bE j))
      (MaskedReset.machine (PacketsMeta.Prog.prog PrimThrW.W6Meta.tailE) (fun _ => true)))

theorem body1_run (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (codes : List ℕ)
    (tl : List Bool) (ncar capT V : ℕ) (ha : a' ≤ 4)
    (c1 : 2 ^ (natBitLength P.n + 1) ≤ 2 * V + 2) (c2 : 2 ^ (natBitLength a' + 1) ≤ 2 * V + 2)
    (c3 : 2 * (payF alg Cs 0 ++ payF alg Cs 1 ++ payF alg Cs 2 ++ payF alg Cs 3).length + 4 ≤ 2 * V + 2)
    (c4 : 4 ≤ 2 * V + 2) (c5 : fnw.length ≤ 2 * V + 2)
    (c6 : ∀ j, 2 ^ (natBitLength (szOf Cs j) + 1) + (Primitive.thrOccs P Cs).length ≤ 2 * V + 2)
    (c7 : ncar ≤ 2 * V + 2) (c8 : capT ≤ 2 * V + 2) :
    ∃ (τ : WL) (m : ℕ), Step body1M m
        (wenc (2 * V + 2) (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)).H
        (wenc (2 * V + 2) (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)).A
        (wenc (2 * V + 2) τ).H (wenc (2 * V + 2) τ).A ∧
      m ≤ 30 * (opU (2 * V + 2) + 1) + 1 + pcC alg P Cs + 1 + pcE alg P Cs ∧
      τ.val 48 = P.n ∧ τ.val 49 = a' ∧ τ.val 50 = (Primitive.thrOccs P Cs).length ∧ τ.val 51 = ncar ∧
      τ.val 52 = capT ∧ (∀ r : Fin 80, r ≠ 48 → r ≠ 49 → r ≠ 50 → r ≠ 51 → r ≠ 52 → τ.val r = 0) ∧
      τ.st (sBC 1) = List.replicate (Fintype.card (Primitive.ThrEq P Cs alg)) true ∧ τ.sh (sBC 1) = 0 ∧
      τ.st (sBE 1) = List.replicate (familyMagnitudeExponent (Primitive.thrRealize P Cs alg)) true ∧
      τ.sh (sBE 1) = 0 ∧
      (∀ s, (∀ k, s ≠ sBC k) → (∀ k, s ≠ sBE k) →
        τ.st s = (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs).st s) ∧
      (∀ s, (∀ k, s ≠ sBC k) → (∀ k, s ≠ sBE k) → s ≠ sReq → s ≠ sNc → s ≠ sCap → (∀ i, s ≠ sPay i) → τ.sh s = 0) ∧
      τ.cell = false := by
  have four : (Primitive.thrRequest P Cs).circuits.length ≤ 4 := by show (List.ofFn Cs).length ≤ 4; rw [List.length_ofFn]; exact ha
  have hcat := payF_cat alg P Cs ha
  refine (p1_spec2 (2 * V + 2) (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs) P.n a'
    (Primitive.thrOccs P Cs).length ncar capT (payF alg Cs) (szOf Cs) _ ha (payF_frame alg Cs) (payF_nil alg Cs)
    (payF_sz alg Cs) (M_sum P Cs ha) (by rw [σ1_req, req_form]) (σ1_pay alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs) (σ1_nc alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)
    (σ1_cap alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs) (fun k => σ1_blank alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs _ (by left; show 30 ≤ 30 + k.val; omega))
    (fun k => σ1_blank alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs _ (by left; show 30 ≤ 91 + k.val; omega)) (fun s => rfl) (fun r => rfl)
    c1 c2 c3 c4 c5 c6 c7 c8).elim fun τ1 h1 => h1.elim fun m1 h1' => ?_
  have e1 := h1'.1
  have hm1 := h1'.2.1
  have post := h1'.2.2
  have s1 := (WExec.exec (2 * V + 2) e1).step
  have hne : ∀ k k' : Fin 61, sBC k ≠ sBE k' := fun k k' h => by
    have := congrArg Fin.val h; simp only [sBC, sBE] at this; omega
  have hnePay : ∀ (i : Fin 4) (k : Fin 61), sBC k ≠ sPay i ∧ sBE k ≠ sPay i := fun i k => by
    constructor <;> intro h <;> have := congrArg Fin.val h <;> simp only [sBC, sBE, sPay] at this <;> omega
  have hneL : ∀ k : Fin 61, sBC k ≠ sReq ∧ sBC k ≠ sNc ∧ sBC k ≠ sCap ∧ sBE k ≠ sReq ∧ sBE k ≠ sNc ∧ sBE k ≠ sCap :=
    fun k => by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;>
        simp only [sBC, sBE, sReq, sNc, sCap] at this <;> omega
  have hC0 : τ1.st (sBC 0) = frame (twOf (dsOf alg (Primitive.thrRequest P Cs))) := by rw [post.twC.1, hcat]
  have hC2 : τ1.st (sBC 2) = frame PrimThrW.W6Meta.nw0 := post.nwC.1
  have hCb : ∀ k : Fin 61, k.val ≠ 0 → k.val ≠ 2 → τ1.st (sBC k) = [] := fun k h0 h2 => by
    rw [post.st (sBC k) (fun h => h0 (by have := congrArg Fin.val h; simp only [sBC] at this; omega)) (hne k 0)
      (fun h => h2 (by have := congrArg Fin.val h; simp only [sBC] at this; omega)) (hne k 2)]
    exact σ1_blank alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs _ (by left; show 30 ≤ 30 + k.val; omega)
  have hCsh : ∀ k : Fin 61, τ1.sh (sBC k) = 0 := fun k => by
    rw [post.sh (sBC k) (hneL k).1 (hneL k).2.1 (hneL k).2.2.1 (fun i => (hnePay i k).1)]; rfl
  refine (progC_dock2 (2 * V + 2) alg (Primitive.thrRequest P Cs) four τ1 hC0 hC2 hCb hCsh).elim fun τ2 hC => ?_
  have s2 := hC.1
  have hC1 := hC.2.1
  have hC1sh := hC.2.2.1
  have hCout := hC.2.2.2.1
  have hCval := hC.2.2.2.2.1
  have hCcell := hC.2.2.2.2.2
  have hE0 : τ2.st (sBE 0) = frame (twOf (dsOf alg (Primitive.thrRequest P Cs))) := by
    rw [(hCout (sBE 0) (fun k h => hne k 0 h.symm)).1, post.twE.1, hcat]
  have hE2 : τ2.st (sBE 2) = frame PrimThrW.W6Meta.nw0 := by
    rw [(hCout (sBE 2) (fun k h => hne k 2 h.symm)).1]; exact post.nwE.1
  have hEb : ∀ k : Fin 61, k.val ≠ 0 → k.val ≠ 2 → τ2.st (sBE k) = [] := fun k h0 h2 => by
    rw [(hCout (sBE k) (fun k' h => hne k' k h.symm)).1,
      post.st (sBE k) (fun h => hne 0 k h.symm)
        (fun h => h0 (by have := congrArg Fin.val h; simp only [sBE] at this; omega)) (fun h => hne 2 k h.symm)
        (fun h => h2 (by have := congrArg Fin.val h; simp only [sBE] at this; omega))]
    exact σ1_blank alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs _ (by left; show 30 ≤ 91 + k.val; omega)
  have hEsh : ∀ k : Fin 61, τ2.sh (sBE k) = 0 := fun k => by
    rw [(hCout (sBE k) (fun k' h => hne k' k h.symm)).2,
      post.sh (sBE k) (hneL k).2.2.2.1 (hneL k).2.2.2.2.1 (hneL k).2.2.2.2.2 (fun i => (hnePay i k).2)]; rfl
  refine (progE_dock2 (2 * V + 2) alg (Primitive.thrRequest P Cs) four τ2 hE0 hE2 hEb hEsh).elim fun τ3 hE => ?_
  have s3 := hE.1
  have hE1 := hE.2.1
  have hE1sh := hE.2.2.1
  have hEout := hE.2.2.2.1
  have hEval := hE.2.2.2.2.1
  have hEcell := hE.2.2.2.2.2
  have sAll : Step body1M (m1 + 1 + pcC alg P Cs + 1 + pcE alg P Cs)
      (wenc (2 * V + 2) (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)).H (wenc (2 * V + 2) (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)).A
      (wenc (2 * V + 2) τ3).H (wenc (2 * V + 2) τ3).A := (s1.seq s2).seq s3
  have hbd : m1 + 1 + pcC alg P Cs + 1 + pcE alg P Cs ≤ 30 * (opU (2 * V + 2) + 1) + 1 + pcC alg P Cs + 1 + pcE alg P Cs := by
    generalize pcC alg P Cs = X
    generalize pcE alg P Cs = Y
    omega
  refine ⟨τ3, _, sAll, hbd, ?_, ?_, ?_, ?_, ?_, fun r h48 h49 h50 h51 h52 => ?_,
    ?_, ?_, ?_, ?_, fun s hC hE => ?_, fun s hC hE h1 h2 h3 h4 => ?_, ?_⟩
  · rw [hEval, hCval]; exact post.vN
  · rw [hEval, hCval]; exact post.vA
  · rw [hEval, hCval]; exact post.vM
  · rw [hEval, hCval]; exact post.vNc
  · rw [hEval, hCval]; exact post.vCap
  · rw [hEval, hCval, post.v0 r h48 h49 h50 h51 h52]; rfl
  · rw [(hEout (sBC 1) (fun k h => hne 1 k h)).1, hC1, PrimThrW.W6Meta.Cv_thr alg P Cs ha]
  · rw [(hEout (sBC 1) (fun k h => hne 1 k h)).2]; exact hC1sh 1
  · rw [hE1, PrimThrW.W6Meta.E_thr alg P Cs ha]
  · exact hE1sh 1
  · rw [(hEout s hE).1, (hCout s hC).1]
    exact post.st s (hC 0) (hE 0) (hC 2) (hE 2)
  · rw [(hEout s hE).2, (hCout s hC).2, post.sh s h1 h2 h3 h4]; rfl
  · rw [hEcell, hCcell, post.cell]; rfl

end NearCubicWires.WireExponent3_5.PrimT.W6
