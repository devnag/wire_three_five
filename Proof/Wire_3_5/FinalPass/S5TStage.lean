import Proof.Wire_3_5.FinalPass.S5TPre7

/-! # S5-THR, part 27: the THR half's stage (P3:3083-3086, 3170-3181)

The stage the scrub runs: the parse (`parseW`: `n`, `a`, the mode flag), then the mode branch
(`iteMachine` on the flag's register): the THR path at a THR call, nothing at a SYM call.

* `ite_stepT`, `ite_stepF` (a branch machine runs the taken branch, one test step);
* `stageM`, **`stage_thr`** (all eight THR slots written), **`stage_sym`** (the THR slots kept blank).

Paper quantities of the main types: THR slots `8 … 15` at a THR call (S2's words and numbers); at a SYM call the
THR slots stay empty (`frontWordsOfW` at a SYM request, slots `8 … 15`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.HashSeed NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2InPorts tf2OutPorts TF2Ok)
open NearCubicWires.SupplierPipeline

section Ite
variable {t : ℕ}

theorem ite_stepT (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (bk c : Bank t) (n : ℕ)
    (hb : bk.bit i = true) (h : Step p n bk.H bk.A c.H c.A) : Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A :=
  ite_branch_step i p q bk c n (iteL b) p (by simp [hb]) (ite_halted_L i p q) (ite_step_L i p q) h

theorem ite_stepF (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (bk c : Bank t) (n : ℕ)
    (hb : bk.bit i = false) (h : Step q n bk.H bk.A c.H c.A) : Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A :=
  ite_branch_step i p q bk c n (iteR a) q (by simp [hb]) (ite_halted_R i p q) (ite_step_R i p q) h

end Ite

section Stage
variable (D : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (cap : ℕ)

/-- **The THR half's stage**: the parse, then the mode branch (the THR path, or nothing). -/
noncomputable def stageM (l : Literals) (cr j0 jL j1 : ℕ) :=
  Composition.machine
    (parseW (sIn D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x)
      (sTm D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) pR :
      WM (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) nrL).toProg.compile
    (iteMachine (rTape (pR 6)) (thrPathM D alg Dexp l cr j0 jL j1)
      (Prog.skip : Prog (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 2 + nrL)).compile)

theorem sIn_ne_sTm : sIn D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ≠
    sTm D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x := fun h => by
  have := congrArg Fin.val h; simp [sIn, sTm] at this

/-- **The stage at a SYM call**: the parse, then nothing; the THR slots and every stream kept. -/
theorem stage_sym (l : Literals) (cr j0 jL j1 : ℕ)
    (σ : WState (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) nrL)
    (n : ℕ) (codes cc : List ℕ) (tl : List Bool)
    (hIn : σ.st (sIn D _ _) = frame (PrimAsm.Data.reqW n false codes cc tl)) (hIh : σ.sh (sIn D _ _) = 0)
    (hT : σ.st (sTm D _ _) = sent ((PrimAsm.Data.reqW n false codes cc tl).length + 1)) (hTh : σ.sh (sTm D _ _) = 0)
    (hz : ∀ r, σ.val r = 0) (hcap : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength codes.length + 1) + 1 ≤ cap)
    (hn : n ≤ cap) (ha : codes.length ≤ cap) :
    ∃ σE, Step (stageM D alg Dexp l cr j0 jL j1)
        (parseCost n codes.length ((PrimAsm.Data.reqW n false codes cc tl).length + 1) + 1 + (0 + 1))
        (wenc cap σ).H (wenc cap σ).A (wenc cap σE).H (wenc cap σE).A ∧
      σE.st = σ.st ∧ (∀ r, σE.val r ≤ cap) := by
  have e1 := parseW_spec cap (sIn D _ _) (sTm D _ _) (sIn_ne_sTm D alg Dexp) pR n false codes cc tl
    ((PrimAsm.Data.reqW n false codes cc tl).length + 1) σ hIn hIh hT hTh (by omega) (fun j => hz _) hcap
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = ((σ.setv (pR 2) n).setv (pR 3) codes.length).setv (pR 6) (if false = true then 1 else 0) :=
    ⟨_, rfl⟩
  rw [← hσ1] at e1
  have hb : (wenc cap σ1).bit (rTape (pR 6)) = false := by
    rw [wbit_r, hσ1]; simp
  refine ⟨σ1, Step.seq (Exec.step (WExec.exec cap e1)) (ite_stepF _ _ _ (wenc cap σ1) (wenc cap σ1) 0 hb
    (skip_step _)), by rw [hσ1]; rfl, ?_⟩
  intro r
  rw [hσ1]
  simp only [WState.setv_val, Function.update_apply]
  have h1 : 1 ≤ cap := le_trans (Nat.le_add_left 1 _) hcap
  split_ifs <;> first | omega | exact ha | exact hn | (rw [hz]; omega)

theorem stage_thr (l : Literals) (cr j0 jL j1 : ℕ) (hj0 : j0 ≤ D) (hjL : jL ≤ D) (hj1 : j1 ≤ D)
    (σ : WState (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) nrL)
    (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (tl : List Bool) (Wp L Wt : ℕ) (pre : List Bool)
    (s : Fin (2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).t * (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0) → Bool)
    (hu : PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl =
      pre ++ frame (List.ofFn s))
    (hIn : σ.st (sIn D _ _) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
      (carriers.map Stars.Carrier.code) tl))
    (hT : σ.st (sTm D _ _) = sent ((pre ++ frame (List.ofFn s)).length + 1))
    (hx0 : σ.st (xsN D _ _ j0) = sent Wp) (hxL : σ.st (xsN D _ _ jL) = sent L)
    (hxW : σ.st (xsN D _ _ j1) = sent Wt)
    (hbl : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1),
      (1 ≤ i.val ∧ i.val ≤ 8) ∨ (13 + D ≤ i.val ∧ i.val ≠ 21 + D) → σ.st i = [])
    (hsh : ∀ i, σ.sh i = 0) (hz0 : ∀ r, σ.val r = 0)
    (hpcap : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength (PrimAsm.ReqBridge.thrCodes Cs).length + 1) + 1 ≤ cap)
    (hacap : a' ≤ cap)
    (hKb : ∀ c ∈ PrimAsm.ReqBridge.thrCodes Cs, natBitLength c ≤ Wp) (ha : a' ≤ 4) (hnc : carriers.length ≤ 2)
    (hN : PrimT.TS4.needT l cr P.n ≤ 2 * Wp + 2) (hn : 1 ≤ P.n) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
    (hcap1 : 1 ≤ PrimT.TS4.capTL l cr P.n)
    (hok : TF2Ok Cs (carriers.map Stars.Carrier.code) (Wp + (P.n + 1) ^ 26))
    (hneed : (PrimT.W6.numsW6 alg Dexp).need (P.n + PrimT.TS4.capTL l cr P.n) ≤ Wp + (P.n + 1) ^ 26)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ P.n + L) (hcN : natBitLength P.n + 1 ≤ 2 * Wt + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * Wt + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * Wt + 2)
    (hcx : ∀ x ∈ PrimAsm.ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + L ≤
      2 * Wt + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + P.n + L ≤
      2 * Wt + 2)
    (hcu : 2 * (PrimAsm.Data.unaryList (PrimAsm.ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * Wt + 2)
    (hcapn : P.n ≤ cap)
    (hc1 : 100 * ((pre ++ frame (List.ofFn s)).length + 1) + 10 * ((mpOf (vOf l cr P Cs alg Dexp carriers)).t + (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0) ≤ cap)
    (hc2 : 2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).t * (2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 + 2) + 1 + (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 + (mpOf (vOf l cr P Cs alg Dexp carriers)).t ≤ cap)
    (hc3 : (Hash4.winWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W).length ≤ cap) (hc4 : 2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 + 2 ≤ cap)
    (hcapS : (Hash4.seedWord (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 (Hash4.coefsRev (MajorantBits.coefVal (mpOf (vOf l cr P Cs alg Dexp carriers)) s))).length + 2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 + 2 ≤ cap)
    (hcapO : (ListEval.levelWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W (ListEval.rowsOf (MajorantBits.dataBits (mpOf (vOf l cr P Cs alg Dexp carriers)) s) (mpOf (vOf l cr P Cs alg Dexp carriers)).M)).length + 1 ≤
      cap) (hM : (mpOf (vOf l cr P Cs alg Dexp carriers)).M ≤ cap) (hJ : (mpOf (vOf l cr P Cs alg Dexp carriers)).J ≤ cap) (hc5 : a' + (vOf l cr P Cs alg Dexp carriers).nG + (vOf l cr P Cs alg Dexp carriers).dig + (mpOf (vOf l cr P Cs alg Dexp carriers)).M + 4 ≤ cap) :
    ∃ σE c, Step (stageM D alg Dexp l cr j0 jL j1) c (wenc cap σ).H (wenc cap σ).A (wenc cap σE).H
        (wenc cap σE).A ∧
      c ≤ parseCost P.n (PrimAsm.ReqBridge.thrCodes Cs).length ((pre ++ frame (List.ofFn s)).length + 1) + 1 + (1 + (chainACost alg Dexp l cr P.n (PrimAsm.ReqBridge.thrCodes Cs).length (carriers.map Stars.Carrier.code).length
          Wp + 1 + (chainBCost alg Cs carriers (Wp + (P.n + 1) ^ 26) L Wt + 1 +
        tailCost (pre ++ frame (List.ofFn s)).length (mpOf (vOf l cr P Cs alg Dexp carriers)).t (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 (Hash4.winWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W).length
          (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (Hash4.coefsRev (MajorantBits.coefVal (mpOf (vOf l cr P Cs alg Dexp carriers)) s)).length
          (ListEval.levelWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W (ListEval.rowsOf (MajorantBits.dataBits (mpOf (vOf l cr P Cs alg Dexp carriers)) s) (mpOf (vOf l cr P Cs alg Dexp carriers)).M)).length a'
          (vOf l cr P Cs alg Dexp carriers).nG (vOf l cr P Cs alg Dexp carriers).dig))) ∧
      σE.st (sIn D _ _) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
        (carriers.map Stars.Carrier.code) tl) ∧
      σE.st (sSlot D _ _ 0) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ (k : ℕ) (hk : k < 4), σE.st (sSlot D _ _ ⟨k + 1, by omega⟩) =
        tf2OutPorts alg (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
          tl) (Wp + (P.n + 1) ^ 26) Cs ⟨k + 2, by omega⟩) ∧
      σE.st (sSlot D _ _ 5) = PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (vOf l cr P Cs alg Dexp carriers).cut) ∧
      σE.st (sSlot D _ _ 6) = ListEval.levelWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W (ListEval.rowsOf (MajorantBits.dataBits (mpOf (vOf l cr P Cs alg Dexp carriers)) s) (mpOf (vOf l cr P Cs alg Dexp carriers)).M) ∧
      σE.st (sSlot D _ _ 7) = PrimAsm.Data.unaryList [a', (vOf l cr P Cs alg Dexp carriers).nG, (vOf l cr P Cs alg Dexp carriers).dig, (mpOf (vOf l cr P Cs alg Dexp carriers)).M] ∧
      σE.st (xsN D _ _ D) = σ.st (xsN D _ _ D) ∧ (∀ r, σE.val r ≤ cap)  := by
  have hal : (PrimAsm.ReqBridge.thrCodes Cs).length = a' := by simp [PrimAsm.ReqBridge.thrCodes]
  have e1 := parseW_spec cap (sIn D _ _) (sTm D _ _) (sIn_ne_sTm D alg Dexp) pR P.n true (PrimAsm.ReqBridge.thrCodes Cs)
    (carriers.map Stars.Carrier.code) tl ((pre ++ frame (List.ofFn s)).length + 1) σ hIn (hsh _)
    hT (hsh _) (by rw [hu]; omega) (fun j => hz0 _) hpcap
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = ((σ.setv (pR 2) P.n).setv (pR 3) (PrimAsm.ReqBridge.thrCodes Cs).length).setv (pR 6)
      (if true = true then 1 else 0) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have st1 : σ1.st = σ.st := by rw [hσ1]; rfl
  have sh1 : σ1.sh = σ.sh := by rw [hσ1]; rfl
  have hb : (wenc cap σ1).bit (rTape (pR 6)) = true := by
    rw [wbit_r, hσ1]; simp
  have v2 : σ1.val (pR 2) = P.n := by rw [hσ1]; simp [Function.update_apply, pR]
  have v3 : σ1.val (pR 3) = a' := by rw [hσ1]; simp [Function.update_apply, pR, hal]
  have vz : ∀ r : Fin nrL, 10 ≤ r.val → r.val < 53 → σ1.val r = 0 := fun r h1 _ => by
    rw [hσ1]; simp only [WState.setv_val, Function.update_apply]
    have e2 : r ≠ pR 2 := fun e => by rw [e] at h1; simp [pR] at h1
    have e3 : r ≠ pR 3 := fun e => by rw [e] at h1; simp [pR] at h1
    have e6 : r ≠ pR 6 := fun e => by rw [e] at h1; simp [pR] at h1
    rw [if_neg e6, if_neg e3, if_neg e2, hz0]
  have vc : ∀ r, σ1.val r ≤ cap := fun r => by
    have h1 : 1 ≤ cap := le_trans (Nat.le_add_left 1 _) hpcap
    rw [hσ1]; simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> first | omega | (rw [hz0]; omega) | (rw [hal]; exact hacap) | exact hcapn
  obtain ⟨σE, c, sP, hc, f0, f8, f9, f13, f14, f15, fD, fv⟩ := thrPath_spec D alg Dexp cap l cr j0 jL j1 hj0 hjL hj1 σ1
    P Cs carriers tl Wp L Wt pre s hu (by rw [st1]; exact hIn) (by rw [st1]; exact hT) (by rw [st1]; exact hx0)
    (by rw [st1]; exact hxL) (by rw [st1]; exact hxW) (fun i hi => by rw [st1]; exact hbl i hi)
    (fun i => by rw [sh1]; exact hsh i) v2 v3 vz vc hKb ha hnc hN hn hd hcap1 hok hneed hL hLX h2 hcN hcA hcK hcx
    hcy hcu hcapn hc1 hc2 hc3 hc4 hcapS hcapO hM hJ hc5
  refine ⟨σE, _, Step.seq (Exec.step (WExec.exec cap e1)) (ite_stepT _ _ _ (wenc cap σ1) (wenc cap σE) c hb sP),
    by omega, f0, f8, f9, f13, f14, f15, by rw [fD, st1], fv⟩

end Stage

end NearCubicWires.WireExponent3_5.FinalPass.S5T
