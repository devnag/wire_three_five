import Proof.Wire_3_5.Primitive.SeedFix.HbCells

/-! # C4.Hb, machine part 17: one cell as one step (`filt:soft`, P3:2253-2290)

"for each product and each `J_j`, the Gaussian-elimination machine counts [...]; the cleared weights make every
coefficient an integer" (P3:2262-2268). One cell of the Hb machine is five docked stages on the Hb bank: the validity
program, the records program, the elimination, the term program and the odometer's step. **`cell_step`**: from a bank
satisfying the loop invariant before cell `c` (**`HbX.Inv`**: the output `outAt c`, the odometer at `c`, the fixed
words, the elimination's registers `Ok`), the cell's machine reaches a bank satisfying the invariant before `c + 1`,
within `cellCost c`.

Paper quantity of the main type: the printed words `outAt c` (through `HbX.Inv`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord)

/-- A boundary word state: every head and register at `0`. -/
def bnd (st : Fin 24 → List Bool) : HS := ⟨fun _ => 0, st, fun _ => 0, false⟩

namespace HbX
variable (X : HbX)

/-- The elimination's own tapes at its state `(R, O, W, P)`. -/
def ex (R : SeedFix.Regs) (O W P : List Bool) : Fin 28 → List Bool :=
  ex28 X.mod X.ℓ X.T2 X.plen X.pfx X.m X.c1 X.c2 X.c3 X.c4 X.RV X.cL X.cE X.cK X.cC R O W P

/-- The word state's streams before cell `c`. -/
structure Streams (c : ℕ) (st : Fin 24 → List Bool) : Prop where
  out : st sOUT = X.outAt c
  olen : st sOLEN = List.replicate (X.outAt c).length true
  ht : st sHT = htWord X.Fs
  pops : st sPOPS = popsWord X.pops
  wt : st sWT = wtWord X.Ws
  ctr : st sCTR = binary X.L (X.d0 c)
  lam : st sLAM = unary (X.lamOf c) (X.J + 1)
  pc : st sPC = unary (X.pOf c) X.P
  ec : st sEC = unary (X.eOf c) X.nE
  qc : st sQC = unary (X.qOf c) X.N2
  more : st sMORE = [decide (c < X.n)]
  tt : st sTT = List.replicate X.T2 true
  ll : st sLL = List.replicate X.ℓ true
  jj : st sJJ = List.replicate X.J true
  gg : st sGG = List.replicate X.G true
  nn : st sNN = List.replicate (X.N2 - 1) true
  ee : st sEE = List.replicate (X.nE - 1) true
  pp : st sPP = List.replicate (X.P - 1) true
  cr : st sCR = List.replicate X.L true

/-- **The loop invariant** before cell `c`. -/
def Inv (c : ℕ) (A : Fin 94 → List Bool) : Prop :=
  ∃ (st : Fin 24 → List Bool) (R : SeedFix.Regs) (O W P : List Bool) (g v : Bool),
    A = hbBank X.cap X.capL (bnd st) (X.ex R O W P) ∧ R.Ok X.ℓ X.T2 ∧ X.Streams c st ∧ st sGF = [g] ∧ st sVAL = [v]

/-- The elimination block at width `k` (`elimX_run` at the Hb machine's capacities). -/
def ElimOk (k : ℕ) : Prop :=
  ∀ (R : SeedFix.Regs) (cons : List (ℕ × ℕ)) (stale O W P Xold : List Bool) (g0 : Bool), R.Ok X.ℓ X.T2 →
    (∀ con ∈ cons, con.1 < 2 ^ X.ℓ) → cons.length = X.T2 →
    Step SeedFix.elimM (SeedFix.elimCost X.ℓ X.T2 k X.plen X.T2) (fun _ => 0)
      (SeedFix.bank31 X.mod X.ℓ X.T2 X.plen X.pfx X.m X.c1 X.c2 X.c3 X.c4 X.RV X.cL X.cE R O
        (SeedFix.consTape X.ℓ k cons stale) W P (pad X.cK []) (pad X.cC (List.replicate (X.T2 * X.ℓ - X.plen) true))
        [g0] Xold)
      (fun _ => 0)
      (SeedFix.bank31 X.mod X.ℓ X.T2 X.plen X.pfx X.m X.c1 X.c2 X.c3 X.c4 X.RV X.cL X.cE
        (SeedFix.regsAt X.mod X.ℓ X.T2 k X.plen R cons cons.length)
        (SeedFix.ElimX.elimO X.mod X.ℓ X.T2 k X.plen X.pfx cons O W P) (SeedFix.consTape X.ℓ k cons stale)
        (SeedFix.ElimX.elimW X.mod X.ℓ X.T2 k X.plen X.pfx cons O W P)
        (SeedFix.ElimX.elimP X.mod X.ℓ X.T2 k X.plen X.pfx cons O W P) (pad X.cK [])
        (pad X.cC (List.replicate (X.T2 * X.ℓ - X.plen) true))
        [(JoinElimination.gauss (X.T2 * X.ℓ - X.plen) (JoinElimination.system X.mod X.ℓ X.T2 k X.plen X.pfx cons)).1]
        (overlay (List.replicate (X.T2 * X.ℓ - X.plen -
          (JoinElimination.gauss (X.T2 * X.ℓ - X.plen) (JoinElimination.system X.mod X.ℓ X.T2 k X.plen X.pfx cons)).2)
            true ++ [false]) Xold))

/-- The term program's bound at cell `c`. -/
def tcB (c : ℕ) : ℕ :=
  13 * (16 * ldSum (X.qOf c) X.G (X.lamOf c) X.J (X.pOf c) (X.eOf c) X.nE X.T2 X.ℓ + 15) + 5 + 1 +
    (2 + (termBound X.Fs X.pops X.Ws (X.outAt c).length X.T2 (X.lamOf c) X.J (X.xOf c) (X.eOf c) (X.qOf c) X.nE
      (X.idxOf c) (X.pOf c) X.G X.ℓ + 1 + ((X.tbOf c).length * 7 + 1))) + 1 +
    40 * (3 * (ldSum (X.qOf c) X.G (X.lamOf c) X.J (X.pOf c) (X.eOf c) X.nE X.T2 X.ℓ + 1) + 2)

/-- The odometer step's bound. -/
def advB : ℕ := 7 * X.L + 15 * (X.J + 1 + X.P + X.nE + X.N2) + 100

/-- **One cell's cost.** -/
def cellCost (c : ℕ) : ℕ :=
  (2 * valBound (X.lamOf c) X.J (X.pOf c) X.T2 X.ℓ (X.popOf c).2.length (popsWord X.pops).length + 2) + 1 +
    (2 * consBound (X.lamOf c) X.J X.T2 X.ℓ + 2) + 1 + SeedFix.elimCost X.ℓ X.T2 (X.kOfC c) X.plen X.T2 + 1 +
    (2 * X.tcB c + 2) + 1 + (2 * X.advB + 2)

/-- The global conditions on the Hb machine's data. -/
structure HbOk : Prop where
  hT : 1 ≤ X.T2
  hJℓ : X.J ≤ X.ℓ
  hW : X.Ws.length = X.J + 1
  hF : X.N2 * X.nE ≤ X.Fs.length
  hG : ∀ pop ∈ X.pops, ∀ gi ∈ pop.2, gi ≤ X.G
  hcap1 : 1 ≤ X.cap

/-- The per-cell capacity conditions. -/
structure CellOk (c : ℕ) : Prop where
  elim : X.ElimOk (X.kOfC c)
  capV : X.lamOf c + X.J + X.pOf c + X.T2 + X.ℓ + (popsWord X.pops).length + 2 ^ (X.ℓ + 1) + 4 ≤ X.cap
  capC : X.lamOf c + X.J + X.T2 + X.ℓ + 2 ≤ X.cap
  capS : ldSum (X.qOf c) X.G (X.lamOf c) X.J (X.pOf c) (X.eOf c) X.nE X.T2 X.ℓ + 2 ≤ X.cap
  capT1 : X.T2 + X.lamOf c + X.J + 5 + 2 * X.xOf c + (wtWord X.Ws).length ≤ X.cap
  capT2 : 3 + 2 * X.xOf c + (wtWord X.Ws).length + 1 + (htWord X.Fs).length + X.eOf c + X.qOf c * X.nE + X.nE +
    X.qOf c + X.T2 * (10 * monoRoom (4 * X.qOf c) X.G X.G + 2) + 1 + 11 * monoRoom (4 * X.qOf c) X.G X.G +
    (popsWord X.pops).length + 2 ^ (X.ℓ + 1) + X.pOf c + X.ℓ + X.G + X.T2 + 2 ≤ X.cap
  capT3 : (X.tbOf c).length ≤ X.cap
  logV : valBound (X.lamOf c) X.J (X.pOf c) X.T2 X.ℓ (X.popOf c).2.length (popsWord X.pops).length ≤ X.capL
  logC : consBound (X.lamOf c) X.J X.T2 X.ℓ ≤ X.capL
  logT : X.tcB c ≤ X.capL
  logA : X.advB ≤ X.capL

end HbX

/-- **One cell's machine**: validity, records, elimination, term, odometer step. -/
noncomputable def cellM := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (wmM valW) (wmM consW)) (RecoveryFocus.machine slE SeedFix.elimM)) (wmM tcellW)) (wmM advW)

section Step
variable (X : HbX)

theorem hbBank_bnd (cap capL : ℕ) (τ : HS) (st : Fin 24 → List Bool) (E : Fin 28 → List Bool) (hst : τ.st = st)
    (hv : τ.val = fun _ => 0) (hc : τ.cell = false) : hbBank cap capL τ E = hbBank cap capL (bnd st) E := by
  unfold hbBank; rw [wenc_A_congr cap τ (bnd st) hst hv hc]

theorem validB_pos (L lam J : ℕ) (γs : List Bool) (ιs : List ℕ) (h : validB L lam J γs ιs = true) :
    ∀ i ∈ ιs, i < L := by
  intro i hi
  unfold validB iB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hi
  have := (h.2 r hr).1
  rwa [List.getD_eq_getElem _ _ hr] at this

theorem overlay_term (w B : List Bool) : overlay (w ++ [false]) B = w ++ false :: B.drop (w.length + 1) := by
  simp [overlay]

theorem tbOf_eq (c : ℕ) (hlam : X.lamOf c < X.Ws.length) (hidx : X.idxOf c < X.Fs.length) (hp : X.pOf c < X.pops.length) :
    X.tbOf c = termBits (X.lamOf c < X.J ∧ parZ (X.γsOf c) = 1) (X.xOf c) X.Ws[X.lamOf c] X.Fs[X.idxOf c]
      ((X.ιsOf c).flatMap fun i => zRec X.G (X.qOf c) X.pops[X.pOf c].1 (X.pops[X.pOf c].2.getD i 0)) := by
  unfold HbX.tbOf HbX.popOf
  rw [List.getD_eq_getElem _ _ hlam, List.getD_eq_getElem _ _ hidx, List.getD_eq_getElem _ _ hp]

/-- **One cell as one step** between invariant banks. -/
theorem cell_step (c : ℕ) (hc : c < X.n) (hok : X.HbOk) (hcell : X.CellOk c) (A : Fin 94 → List Bool)
    (hA : X.Inv c A) : ∃ A', X.Inv (c + 1) A' ∧ Step cellM (X.cellCost c) (fun _ => 0) A (fun _ => 0) A' := by
  obtain ⟨st, R, O, W, P, g, v, rfl, hR, hs, hg, hv⟩ := hA
  obtain ⟨hB, hJ, hP, hE, hN⟩ := pos_of_lt_n X c hc
  have hp : X.pOf c < X.pops.length := Nat.mod_lt _ hP
  have hpop : X.popOf c = X.pops[X.pOf c] := List.getD_eq_getElem _ _ hp
  have hlamJ : X.lamOf c ≤ X.J := Nat.lt_succ_iff.mp (Nat.mod_lt _ hJ)
  have he : X.eOf c < X.nE := Nat.mod_lt _ hE
  have hq : X.qOf c < X.N2 := Nat.mod_lt _ hN
  have hγl : (X.γsOf c).length = X.T2 := binary_length _ _
  have hιl : (X.ιsOf c).length = X.T2 := by simp [HbX.ιsOf]
  have hι2 : ∀ i ∈ X.ιsOf c, i < 2 ^ X.ℓ := by
    intro i hi; simp only [HbX.ιsOf, List.mem_map] at hi; obtain ⟨r, _, rfl⟩ := hi; exact Nat.mod_lt _ (by positivity)
  have hC : st sCTR = ctrWord (X.γsOf c) (X.ιsOf c) X.ℓ := by rw [hs.ctr, ctrWord_eq]
  have hlamW : X.lamOf c < X.Ws.length := by rw [hok.hW]; omega
  have hidx : X.idxOf c < X.Fs.length := by
    have h1 : (X.qOf c + 1) * X.nE ≤ X.N2 * X.nE := Nat.mul_le_mul_right _ hq
    have := hok.hF; unfold HbX.idxOf; rw [Nat.add_mul, Nat.one_mul] at h1; omega
  -- 1: validity
  obtain ⟨τ1, n1, hn1, w1, st1e, v1e, c1e⟩ := valW_spec X.cap (X.γsOf c) (X.ιsOf c) X.pops (X.lamOf c) X.J (X.pOf c)
    X.T2 X.ℓ v hp hγl hιl hok.hT hι2 (bnd st) (fun _ => rfl) (fun _ => rfl) hs.pops hC hs.lam hs.jj hs.pc hs.tt
    hs.ll hv hcell.capV
  have hvc : validB X.pops[X.pOf c].2.length (X.lamOf c) X.J (X.γsOf c) (X.ιsOf c) = X.validC c := by
    unfold HbX.validC; rw [hpop]
  rw [hvc] at st1e
  have hlogV := hcell.logV
  rw [hpop] at hlogV
  have S1 := wmStep X.cap X.capL valW (bnd st) τ1 n1 w1 (fun _ => rfl) (fun _ => rfl) (by omega) (X.ex R O W P)
  set st1 := Function.update st sVAL [X.validC c] with hst1
  rw [hbBank_bnd X.cap X.capL τ1 st1 _ st1e v1e c1e] at S1
  -- 2: the records
  have hC1 : st1 sCTR = ctrWord (X.γsOf c) (X.ιsOf c) X.ℓ := by simp [st1, hC]
  obtain ⟨τ2, n2, hn2, w2, st2e, v2e, c2e⟩ := consW_spec X.cap (X.γsOf c) (X.ιsOf c) X.ℓ X.T2 (X.lamOf c) X.J
    hγl hιl (st1 sCONS) (st1 sS2) (bnd st1) (fun _ => rfl) (fun _ => rfl) hC1 (by simp [bnd, st1, hs.lam])
    (by simp [bnd, st1, hs.jj]) (by simp [bnd, st1, hs.tt]) (by simp [bnd, st1, hs.ll]) rfl rfl hcell.capC
  have S2 := wmStep X.cap X.capL consW (bnd st1) τ2 n2 w2 (fun _ => rfl) (fun _ => rfl)
    (by have := hcell.logC; omega) (X.ex R O W P)
  set recs := recsUpTo X.ℓ (X.lamOf c) (decide (X.lamOf c < X.J)) (X.γsOf c) (X.ιsOf c) X.T2 with hrecs
  set st2 := Function.update (Function.update st1 sS2 (overlay (X.γsOf c) (st1 sS2))) sCONS
    (overlay (recs ++ [false]) (st1 sCONS)) with hst2
  rw [hbBank_bnd X.cap X.capL τ2 st2 _ st2e v2e (by rw [c2e]; rfl)] at S2
  -- 3: the elimination
  set stale := (st1 sCONS).drop (recs.length + 1) with hstale
  have hcons : st2 sCONS = SeedFix.consTape X.ℓ (X.kOfC c) (X.consOfC c) stale := by
    have e := recs_consTape X.ℓ (X.lamOf c) X.J (X.γsOf c) (X.ιsOf c) hlamJ stale
    rw [hιl] at e
    simp only [st2, Function.update_self, overlay_term]
    exact e
  have hlab : ∀ con ∈ X.consOfC c, con.1 < 2 ^ X.ℓ := by
    intro con hcon
    simp only [HbX.consOfC, consL, List.mem_map, List.mem_range] at hcon
    obtain ⟨r, hr, rfl⟩ := hcon
    rw [List.getD_eq_getElem _ _ hr]; exact hι2 _ (List.getElem_mem _)
  have hconsl : (X.consOfC c).length = X.T2 := by simp [HbX.consOfC, consL, hιl]
  have hE3 := hcell.elim R (X.consOfC c) stale O W P (st2 sXE) g hR hlab hconsl
  rw [← hcons] at hE3
  have hg2 : st2 sGF = [g] := by simp [st2, st1, hg]
  have S3 := elimDock X.cap X.capL X.mod X.ℓ X.T2 X.plen X.pfx X.m X.c1 X.c2 X.c3 X.c4 X.RV X.cL X.cE X.cK X.cC _ R
    _ O _ W _ P _ (st2 sXE) _ g _ (bnd st2) hg2 rfl hE3
  set X3 := overlay (List.replicate (X.xOf c) true ++ [false]) (st2 sXE) with hX3
  set st3 := Function.update (Function.update st2 sGF [(X.ggOf c).1]) sXE X3 with hst3
  have eb3 : ((bnd st2).sets sGF [(X.ggOf c).1]).sets sXE X3 = bnd st3 := rfl
  rw [show (X.T2 * X.ℓ - X.plen - (JoinElimination.gauss (X.T2 * X.ℓ - X.plen)
      (JoinElimination.system X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c))).2) = X.xOf c from rfl] at S3
  rw [show (JoinElimination.gauss (X.T2 * X.ℓ - X.plen)
      (JoinElimination.system X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c))) = X.ggOf c from rfl, eb3] at S3
  -- 4: the term
  have hX3' : st3 sXE = List.replicate (X.xOf c) true ++ false :: (st2 sXE).drop (X.xOf c + 1) := by
    simp only [st3, Function.update_self, hX3, overlay_term, List.length_replicate]
  have hιv : X.validC c = true → ∀ i ∈ X.ιsOf c, i < X.pops[X.pOf c].2.length := by
    intro h; rw [← hpop]; exact validB_pos _ _ _ _ _ h
  have hGp : ∀ gi ∈ X.pops[X.pOf c].2, gi ≤ X.G := hok.hG _ (List.getElem_mem _)
  have hcap3 := hcell.capT3
  rw [tbOf_eq X c hlamW hidx hp] at hcap3
  obtain ⟨τ4, n4, hn4, w4, st4e, v4e, c4e⟩ := tcellW_spec X.cap X.Fs (X.γsOf c) (X.ιsOf c) X.pops X.Ws X.G (X.qOf c)
    X.ℓ (X.pOf c) (X.eOf c) X.nE X.N2 (X.idxOf c) (X.lamOf c) X.J X.T2 (X.xOf c) ((st2 sXE).drop (X.xOf c + 1))
    (X.validC c) (X.ggOf c).1 hE rfl hidx hp hlamW hlamJ hγl hιl hιv hι2 hGp (bnd st3) (fun _ => rfl)
    (fun _ => rfl) (by simp [bnd, st3, st2, st1, hs.olen, hs.out]) (by simp [bnd, st3, st2, st1, hs.ht])
    (by simp [bnd, st3, st2, st1, hs.pops]) (by simp [bnd, st3, st2, st1, hs.wt]) (by simp [bnd, st3, st2, st1, hC])
    (by simp [bnd, st3, st2, st1, hs.lam]) (by simp [bnd, st3, st2, st1, hs.pc, HbX.P]) (by simp [bnd, st3, st2, st1, hs.ec])
    (by simp [bnd, st3, st2, st1, hs.qc]) (by simp [bnd, st3, st2, st1, hs.jj]) (by simp [bnd, st3, st2, st1, hs.gg])
    (by simp [bnd, st3, st2, st1, hs.ee]) (by simp [bnd, st3, st2, st1, hs.tt]) (by simp [bnd, st3, st2, st1, hs.ll]) hX3'
    (by simp [bnd, st3, st2, st1]) (by simp [bnd, st3]) hcell.capS hcell.capT1 hcell.capT2 hcap3
  have hout3 : (bnd st3).st sOUT = X.outAt c := by simp [bnd, st3, st2, st1, hs.out]
  rw [hout3, ← tbOf_eq X c hlamW hidx hp] at st4e
  rw [hout3, ← tbOf_eq X c hlamW hidx hp] at hn4
  have hn4' : n4 ≤ X.tcB c := by
    have ht : termBound X.Fs X.pops X.Ws (X.outAt c).length X.T2 (X.lamOf c) X.J (X.xOf c) (X.eOf c) (X.qOf c) X.nE
      (X.idxOf c) (X.pOf c) X.G X.ℓ = termBound X.Fs X.pops X.Ws (X.outAt c).length X.T2 (X.lamOf c) X.J (X.xOf c)
      (X.eOf c) (X.qOf c) X.nE (X.idxOf c) (X.pOf c) X.G X.ℓ := rfl
    unfold HbX.tcB; omega
  have S4 := wmStep X.cap X.capL tcellW (bnd st3) τ4 n4 w4 (fun _ => rfl) (fun _ => rfl)
    (by have := hcell.logT; omega) (X.ex (SeedFix.regsAt X.mod X.ℓ X.T2 (X.kOfC c) X.plen R (X.consOfC c)
      (X.consOfC c).length) (SeedFix.ElimX.elimO X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c) O W P)
      (SeedFix.ElimX.elimW X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c) O W P)
      (SeedFix.ElimX.elimP X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c) O W P))
  have hcw : (if X.validC c = true ∧ (X.ggOf c).1 = true then X.tbOf c else []) = X.cellWord c := rfl
  rw [hcw] at st4e
  set st4 := Function.update (Function.update st3 sOUT (X.outAt c ++ X.cellWord c)) sOLEN
    (List.replicate ((X.outAt c).length + (X.cellWord c).length) true) with hst4
  rw [hbBank_bnd X.cap X.capL τ4 st4 _ st4e v4e (by rw [c4e]; rfl)] at S4
  -- 5: the odometer's step
  obtain ⟨hn1', hodo⟩ := odo_next X c hc
  obtain ⟨τ5, n5, hn5, w5, st5e, v5e, c5e⟩ := advW_spec X.cap (binary X.L (X.d0 c)) X.J X.P X.nE X.N2 (X.lamOf c)
    (X.pOf c) (X.eOf c) (X.qOf c) (decide (c < X.n)) (by omega) hp he hq (bnd st4) (fun _ => rfl) (fun _ => rfl)
    (by simp [bnd, st4, st3, st2, st1, hs.ctr]) (by simp [bnd, st4, st3, st2, st1, hs.cr, binary_length])
    (by simp [bnd, st4, st3, st2, st1, hs.lam]) (by simp [bnd, st4, st3, st2, st1, hs.jj])
    (by simp [bnd, st4, st3, st2, st1, hs.pc]) (by simp [bnd, st4, st3, st2, st1, hs.pp])
    (by simp [bnd, st4, st3, st2, st1, hs.ec]) (by simp [bnd, st4, st3, st2, st1, hs.ee])
    (by simp [bnd, st4, st3, st2, st1, hs.qc]) (by simp [bnd, st4, st3, st2, st1, hs.nn])
    (by simp [bnd, st4, st3, st2, st1, hs.more]) hok.hcap1
  simp only [binary_length] at st5e
  rw [hodo, hn1'] at st5e
  have S5 := wmStep X.cap X.capL advW (bnd st4) τ5 n5 w5 (fun _ => rfl) (fun _ => rfl)
    (by have := hcell.logA; unfold HbX.advB at this; rw [binary_length] at hn5; omega)
    (X.ex (SeedFix.regsAt X.mod X.ℓ X.T2 (X.kOfC c) X.plen R (X.consOfC c) (X.consOfC c).length)
      (SeedFix.ElimX.elimO X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c) O W P)
      (SeedFix.ElimX.elimW X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c) O W P)
      (SeedFix.ElimX.elimP X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c) O W P))
  set st5 := τ5.st with hst5
  rw [hbBank_bnd X.cap X.capL τ5 st5 _ rfl v5e (by rw [c5e]; rfl)] at S5
  refine ⟨_, ⟨st5, _, _, _, _, (X.ggOf c).1, X.validC c, rfl,
    SeedFix.regsAt_ok _ _ _ _ _ R _ hR _, ?_, ?_, ?_⟩,
    ((((S1.seq S2).seq S3).seq S4).seq S5).enlarge ?_⟩
  · have hmore : (if (if c + 1 = X.n then 1 else 0) = 1 then false else decide (c < X.n)) = decide (c + 1 < X.n) := by
      by_cases h : c + 1 = X.n
      · simp [h]
      · rw [if_neg (by simp [h])]; simp; omega
    rw [hmore] at st5e
    constructor
    · rw [st5e]; simp [bnd, st4, X.outAt_succ]
    · rw [st5e]; simp [bnd, st4, X.outAt_succ]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.ht]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.pops]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.wt]
    · rw [st5e]; simp [bnd]
    · rw [st5e]; simp [bnd]
    · rw [st5e]; simp [bnd, HbX.P]
    · rw [st5e]; simp [bnd]
    · rw [st5e]; simp [bnd]
    · rw [st5e]; simp [bnd]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.tt]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.ll]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.jj]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.gg]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.nn]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.ee]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.pp]
    · rw [st5e]; simp [bnd, st4, st3, st2, st1, hs.cr]
  · rw [st5e]; simp [bnd, st4, st3]
  · rw [st5e]; simp [bnd, st4, st3, st2, st1]
  · unfold HbX.cellCost
    rw [binary_length] at hn5
    unfold HbX.advB
    have hv' : valBound (X.lamOf c) X.J (X.pOf c) X.T2 X.ℓ X.pops[X.pOf c].2.length (popsWord X.pops).length =
        valBound (X.lamOf c) X.J (X.pOf c) X.T2 X.ℓ (X.popOf c).2.length (popsWord X.pops).length := by rw [hpop]
    omega

end Step

end NearCubicWires.WireExponent3_5.PrimT.HbM
