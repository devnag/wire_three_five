import Proof.Wire_3_5.Primitive.SeedFix.NwB11

/-! # NW phase (b), part 12: phase (b)'s machine and its run

**`bM`** = `compile(wa1W ; wa2W)` ; `docksMT` (the front end and W6, docked) ; `compile(wbW)` with W6's ports `3, 5, 6, 7`
(`|𝒢|`, `cut`, `#primes`, `Σp`). **`b_run`**: from (c)'s exit bank at a THR request word
`reqW n true (thrCodes Cs) cc tl` on `sIn`, the register programs at the virtual capacity `c₀ ≤ cap` (`capUp'`), the
docks at `cap`: the input kept, the word streams blank, every head at `0`, `rN … rT` kept, `rV = vVal …`, every other
register `0`.

Paper quantity of the main type: phase (b)'s value `V = |PrimeIndex(cut)|·|E|·Q` in `rV` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.SupplierPipeline

variable (x : ℕ)

/-- The first half's cost. -/
def wa1Cost (c vN vM vE vT n a nc wl cr fe kh feL : ℕ) : ℕ :=
  7 * (vN + vM + vE + vT) + 8 + 1 + (40 * wl + 60 * UnaryPow.sq c + 1 +
    (ThrDecF.tACost n a nc wl cr fe c + 1 + (7 * (kh + feL) + 4)))

/-- The second half's cost. -/
def wa2Cost (c n cr t sp L tv ncar capT Dn : ℕ) : ℕ :=
  20 * (3 * c + 2) + 1 + (TS4.capTCost c n cr t sp L + 1 + (6 * c + 6 + 2 * UnaryPow.sq c + 1 +
    (150 * UnaryPow.sq c + (Dn + 1) * (4 * UnaryPow.sq c) + 40 * (tv + ncar + capT) + 40)))

/-- The program after the docks' cost. -/
def wbCost (c vN vM vE vT V : ℕ) : ℕ :=
  4 * UnaryPow.sq c + 48 * c + 20 + 1 + (250 * UnaryPow.sq c + 1 + (50 * UnaryPow.sq c + 40000 + 1 +
    (512 * (3 * c + 2) + 7 * (vN + vM + vE + vT + V) + 10)))

section Run
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- W6's out-port `3 + k` (the `k`-th THR number, unary). -/
def pB (hx : ThrDecF.dX T N ≤ x) (k : ℕ) (hk : k < 14) : Fin (LNS x + 1) :=
  ThrDecF.w6M T N x hx (Fin.castAdd N.x ⟨k + 3, by omega⟩)

/-- **Phase (b)'s machine.** -/
noncomputable def bM (hx : ThrDecF.dX T N ≤ x) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) :=
  Composition.machine (Composition.machine (WM.seq (wa1W x cr fe) (wa2W x T N hx cr ζ Cδ C)).toProg.compile
    (ThrDecF.docksMT T N x hx))
    (wbW x (pB x T N hx 0 (by omega)) (pB x T N hx 2 (by omega)) (pB x T N hx 3 (by omega))
      (pB x T N hx 4 (by omega))).toProg.compile

theorem get_nG (v : PrimThrW.Joins.ThrNumVals) : v.get 0 = v.nG := rfl
theorem get_cut (v : PrimThrW.Joins.ThrNumVals) : v.get 2 = v.cut := rfl
theorem get_nPr (v : PrimThrW.Joins.ThrNumVals) : v.get 3 = v.nPr := rfl
theorem get_pSum (v : PrimThrW.Joins.ThrNumVals) : v.get 4 = v.pSum := rfl

theorem sIn_sk : NumsPh2.sIn x = sk x 150 := Fin.ext rfl
theorem sW0_sk : NumsPh2.sW0 x = sk x 151 := Fin.ext rfl
theorem sW1_sk : NumsPh2.sW1 x = sk x 152 := Fin.ext rfl

/-- **Phase (b)'s run.** -/
theorem b_run (hx : ThrDecF.dX T N ≤ x) (cr fe cap c₀ : ℕ) (hc₀ : c₀ ≤ cap) (P : Shared.StarParams)
    (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (cc : List ℕ) (tl : List Bool)
    (hKb : ∀ c ∈ ReqBridge.thrCodes Cs,
      natBitLength c ≤ (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length)
    (σ : WState (LNS x) LNR) (vN vM vE vT : ℕ)
    (hin : σ.st (NumsPh2.sIn x) = frame (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl))
    (hcl : ∀ i, i ≠ NumsPh2.sIn x → σ.st i = []) (hsh : ∀ i, σ.sh i = 0)
    (hN : σ.val NumsPh2.rN = vN) (hM : σ.val NumsPh2.rM = vM) (hE : σ.val NumsPh2.rE = vE)
    (hT : σ.val NumsPh2.rT = vT)
    (hz : ∀ q, q ≠ NumsPh2.rN → q ≠ NumsPh2.rM → q ≠ NumsPh2.rE → q ≠ NumsPh2.rT → σ.val q = 0)
    (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hnc : cc.length ≤ 2)
    (hB1 : 1 ≤ Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (hok : PrimThrW.TopFront2.TF2Ok Cs cc (ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn))
    (hneed : N.need (P.n + Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) ≤
      ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn)
    (cN : vN ≤ c₀) (cM : vM ≤ c₀) (cE : vE ≤ c₀) (cT : vT ≤ c₀)
    (hc1 : 2 * (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length + 2 ≤ c₀)
    (hcP : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength (ReqBridge.thrCodes Cs).length + 1) +
      2 ^ (natBitLength cc.length + 1) + (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length + P.n +
      (ReqBridge.thrCodes Cs).length + 1 ≤ c₀)
    (hc3 : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ c₀)
    (hkc : P.s * (P.r / 2) ≤ c₀) (hfc : fe * Nat.clog 2 (P.n + 2) ≤ c₀)
    (hcS : 4 * P.n + 2 * cr + 20 ≤ c₀)
    (hcP' : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ c₀)
    (hcC : SymDec.CapNeed C .thr P.n (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) c₀)
    (hcA : (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length + (P.n + 1) ^ 26 * 2 + P.n +
      Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + 42 ≤ c₀)
    (hCn : N.Cn ≤ c₀)
    (hPD : (P.n + Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + 1) ^ N.Dn ≤ c₀)
    (hcB : ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn + P.n +
      Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + cc.length + 42 ≤ c₀)
    (cvl : ∀ i : Fin 14, (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).get i ≤ c₀)
    (hcT : Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 32 + 2 ≤ c₀)
    (hcN : 2 * (P.n + 1) ^ 26 + 8 ≤ c₀) (hcF : fe * Nat.clog 2 (P.n + 2) + 4 ≤ c₀)
    (hsc : 2 ^ ((SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
      (fe * Nat.clog 2 (P.n + 2))).seedBits + 1) ≤ c₀)
    (hlc : (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
      (fe * Nat.clog 2 (P.n + 2))).labelBits +
      (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
      (fe * Nat.clog 2 (P.n + 2))).fieldBits +
      (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
      (fe * Nat.clog 2 (P.n + 2))).walkLen + 512 ≤ c₀)
    (hqc : 2 * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nG *
      (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).cut) + 1 ≤ c₀)
    (hnp1 : 1 ≤ (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nPr)
    (hV : vVal (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nG
      (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).cut
      (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).pSum
      (2 ^ (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
        (fe * Nat.clog 2 (P.n + 2))).seedBits)
      (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nPr
      P.n (P.s * (P.r / 2)) ≤ c₀) :
    ∃ (τ : WState (LNS x) LNR) (m : ℕ), Step (bM x T N hx cr fe ζ Cδ C) m (wenc cap σ).H (wenc cap σ).A
        (wenc cap τ).H (wenc cap τ).A ∧
      m ≤ wa1Cost c₀ vN vM vE vT P.n (ReqBridge.thrCodes Cs).length cc.length
          (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length cr fe (P.s * (P.r / 2))
          (fe * Nat.clog 2 (P.n + 2)) + 1 +
        wa2Cost c₀ P.n cr (Ledger.rowBt h0 h1 P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) (Ledger.Lq P.n)
          (ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn)
          cc.length (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Dn + 1 +
        (T.cost (ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn) + 1 +
          N.cost (P.n + ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn +
            Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)) + 1 +
        wbCost c₀ vN vM vE vT (vVal (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nG
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).cut
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).pSum
          (2 ^ (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
            (fe * Nat.clog 2 (P.n + 2))).seedBits)
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nPr
          P.n (P.s * (P.r / 2))) ∧
      τ.st (NumsPh2.sIn x) = frame (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) ∧
      τ.st (NumsPh2.sW0 x) = [] ∧ τ.st (NumsPh2.sW1 x) = [] ∧ (∀ i, τ.sh i = 0) ∧ τ.cell = σ.cell ∧
      τ.val NumsPh2.rN = vN ∧ τ.val NumsPh2.rM = vM ∧ τ.val NumsPh2.rE = vE ∧ τ.val NumsPh2.rT = vT ∧
      τ.val NumsPh2.rV = vVal (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nG
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).cut
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).pSum
          (2 ^ (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
            (fe * Nat.clog 2 (P.n + 2))).seedBits)
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nPr
          P.n (P.s * (P.r / 2)) ∧
      (∀ q, q ≠ NumsPh2.rN → q ≠ NumsPh2.rM → q ≠ NumsPh2.rE → q ≠ NumsPh2.rT → q ≠ NumsPh2.rV → τ.val q = 0) := by
  have h0' : σ.st (sk x 0) = [] := hcl _ (fun e => by
    have := congrArg Fin.val e; rw [sk_val, NumsPh2.sIn_val] at this; exact absurd this (by decide))
  -- the first half
  obtain ⟨τ1, c1, e1, c1le, a0, aIn, aoth, ash, acl, as0, as1, as2, as3, aKH, aFL, adN, adNC, aLEN, aZ⟩ :=
    wa1_spec c₀ x cr fe P hrP _ (ReqBridge.thrCodes Cs) cc tl rfl hKb σ vN vM vE vT hin h0' hsh hN hM hE hT hz
      cN cM cE cT hc1 hcP hc3 hkc hfc
  have hb0 : ∀ r, σ.val r ≤ c₀ := fun r => by
    by_cases e1 : r = NumsPh2.rN
    · rw [e1, hN]; exact cN
    by_cases e2 : r = NumsPh2.rM
    · rw [e2, hM]; exact cM
    by_cases e3 : r = NumsPh2.rE
    · rw [e3, hE]; exact cE
    by_cases e4 : r = NumsPh2.rT
    · rw [e4, hT]; exact cT
    rw [hz r e1 e2 e3 e4]; exact Nat.zero_le _
  have hb1 := FinalPass.S5T.WExec.val_le c₀ e1 hb0
  have hbl : ∀ i : Fin (LNS x + 1), (130 ≤ i.val ∧ i.val ≤ 136) ∨ 161 ≤ i.val → τ1.st i = [] := fun i hi => by
    have n0 : i ≠ sk x 0 := fun e => by rw [e, sk_val] at hi; simp at hi
    have nI : i ≠ NumsPh2.sIn x := fun e => by rw [e, NumsPh2.sIn_val] at hi; omega
    rw [aoth i n0 nI]; exact hcl i nI
  obtain ⟨τ2, c2, e2, c2le, dIn, dR, dZ, dK, ddN, d13, dst, dsh, dcl⟩ :=
    wa2_spec c₀ x T N hx cr h0 h1 Cδ C P.n cc.length (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length
      (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) τ1 a0 (ash _) hbl (fun i _ => ash i) adN adNC aLEN
      aZ hb1 hcS hcP' hcC hcA hCn hPD hcB
  have st12 := (WExec.exec cap (ThrDecF.capUp' hc₀ (WExec.seq e1 e2))).step
  -- the docks
  obtain ⟨τD, sD, oD, pD, hD⟩ := ThrDecF.docksT_run3 T N cap x hx τ2 P Cs cc tl _ cc.length _ dIn hn ha hd hnc
    hB1 hok hneed
  have hDsh : ∀ i, τD.sh i = 0 := hD (fun i => by rw [dsh]; exact ash i)
  -- after the docks
  have vD := oD.val
  have hb2 : ∀ r, τD.val r ≤ c₀ := fun r => by rw [vD]; exact FinalPass.S5T.WExec.val_le c₀ e2 hb1 r
  obtain ⟨τ, c3, e3, c3le, tN, tM, tE, tT, tV, tz, tst, tsh, tcl⟩ := wb_spec c₀ x
    (pB x T N hx 0 (by omega)) (pB x T N hx 2 (by omega)) (pB x T N hx 3 (by omega)) (pB x T N hx 4 (by omega))
    _ _ _ _ _ P.n (fe * Nat.clog 2 (P.n + 2)) (P.s * (P.r / 2)) vN vM vE vT τD
    (pD 0) (pD 2) (pD 3) (pD 4) (hDsh _) (hDsh _) (hDsh _) (hDsh _)
    (fun r a b c => by rw [vD]; exact dZ r a b c) (by rw [vD]; exact d13) (by rw [vD]; exact ddN)
    (by rw [vD, dK sFL (by decide) (by decide)]; exact aFL) (by rw [vD, dK sKH (by decide) (by decide)]; exact aKH)
    (by rw [vD, dK s0 (by decide) (by decide)]; exact as0) (by rw [vD, dK s1 (by decide) (by decide)]; exact as1)
    (by rw [vD, dK s2 (by decide) (by decide)]; exact as2) (by rw [vD, dK s3 (by decide) (by decide)]; exact as3)
    hb2 (cvl 0) (cvl 2) (cvl 3) (cvl 4) hB1 hcT hcN hcF hsc hlc hqc hnp1 hn hV
  have st3 := (WExec.exec cap (ThrDecF.capUp' hc₀ e3)).step
  refine ⟨τ, _, Step.seq (Step.seq st12 sD) st3, ?_, ?_, ?_, ?_, fun i => by rw [tsh]; exact hDsh i, ?_,
    tN, tM, tE, tT, tV, tz⟩
  · rw [get_nG, get_cut, get_nPr, get_pSum] at c3le
    unfold wa1Cost wa2Cost wbCost at *
    omega
  · rw [tst, sIn_sk, (oD.other 150 (by decide) (by decide)).1, dst _ (Or.inl (by
      show 150 < 161 + ThrDecF.bT T N; omega)), ← sIn_sk]
    exact aIn
  · have hs : NumsPh2.sW0 x ≠ sk x 0 := fun e => by
      have := congrArg Fin.val e; rw [NumsPh2.sW0_val, sk_val] at this; exact absurd this (by decide)
    have hs' : NumsPh2.sW0 x ≠ NumsPh2.sIn x := fun e => by
      have := congrArg Fin.val e; rw [NumsPh2.sW0_val, NumsPh2.sIn_val] at this; exact absurd this (by decide)
    rw [tst, sW0_sk, (oD.other 151 (by decide) (by decide)).1, dst _ (Or.inl (by
      show 151 < 161 + ThrDecF.bT T N; omega)), ← sW0_sk, aoth _ hs hs']
    exact hcl _ hs'
  · have hs : NumsPh2.sW1 x ≠ sk x 0 := fun e => by
      have := congrArg Fin.val e; rw [NumsPh2.sW1_val, sk_val] at this; exact absurd this (by decide)
    have hs' : NumsPh2.sW1 x ≠ NumsPh2.sIn x := fun e => by
      have := congrArg Fin.val e; rw [NumsPh2.sW1_val, NumsPh2.sIn_val] at this; exact absurd this (by decide)
    rw [tst, sW1_sk, (oD.other 152 (by decide) (by decide)).1, dst _ (Or.inl (by
      show 152 < 161 + ThrDecF.bT T N; omega)), ← sW1_sk, aoth _ hs hs']
    exact hcl _ hs'
  · rw [tcl, oD.cell, dcl, acl]

end Run

end NearCubicWires.WireExponent3_5.PrimT.NwB
