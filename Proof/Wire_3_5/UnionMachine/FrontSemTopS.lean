import Lean
import Proof.Wire_3_5.UnionMachine.FrontSemEnvS
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.FrontCaps
import Proof.Wire_3_5.UnionMachine.FrontOutRef
import Proof.Wire_3_5.UnionMachine.FrontSelReq
import Proof.Wire_3_5.UnionMachine.FrontSemC1Cap
import Proof.Wire_3_5.UnionMachine.FrontSemCap1
import Proof.Wire_3_5.UnionMachine.FrontSemCap2
import Proof.Wire_3_5.UnionMachine.FrontSemEvS
import Proof.Wire_3_5.UnionMachine.FrontSemPath
import Proof.Wire_3_5.UnionMachine.FrontSemPathCaps
import Proof.Wire_3_5.UnionMachine.FrontSemRun
import Proof.Wire_3_5.UnionMachine.FrontSemSUE
import Proof.Wire_3_5.UnionMachine.FrontSemSize
import Proof.Wire_3_5.UnionMachine.FrontSemTW
import Proof.Wire_3_5.UnionMachine.PlanW2
import Proof.Wire_3_5.UnionMachine.PlanW3
import W3.Front.ColdNative
import Proof.Wire_3_5.UnionMachine.FrontSemTopSBase


noncomputable section
set_option maxRecDepth 120000


/-! # C6 front, the semantic core (20): the machine's parameters at the pinned setup (P3:3669-3691)

The front's fixed parameters at `SUE`, each from a polynomial bound in the width: the thresholds' numerators and
denominators (`aVS`, `bVS`, `aTS`, `bTS`, and `c0S` their sum), the master bound `MSS := MS c0S`, the data bound
`KbS (q+1)^{DbS} ≥ BK (MSS q)` (**`KbS_spec`**), the width `KwS (q+1)^{DwS} ≥ Wreq q` (**`KwS_spec`**: every width
requirement of `PathCaps`, `EndCaps` and `NumsCaps`), the fold's exponents (`DeS`, `CeS`, `tS`, `DtS`, `CtS`), C1's
input-size degree `dS`.

Paper quantity: none (the front's time, fixed polynomials of the width). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTopS
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU PQ)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap2 (BK PW)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1 (CN EW)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnvS (MS MS_pq)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound (eT)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemFold (eMt)

section SUE
variable (l : Literals) (F : GateFree l) (e coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

/-- The thresholds' numerators and denominators. -/
noncomputable def aVS : ℕ := numN (gateParams1 l).v0
noncomputable def bVS : ℕ := (gateParams1 l).v0.den
noncomputable def aTS : ℕ := numN (gateParams1 l).threshold
noncomputable def bTS : ℕ := (gateParams1 l).threshold.den

/-- The free constant of the master bound. -/
noncomputable def c0S : ℕ := aVS l + bVS l + aTS l + bTS l

/-- **The master bound at the pinned setup.** -/
noncomputable def MSS (q : ℕ) : ℕ := MS l F e coef A L hL (c0S l) q

theorem MSS_pq : PQ (MSS l F e coef A L hL) := MS_pq l F e coef A L hL (c0S l)

theorem bk_pq : PQ (fun q => BK (MSS l F e coef A L hL q)) := by
  unfold BK
  exact PQ.mul (PQ.const 64) (PQ.pow (PQ.add (MSS_pq l F e coef A L hL) (PQ.const 1)) 3)

/-- The data bound's coefficient and exponent. -/
noncomputable def KbS : ℕ := Classical.choose (bk_pq l F e coef A L hL)
noncomputable def DbS : ℕ := Classical.choose (Classical.choose_spec (bk_pq l F e coef A L hL))

theorem KbS_spec (q : ℕ) : BK (MSS l F e coef A L hL q) ≤ KbS l F e coef A L hL * (q + 1) ^ DbS l F e coef A L hL :=
  Classical.choose_spec (Classical.choose_spec (bk_pq l F e coef A L hL)) q

/-- The schedule's block length at the setup's `ζ`. -/
noncomputable def JS : ℕ := Classical.choose (Schedule.exists_block (gateZeta_pos l) (gateZeta_lt l))

theorem JS_spec : ((1 - (gateCParams1 l).ζ) ^ 16) ^ JS l ≤ 1 / 8 :=
  Classical.choose_spec (Schedule.exists_block (gateZeta_pos l) (gateZeta_lt l))

/-- The accumulators' starting values' bound. -/
noncomputable def AccB (q : ℕ) : ℕ :=
  MSS l F e coef A L hL q ^ 4 * (4 * (q + 1)) * (MSS l F e coef A L hL q * 2) *
    (2 * FrontCaps.vcOf (SUE l F e coef A L hL) + (1 + MSS l F e coef A L hL q) ^ 4) + 1

/-- **Every width requirement** of the front's capacities. -/
noncomputable def Wreq (q : ℕ) : ℕ :=
  PW (MSS l F e coef A L hL q) +
    (FrontSemCarPre.CP * (MSS l F e coef A L hL q + 2) ^ 51 + 4 * MSS l F e coef A L hL q + 4) +
    (KbS l F e coef A L hL * (q + 1) ^ DbS l F e coef A L hL + KbS l F e coef A L hL + (q + 1) ^ DbS l F e coef A L hL) +
    (CN (MSS l F e coef A L hL q) * EW (MSS l F e coef A L hL q) +
      30 * (KbS l F e coef A L hL * (q + 1) ^ DbS l F e coef A L hL) + 41) +
    PrimAsm.SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Lq q) (rowBt (gateZeta_pos l) (gateZeta_lt l) q - 1) +
    ((32 * coef + 1) * (q + 1) ^ (gate0 l F).E.Amain + 1000 * (q + 7) + 2 * F.cr + 100) +
    AccB l F e coef A L hL q

theorem Wreq_pq : PQ (Wreq l F e coef A L hL) := by
  have hM := MSS_pq l F e coef A L hL
  have hB : PQ (fun q => KbS l F e coef A L hL * (q + 1) ^ DbS l F e coef A L hL) :=
    PQ.mul (PQ.const _) (PQ.pow (PQ.add PQ.var (PQ.const 1)) _)
  have hq1 : PQ (fun q : ℕ => (q + 1) ^ DbS l F e coef A L hL) := PQ.pow (PQ.add PQ.var (PQ.const 1)) _
  have a1 : PQ (fun q => PW (MSS l F e coef A L hL q)) := by
    unfold PW; exact PQ.mul (PQ.const _) (PQ.pow (PQ.add hM (PQ.const 1)) 9)
  have a2 : PQ (fun q => FrontSemCarPre.CP * (MSS l F e coef A L hL q + 2) ^ 51 + 4 * MSS l F e coef A L hL q + 4) :=
    PQ.add (PQ.add (PQ.mul (PQ.const _) (PQ.pow (PQ.add hM (PQ.const 2)) 51)) (PQ.mul (PQ.const 4) hM)) (PQ.const 4)
  have a3 : PQ (fun q => KbS l F e coef A L hL * (q + 1) ^ DbS l F e coef A L hL + KbS l F e coef A L hL +
      (q + 1) ^ DbS l F e coef A L hL) := PQ.add (PQ.add hB (PQ.const _)) hq1
  have hCN : PQ (fun q => CN (MSS l F e coef A L hL q)) := by
    unfold CN
    exact PQ.mul (PQ.mul (PQ.const 24) hM) (PQ.pow (PQ.add (PQ.const 1) (PQ.mul (PQ.mul (PQ.const 2) hM)
      (PQ.add hM (PQ.const 1)))) 4)
  have hEW : PQ (fun q => EW (MSS l F e coef A L hL q)) := by
    unfold EW
    exact PQ.add (PQ.add (PQ.mul (PQ.const 2) (PQ.pow (PQ.add hM hM) 4)) (PQ.mul (PQ.const 22) hM)) (PQ.const 54)
  have a4 : PQ (fun q => CN (MSS l F e coef A L hL q) * EW (MSS l F e coef A L hL q) +
      30 * (KbS l F e coef A L hL * (q + 1) ^ DbS l F e coef A L hL) + 41) :=
    PQ.add (PQ.add (PQ.mul hCN hEW) (PQ.mul (PQ.const 30) hB)) (PQ.const 41)
  have a5 := FrontSemCap3.sparse_pq (gateZeta_pos l) (gateZeta_lt l) (JS_spec l) (gateCδ1 l)
  have a6 : PQ (fun q : ℕ => (32 * coef + 1) * (q + 1) ^ (gate0 l F).E.Amain + 1000 * (q + 7) + 2 * F.cr + 100) :=
    PQ.add (PQ.add (PQ.add (PQ.mul (PQ.const _) (PQ.pow (PQ.add PQ.var (PQ.const 1)) _))
      (PQ.mul (PQ.const 1000) (PQ.add PQ.var (PQ.const 7)))) (PQ.const _)) (PQ.const 100)
  have a7 : PQ (AccB l F e coef A L hL) := by
    unfold AccB
    exact PQ.add (PQ.mul (PQ.mul (PQ.mul (PQ.pow hM 4) (PQ.mul (PQ.const 4) (PQ.add PQ.var (PQ.const 1))))
      (PQ.mul hM (PQ.const 2))) (PQ.add (PQ.const _) (PQ.pow (PQ.add (PQ.const 1) hM) 4))) (PQ.const 1)
  unfold Wreq
  exact PQ.add (PQ.add (PQ.add (PQ.add (PQ.add (PQ.add a1 a2) a3) a4) a5) a6) a7

/-- The width's coefficient and exponent. -/
noncomputable def KwS : ℕ := Classical.choose (Wreq_pq l F e coef A L hL)
noncomputable def DwS : ℕ := Classical.choose (Classical.choose_spec (Wreq_pq l F e coef A L hL))

theorem KwS_spec (q : ℕ) : Wreq l F e coef A L hL q ≤ KwS l F e coef A L hL * (q + 1) ^ DwS l F e coef A L hL :=
  Classical.choose_spec (Classical.choose_spec (Wreq_pq l F e coef A L hL)) q

/-- The fold's exponents: the envelope capacity above both modes' `eT`, the tapes above both modes' `eMt`. -/
noncomputable def DeS : ℕ :=
  eT (FrontCh5.PwM .thr) (FrontCh5.CwM .thr) (IUE l F e coef A).carrierDeg +
    eT (FrontCh5.PwM .sym) (FrontCh5.CwM .sym) (IUE l F e coef A).carrierDeg
noncomputable def CeS : ℕ := 2 ^ DeS l F e coef A
noncomputable def tS : ℕ := CeS l F e coef A + DeS l F e coef A * (KwS l F e coef A L hL + DwS l F e coef A L hL)
noncomputable def DtS : ℕ :=
  eMt (FrontCh5.PwM .thr) (FrontCh5.CwM .thr) (IUE l F e coef A).carrierDeg (tS l F e coef A L hL) +
    eMt (FrontCh5.PwM .sym) (FrontCh5.CwM .sym) (IUE l F e coef A).carrierDeg (tS l F e coef A L hL) + 6
noncomputable def CtS : ℕ := 2 * 2 ^ DtS l F e coef A L hL

/-- C1's input-size degree. -/
noncomputable def dS : ℕ := 6 * Classical.choose (Classical.choose_spec (MSS_pq l F e coef A L hL)) + 1

theorem AccB_pq : PQ (AccB l F e coef A L hL) := by
  have hM := MSS_pq l F e coef A L hL
  unfold AccB
  exact PQ.add (PQ.mul (PQ.mul (PQ.mul (PQ.pow hM 4) (PQ.mul (PQ.const 4) (PQ.add PQ.var (PQ.const 1))))
    (PQ.mul hM (PQ.const 2))) (PQ.add (PQ.const _) (PQ.pow (PQ.add (PQ.const 1) hM) 4))) (PQ.const 1)

/-- The capacity is at least `2^{q − ⌊k/4⌋}`. -/
theorem capOf_ge (q : ℕ) :
    2 ^ (q - (BU l F e coef A).kOf q / 4) ≤ FrontTail.capOf F.cr (32 * coef + 1) (gate0 l F).E.Amain q := by
  unfold FrontTail.capOf FrontTail.mOf
  have h1 : 1 ≤ (q + 1) ^ (gate0 l F).E.Amain * (32 * coef + 1) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
  have ek : (BU l F e coef A).kOf q = Cost.starWidth (rowBr F.cr q) q := rfl
  rw [← ek]
  calc 2 ^ (q - (BU l F e coef A).kOf q / 4) = 1 * 2 ^ (q - (BU l F e coef A).kOf q / 4) := (one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ h1

/-- **The approved capacity is the tail's.** -/
theorem capQ_eq (q : ℕ) : FrontCaps.capQ l F e coef A q = FrontTail.capOf F.cr (32 * coef + 1) (gate0 l F).E.Amain q := by
  unfold FrontCaps.capQ FrontTail.capOf FrontTail.mOf
  have ek : (BU l F e coef A).kOf q = Cost.starWidth (rowBr F.cr q) q := rfl
  rw [ek]; ring

theorem RQ_eq (q : ℕ) : FrontCaps.RQ l F e coef A q = FrontTail.rOf F.cr (32 * coef + 1) (gate0 l F).E.Amain q := by
  unfold FrontCaps.RQ FrontTail.rOf
  rw [capQ_eq]; ring

/-- **The eventual facts in the width**: C1's degree, the capacity above the accumulators and `L(q)`. -/
theorem q_ev : ∀ᶠ q : ℕ in Filter.atTop,
    100 * MSS l F e coef A L hL q ^ 6 ≤ (q + 1) ^ dS l F e coef A L hL ∧
    AccB l F e coef A L hL q ≤ 2 ^ (q - (BU l F e coef A).kOf q / 4) ∧
    1 * (q + 1) ^ 1 ≤ 2 ^ (q - (BU l F e coef A).kOf q / 4) := by
  obtain ⟨cA, dA, hA⟩ := AccB_pq l F e coef A L hL
  have hM := Classical.choose_spec (Classical.choose_spec (MSS_pq l F e coef A L hL))
  set cM := Classical.choose (MSS_pq l F e coef A L hL) with hcM
  set dM := Classical.choose (Classical.choose_spec (MSS_pq l F e coef A L hL)) with hdM
  have e1 := FrontCaps.two_pow_small l F e coef A cA dA
  have e2 := FrontCaps.two_pow_small l F e coef A 1 1
  have e3 : ∀ᶠ q : ℕ in Filter.atTop, 100 * cM ^ 6 ≤ q + 1 := Filter.eventually_ge_atTop (100 * cM ^ 6) |>.mono
    (fun q hq => by omega)
  filter_upwards [e1, e2, e3] with q h1 h2 h3
  refine ⟨?_, (hA q).trans h1, h2⟩
  have hm := hM q
  have hp : MSS l F e coef A L hL q ^ 6 ≤ (cM * (q + 1) ^ dM) ^ 6 := Nat.pow_le_pow_left hm 6
  have e4 : (cM * (q + 1) ^ dM) ^ 6 = cM ^ 6 * (q + 1) ^ (6 * dM) := by rw [mul_pow, ← pow_mul, mul_comm dM]
  have e5 : (q + 1) ^ dS l F e coef A L hL = (q + 1) * (q + 1) ^ (6 * dM) := by
    unfold dS; rw [← hdM, pow_succ, mul_comm]
  rw [e5]
  calc 100 * MSS l F e coef A L hL q ^ 6 ≤ 100 * (cM ^ 6 * (q + 1) ^ (6 * dM)) := by rw [← e4]; omega
    _ = (100 * cM ^ 6) * (q + 1) ^ (6 * dM) := by ring
    _ ≤ (q + 1) * (q + 1) ^ (6 * dM) := Nat.mul_le_mul_right _ h3

/-- **The caps at a guess past the onset** (TopFacts' `caps`). -/
theorem caps_at (c : Plan.C1At (dS l F e coef A L hL)) {N : ℕ}
    (hnw : (SUE l F e coef A L hL).width N = (BU l F e coef A).q N)
    (hstar : (IUE l F e coef A).StarAt ((BU l F e coef A).q N))
    (hev : 100 * MSS l F e coef A L hL ((BU l F e coef A).q N) ^ 6 ≤ ((BU l F e coef A).q N + 1) ^ dS l F e coef A L hL ∧
      AccB l F e coef A L hL ((BU l F e coef A).q N) ≤
        2 ^ ((BU l F e coef A).q N - (BU l F e coef A).kOf ((BU l F e coef A).q N) / 4) ∧
      1 * ((BU l F e coef A).q N + 1) ^ 1 ≤
        2 ^ ((BU l F e coef A).q N - (BU l F e coef A).kOf ((BU l F e coef A).q N) / 4))
    (x : BitInput N) (g : UnionGuess (SUE l F e coef A L hL) x)
    (hgd : UnionGuards (SUE l F e coef A L hL) x g)
    (hat : PlanW3.AtomsOkG g) (hsg : (g.checkData g.translation).signsOk = true) :
    FrontSemPath.PathCaps g (gateZeta_pos l) (gateZeta_lt l) (KwS l F e coef A L hL) (DwS l F e coef A L hL)
        (IUE l F e coef A).descDeg (DeS l F e coef A) (CeS l F e coef A) (DtS l F e coef A L hL) (CtS l F e coef A L hL)
        (KbS l F e coef A L hL) (DbS l F e coef A L hL) (gateCδ1 l) F.cr
        (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N)) c ∧
      FrontSemTW.EndCaps (gateZeta_pos l) (gateZeta_lt l) g (KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL)
        (KbS l F e coef A L hL) (DbS l F e coef A L hL) (gateCδ1 l) (aVS l) (bVS l) (aTS l) (bTS l) F.cr (32 * coef + 1)
        (gate0 l F).E.Amain ∧
      (Plan.c1sized (dS l F e coef A L hL) c.E₁ c.c₁).pre (FrontSelReq.selReqOf g) := by
  have harity : g.q = (SUE l F e coef A L hL).width N := q_eq_width _ g hgd.2.1 hgd.2.2.1
  have hqB : g.q = (BU l F e coef A).q N := harity.trans hnw
  rw [← hqB] at hstar hev
  obtain ⟨hd, hacc, hlq⟩ := hev
  have hG := FrontSemEnvS.genv_of l F e coef A L hL (c0S l) x g hgd hat hstar
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12⟩ := FrontSemEnvS.MS_ge l F e coef A L hL (c0S l) g.q
  have hWr := KwS_spec l F e coef A L hL g.q
  have hBr := KbS_spec l F e coef A L hL g.q
  unfold Wreq at hWr
  unfold MSS at hWr hBr hd
  have hr := FrontSemEnvS.KsS_spec l F e coef A L hL N x g.pair hgd.2.1 hgd.2.2.1 hgd.2.2.2.2.1
  have hnv := FrontSemSize.nv_le x g.pair _ hr
  have hcb := FrontSemSize.cb_le x g.pair _ hr
  have eK : FrontSemEnvS.KpS l F e coef A L hL g.q = FrontSemSize.Kp (SUE l F e coef A L hL)
      (FrontSemEnvS.KsS l F e coef A L hL) (FrontSemEnvS.σS l F e coef A L hL) ((SUE l F e coef A L hL).width N) := by
    unfold FrontSemEnvS.KpS; rw [harity]
  have hnv' : g.pcpp.systematicBits + g.pcpp.auxiliaryBits ≤ 2 * FrontSemEnvS.KpS l F e coef A L hL g.q := by
    rw [eK]; exact hnv
  have hcb' : 2 ^ g.pcpp.clauseBits ≤ FrontSemEnvS.KpS l F e coef A L hL g.q := by rw [eK]; exact hcb
  have e1 : 2 ^ (g.pcpp.clauseBits + 1) = 2 * 2 ^ g.pcpp.clauseBits := by rw [pow_succ]; ring
  have e2 : 2 ^ (g.pcpp.clauseBits + 2) = 4 * 2 ^ g.pcpp.clauseBits := by rw [pow_add]; ring
  have hnvG : FrontSemTW.nvG g = g.pcpp.systematicBits + g.pcpp.auxiliaryBits := rfl
  have hr4 : 4 * (BU l F e coef A).rOf g.q ≤ g.q := hstar.2.2.1
  have hrr : rowBr F.cr g.q = (BU l F e coef A).rOf g.q := rfl
  have hpA := FrontSemSUE.sue_parity l F e coef A L hL
  have hDD : ∀ k, k ≤ FrontSemEnvS.DD l F e coef A →
      (g.q + 1) ^ k ≤ (g.q + 1) ^ FrontSemEnvS.DD l F e coef A := fun k hk => Nat.pow_le_pow_right (by omega) hk
  have hLd : ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ MS l F e coef A L hL (c0S l) g.q :=
    fun X a => ((hat X a).trans (hDD _ (by unfold FrontSemEnvS.DD; omega))).trans m9
  have hPd : ∀ X, g.mode.descriptionBits (g.parity X) ≤ MS l F e coef A L hL (c0S l) g.q := by
    intro X
    show g.mode.descriptionBits ((SUE l F e coef A L hL).parityAtom g.mode g.q (g.support X)) ≤ _
    rw [hpA]
    exact ((unionParityAtom_descriptionBits_le _ _ _).trans (hDD 4 (by unfold FrontSemEnvS.DD; omega))).trans m9
  have hsS : g.s = rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) g.q :=
    FrontSemSUE.sue_gridSize l F e coef A L hL g.q
  have hDe : ∀ m : Mode, eT (FrontCh5.PwM m) (FrontCh5.CwM m) (IUE l F e coef A).carrierDeg ≤ DeS l F e coef A := by
    intro m; cases m <;> unfold DeS <;> omega
  have hDt : ∀ m : Mode, eMt (FrontCh5.PwM m) (FrontCh5.CwM m) (IUE l F e coef A).carrierDeg (tS l F e coef A L hL) + 6 ≤
      DtS l F e coef A L hL := by
    intro m; cases m <;> unfold DtS <;> omega
  have hT : BlockPlatform.UnaryCalc.value (DeS l F e coef A) (CeS l F e coef A)
      (KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL) ≤
      (MS l F e coef A L hL (c0S l) g.q + 2) ^ tS l F e coef A L hL :=
    FrontSemFold.valueW_le _ _ _ _ g.q _ (by omega)
  have hK3 : 3 ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have hrK : (BU l F e coef A).rOf g.q ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have hrrK : rowBr F.cr g.q ≤ MS l F e coef A L hL (c0S l) g.q := by rw [hrr]; exact hrK
  have hV2 : 2 * FrontSemTW.nvG g ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have hcb4 : 2 ^ (g.pcpp.clauseBits + 2) ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have hcb1 : 2 ^ (g.pcpp.clauseBits + 1) ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have hspW : PrimAsm.SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Lq g.q)
      (rowBt (gateZeta_pos l) (gateZeta_lt l) g.q - 1) ≤
      2 * (KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL) + 2 := by omega
  have hW1 : PW (MS l F e coef A L hL (c0S l) g.q) ≤ KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL := by
    omega
  have hW3 : KbS l F e coef A L hL * (g.q + 1) ^ DbS l F e coef A L hL + KbS l F e coef A L hL +
      (g.q + 1) ^ DbS l F e coef A L hL ≤ KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL := by omega
  have hHd : FrontSemCarPre.CP * (MS l F e coef A L hL (c0S l) g.q + 2) ^ 51 + 4 * MS l F e coef A L hL (c0S l) g.q + 4 ≤
      KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL := by omega
  have hW2 : CN (MS l F e coef A L hL (c0S l) g.q) * EW (MS l F e coef A L hL (c0S l) g.q) +
      30 * (KbS l F e coef A L hL * (g.q + 1) ^ DbS l F e coef A L hL) + 41 ≤
      2 * (KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL) + 2 := by omega
  have hcapW : (32 * coef + 1) * (g.q + 1) ^ (gate0 l F).E.Amain + 1000 * (g.q + 7) + 2 * F.cr + 100 ≤
      2 * (KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL) + 2 := by omega
  have hc0 : c0S l = aVS l + bVS l + aTS l + bTS l := rfl
  have haV : aVS l ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have hbV : bVS l ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have haT : aTS l ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have hbT : bTS l ≤ MS l F e coef A L hL (c0S l) g.q := by omega
  have h4 : 4 * rowBr F.cr g.q ≤ g.q := by rw [hrr]; exact hr4
  have hPC := FrontSemPathCaps.pathCaps_of (gateZeta_pos l) (gateZeta_lt l) hG (t := tS l F e coef A L hL)
    (Kw := KwS l F e coef A L hL) (Dw := DwS l F e coef A L hL) (Dl := (IUE l F e coef A).descDeg)
    (Kb := KbS l F e coef A L hL) (Db := DbS l F e coef A L hL) (Cδ := gateCδ1 l) (cr := F.cr)
    (De := DeS l F e coef A) (Ce := CeS l F e coef A) (Dt := DtS l F e coef A L hL) (Ct := CtS l F e coef A L hL)
    c hsS rfl hV2 hcb4 hK3 m10 hrK hrrK hLd hPd hstar hspW hBr hW1 hW3 hHd hDe
    (fun m => Nat.pow_le_pow_right (by norm_num) (hDe m)) hT hDt le_rfl
  -- the accumulators
  have hs : (g.checkData g.translation).s ≤ MS l F e coef A L hL (c0S l) g.q := hG.s
  have hl : rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 g.q ≤ MS l F e coef A L hL (c0S l) g.q := hG.lam
  have hcbK : 2 ^ (g.checkData g.translation).pcpp.clauseBits ≤ MS l F e coef A L hL (c0S l) g.q := hG.cb
  have h2p : 2 ^ Lq g.q ≤ 4 * (g.q + 1) := FrontCaps.two_pow_unionBits g.q
  have hacS : ∀ i, FrontOutRef.accStart (SUE l F e coef A L hL) (g.checkData g.translation) (Lq g.q) i ≤
      AccB l F e coef A L hL g.q := by
    intro i
    refine (FrontCaps.accStart_le (SUE l F e coef A L hL) (g.checkData g.translation) (Lq g.q)
      (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 g.q) hG.mass i).trans ?_
    unfold AccB MSS
    exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hs 4) h2p)
      (Nat.mul_le_mul_right 2 hcbK)) (Nat.add_le_add_left (Nat.pow_le_pow_left (Nat.add_le_add_left hl 1) 4) _)) 1
  have hacc' : AccB l F e coef A L hL g.q ≤ 2 ^ (g.q - (BU l F e coef A).kOf g.q / 4) := hacc
  have hcap := capOf_ge l F e coef A g.q
  have hLq := Lq_le g.q
  have hAW : AccB l F e coef A L hL g.q ≤ KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL := by omega
  have hlq' : g.q + 1 ≤ 2 ^ (g.q - (BU l F e coef A).kOf g.q / 4) := by rw [pow_one, one_mul] at hlq; exact hlq
  have hEC := FrontSemCap2.endCaps_of (gateZeta_pos l) (gateZeta_lt l) hG hpA hsg
    (W := KwS l F e coef A L hL * (g.q + 1) ^ DwS l F e coef A L hL) (Kb := KbS l F e coef A L hL)
    (Db := DbS l F e coef A L hL) (crT := F.cr) (KT := 32 * coef + 1) (AT := (gate0 l F).E.Amain)
    (aV := aVS l) (bV := bVS l) (aT := aTS l) (bT := bTS l) (Cδ := gateCδ1 l)
    hsS rfl haV hbV haT hbT hspW hBr hW1 hW2 hW3 F.cr_pos h4 (by omega) hcapW (by omega)
    (fun i => ((hacS i).trans hacc').trans hcap) (fun i => by have := hacS i; omega)
  have hpre := FrontSemC1Cap.pre_of hG hstar c hrK hLd hPd hcb1 hd
  have eV : MS l F e coef A L hL (c0S l) g.q = MSS l F e coef A L hL ((SUE l F e coef A L hL).width N) := by
    unfold MSS; rw [harity]
  exact ⟨eV ▸ hPC, hEC, hpre⟩

/-- **The numbers' caps for every pair within the size cap** (TopFacts' `nums`). -/
theorem nums_at {N : ℕ} (x : BitInput N) (O : NearCubicGates.Close.Outer.OuterGuess ((SUE l F e coef A L hL).width N))
    (hN : N = 2 ^ Nat.log 2 N) (hon : (SUE l F e coef A L hL).onset ≤ Nat.log 2 N)
    (hO : O.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (SUE l F e coef A L hL).G
      ((SUE l F e coef A L hL).width N)) :
    FrontCh3P.NumsCaps (2 * (KwS l F e coef A L hL * ((SUE l F e coef A L hL).width N + 1) ^
        DwS l F e coef A L hL) + 2) (gateZeta_pos l) (gateZeta_lt l) (KbS l F e coef A L hL) (DbS l F e coef A L hL)
      (gateCδ1 l) ((SUE l F e coef A L hL).width N) ((SUE l F e coef A L hL).pcppOf x O).systematicBits
      ((SUE l F e coef A L hL).pcppOf x O).auxiliaryBits ((SUE l F e coef A L hL).pcppOf x O).clauseBits := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12⟩ :=
    FrontSemEnvS.MS_ge l F e coef A L hL (c0S l) ((SUE l F e coef A L hL).width N)
  have hr := FrontSemEnvS.KsS_spec l F e coef A L hL N x O hN hon hO
  have hnv := FrontSemSize.nv_le x O _ hr
  have hcb := FrontSemSize.cb_le x O _ hr
  have eK : FrontSemEnvS.KpS l F e coef A L hL ((SUE l F e coef A L hL).width N) =
      FrontSemSize.Kp (SUE l F e coef A L hL) (FrontSemEnvS.KsS l F e coef A L hL) (FrontSemEnvS.σS l F e coef A L hL)
        ((SUE l F e coef A L hL).width N) := rfl
  rw [← eK] at hnv hcb
  have hWr := KwS_spec l F e coef A L hL ((SUE l F e coef A L hL).width N)
  have hBr := KbS_spec l F e coef A L hL ((SUE l F e coef A L hL).width N)
  unfold Wreq at hWr
  unfold MSS at hWr hBr
  exact FrontSemCap3.numsCaps_of (gateZeta_pos l) (gateZeta_lt l) (K := MS l F e coef A L hL (c0S l)
    ((SUE l F e coef A L hL).width N)) (by omega) (by omega) (by omega)
    ((FrontSemEnvS.sp_le l _).trans m4) (one_le_gridSize (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCδ1_pos l) _)
    ((FrontSemEnvS.lam_le l _).trans m3) (by omega) hBr (by omega) (by omega)

/-- The cold front end at the pinned setup (the shared cold-front-end producer; cutoff `0`, one policy copy). -/
noncomputable def cnwS : W3.NearCubicWires.RepairSource.Outer3.ColdNativeW (SUE l F e coef A L hL).mw
    (SUE l F e coef A L hL).SV (SUE l F e coef A L hL).pcppAlg 0 1 (SUE l F e coef A L hL).G 0 0 :=
  W3.NearCubicWires.RepairSource.Outer3.coldNativeW_of (SUE l F e coef A L hL).mw (SUE l F e coef A L hL).SV
    (SUE l F e coef A L hL).pcppAlg 0 1 (SUE l F e coef A L hL).G 0 0 le_rfl

/-- **The front's facts past the onset at the live pinned setup.** -/
theorem topFacts_ev (h : L = recL l (kE l e)) (c : Plan.C1At (dS l F e coef A L hL)) : ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
    FrontSemRun.TopFacts (S := SUE l F e coef A L hL) (cnwS l F e coef A L hL) (kE l e) (gateApad l)
      (DwS l F e coef A L hL) (DeS l F e coef A) (DtS l F e coef A L hL) c (KwS l F e coef A L hL) (gateZeta_pos l)
      (gateZeta_lt l) (KbS l F e coef A L hL) (DbS l F e coef A L hL) (gateCδ1 l) (CeS l F e coef A)
      (CtS l F e coef A L hL) F.cr (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N)) (aVS l) (bVS l) (aTS l)
      (bTS l) F.cr (32 * coef + 1) (gate0 l F).E.Amain (fun N => FrontCaps.capQ l F e coef A ((BU l F e coef A).q N))
      (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N))
      (fun N => FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1) N := by
  obtain ⟨N₁, hN₁⟩ := FrontSemEvS.sue_ev l F e coef A L hL h
  have hq : Filter.Tendsto (BU l F e coef A).q Filter.atTop Filter.atTop :=
    Ledger.tendsto_nativeWidth (kE l e) (gateApad l)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (hq.eventually (q_ev l F e coef A L hL))
  set o1 := (SUE l F e coef A L hL).onset with ho1
  set o2 := (cnwS l F e coef A L hL).onset with ho2
  refine ⟨max (max N₁ N₂) (2 ^ (o1 + o2) + 1), fun N hN => ?_⟩
  obtain ⟨hnw, hmin, hstar, hfit, h4q, hnb, horc, h16⟩ := hN₁ N (by omega)
  have hev := hN₂ N (by omega)
  have hlog : o1 + o2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hW : (SUE l F e coef A L hL).width N = Ledger.nativeWidth (kE l e) (gateApad l) N :=
    FrontSemSUE.sue_width l F e coef A L hL h N
  exact
    { hW := hW
      hmin := by rw [FrontSemSUE.sue_alg, hnw]; exact hmin
      hlive := FrontSemSUE.sue_live l F e coef A L hL h
      hon := by omega
      hcut := Nat.zero_le _
      hcon := by omega
      hStar := by rw [hnw]; exact hstar
      hFit := by rw [hnw]; exact hfit
      ph1 := fun x w hw => FrontSemEvS.ph1ok l e x w hw h16 h4q hnb
      hq3 := by rw [hnw]; omega
      nums := fun x O hNd hO => nums_at l F e coef A L hL x O hNd (by omega) hO
      caps := fun x g hgd hat hsg => caps_at l F e coef A L hL c hnw hstar hev x g hgd hat hsg
      hcapF := by show FrontCaps.capQ l F e coef A ((BU l F e coef A).q N) = _; rw [hnw]; exact capQ_eq l F e coef A _
      hRF := by show FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) = _; rw [hnw]; exact RQ_eq l F e coef A _
      hLgF := by show FrontCaps.RQ l F e coef A ((BU l F e coef A).q N) + 1 = _; rw [hnw, RQ_eq] }

end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTopS

end
