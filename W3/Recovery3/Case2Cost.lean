import W3.Recovery3.Case2KitV
import Proof.CaseAnalysis.CaseTwoWholeBudgetLocal
import Proof.CaseAnalysis.CaseTwoBudget
import Proof.PCP.PCPPSourceCacheBounds
import Recovery.HTWord
import CheckedPCPP.PolyClass

/-!
# The Case-2 chain, part 8: the Case-2 kit's cost class `C·(2^n+1)^E`

The run bound. the near-cubic-wires paper ("H_B is a circuit of size q^{O(1)}", Fact C.1/C.2 size clauses) and the C.12
envelope: every quantity of the Case-2 execution at a kit instance (the word of `C_{⟨B*_src⟩_ν}`, `⟨B*_pf⟩`, `H_{B*}`,
its descriptor, the PCPP measure, proof 1's converter and block costs) is polynomial in the source length `2^ν ≤ 2^n`.
Gates' `PolyB` (measure `2^ν`) with the size lemmas `outC_size_le`, `ell_le_width`, `Dat_size_le`, `word_len_le`,
`desc_len_le'`; proof 1's `ColdBudget.polynomial`, `WholeBudget.occurrence_bound`/`local_polynomial`/`components`,
`PCPPSourceCache.budget_bound`; the fold by `budget_uniform` (base `FixedFold.budget_uniform`, restated).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicGates.Close NearCubicGates.Close.CheckedPCPP

namespace W3.NearCubicWires.RepairSource.Outer3.Case2

noncomputable section

/-- Base `WholeBudget.request_source_bound`. -/
theorem request_source_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    RequestSource.budget a r ≤ 2 * PCPPSourceCache.totalBudget a r + 8 * (pcppInput r).length + 16 := by
  have hb := PCPPSourceCache.budget_bound a r
  unfold PCPPSourceCache.budget PCPPRequestSource.budget at hb
  unfold RequestSource.budget RequestInput.budget SourceCache.budget SourceCall.budget
  omega

variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (d : ℕ)

/-- A kit instance past the outer verifier's onset. -/
structure KI where
  ν : ℕ
  z : BitInput (2 ^ ν)
  h : IsCaseTwo mw SV d ν z
  hq : a.minimumArity ≤ Outer.width mw SV (2 ^ ν)
  h1 : 1 ≤ ν
  hon : SV.onset ≤ ν

variable {mw SV a d}

/-! ## The instance quantities -/

def KI.q (x : KI mw SV a d) : ℕ := Outer.width mw SV (2 ^ x.ν)
def KI.cap (x : KI mw SV a d) : ℕ := oracleSizeBound d x.q
def KI.B (x : KI mw SV a d) := selectedPair mw SV d x.ν x.z x.h
def KI.i (x : KI mw SV a d) : Inst a := kitInst mw SV a d x.ν x.z x.h x.hq
def KI.sz (x : KI mw SV a d) : ℕ := (Outer.outC mw SV x.ν x.B.src).circuit.size
def KI.w (x : KI mw SV a d) : ℕ := (Outer.outC mw SV x.ν x.B.src).word.length
def KI.pf (x : KI mw SV a d) : ℕ := x.B.pf.size
def KI.dd (x : KI mw SV a d) : ℕ := (PCPPNative.descriptor x.B.pf).length
def KI.m (x : KI mw SV a d) : ℕ := x.i.req.circuit.size
def KI.dc (x : KI mw SV a d) : ℕ := (PCPPNative.descriptor x.i.req.circuit).length
def KI.M (x : KI mw SV a d) : ℕ := WholeBudget.measure a x.i.req

/-! ## The exact budget under the majorant -/

/-! ## Each quantity is polynomial in `2^ν` -/

theorem poly_q : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.q) := by
  obtain ⟨Cw, mw', hW⟩ := Outer.widthOf_pow k (Outer.apad mw SV)
  exact ⟨Cw, mw', fun x => (Nat.lt_two_pow_self.le).trans (hW (2 ^ x.ν))⟩

theorem poly_cap : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.cap) := by
  obtain ⟨co, eo, _, ho⟩ := oracleSizeBound_polynomiallyBounded d
  exact (poly_q (a := a) (d := d)).comp ⟨co, eo, ho⟩

theorem poly_sz : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.sz) := by
  set K := (Outer.alg mw SV).coefficient
  set se := (Outer.alg mw SV).sizeExp
  obtain ⟨M0, hT⟩ := Outer.natBitLength_T_le SV
  have hS : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => K * (Outer.instLength L x.ν +
      natBitLength (SV.T (Outer.instLength L x.ν)) + 1) ^ se) := by
    refine (PolyB.mul (PolyB.const K) (PolyB.pow (PolyB.add (PolyB.add (PolyB.pow PolyB.size (L + 2))
      (PolyB.add (PolyB.const M0) (PolyB.mul (PolyB.const (k + 2)) PolyB.size))) (PolyB.const 1)) se)).mono
      fun x => ?_
    have h1 : Outer.instLength L x.ν ≤ (2 ^ x.ν) ^ (L + 2) :=
      Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    have h2 := hT x.ν
    have h3 : (k + 2) * x.ν ≤ (k + 2) * 2 ^ x.ν := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  exact hS.mono fun x => Outer.outC_size_le mw SV x.ν x.h1 x.B.src

theorem poly_w : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.w) := by
  have hS := poly_sz (a := a) (d := d) (mw := mw) (SV := SV)
  have hq := poly_q (a := a) (d := d) (mw := mw) (SV := SV)
  refine (PolyB.mul (PolyB.add hS (PolyB.const 3)) (PolyB.mul (PolyB.add hq (PolyB.const 3))
    (PolyB.add (PolyB.mul (PolyB.const 2) (PolyB.add (PolyB.add hS hq) (PolyB.const 5))) (PolyB.const 3)))).mono
    fun x => ?_
  have hel := Outer.ell_le_width mw SV x.ν x.B.src x.hon x.h1
  have hwl := Recovery.HT.word_len_le (Outer.outC mw SV x.ν x.B.src)
  refine hwl.trans ?_
  change _ ≤ (x.sz + 3) * ((x.q + 3) * (2 * (x.sz + x.q + 5) + 3))
  have a2 : (Outer.outC mw SV x.ν x.B.src).ell + 3 ≤ x.q + 3 := by unfold KI.q; omega
  have a3 : 2 * ((Outer.outC mw SV x.ν x.B.src).circuit.size + (Outer.outC mw SV x.ν x.B.src).ell + 5) + 3 ≤
      2 * (x.sz + x.q + 5) + 3 := by unfold KI.q KI.sz; omega
  exact Nat.mul_le_mul le_rfl (Nat.mul_le_mul a2 a3)

theorem pf_le_cap (x : KI mw SV a d) : x.pf ≤ x.cap :=
  (RecoveryChoice.oracleSelector _ d x.z x.h.2.2.2).sizeBounded

theorem poly_pf : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.pf) :=
  (poly_cap (a := a) (d := d) (mw := mw) (SV := SV)).mono pf_le_cap

theorem poly_dd : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.dd) := by
  have hp := poly_pf (a := a) (d := d) (mw := mw) (SV := SV)
  have hq := poly_q (a := a) (d := d) (mw := mw) (SV := SV)
  refine ((((PolyB.mul (PolyB.add hp (PolyB.const 1)) (PolyB.add (PolyB.mul (PolyB.const 6)
    (PolyB.add (PolyB.add hp hq) (PolyB.const 4))) (PolyB.const 9))).add (PolyB.mul (PolyB.const 2) hq)).add
    (PolyB.mul (PolyB.const 4) hp)).add (PolyB.const 9)).mono fun x => ?_
  exact Recovery.HT.desc_len_le' x.B.pf

theorem poly_m : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.m) := by
  have hS := poly_sz (a := a) (d := d) (mw := mw) (SV := SV)
  have hp := poly_pf (a := a) (d := d) (mw := mw) (SV := SV)
  have hq := poly_q (a := a) (d := d) (mw := mw) (SV := SV)
  refine ((PolyB.mul hS (PolyB.add hp (PolyB.const 1))).add (PolyB.add hq (PolyB.const 2))).mono fun x => ?_
  have h := Outer.Dat_size_le mw SV x.ν x.B
  change x.m ≤ x.sz * (x.pf + 1) + (x.q + 2)
  have : x.m = (Outer.Dat mw SV x.ν x.B).D.size := rfl
  unfold KI.sz KI.pf KI.q
  omega

theorem poly_dc : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.dc) := by
  have hm := poly_m (a := a) (d := d) (mw := mw) (SV := SV)
  have hq := poly_q (a := a) (d := d) (mw := mw) (SV := SV)
  refine ((((PolyB.mul (PolyB.add hm (PolyB.const 1)) (PolyB.add (PolyB.mul (PolyB.const 6)
    (PolyB.add (PolyB.add hm hq) (PolyB.const 4))) (PolyB.const 9))).add (PolyB.mul (PolyB.const 2) hq)).add
    (PolyB.mul (PolyB.const 4) hm)).add (PolyB.const 9)).mono fun x => ?_
  exact Recovery.HT.desc_len_le' x.i.req.circuit

theorem poly_M : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.M) := by
  have hm := poly_m (a := a) (d := d) (mw := mw) (SV := SV)
  have hq := poly_q (a := a) (d := d) (mw := mw) (SV := SV)
  refine (PolyB.mul (PolyB.const (PCPPQueryCachedBounds.coefficient a))
    (PolyB.pow (PolyB.add (PolyB.add hm hq) (PolyB.const 1)) (PCPPQueryCachedBounds.degree a))).mono fun x => ?_
  unfold KI.M WholeBudget.measure PCPPQueryCachedBounds.capacity
  exact le_rfl

theorem poly_block : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => (blockV h2 a).budget x.i) := by
  have hw := poly_w (a := a) (d := d) (mw := mw) (SV := SV)
  have hdd := poly_dd (a := a) (d := d) (mw := mw) (SV := SV)
  have hdc := poly_dc (a := a) (d := d) (mw := mw) (SV := SV)
  have hq := poly_q (a := a) (d := d) (mw := mw) (SV := SV)
  have hm := poly_m (a := a) (d := d) (mw := mw) (SV := SV)
  have hM := poly_M (a := a) (d := d) (mw := mw) (SV := SV)
  have c (v : ℕ) : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun _ => v) := PolyB.const v
  have hcost : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => Case2.cost2 h2 x.w x.dd x.dc x.q x.m) := by
    refine ((((((PolyB.mul (c 200) (hdd.add (c 1))).add (PolyB.mul (c UF.K) (hdd.add (c 1)))).add
      (PolyB.mul (c h2.K) (PolyB.pow (((hw.add hdd).add hq).add (c 1)) h2.e))).add
      (PolyB.mul (c 2) (PolyB.mul (hdc.add (c 3)) ((PolyB.mul (c 80) hdc).add (c 120))))).add
      (PolyB.mul (c 34) hm)).add ((PolyB.mul (c 34) hq).add (c 34))).mono fun x => ?_
    unfold Case2.cost2 CheckedPCPP.DescW.readCost
    omega
  have htot : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => PCPPSourceCache.totalBudget a x.i.req) := by
    refine (PolyB.mul (c (PCPPSourceCache.coefficient a))
      (PolyB.pow ((hq.add hm).add (c 5)) (PCPPSourceCache.totalDegree a))).mono fun x => ?_
    unfold PCPPSourceCache.totalBudget PCPPRequestRuntime.sourceParameter
    exact le_rfl
  have hinp : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => (pcppInput x.i.req).length) :=
    ((PolyB.mul (c 3) hM).add (c 3)).mono fun x => (WholeBudget.components a x.i.req).2.2.1
  have hreq : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => RequestSource.budget a x.i.req) :=
    (((PolyB.mul (c 2) htot).add (PolyB.mul (c 8) hinp)).add (c 16)).mono fun x =>
      request_source_bound a x.i.req
  refine ((((PolyB.mul (c 2) hcost).add (c 2)).add (c 1)).add hreq).mono fun x => ?_
  exact le_rfl

end

end W3.NearCubicWires.RepairSource.Outer3.Case2
