import Proof.Packets.SrcMetaRun
import Proof.Foundations.PolynomialSchedule

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceStart.MetaCost
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceBudget.Pow2
open NearCubicWires.Admission NearCubicWires.SourceConstruction
open NearCubicWires.SourceStart.MetaTM NearCubicWires.SourceStart.MetaWords NearCubicWires.SourceStart.MetaAsm
open NearCubicWires.SourceStart.MetaRun
open NearCubicWires.PolynomialSchedule
noncomputable section

/-! ## 1. Small facts -/

theorem pb_cpow (c e : ℕ) : PolynomiallyBounded (fun q => c * (q+1)^e) :=
  ⟨c + 1, e, by omega, fun n => Nat.mul_le_mul_right _ (Nat.le_succ c)⟩

theorem clog_le (m : ℕ) : Nat.clog 2 (m + 1) ≤ m + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := m + 1)).le

theorem bitlen_le (n : ℕ) : natBitLength n ≤ n + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 n
  omega

theorem natWord_len (n : ℕ) : (natWord n).length ≤ 2*n + 3 := by
  rw [natWord_eq]
  simp only [List.length_append, List.length_replicate, List.length_cons, SignedSortKey.binary_length]
  have := bitlen_le n
  omega

theorem bits_len (m : ℕ) : (CloseoutRowsCountBinary.bits m).length ≤ m + 1 := by
  unfold CloseoutRowsCountBinary.bits
  split_ifs
  · simp
  · rw [SignedSortKey.binary_length]; exact bitlen_le m

theorem budget_poly : PolynomiallyBounded CloseoutRowsCountBinary.budget := by
  refine ⟨124, 2, by omega, fun n => ?_⟩
  unfold CloseoutRowsCountBinary.budget
  nlinarith

/-! ## 2. Phase A's cost and `|MB|` through the pieces -/

theorem asmCost_eq {N : ℕ} (w : Fin N → List Bool) :
    ∀ js : List (Fin N), asmCost w js = (js.map (fun j => 2*(w j).length + 2)).sum
  | [] => rfl
  | j :: js => by
    rw [asmCost, List.map_cons, List.sum_cons, asmCost_eq w js]

theorem finRange_map_getD (l : List (List Bool)) (g : List Bool → ℕ) :
    (List.finRange l.length).map (fun i => g (l.getD i.val [])) = l.map g := by
  have hm : (List.finRange l.length).map (fun i => l.getD i.val []) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD]
  have h := congrArg (List.map g) hm
  rw [List.map_map] at h
  exact h

theorem sum_map_two (l : List (List Bool)) :
    (l.map (fun x => 2*x.length + 2)).sum = 2*(l.map List.length).sum + 2*l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

theorem sum_map_body (l : List (List Bool)) :
    (l.map (fun x => (body false x).length)).sum = 2*(l.map List.length).sum := by
  have e : l.map (fun x => (body false x).length) = l.map (fun x => 2 * x.length) :=
    List.map_congr_left (fun x _ => body_length false x)
  rw [e, List.sum_map_mul_left]

/-- The 25 pieces' lengths, with every component abstract. -/
theorem sum_lengths (a1 a2 a3 a4 b1 b2 : List Bool) (bc xc yh ycc bv xv yr : ℕ) :
    ([a1, a2, a3, List.replicate bc true, [false], List.replicate xc false, b1, a4 ++ [true],
      List.replicate yh true, [false], List.replicate yh false, [true, true],
      List.replicate ycc true, [false], List.replicate ycc false, [true],
      List.replicate bv true, [false], List.replicate xv false, b2,
      [true], List.replicate yr true, [false], List.replicate yr false, [true]].map List.length).sum =
      a1.length + a2.length + a3.length + bc + 1 + xc + b1.length + (a4.length + 1) + yh + 1 + yh + 2 + ycc + 1 + ycc + 1 +
        bv + 1 + xv + b2.length + 1 + yr + 1 + yr + 1 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_replicate, List.length_append,
    List.length_cons, List.length_nil]
  omega

variable (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ)

/-- Phase A's cost is linear in the pieces' total length. -/
theorem costA_pieces (cz vz : Bool) (q : ℕ) :
    costA 25 (pwF selector s p packets L cz vz q) =
      2*(2*((pw selector s p packets L cz vz q).map List.length).sum + 50 + 1 + (2*0+1)) + 2 := by
  unfold costA
  rw [asmCost_eq, List.map_map]
  have e1 : (List.finRange 25).map ((fun j : Fin (25 + 2) =>
      2*((if h : j.val < 25 then pwF selector s p packets L cz vz q ⟨j.val, h⟩ else []).length) + 2) ∘ Fin.castAdd 2) =
      (List.finRange 25).map (fun k => (fun x : List Bool => 2*x.length + 2) ((pw selector s p packets L cz vz q).getD k.val [])) := by
    apply List.map_congr_left
    intro k _
    simp [pwF, k.isLt]
  have e2 := finRange_map_getD (pw selector s p packets L cz vz q) (fun x => 2*x.length + 2)
  rw [show (pw selector s p packets L cz vz q).length = 25 from rfl] at e2
  rw [e1, e2, sum_map_two]
  rfl

/-- **`|MB| = Σ|piece|`.** -/
theorem MB_len (cz vz : Bool) (q : ℕ)
    (hcz : cz = true ↔ Meta.mC selector s p q = 0) (hvz : vz = true ↔ Meta.mV selector s p q = 0) :
    (MBof selector s p packets L q).length = ((pw selector s p packets L cz vz q).map List.length).sum := by
  have h := congrArg List.length (pieces_frame selector s p packets L cz vz q hcz hvz)
  have e := finRange_flatMap_getD (pw selector s p packets L cz vz q) (body false)
  rw [show (pw selector s p packets L cz vz q).length = 25 from rfl] at e
  unfold pwF at h
  rw [e, List.length_append, List.length_flatMap, sum_map_body, RepairOrdinary.frame_length] at h
  simp only [List.length_singleton] at h
  omega

/-! ## 3. The size scale and the pieces' total length -/

/-- **The size scale** of the meta word's values. -/
def Sz (q : ℕ) : ℕ :=
  q + Meta.mC selector s p q + Meta.mV selector s p q +
    hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L*
      (q+1)^hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L +
    cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
      (q+1)^cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) +
    cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
      (q+1)^cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) +
    ((packets (decompositionOf s)).coefficient*rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1)*
      (q+1)^rowsE (decompositionOf s) p.clauseDegree (tgt s p)

theorem Sz_poly : PolynomiallyBounded (Sz selector s p packets L) := by
  unfold Sz Meta.mC Meta.mV
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_add (polynomiallyBounded_add polynomiallyBounded_id (pb_cpow _ _)) (pb_cpow _ _)) (pb_cpow _ _))
    (pb_cpow _ _)) (pb_cpow _ _)) (pb_cpow _ _)

theorem yH_le (q : ℕ) : yH selector s p L q ≤ Sz selector s p packets L q + 1 := by
  unfold yH
  have h1 := clog_le (hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L*
      (q+1)^hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L)
  unfold Sz
  omega

theorem yCC_le (q : ℕ) : yCC selector s p L q ≤ 2*Sz selector s p packets L q + 3 := by
  unfold yCC yA yB
  have h1 := clog_le (cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
      (q+1)^cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p))
  have h2 := clog_le (cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
      (q+1)^cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p))
  unfold Sz
  omega

theorem yR_le (q : ℕ) : yR selector s p packets q ≤ Sz selector s p packets L q + 1 := by
  unfold yR
  have h1 := clog_le (((packets (decompositionOf s)).coefficient*rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1)*
      (q+1)^rowsE (decompositionOf s) p.clauseDegree (tgt s p))
  unfold Sz
  omega

theorem BC_le (cz : Bool) (q : ℕ) : BC selector s p cz q ≤ Sz selector s p packets L q + 1 := by
  unfold BC
  have h1 := clog_le (Meta.mC selector s p q)
  unfold Sz
  split_ifs
  · omega
  · omega

theorem BV_le (vz : Bool) (q : ℕ) : BV selector s p L vz q ≤ Sz selector s p packets L q + 1 := by
  unfold BV
  have h1 := clog_le (Meta.mV selector s p q)
  unfold Sz
  split_ifs
  · omega
  · omega

theorem XC_le (cz : Bool) (q : ℕ) : XC cz q ≤ q + 1 := by
  unfold XC; split_ifs
  · omega
  · omega

theorem XV_le (vz : Bool) (q : ℕ) : XV L vz q ≤ q + 1 := by
  unfold XV; split_ifs
  · omega
  · omega

/-- **The pieces' total length** is linear in the size scale. -/
theorem pieces_sum_le (cz vz : Bool) (q : ℕ) :
    ((pw selector s p packets L cz vz q).map List.length).sum ≤ 40*Sz selector s p packets L q + 200 := by
  have a1 := natWord_len 3
  have a2 := natWord_len (wA q L)
  have a3 := natWord_len (uniformDeg q L)
  have a4 := natWord_len 4
  have w1 := wA_le q L
  have w2 := deg_le q L
  have b1 := bits_len (Meta.mC selector s p q)
  have b2 := bits_len (Meta.mV selector s p q)
  have c1 := BC_le selector s p packets L cz q
  have c2 := XC_le cz q
  have c3 := yH_le selector s p packets L q
  have c4 := yCC_le selector s p packets L q
  have c5 := BV_le selector s p packets L vz q
  have c6 := XV_le L vz q
  have c7 := yR_le selector s p packets L q
  have hq : q + Meta.mC selector s p q + Meta.mV selector s p q ≤ Sz selector s p packets L q := by unfold Sz; omega
  unfold pw
  rw [sum_lengths]
  omega

/-! ## 4. The whole program -/

/-- **The meta program's cost bound** (a source polynomial). -/
def costBound (V : Meta.MetaVals2 selector s p packets L) (q : ℕ) : ℕ :=
  V.costC * (q+1)^V.costE + 2*(256*(q+1)^2) + CloseoutRowsCountBinary.budget (Meta.mC selector s p q) +
    CloseoutRowsCountBinary.budget (Meta.mV selector s p q) + 1000*Sz selector s p packets L q + 100000

theorem costBound_poly (V : Meta.MetaVals2 selector s p packets L) : PolynomiallyBounded (costBound selector s p packets L V) := by
  unfold costBound
  refine polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_add (pb_cpow _ _) (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (pb_cpow _ _)))
    ?_) ?_) (polynomiallyBounded_mul (polynomiallyBounded_constant 1000) (Sz_poly selector s p packets L)))
    (polynomiallyBounded_constant _)
  · exact polynomiallyBounded_comp budget_poly (by unfold Meta.mC; exact pb_cpow _ _)
  · exact polynomiallyBounded_comp budget_poly (by unfold Meta.mV; exact pb_cpow _ _)

theorem progCost_le (V : Meta.MetaVals2 selector s p packets L) (cz vz : Bool) (q : ℕ)
    (hcz : cz = true ↔ Meta.mC selector s p q = 0) (hvz : vz = true ↔ Meta.mV selector s p q = 0) :
    progCost V cz vz q ≤ costBound selector s p packets L V q := by
  have hV := V.cost_le q
  have n1 := CloseoutRowsEstimatorParity.Natural.budget_fit q (wA q L) (wA_le q L)
  have n2 := CloseoutRowsEstimatorParity.Natural.budget_fit q (uniformDeg q L) (deg_le q L)
  have hA := costA_pieces selector s p packets L cz vz q
  have hMB := MB_len selector s p packets L cz vz q hcz hvz
  have hP := pieces_sum_le selector s p packets L cz vz q
  have c1 := BC_le selector s p packets L cz q
  have c2 := XC_le cz q
  have c3 := yH_le selector s p packets L q
  have c4 := yCC_le selector s p packets L q
  have c5 := BV_le selector s p packets L vz q
  have c6 := XV_le L vz q
  have c7 := yR_le selector s p packets L q
  have hq : q ≤ Sz selector s p packets L q := by unfold Sz; omega
  have f3 : (RepairOrdinary.frame (natWord 3)).length ≤ 19 := by
    rw [RepairOrdinary.frame_length]; have := natWord_len 3; omega
  have f4 : (RepairOrdinary.frame (natWord 4 ++ [true])).length ≤ 25 := by
    rw [RepairOrdinary.frame_length, List.length_append]; have := natWord_len 4; simp only [List.length_singleton]; omega
  have ff : (RepairOrdinary.frame [false]).length = 3 := rfl
  have ft : (RepairOrdinary.frame [true]).length = 3 := rfl
  have ftt : (RepairOrdinary.frame [true, true]).length = 5 := rfl
  have fone : ([true] : List Bool).length = 1 := rfl
  have hcap : CloseoutRowsEstimatorParity.Capacity.value q = 256*(q+1)^2 := rfl
  unfold progCost costBound
  rw [hA, hMB]
  omega

/-- **Census H7, the meta part: the meta program's cost is a source polynomial.** -/
theorem progCost_poly (V : Meta.MetaVals2 selector s p packets L) (cz vz : Bool)
    (hcz : ∀ q, cz = true ↔ Meta.mC selector s p q = 0) (hvz : ∀ q, vz = true ↔ Meta.mV selector s p q = 0) :
    PolynomiallyBounded (progCost V cz vz) :=
  polynomiallyBounded_mono (fun q => progCost_le selector s p packets L V cz vz q (hcz q) (hvz q))
    (costBound_poly selector s p packets L V)

end
end NearCubicWires.SourceStart.MetaCost

