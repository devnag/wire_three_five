import Proof.Wire_3_5.Compiler.MachineTopInit
import Proof.Wire_3_5.Compiler.MachineReqContract3

/-! # C3 v2 top level: the compiler stages on the request (P3:1916-1936)

Paper: "Multiply the expression by `2^{m−1}` [...] Substitute the disjoint exact children in each polynomial [...]
Apply Lemma alg:binlift at precision `Q'` to each polynomial" (P3:1918-1932). MC5's `subsets_run` runs these stages
for every counter value `j < 2^m` and every term, writing the groups `groupsRef Q' (shapeOf D) m V` (the lifted unions
of each polarized, substituted and cancelled polynomial) on its output tape. This module instantiates it on a C3 v2
request: the stage's fixed tapes (`sFix`: the expression, C3a's children table, the constant templates of T2), its
initial registers (`sSt0`: zero registers of the entry width), and every hypothesis of `SubsetPre` from `C3Req.Pre`
(`subsetPre_of`: atoms inside the pool, degrees, the per-polynomial counts `(P_ex+1)^d` and `Q'(P_ex+1)^{Q'd}`, and the
list maxima `sNF`, `sCB`, `sB`, `sCBW`), with the log capacities as hypotheses (`SubCaps`). **`subsets_stage`**: the
stages, then the output's terminator, every head back at cell 0: the output tape holds `groupsRef … ++ [false]`, the
input of the emit stage (T4). The paper quantity is the stages' output `groupsRef`. Main declarations: `listMax`,
`le_listMax`, `sNF`, `sCB`, `sB`, `sCBW`, `sNG`, `sNU`, `sFix`, `sSt0`, `sSt0_inv`, `SubCaps`, **`subsetPre_of`**,
`sOut`, **`subsets_stage`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The largest entry of a list of naturals (`0` for the empty list). -/
def listMax (l : List ℕ) : ℕ := l.foldr max 0

theorem le_listMax : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ listMax l
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (le_listMax l x h).trans (le_max_right _ _)

variable (a : DecompositionAlgorithm)

/-- The largest number of monomials of a factor. -/
def sNF (R : C3Req) : ℕ := listMax (R.V.flatMap fun t => t.2.map List.length)

/-- The largest monomial code. -/
def sCB (R : C3Req) : ℕ := listMax (R.V.flatMap fun t => t.2.flatMap fun f => f.map fun mono => (codeBits mono).length)

/-- The largest number of masks of a term's monomials. -/
def sB (R : C3Req) : ℕ := listMax (R.V.map fun t => (t.2.flatten.flatMap (monoMasks (shapeOf (R.D a)))).length)

/-- The largest coefficient code. -/
def sCBW (R : C3Req) : ℕ := listMax (R.V.map fun t => (cbits t.1).length)

/-- The per-polynomial count of cancelled masks, `(P_ex+1)^d`. -/
def sNG (R : C3Req) : ℕ := ((shapeOf (R.D a)).flatten.length + 1) ^ R.d

/-- The per-polynomial count of lifted unions, `Q'(P_ex+1)^{Q'd}` (alg:eq-occurrences, P3:1887-1888). -/
def sNU (R : C3Req) : ℕ := R.P.Q * ((shapeOf (R.D a)).flatten.length + 1) ^ (R.P.Q * R.d)

/-- The fixed tapes of the stages on the request. -/
def sFix (R : C3Req) (cap cap2 cap3 cap4 : ℕ) : TFix :=
  ⟨R.V.flatMap termRec ++ [false], tableTape (childTable R.P.Q (shapeOf (R.D a))) [], cap, cap2, cap3, cap4,
    z0 R.P.Q (shapeOf (R.D a)).flatten.length, [], lastT R.P.Q (shapeOf (R.D a)).flatten.length,
    levelT R.P.Q (shapeOf (R.D a)).flatten.length, zeroT R.P.Q (shapeOf (R.D a)).flatten.length, []⟩

/-- The stages' initial registers: zero registers `L` of the entry width, empty lists, `false` flags. -/
def sSt0 (L : List Bool) : TS :=
  ⟨⟨[], [], [], L, L, L, [], [], [], L, L, false⟩, false, [], [false], [], L, L, L, L, false, []⟩

theorem zeroT_length (Q W : ℕ) : (zeroT Q W).length = Q + W + 1 := by simp [zeroT]

theorem sSt0_inv (Q W : ℕ) : TSInv (Q + W + 1) (sSt0 (zeroT Q W)) := by
  refine ⟨⟨zeroT_length Q W, zeroT_length Q W, zeroT_length Q W, zeroT_length Q W, zeroT_length Q W, by simp [sSt0]⟩,
    by simp [sSt0], ⟨by simp, zeroT_length Q W, zeroT_length Q W, zeroT_length Q W, zeroT_length Q W⟩⟩

/-- The capacities the stages need (MC5's `SubsetPre` log fields), at the request's parameters. -/
structure SubCaps (R : C3Req) (cap cap2 cap3 cap4 cap5 : ℕ) : Prop where
  hc : Caps R.d (shapeOf (R.D a)).length R.P.Q (shapeOf (R.D a)).flatten.length (sB a R) cap cap2 cap3
  hcap4 : 1 + 1 + (R.m * (factorCost (sNF R) (sCB R) R.d (shapeOf (R.D a)).length R.P.Q
    (shapeOf (R.D a)).flatten.length (sB a R) + 2) + 1) ≤ cap4
  hcwc : 2 * sCBW R + 1 ≤ cap
  hcap2u : pass1Cost (sNU a R) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) ≤ cap2 ∧
    appendCost (sNU a R) (sNU a R + 1) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) ≤ cap2
  hcap3u : sNG a R * (aCost (sNU a R) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) + 2) + 1 ≤ cap3
  hcap3o : sNU a R * (2 * (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) + 1 + 1 + 1 + 2) + 1 ≤ cap3
  hcapm : 2 * R.m + 2 ≤ cap
  hcap5 : R.V.length * (termCost (sCBW R) R.m (sNF R) (sCB R) R.d (shapeOf (R.D a)).length R.P.Q
    (shapeOf (R.D a)).flatten.length (sB a R) (sNG a R) (sNU a R) + 2) + 1 ≤ cap5

theorem shapeOf_length {α : Type} (D : List (List α)) : (shapeOf D).length = D.length := by simp [shapeOf]

/-- **MC5's hypotheses from the C3 v2 precondition** (and the capacities). -/
theorem subsetPre_of (R : C3Req) (hR : R.Pre a) (cap cap2 cap3 cap4 cap5 : ℕ)
    (hcaps : SubCaps a R cap cap2 cap3 cap4 cap5) :
    SubsetPre R.P.Q (shapeOf (R.D a)) R.m R.V [] [] (sFix a R cap cap2 cap3 cap4) cap5 R.d (sB a R) (sNF R) (sCB R)
      (sCBW R) (sNG a R) (sNU a R) := by
  obtain ⟨_, _, hQ, hV, hmono, _⟩ := hR
  have hdeg : ∀ t ∈ R.V, ∀ j, ∀ mono ∈ (selectBits t.2 j).flatten, mono.length ≤ R.d := by
    intro t ht j mono hmn
    obtain ⟨f, hf, hmf⟩ := List.mem_flatten.mp hmn
    exact (hmono t ht f ((selectBits_sublist t.2 j).subset hf) mono hmf).1
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hQ, hV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcaps.hc, hcaps.hcap4, hcaps.hcwc,
    hcaps.hcap2u, hcaps.hcap3u, hcaps.hcap3o, hcaps.hcapm, hcaps.hcap5⟩
  · intro t ht f hf mono hmn x hx
    rw [shapeOf_length, C3Req.D, densePool_length]
    exact (hmono t ht f hf mono hmn).2 x hx
  · intro t ht f hf mono hmn
    exact (hmono t ht f hf mono hmn).1
  · intro t ht f hf
    exact le_listMax _ _ (List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨f, hf, rfl⟩⟩)
  · intro t ht f hf mono hmn
    exact le_listMax _ _ (List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨f, hf, List.mem_map.mpr ⟨mono, hmn, rfl⟩⟩⟩)
  · intro t ht
    exact le_listMax _ _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
  · intro t ht
    exact le_listMax _ _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
  · intro j t ht
    rw [(oddMasksM_perm _ _).length_eq]
    exact oddMasks_length_le _ R.d _ (hdeg t ht j)
  · intro j t ht
    exact Emit.unionsM_length_le _ R.P.Q R.d _ (hdeg t ht j)

/-! ## The stages, then the output's terminator -/

def s31 : Fin 1 → Fin 37 := ![31]

theorem s31_inj : Function.Injective s31 := by decide

theorem install_s31 (A : Fin 37 → List Bool) (v : Fin 1 → List Bool) :
    install s31 A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17,
      A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, v 0, A 32, A 33, A 34, A 35,
      A 36] := by
  funext i
  fin_cases i
  all_goals first
    | exact install_slot s31 s31_inj A v 0
    | exact install_other s31 A v _ (by decide)

/-- The stages' tapes after the last counter value, with the output `G`. -/
def sOut (x : TFix) (m : ℕ) (st : TS) (cap5 : ℕ) (G : List Bool) : Fin 37 → List Bool :=
  ![x.VT, x.TT, st.ps.Ea, st.ps.LA, st.ps.LB, frame st.ps.R, frame st.ps.R2, frame st.ps.R3, List.replicate x.cap false,
    List.replicate x.cap2 false, List.replicate x.cap3 false, frame x.z, streamTape st.ps.G st.ps.staleG, st.ps.O,
    frame st.ps.X, frame st.ps.Y, [st.ps.Ec], [false], frame (binary m (2 ^ m)), [st.PJ], st.CW, st.Sp, st.Op,
    frame st.Gw, frame st.Rp, frame st.Zu, frame st.Z2u, frame x.T1, frame x.T2, frame x.ZT, [st.Cu], G,
    List.replicate x.cap4 false, List.replicate cap5 false, frame (List.replicate m true), [false], [true]]

/-- The stages then the terminator, every head back at cell 0. -/
noncomputable def subsetsStageM :=
  MaskedReset.machine (Composition.machine subsetLoopM (RecoveryFocus.machine s31 (putM false))) (fun _ => true)

/-- The cost of the stages. -/
def subsetsCost (R : C3Req) : ℕ :=
  2 ^ R.m * (subsetCost R.V.length (sCBW R) R.m (sNF R) (sCB R) R.d (shapeOf (R.D a)).length R.P.Q
    (shapeOf (R.D a)).flatten.length (sB a R) (sNG a R) (sNU a R) + 2) + 1

/-- **The compiler stages on the request**: from the fixed tapes and the zero registers, the output tape holds the
groups `groupsRef Q' (shapeOf D) m V` and a terminator; every head is back at cell 0. -/
theorem subsets_stage (R : C3Req) (hR : R.Pre a) (cap cap2 cap3 cap4 cap5 capL : ℕ)
    (hcaps : SubCaps a R cap cap2 cap3 cap4 cap5) (hL : subsetsCost a R + 1 + 1 ≤ capL) :
    Step subsetsStageM (2 * (subsetsCost a R + 1 + 1) + 2) (fun _ => 0)
      (Fin.addCases (sBank (sFix a R cap cap2 cap3 cap4) R.m 0
        (sSt0 (zeroT R.P.Q (shapeOf (R.D a)).flatten.length)) cap5 true) (fun _ : Fin 1 => List.replicate capL false))
      (fun _ => 0)
      (Fin.addCases (sOut (sFix a R cap cap2 cap3 cap4) R.m
        (stAt R.P.Q (shapeOf (R.D a)) R.V (sSt0 (zeroT R.P.Q (shapeOf (R.D a)).flatten.length)) (2 ^ R.m)) cap5
        (groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ [false])) (fun _ : Fin 1 => List.replicate capL false)) := by
  have hpre := subsetPre_of a R hR cap cap2 cap3 cap4 cap5 hcaps
  set x := sFix a R cap cap2 cap3 cap4 with hx
  set st0 := sSt0 (zeroT R.P.Q (shapeOf (R.D a)).flatten.length) with hst0
  set stF := stAt R.P.Q (shapeOf (R.D a)) R.V st0 (2 ^ R.m) with hstF
  have e1 := subsets_run R.P.Q (shapeOf (R.D a)) R.m R.V [] [] x st0 cap5 R.d (sB a R) (sNF R) (sCB R) (sCBW R)
    (sNG a R) (sNU a R) hpre (sSt0_inv R.P.Q _)
  have hout : stF.outs = groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V := by
    rw [hstF, subsets_outs R.P.Q _ R.m R.V st0 hpre.hQ hpre.hp]
    rfl
  have e2 := putStep false (overlay stF.outs []) stF.outs.length
  have ex : overlay (stF.outs ++ [false]) [] = groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ [false] := by
    rw [overlay_nil_right, hout]
  rw [overlay_write, ex] at e2
  have s2 := dockRun e2 s31 s31_inj (sHead stF.outs.length) (sBank x R.m (2 ^ R.m) stF cap5 false)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_s31] at s2
  have s2' := s2.congr (tout' := sOut x R.m stF cap5 (groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ [false])) rfl rfl
  have j := e1.seq s2'
  have m := j.mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hL
  exact (m.congr_in (addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (mask_heads_zero _) rfl


end NearCubicWires.WireExponent3_5.CompilerMachine.Top
