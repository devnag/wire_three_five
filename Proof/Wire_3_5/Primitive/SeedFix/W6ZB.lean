import Proof.Wire_3_5.Primitive.SeedFix.W6ZA
import Proof.Packets.PhysicalStepSupport

/-! # W6, part 28: the numbers machine on its ports

P3:2543-2558 (the THR call's numbers from its request, `Nums4.NumsPort4`'s ports `nums3InPorts`/`nums3OutPorts`): the front
end and the fill (`pre_run`), the body embedded beside the front end's scratch (`body_run`, `Step.embed`), every head back
at `0` (`MaskedReset`, `ListMachine.Row.maskBlank`), the ports placed on their streams (`portMap6`, `Step.dock`), as
`TF3Port.port_run` does for the front end:
* `step_mono` (a step with more fuel), `innerM6`, `outerM6`, `portTape6`, `portMap6`, **`numsM6`**, `bodyB`,
  **`nums_run`**: from `nums3InPorts w ncar cap_T V` to `nums3OutPorts w ncar cap_T V (thrNumVals …)` in `2T + 2` steps
  (any `T` above the front end's cost, the fill and the body's bound), the other tapes bounded by `2T + 3`.

Paper quantities of the main type: the THR numbers on the machine's ports. -/

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
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.RecoveryRootRound

theorem step_mono {t s : ℕ} {p : Machine t s} {n m : ℕ} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (hle : n ≤ m) : Step p m hin tin hout tout := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact ⟨r, RepairOrdinary.runFrom_moreFuel p n e _ r hr, hh, ht, by omega⟩

theorem addC_zero {t e : ℕ} :
    Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin t => 0) (fun _ : Fin e => 0) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

variable (alg : DecompositionAlgorithm)

/-- The front end and the fill, then the body beside the front end's scratch. -/
noncomputable def innerM6 (Dexp : ℕ) := Composition.machine (preM alg) (TapeEmbedding.machine (tf alg).x (bodyM Dexp))

/-- Every head back at `0`. -/
noncomputable def outerM6 (Dexp : ℕ) := MaskedReset.machine (innerM6 alg Dexp) (fun _ => true)

/-- The 21 ports on the inner tapes (`+1`: the reset's log tape last). -/
noncomputable def portTape6 (p : Fin 21) : Fin (TI alg + 1) := Fin.castAdd 1 (Fin.castAdd (tf alg).x (sTape (nr := 80) (portS p)))

theorem portTape6_inj : Function.Injective (portTape6 alg) := fun a b h =>
  portS_inj (sTape_inj (Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ h)))

/-- **The port map**: port tapes to `0 … 20`, every other tape `j` to `21 + j`. -/
noncomputable def portMap6 (j : Fin (TI alg + 1)) : Fin (21 + (TI alg + 1)) :=
  if h : ∃ p, portTape6 alg p = j then Fin.castAdd (TI alg + 1) (Fin.find (fun p => portTape6 alg p = j) h)
  else Fin.natAdd 21 j

theorem portMap6_port (p : Fin 21) : portMap6 alg (portTape6 alg p) = Fin.castAdd (TI alg + 1) p := by
  have h : ∃ q, portTape6 alg q = portTape6 alg p := ⟨p, rfl⟩
  unfold portMap6
  rw [dif_pos h]
  congr 1
  exact portTape6_inj alg (Fin.find_spec h)

theorem portMap6_other (j : Fin (TI alg + 1)) (hj : ∀ p, portTape6 alg p ≠ j) : portMap6 alg j = Fin.natAdd 21 j := by
  unfold portMap6
  rw [dif_neg (fun ⟨p, hp⟩ => hj p hp)]

theorem portMap6_inj : Function.Injective (portMap6 alg) := by
  intro j k e
  by_cases hj : ∃ p, portTape6 alg p = j <;> by_cases hk : ∃ p, portTape6 alg p = k
  · obtain ⟨p, rfl⟩ := hj
    obtain ⟨q, rfl⟩ := hk
    rw [portMap6_port, portMap6_port] at e
    rw [Fin.castAdd_inj.mp e]
  · obtain ⟨p, rfl⟩ := hj
    rw [portMap6_port, portMap6_other alg k (fun q hq => hk ⟨q, hq⟩)] at e
    have := congrArg Fin.val e
    simp at this
    omega
  · obtain ⟨q, rfl⟩ := hk
    rw [portMap6_port, portMap6_other alg j (fun q hq => hj ⟨q, hq⟩)] at e
    have := congrArg Fin.val e
    simp at this
    omega
  · rw [portMap6_other alg j (fun q hq => hj ⟨q, hq⟩), portMap6_other alg k (fun q hq => hk ⟨q, hq⟩)] at e
    have := congrArg Fin.val e
    simp at this
    exact Fin.ext this

/-- **The numbers machine.** -/
noncomputable def numsM6 (Dexp : ℕ) := RecoveryFocus.machine (portMap6 alg) (outerM6 alg Dexp)

/-- The raw input off the ports is blank. -/
theorem rawIn_other (w : List Bool) (ncar capT V : ℕ) (i : Fin T0) (hi : ∀ p, sTape (nr := 80) (portS p) ≠ i) :
    rawB (fIn w ncar capT V (fun _ => []) (fun _ => [])) i = [] := by
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [rawB_s]
    have hs : ∀ p : Fin 21, portS p ≠ s := fun p h => hi p (by rw [h])
    have h0 := hs 0
    have h1 := hs 1
    have h2 := hs 2
    have hlo : ¬ (5 ≤ s.val ∧ s.val ≤ 21) := fun ⟨a, b⟩ => hs ⟨s.val - 2, by omega⟩ (Fin.ext (by
      show (if s.val - 2 = 0 then 0 else if s.val - 2 = 1 then 2 else if s.val - 2 = 2 then 3 else if s.val - 2 = 20 then 1 else s.val - 2 + 2) = s.val
      split_ifs <;> omega))
    have h20 := hs 20
    have v0 : s.val ≠ 0 := fun e => h0 (Fin.ext (by rw [e]; rfl))
    have v2 : s.val ≠ 2 := fun e => h1 (Fin.ext (by rw [e]; rfl))
    have v3 : s.val ≠ 3 := fun e => h2 (Fin.ext (by rw [e]; rfl))
    have v1 : s.val ≠ 1 := fun e => h20 (Fin.ext (by rw [e]; rfl))
    unfold fIn
    split_ifs <;> first | rfl | omega
  · exact rawB_c _
  · exact rawB_r _ r

theorem nums3In_port (w : List Bool) (ncar capT V : ℕ) (p : Fin 21) :
    PrimThrW.Nums3.nums3InPorts w ncar capT V p = fIn w ncar capT V (fun _ => []) (fun _ => []) (portS p) := by
  have hp := p.isLt
  rcases (show p.val = 0 ∨ p.val = 1 ∨ p.val = 2 ∨ p.val = 20 ∨ (3 ≤ p.val ∧ p.val ≤ 19) by omega) with h | h | h | h | h
  · have e : p = 0 := Fin.ext h
    subst e
    simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, fIn, portS]
  · have e : p = 1 := Fin.ext h
    subst e
    simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, fIn, portS]
  · have e : p = 2 := Fin.ext h
    subst e
    simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, fIn, portS]
  · have e : p = 20 := Fin.ext h
    subst e
    simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, fIn, portS]
  · have hps : portS p = ⟨p.val + 2, by omega⟩ := by
      apply Fin.ext
      show (if p.val = 0 then 0 else if p.val = 1 then 2 else if p.val = 2 then 3 else if p.val = 20 then 1 else p.val + 2) = p.val + 2
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hps]
    unfold PrimThrW.Nums3.nums3InPorts PrimThrW.NumsP.numsInPorts fIn
    rw [dif_pos (by omega)]
    simp only [Fin.val_mk]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

theorem portIn_eq (w : List Bool) (ncar capT V : ℕ) (j : Fin (TI alg + 1)) :
    Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool)
      (PrimThrW.Nums3.nums3InPorts w ncar capT V) (fun _ => []) (portMap6 alg j) =
    Fin.addCases (m := TI alg) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := T0) (n := (tf alg).x) (motive := fun _ => List Bool)
        (rawB (fIn w ncar capT V (fun _ => []) (fun _ => []))) (fun _ => []))
      (fun _ => List.replicate 0 false) j := by
  by_cases hj : ∃ p, portTape6 alg p = j
  · obtain ⟨p, rfl⟩ := hj
    rw [portMap6_port, Fin.addCases_left]
    unfold portTape6
    rw [Fin.addCases_left, Fin.addCases_left, rawB_s]
    exact nums3In_port w ncar capT V p
  · rw [portMap6_other alg j (fun p hp => hj ⟨p, hp⟩), Fin.addCases_right]
    refine Fin.addCases (motive := fun j => (¬ ∃ p, portTape6 alg p = j) → [] =
      Fin.addCases (m := TI alg) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := T0) (n := (tf alg).x) (motive := fun _ => List Bool)
          (rawB (fIn w ncar capT V (fun _ => []) (fun _ => []))) (fun _ => []))
        (fun _ => List.replicate 0 false) j) (fun i hi => ?_) (fun u _ => ?_) j hj
    · rw [Fin.addCases_left]
      refine Fin.addCases (motive := fun i => (¬ ∃ p, portTape6 alg p = Fin.castAdd 1 i) →
        [] = Fin.addCases (m := T0) (n := (tf alg).x) (motive := fun _ => List Bool)
          (rawB (fIn w ncar capT V (fun _ => []) (fun _ => []))) (fun _ => []) i) (fun i0 hi0 => ?_)
        (fun e _ => ?_) i hi
      · rw [Fin.addCases_left]
        exact (rawIn_other w ncar capT V i0 (fun p hp => hi0 ⟨p, by unfold portTape6; rw [hp]⟩)).symm
      · rw [Fin.addCases_right]
    · rw [Fin.addCases_right]
      rfl

/-- The body's step bound. -/
noncomputable def bodyB (Dexp : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (ncar capT V : ℕ) : ℕ :=
  30 * (opU (2 * V + 2) + 1) + 1 + pcC alg P Cs + 1 + pcE alg P Cs + 1 +
      (7 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG + 7 * (familyMagnitudeExponent (Primitive.thrRealize P Cs alg)) + (Dexp + 1) * opU (2 * V + 2) + 40 * (opU (2 * V + 2) + 1) + 1 +
        ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut * (8 * (opU (2 * V + 2) + 1) + 4) + 14 * (opU (2 * V + 2) + 1) + 4) + 8 * (opU (2 * V + 2) + 1)) + 1 +
        100 * (opU (2 * V + 2) + 1) + 1 + (20 * (opU (2 * V + 2) + 1) + UnionMachine.EwSize.ewBound ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den))) + 1 +
      ((20 * (4 * (opU (2 * V + 2) + 1) + 1) + 1 + GF2.searchCost (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 1 +
        (opU (2 * V + 2) + 2 * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 2) * (40 * 2 ^ (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 40))) + 1 + 14 * (4 * (opU (2 * V + 2) + 1) + 1))

theorem nums_run (Dexp : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (codes : List ℕ) (tl : List Bool) (ncar capT V T : ℕ) (hn1 : 1 ≤ P.n) (ha : a' ≤ 4)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hok : PrimThrW.TopFront2.TF2Ok Cs codes V)
    (c1 : 2 ^ (natBitLength P.n + 1) ≤ (2 * V + 2)) (c2 : 2 ^ (natBitLength a' + 1) ≤ (2 * V + 2))
    (c3 : 2 * (payF alg Cs 0 ++ payF alg Cs 1 ++ payF alg Cs 2 ++ payF alg Cs 3).length + 4 ≤ (2 * V + 2))
    (c4 : 4 ≤ (2 * V + 2)) (c5 : fnw.length ≤ (2 * V + 2))
    (c6 : ∀ j, 2 ^ (natBitLength (szOf Cs j) + 1) + (Primitive.thrOccs P Cs).length ≤ (2 * V + 2))
    (c7 : ncar ≤ (2 * V + 2)) (c8 : capT ≤ (2 * V + 2))
    (hbA : MidBoundsA (2 * V + 2) P.n (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG (familyMagnitudeExponent (Primitive.thrRealize P Cs alg)) Dexp (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut)
    (hbC : MidBounds (2 * V + 2) (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).dig a' ncar capT (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M)
    (bE : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ee ≤ (2 * V + 2)) (hneed : UnionMachine.EwSize.ewNeed ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den) ≤ (2 * V + 2))
    (hbg : 2 ^ ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 1) + 2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 4 ≤ (2 * V + 2)) (hbv : ∀ k, 2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get k + 4 ≤ (2 * V + 2))
    (hT : (tf alg).cost V + 1 + (11 * V + 20 + 1 + 1) + 1 + bodyB alg Dexp P Cs ncar capT V ≤ T) :
    ∃ J : Fin (TI alg + 1) → List Bool, (∀ j, (J j).length ≤ 2 * T + 3) ∧
      Step (numsM6 alg Dexp) (2 * T + 2) (fun _ => 0)
        (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool)
          (PrimThrW.Nums3.nums3InPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool)
          (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT)) J) := by
  refine ((tf alg).run Cs codes tl V hn1 ha hd hok).elim fun J0 hJ0 => ?_
  have pre := pre_run alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs J0 ((tf alg).cost V) hJ0.2
  refine (body_run alg P Cs codes tl ncar capT V Dexp ha c1 c2 c3 c4 c5 c6 c7 c8 hbA hbC bE hneed hbg hbv).elim
    fun τ h => h.elim fun m hb => ?_
  have emb := hb.1.embed (fun _ : Fin (tf alg).x => 0) J0
  have inner : Step (innerM6 alg Dexp) T (fun _ => 0)
      (Fin.addCases (rawB (fIn (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V (fun _ => []) (fun _ => []))) (fun _ => []))
      (Fin.addCases (wenc (2 * V + 2) τ).H (fun _ => 0)) (Fin.addCases (wenc (2 * V + 2) τ).A J0) :=
    step_mono (pre.seq emb) ((Nat.add_le_add_left (show m ≤ bodyB alg Dexp P Cs ncar capT V from hb.2.1) _).trans hT)
  refine (ListMachine.Row.maskBlank inner (fun _ => true) (fun _ _ => rfl) 0).elim fun k sm => ?_
  have eh : (Fin.addCases (fun i => if (fun _ : Fin (TI alg) => true) i = true then 0 else
      Fin.addCases (m := T0) (n := (tf alg).x) (motive := fun _ => ℕ) (wenc (2 * V + 2) τ).H (fun _ => 0) i)
      (fun _ : Fin 1 => (0 : ℕ)) : Fin (TI alg + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun u => ?_) i <;> simp
  have sm2 := (sm.congr_in addC_zero rfl).congr eh rfl
  have d := sm2.dock (portMap6 alg) (portMap6_inj alg) (fun _ => 0) _ (fun _ => rfl) (portIn_eq alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V)
  have edh : dockH (portMap6 alg) (fun _ => (0 : ℕ)) (fun _ => 0) = fun _ => 0 := by
    funext i
    unfold dockH
    split <;> rfl
  have d2 := d.congr edh rfl
  refine ⟨fun j => install (portMap6 alg) (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3InPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V) (fun _ => [])) (Fin.addCases (m := TI alg) (n := 1) (motive := fun _ => List Bool) (Fin.addCases (m := T0) (n := (tf alg).x) (motive := fun _ => List Bool) (wenc (2 * V + 2) τ).A J0) (fun _ => List.replicate k false)) (Fin.natAdd 21 j), fun j => ?_, d2.congr rfl ?_⟩
  · have h1 := Step.tape_length d2 (Fin.natAdd 21 j) 0 0 (le_refl _) (by rw [Fin.addCases_right]; exact le_refl _)
    have h2 : (install (portMap6 alg) (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3InPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V) (fun _ => [])) (Fin.addCases (m := TI alg) (n := 1) (motive := fun _ => List Bool) (Fin.addCases (m := T0) (n := (tf alg).x) (motive := fun _ => List Bool) (wenc (2 * V + 2) τ).A J0) (fun _ => List.replicate k false)) (Fin.natAdd 21 j)).length ≤ max 0 (0 + (2 * T + 2) + 1) := h1
    show (install (portMap6 alg) (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3InPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V) (fun _ => [])) (Fin.addCases (m := TI alg) (n := 1) (motive := fun _ => List Bool) (Fin.addCases (m := T0) (n := (tf alg).x) (motive := fun _ => List Bool) (wenc (2 * V + 2) τ).A J0) (fun _ => List.replicate k false)) (Fin.natAdd 21 j)).length ≤ 2 * T + 3
    omega
  · funext x
    refine Fin.addCases (fun p => ?_) (fun j => ?_) x
    · rw [Fin.addCases_left, ← portMap6_port alg p, install_slot _ (portMap6_inj alg)]
      unfold portTape6
      rw [Fin.addCases_left, Fin.addCases_left, wenc_A_s]
      exact hb.2.2 p
    · rw [Fin.addCases_right]

end NearCubicWires.WireExponent3_5.PrimT.W6
