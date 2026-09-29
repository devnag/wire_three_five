import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Run
import Proof.Packets.PhysicalStepSupport

/-! # TopFrontPort3 body, part 7: the port form (`portM`, `port_run`)

P3:2543-2551 and P3:3071-3091, in the port form of (`PortsE.TopFrontPort3`, W16): in-port `0` the framed
request, in-port `1` the count `1^V`; out-port `2 + i` circuit `i`'s payload, out-port `6 + i` its native word (blank
for `i ≥ a'`), residues on the scratch tapes, every head back at `0`.

* `outerM` (the inner machine under one masked reset), `portTape` (the ten ports on the inner layout), `portMap`
  (ports to `0 … 9`, every other tape to `10 + j`; computable), `portMap_inj`;
* **`port_run`**: from `tf2InPorts w V` (scratch blank), within `2·innerFuel + 2`, every head at `0`, the out-ports
  `tf2OutPorts alg w V Cs` and residues of length at most `2·innerFuel + 3`.

Paper quantities of the main type: as `TopFrontPort3` (each circuit's retained-top children and native word). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TF3Port
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.PrimThrW.TF3Pay
open NearCubicWires.WireExponent3_5.PrimThrW.TF3Run

variable (a : DecompositionAlgorithm)

/-- **The inner machine under one masked reset** (every head back at `0`). -/
noncomputable def outerM := MaskedReset.machine (innerM a) (fun _ => true)

/-- The ten ports on the inner layout (`+1`: the reset's log tape comes last). -/
def portTape (p : Fin 10) : Fin (TT a + 1) :=
  Fin.castAdd 1 (if p.val = 0 then dT a (sTape (nr := DR) sIN) else if p.val = 1 then dT a (sTape (nr := DR) sCT)
    else if h : p.val < 6 then payMap a ⟨p.val - 2, by omega⟩ (PayM.outTop a)
    else dT a (sTape (nr := DR) (sSym ⟨p.val - 6, by omega⟩ 1692)))

theorem outTop_val (i : Fin 4) : Dt + (PayM.Ta a - 1) * i.val ≤ (payMap a i (PayM.outTop a)).val := by
  have h := PayM.outTop_ge a
  rw [payMap_hi a i _ (by omega)]
  omega

theorem portTape_val (p : Fin 10) : (portTape a p).val =
    if p.val = 0 then 0 else if p.val = 1 then 4 else if h : p.val < 6 then (payMap a ⟨p.val - 2, by omega⟩ (PayM.outTop a)).val
    else 14 + 1789 * (p.val - 6) + 1692 + 1 := by
  unfold portTape
  simp only [Fin.val_castAdd]
  split_ifs with h0 h1 h2 <;> simp [dT_val, DockW.sTape_val, sSym_val, sIN, sCT] <;> omega

theorem portTape_inj : Function.Injective (portTape a) := by
  intro p q e
  have hv := congrArg Fin.val e
  rw [portTape_val, portTape_val] at hv
  have hp := p.isLt
  have hq := q.isLt
  apply Fin.ext
  have lo : ∀ i : Fin 4, 9901 ≤ (payMap a i (PayM.outTop a)).val := fun i => by
    have := outTop_val a i
    unfold Dt DS DR at this
    omega
  split_ifs at hv
  all_goals first
    | omega
    | (have h1 := lo ⟨p.val - 2, (by omega)⟩
       omega)
    | (have h1 := lo ⟨q.val - 2, (by omega)⟩
       omega)
    | (by_contra hpq
       exact payMap_disj a ⟨p.val - 2, (by omega)⟩ ⟨q.val - 2, (by omega)⟩
         (fun e => hpq (by have h2 := congrArg Fin.val e; simp only [Fin.val_mk] at h2; omega)) _ _ (Fin.ext hv))

/-- **The port map**: port tapes to `0 … 9`, every other tape `j` to `10 + j`. -/
def portMap (j : Fin (TT a + 1)) : Fin (10 + (TT a + 1)) :=
  if h : ∃ p, portTape a p = j then Fin.castAdd (TT a + 1) (Fin.find (fun p => portTape a p = j) h)
  else Fin.natAdd 10 j

theorem portMap_port (p : Fin 10) : portMap a (portTape a p) = Fin.castAdd (TT a + 1) p := by
  have h : ∃ q, portTape a q = portTape a p := ⟨p, rfl⟩
  unfold portMap
  rw [dif_pos h]
  congr 1
  exact portTape_inj a (Fin.find_spec h)

theorem portMap_other (j : Fin (TT a + 1)) (hj : ∀ p, portTape a p ≠ j) : portMap a j = Fin.natAdd 10 j := by
  unfold portMap
  rw [dif_neg (fun ⟨p, hp⟩ => hj p hp)]

theorem portMap_inj : Function.Injective (portMap a) := by
  intro j k e
  by_cases hj : ∃ p, portTape a p = j <;> by_cases hk : ∃ p, portTape a p = k
  · obtain ⟨p, rfl⟩ := hj
    obtain ⟨q, rfl⟩ := hk
    rw [portMap_port, portMap_port] at e
    rw [Fin.castAdd_inj.mp e]
  · obtain ⟨p, rfl⟩ := hj
    rw [portMap_port, portMap_other a k (fun q hq => hk ⟨q, hq⟩)] at e
    have := congrArg Fin.val e
    simp at this
    omega
  · obtain ⟨q, rfl⟩ := hk
    rw [portMap_port, portMap_other a j (fun q hq => hj ⟨q, hq⟩)] at e
    have := congrArg Fin.val e
    simp at this
    omega
  · rw [portMap_other a j (fun q hq => hj ⟨q, hq⟩), portMap_other a k (fun q hq => hk ⟨q, hq⟩)] at e
    have := congrArg Fin.val e
    simp at this
    exact Fin.ext this

/-- **The front end's port machine.** -/
noncomputable def portM := RecoveryFocus.machine (portMap a) (outerM a)

theorem rawIn_zero (w : List Bool) (V : ℕ) (t : Fin (DS + 2 + DR)) (h0 : t ≠ sTape (nr := DR) sIN)
    (h1 : t ≠ sTape (nr := DR) sCT) : rawIn w 0 0 V t = [] := by
  unfold rawIn
  rw [if_neg h0]
  split_ifs <;> simp_all

theorem innerIn_zero (w : List Bool) (V : ℕ) (j : Fin (TT a)) (h0 : j ≠ dT a (sTape (nr := DR) sIN))
    (h1 : j ≠ dT a (sTape (nr := DR) sCT)) : innerIn a w V j = [] := by
  unfold innerIn
  refine Fin.addCases (fun t ht0 ht1 => ?_) (fun k _ _ => ?_) j h0 h1
  · rw [Fin.addCases_left]
    exact rawIn_zero w V t (fun e => ht0 (by rw [e]; rfl)) (fun e => ht1 (by rw [e]; rfl))
  · rw [Fin.addCases_right]

/-- **The port run.** -/
theorem port_run {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (tl : List Bool)
    (V : ℕ) (hn1 : 1 ≤ n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26)
    (hok : TopFront2.TF2Ok Cs codes V) :
    ∃ J : Fin (TT a + 1) → List Bool, (∀ j, (J j).length ≤ 2 * innerFuel a Cs codes V + 3) ∧
      Step (portM a) (2 * innerFuel a Cs codes V + 2) (fun _ => 0)
        (Fin.addCases (m := 10) (n := TT a + 1) (motive := fun _ => List Bool)
          (TopFront2.tf2InPorts (reqW n true (ReqBridge.thrCodes Cs) codes tl) V) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := 10) (n := TT a + 1) (motive := fun _ => List Bool)
          (TopFront2.tf2OutPorts a (reqW n true (ReqBridge.thrCodes Cs) codes tl) V Cs) J) := by
  set w := reqW n true (ReqBridge.thrCodes Cs) codes tl with hw
  obtain ⟨Hf, Af, s, h0, h1, hpay, hnat⟩ := inner_run a Cs codes tl V hn1 ha hd hok
  obtain ⟨m, sm⟩ := ListMachine.Row.maskBlank s (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun i => if (fun _ : Fin (TT a) => true) i = true then 0 else Hf i)
      (fun _ : Fin 1 => (0 : ℕ)) : Fin (TT a + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun u => ?_) i <;> simp
  rw [addCases_zero, eh] at sm
  set AI := Fin.addCases (m := 10) (n := TT a + 1) (motive := fun _ => List Bool)
    (TopFront2.tf2InPorts w V) (fun _ => []) with hAI
  set tinO := Fin.addCases (m := TT a) (n := 1) (motive := fun _ => List Bool) (innerIn a w V)
    (fun _ => List.replicate 0 false) with htinO
  have hA : ∀ j, AI (portMap a j) = tinO j := by
    intro j
    by_cases hj : ∃ p, portTape a p = j
    · obtain ⟨p, rfl⟩ := hj
      rw [portMap_port, hAI, Fin.addCases_left, htinO]
      unfold portTape TopFront2.tf2InPorts
      simp only [Fin.addCases_left]
      split_ifs with q0 q1 q2
      · simp [innerIn, dT, rawIn]
      · simp [innerIn, dT, rawIn, sIN, sCT, sNT, sLT, sTape_eq_iff']
      · obtain ⟨k, hk⟩ := outTop_hi a ⟨p.val - 2, by omega⟩
        rw [hk]
        simp [innerIn, xT]
      · simp only [innerIn, dT, Fin.addCases_left]
        exact (rawIn_zero w V _ (fun e => absurd (DockW.sTape_inj e) (sSym_ne_low _ _ _ (by decide)))
          (fun e => absurd (DockW.sTape_inj e) (sSym_ne_low _ _ _ (by decide)))).symm
    · rw [portMap_other a j (fun p hp => hj ⟨p, hp⟩), hAI, Fin.addCases_right, htinO]
      refine Fin.addCases (motive := fun j => (¬ ∃ p, portTape a p = j) → [] = tinO j) (fun i hi => ?_)
        (fun u _ => ?_) j hj
      · rw [htinO, Fin.addCases_left]
        exact (innerIn_zero a w V i (fun e => hi ⟨0, by rw [e]; rfl⟩) (fun e => hi ⟨1, by rw [e]; rfl⟩)).symm
      · rw [htinO, Fin.addCases_right]
        rfl
  have d := sm.dock (portMap a) (portMap_inj a) (fun _ => 0) AI (fun _ => rfl) hA
  have edh : dockH (portMap a) (fun _ => (0 : ℕ)) (fun _ => 0) = fun _ => 0 := by
    funext i
    unfold dockH
    split <;> rfl
  rw [edh] at d
  set toutO := Fin.addCases (m := TT a) (n := 1) (motive := fun _ => List Bool) Af
    (fun _ => List.replicate m false) with htoutO
  refine ⟨fun k => install (portMap a) AI toutO (Fin.natAdd 10 k), fun k => ?_, d.congr rfl ?_⟩
  · have h1 := Step.tape_length d (Fin.natAdd 10 k) 0 0 (le_refl _) (by rw [hAI, Fin.addCases_right]; exact le_refl _)
    have h2 : (install (portMap a) AI toutO (Fin.natAdd 10 k)).length ≤
        max 0 (0 + (2 * innerFuel a Cs codes V + 2) + 1) := h1
    show (install (portMap a) AI toutO (Fin.natAdd 10 k)).length ≤ 2 * innerFuel a Cs codes V + 3
    omega
  · funext x
    refine Fin.addCases (fun p => ?_) (fun k => ?_) x
    · rw [Fin.addCases_left, ← portMap_port a p, install_slot _ (portMap_inj a), htoutO]
      unfold portTape TopFront2.tf2OutPorts
      simp only [Fin.addCases_left]
      split_ifs with q0 q1 q2 q3
      · exact h0
      · exact h1
      · rw [hpay ⟨p.val - 2, by omega⟩]
        exact dif_pos (by simp only [Fin.val_mk]; omega)
      · rw [hpay ⟨p.val - 2, by omega⟩]
        exact dif_neg (by simp only [Fin.val_mk]; omega)
      · rw [hnat ⟨p.val - 6, by omega⟩]
        exact dif_pos (by simp only [Fin.val_mk]; omega)
      · rw [hnat ⟨p.val - 6, by omega⟩]
        exact dif_neg (by simp only [Fin.val_mk]; omega)
    · rw [Fin.addCases_right]

end NearCubicWires.WireExponent3_5.PrimThrW.TF3Port
