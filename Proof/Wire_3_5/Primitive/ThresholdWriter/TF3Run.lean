import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Slots
import Proof.Wire_3_5.Primitive.ThresholdWriter.TopFront2

/-! # TopFrontPort3 body, part 6: the inner run (`innerM`, `inner_run`)

P3:3068 (lem:primitive, a tuple arity at most four, the empty tuple included) and P3:2543-2551, 3071-3091 (each
circuit's retained-top children and native word). The inner machine on the layout `TT a`:

* PA's fill (capacity `2V + 2` from the count `1^V`) and the arity guard (`TF3Guard`), then a branch on register `9`
  (`a'`): for `a' ≥ 1` the word stage (`TF3Main`) and the four slots (`TF3Slots`), for `a' = 0` nothing;
* `nbl_le`, `two_pow_nbl`, `big26`, **`caps_of`** (every capacity fact the stages need, from `TF2Ok` at `a' ≥ 1`);
* **`inner_run`**: from the request and the count (everything else blank, heads `0`), within `innerFuel`, the
  request and the count kept, circuit `i`'s payload and native word on slot `i`'s dock tapes (`i < a'`), those
  tapes blank for `i ≥ a'`.

Paper quantities of the main type: the payloads `payOf alg (Cs i)` and native words `thrWord (Cs i)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TF3Run
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.PrimThrW.TF3Pay

/-! ## Arithmetic -/

theorem nbl_le (x : ℕ) (hx : 1 ≤ x) : natBitLength x ≤ x := by
  unfold natBitLength
  have h1 := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
  have h2 : Nat.log 2 x < 2 ^ Nat.log 2 x := Nat.lt_two_pow_self
  omega

theorem two_pow_nbl (x : ℕ) (hx : 1 ≤ x) : 2 ^ natBitLength x ≤ 2 * x := by
  unfold natBitLength
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
  omega

theorem big26 (n : ℕ) (hn : 1 ≤ n) : 2 ^ 25 * (n + 1) ≤ (n + 1) ^ 26 := by
  have h : 2 ^ 25 ≤ (n + 1) ^ 25 := Nat.pow_le_pow_left (show 2 ≤ n + 1 by omega) 25
  rw [pow_succ (n + 1) 25]
  exact Nat.mul_le_mul_right _ h

/-- **The capacities** the word stage needs, from `TF2Ok` once a circuit exists. -/
theorem caps_of {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (V : ℕ)
    (hn1 : 1 ≤ n) (ha1 : 1 ≤ a') (ha : a' ≤ 4) (hok : TopFront2.TF2Ok Cs codes V) :
    (n + 1) ^ 26 ≤ 2 * V ∧ TF3Guard.gPos n a' ≤ V ∧ 2 ^ (natBitLength n + 1) ≤ 2 * V + 2 ∧
      2 * (natWord n).length ≤ V ∧ 4 ≤ 2 * V + 2 := by
  have hx := hok.hcx (encodeNormalizedThresholdThresholdCircuit (Cs ⟨0, by omega⟩))
    (by simp [ReqBridge.thrCodes, List.mem_ofFn])
  have hb := big26 n hn1
  have h1 : (n + 1) ^ 26 ≤ 2 * V := by omega
  have hnw := ParseNat.natWord_length n
  have haw := ParseNat.natWord_length a'
  have hbn := nbl_le n hn1
  have hba := nbl_le a' ha1
  have hp := two_pow_nbl n hn1
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · unfold TF3Guard.gPos
    rw [hnw, haw]
    omega
  · rw [pow_succ]; omega
  · rw [hnw]; omega
  · omega

/-! ## The machines -/

variable (a : DecompositionAlgorithm)

/-- A word-layout machine on the inner layout (the top regions appended, blank). -/
noncomputable def E {s : ℕ} (M : Machine Dt s) := TapeEmbedding.machine (X a) M

/-- The fill and the guard. -/
noncomputable def pre0 := Composition.machine fillAct.compile TF3Guard.gW.toProg.compile

/-- The main branch: the word stage, then the four slots. -/
noncomputable def mainM := Composition.machine (E a TF3Main.mW.toProg.compile) (TF3Slots.pays a)

/-- **The inner machine.** -/
noncomputable def innerM := Composition.machine (E a pre0)
  (Block.branchM (dT a (rTape (ns := DS) (nr := DR) 9)) (mainM a) (Block.idle (TT a)))

/-- The inner machine's fuel (the empty tuple pays only the fill and the guard). -/
noncomputable def innerFuel {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ)
    (V : ℕ) : ℕ :=
  if a' = 0 then (11 * V + 20 + 1 + 1 + 1 + TF3Guard.gCost n 0) + 1 + 2
  else (11 * V + 20 + 1 + 1 + 1 + TF3Guard.gCost n a') + 1 +
    (TF3Main.mCost n ((n + 1) ^ 26) V (2 * V + 2) (ReqBridge.thrCodes Cs) codes + 1 +
      TF3Slots.paysCost a ((n + 1) ^ 26) Cs + 2)

/-- The inner input bank: the request and the count on the word layout, everything else blank. -/
def innerIn (w : List Bool) (V : ℕ) : Fin (TT a) → List Bool := Fin.addCases (rawIn w 0 0 V) (fun _ => [])

theorem addCases_zero {m k : ℕ} :
    (Fin.addCases (m := m) (n := k) (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0) : Fin (m + k) → ℕ) =
      fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem outTop_hi (i : Fin 4) : ∃ k : Fin (X a), payMap a i (PayM.outTop a) = xT a k := by
  have h := PayM.outTop_ge a
  unfold payMap
  rw [dif_neg (by omega)]
  exact ⟨_, rfl⟩

theorem t1692_eq (i : Fin 4) : payMap a i (TF3Slots.t1692 a) = dT a (sTape (nr := DR) (sSym i 1692)) := by
  unfold payMap TF3Slots.t1692
  rw [dif_pos (by norm_num)]
  rfl

/-- The slot docks' entries after the word stage. -/
theorem dock_entry {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (tl : List Bool)
    (V L cap : ℕ) (τ : WState DS DR)
    (hpost : TF3Main.MPost τ (reqW n true (ReqBridge.thrCodes Cs) codes tl) (ReqBridge.thrCodes Cs) n L V)
    (i : Fin 4) (h : i.val < a') (k : Fin (PayM.PT a)) :
    Fin.addCases (wenc cap τ).A (fun _ : Fin (X a) => ([] : List Bool)) (payMap a i k) =
        PayM.payIn a (encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩)) n L k ∧
      Fin.addCases (wenc cap τ).H (fun _ : Fin (X a) => (0 : ℕ)) (payMap a i k) = 0 := by
  have hcl : (ReqBridge.thrCodes Cs).length = a' := by simp [ReqBridge.thrCodes]
  have hi' : i.val < (ReqBridge.thrCodes Cs).length := by rw [hcl]; exact h
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hpost.done i hi'
  obtain ⟨c1, c2⟩ := hpost.cell i hi'
  simp only [symTrip] at d1 d2 d3 d4 d5 d6
  have hget : (ReqBridge.thrCodes Cs).get ⟨i.val, hi'⟩ = encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩) := by
    simp [ReqBridge.thrCodes]
  rw [hget] at d1
  by_cases hk : k.val < 1781
  · have e : payMap a i k = dT a (sTape (nr := DR) (sSym i ⟨k.val, by omega⟩)) := by
      unfold payMap; rw [dif_pos hk]
    rw [e]
    simp only [dT, Fin.addCases_left, wenc_A_s, wenc_H_s]
    unfold PayM.payIn
    rw [dif_pos hk]
    unfold ThrTab.blockIn
    rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ 4 ≤ k.val by omega) with h0 | h0 | h0 | h0 | h0
    · rw [show (⟨k.val, by omega⟩ : Fin 1789) = 0 from Fin.ext h0]
      simp only [h0, if_true]
      exact ⟨d1, d2⟩
    · rw [show (⟨k.val, by omega⟩ : Fin 1789) = 1 from Fin.ext h0]
      simp only [h0, if_true, if_false, show (1 : ℕ) ≠ 0 by decide]
      exact ⟨d3, d4⟩
    · rw [show (⟨k.val, by omega⟩ : Fin 1789) = 2 from Fin.ext h0]
      simp only [h0, if_true, if_false, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide]
      exact ⟨d5, d6⟩
    · rw [show (⟨k.val, by omega⟩ : Fin 1789) = 3 from Fin.ext h0]
      simp only [h0, if_true, if_false, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
        show (3 : ℕ) ≠ 2 by decide]
      exact ⟨c1, c2⟩
    · obtain ⟨f1, f2⟩ := hpost.free i ⟨k.val, by omega⟩ h0
      simp only [Fin.val_mk, show ¬ (k.val = 0) by omega, show ¬ (k.val = 1) by omega, show ¬ (k.val = 2) by omega,
        show ¬ (k.val = 3) by omega, if_false]
      exact ⟨f1, f2⟩
  · have e : payMap a i k = xT a (topT a i ⟨k.val - 1781, by have := k.isLt; unfold PayM.PT at this; omega⟩) := by
      unfold payMap; rw [dif_neg hk]
    rw [e]
    unfold PayM.payIn
    rw [dif_neg hk]
    simp [xT]

/-- **The inner run.** -/
theorem inner_run {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (tl : List Bool)
    (V : ℕ) (hn1 : 1 ≤ n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26)
    (hok : TopFront2.TF2Ok Cs codes V) :
    ∃ (Hf : Fin (TT a) → ℕ) (Af : Fin (TT a) → List Bool),
      Step (innerM a) (innerFuel a Cs codes V) (fun _ => 0)
        (innerIn a (reqW n true (ReqBridge.thrCodes Cs) codes tl) V) Hf Af ∧
      Af (dT a (sTape (nr := DR) sIN)) = frame (reqW n true (ReqBridge.thrCodes Cs) codes tl) ∧
      Af (dT a (sTape (nr := DR) sCT)) = List.replicate V true ∧
      (∀ i : Fin 4, Af (payMap a i (PayM.outTop a)) =
        if h : i.val < a' then TopFront.payOf a (Cs ⟨i.val, h⟩) else []) ∧
      (∀ i : Fin 4, Af (dT a (sTape (nr := DR) (sSym i 1692))) =
        if h : i.val < a' then PCJd4d1d9d7d1fa4313_Production.thrWord (Cs ⟨i.val, h⟩) else []) := by
  have hcl : (ReqBridge.thrCodes Cs).length = a' := by simp [ReqBridge.thrCodes]
  set w := reqW n true (ReqBridge.thrCodes Cs) codes tl with hw
  have s0 : Step fillAct.compile (11 * V + 20 + 1 + 1) (fun _ => 0) (rawIn w 0 0 V)
      (wenc (2 * V + 2) (σ0 w 0 0 V)).H (wenc (2 * V + 2) (σ0 w 0 0 V)).A := Exec.step (fillAct_exec w 0 0 V)
  have g := TF3Guard.g_spec (2 * V + 2) n (ReqBridge.thrCodes Cs) codes tl (σ0 w 0 0 V) (by simp [σ0, hw]) rfl
    (fun _ => rfl) hok.hcN (by rw [hcl]; exact hok.hcA)
  rw [hcl] at g
  set σG := ((σ0 w 0 0 V).seth sIN (TF3Guard.gPos n a')).setv 9 a' with hσG
  have s1 := Exec.step (WExec.exec (2 * V + 2) g)
  have e01 := (s0.seq s1).embed (fun _ : Fin (X a) => (0 : ℕ)) (fun _ => [])
  rw [addCases_zero] at e01
  have hbit : readTapeBit (Fin.addCases (wenc (2 * V + 2) σG).A (fun _ : Fin (X a) => ([] : List Bool))
      (dT a (rTape (ns := DS) (nr := DR) 9)))
      (Fin.addCases (wenc (2 * V + 2) σG).H (fun _ : Fin (X a) => (0 : ℕ)) (dT a (rTape (ns := DS) (nr := DR) 9))) =
      decide (a' ≠ 0) := by
    simp only [dT, Fin.addCases_left]
    have := wbit_r (2 * V + 2) σG 9
    simp only [Bank.bit] at this
    rw [this]
    simp [hσG]
  by_cases ha0 : a' = 0
  · subst ha0
    have sb := Block.branch_false (dT a (rTape (ns := DS) (nr := DR) 9)) (mainM a)
      (ListMachine.Print.idle_step (Fin.addCases (wenc (2 * V + 2) σG).H (fun _ : Fin (X a) => (0 : ℕ)))
        (Fin.addCases (wenc (2 * V + 2) σG).A (fun _ : Fin (X a) => ([] : List Bool)))) (by rw [hbit]; rfl)
    refine ⟨_, _, (e01.seq sb).enlarge ?_, ?_, ?_, ?_, ?_⟩
    · unfold innerFuel; rw [if_pos rfl]
    · simp [dT, hσG, σ0, hw]
    · simp [dT, hσG, σ0, sIN, sNT, sLT, sCT]
    · intro i
      obtain ⟨k, hk⟩ := outTop_hi a i
      rw [hk, dif_neg (by omega)]
      simp [xT]
    · intro i
      rw [dif_neg (by omega)]
      simp only [dT, Fin.addCases_left, wenc_A_s, hσG, WState.setv_st, WState.seth_st]
      exact σ0_sym w 0 V i 1692
  · have ha1 : 1 ≤ a' := by omega
    obtain ⟨h26, hpos, hn, hnV, hc4⟩ := caps_of Cs codes V hn1 ha1 ha hok
    obtain ⟨τ, hm, hpost⟩ := TF3Main.m_spec (2 * V + 2) n (ReqBridge.thrCodes Cs) codes tl V ((n + 1) ^ 26) rfl
      (by rw [hcl]; exact ha) hok.hk (by rw [hcl]; exact hpos) (by omega) hn hnV (by omega) hok.hcN
      (by rw [hcl]; exact hok.hcA) hok.hcK hok.hcx hok.hcy hc4
    rw [hcl] at hm
    have hG : TF3Main.gSt (reqW n true (ReqBridge.thrCodes Cs) codes tl) V n a' = σG := rfl
    rw [hG] at hm
    have sm := (Exec.step (WExec.exec (2 * V + 2) hm)).embed (fun _ : Fin (X a) => (0 : ℕ)) (fun _ => [])
    obtain ⟨H4, A4, sp, hout, hfill, hblank⟩ := TF3Slots.pays_run a Cs ((n + 1) ^ 26) hd
      (Fin.addCases (wenc (2 * V + 2) τ).H (fun _ : Fin (X a) => (0 : ℕ)))
      (Fin.addCases (wenc (2 * V + 2) τ).A (fun _ : Fin (X a) => ([] : List Bool)))
      (fun i h => ⟨fun k => (dock_entry a Cs codes tl V _ _ τ hpost i h k).1,
        fun k => (dock_entry a Cs codes tl V _ _ τ hpost i h k).2⟩)
      (fun i h => by
        have hi' : (ReqBridge.thrCodes Cs).length ≤ i.val := by rw [hcl]; exact h
        obtain ⟨⟨b1, -, -, -, -, -⟩, -, -⟩ := hpost.blank i hi'
        simp only [symTrip] at b1
        simp only [dT, Fin.addCases_left, wenc_A_s]
        exact b1)
    have sb := Block.branch_true (dT a (rTape (ns := DS) (nr := DR) 9)) (Block.idle (TT a)) (sm.seq sp)
      (by rw [hbit]; simp [ha0])
    have hlow : ∀ s : Fin (DS + 1), s.val < 14 → A4 (dT a (sTape (nr := DR) s)) =
        Fin.addCases (wenc (2 * V + 2) τ).A (fun _ : Fin (X a) => ([] : List Bool)) (dT a (sTape (nr := DR) s)) :=
      fun s hs => hout _ (fun i k => payMap_ne_low a i k s hs)
    refine ⟨H4, A4, (e01.seq sb).enlarge ?_, ?_, ?_, ?_, ?_⟩
    · unfold innerFuel; rw [if_neg ha0]
    · rw [hlow sIN (by decide)]
      simp only [dT, Fin.addCases_left, wenc_A_s]
      exact hpost.inp
    · rw [hlow sCT (by decide)]
      simp only [dT, Fin.addCases_left, wenc_A_s]
      exact hpost.cnt
    · intro i
      by_cases h : i.val < a'
      · rw [dif_pos h]; exact (hfill i h).1
      · rw [dif_neg h, hblank i (by omega)]
        obtain ⟨k, hk⟩ := outTop_hi a i
        rw [hk]
        simp [xT]
    · intro i
      rw [← t1692_eq]
      by_cases h : i.val < a'
      · rw [dif_pos h]; exact (hfill i h).2
      · rw [dif_neg h, hblank i (by omega), t1692_eq]
        simp only [dT, Fin.addCases_left, wenc_A_s]
        exact (hpost.free i 1692 (by decide)).1

end NearCubicWires.WireExponent3_5.PrimThrW.TF3Run
