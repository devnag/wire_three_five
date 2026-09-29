import Proof.Wire_3_5.FinalPass.S5TChA

/-! # S5-THR, part 24: the payloads and the tuple's gate table (P3:2543-2558, 3083-3086)

The THR path's next docks: the front end (`tf_dock`: the tuple's top payloads on THR slots `9 … 12`), the data
stage's inputs (`1^n` from the parse's register, `1^L`, `1^{W_t}` from the powers), the data stage (`td_dock` with
`ThrDataStage2.run`: the tuple's gate table on THR slot `8`).

* `tdInW` / `tdInW_spec` (the three unary inputs, heads back at `0`, registers restored);
* `chainBM`, `chainBCost`, **`chainB_spec`**.

Paper quantities of the main type: THR slot `8` (the tuple's gate table `gatesW (tabH G) G`), THR slots `9 … 12`
(the circuits' top payloads `payOf alg C_i`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (dockS updS sTape_val)
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2InPorts tf2OutPorts TF2Ok)
open NearCubicWires.SupplierPipeline

section TdIn
variable {ns nr : ℕ} (cap : ℕ)

/-- The data stage's unary inputs: `1^n` from register `A` onto `O2` (rewound), `1^L`, `1^{W_t}` copied from powers. -/
def tdInW (O2 O3 O4 XL XW : Fin (ns + 1)) (A OP K T : Fin nr) : WM ns nr :=
  .seq (PrimAsm.Emit.repRegW O2 OP A K T [true]) (.seq (WM.rewind O2 OP) (.seq (plainCopy XL O3) (plainCopy XW O4)))

theorem tdInW_spec (O2 O3 O4 XL XW : Fin (ns + 1)) (A OP K T : Fin nr) (h23 : O2 ≠ O3) (h24 : O2 ≠ O4)
    (h34 : O3 ≠ O4) (hL3 : XL ≠ O3) (hW4 : XW ≠ O4) (hL2 : XL ≠ O2) (hW2 : XW ≠ O2) (hW3 : XW ≠ O3)
    (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T) (hKO : K ≠ OP)
    (σ : WState ns nr) (n L W : ℕ) (hA : σ.val A = n) (hK : σ.val K = 0) (hT : σ.val T = 0) (hOP : σ.val OP = 0)
    (h2 : σ.st O2 = []) (h2h : σ.sh O2 = 0) (h3 : σ.st O3 = []) (h3h : σ.sh O3 = 0) (h4 : σ.st O4 = [])
    (h4h : σ.sh O4 = 0) (hXL : σ.st XL = sent L) (hXLh : σ.sh XL = 0) (hXW : σ.st XW = sent W) (hXWh : σ.sh XW = 0)
    (hc : n ≤ cap) :
    WExec cap (tdInW O2 O3 O4 XL XW A OP K T) σ
      (((σ.sets O2 (List.replicate n true)).sets O3 (List.replicate L true)).sets O4 (List.replicate W true))
      (40 * n + 12 * L + 12 * W + 30) := by
  have e1 := PrimAsm.Emit.repRegW_spec cap O2 OP A K T hAK hAT hKT hKO [true] σ hK hT (by rw [h2, h2h]; rfl)
    (by rw [hA]; exact hc) (by rw [hOP, hA]; simp only [List.length_singleton, Nat.mul_one, Nat.zero_add]; exact hc)
  rw [appendO_wSt σ O2 OP _ (by rw [h2, h2h]; rfl), hA, reps_true] at e1
  have e2 := wSt_rew cap O2 OP σ (List.replicate n true) h2 h2h hOP (by simp; omega)
  have e3 := plainCopy_spec cap XL O3 hL3 L (σ.sets O2 (List.replicate n true))
    (by simp [Function.update_apply, hL2, hXL]) (by simpa using hXLh) (by simp [Function.update_apply, Ne.symm h23, h3])
    (by simpa using h3h)
  have e4 := plainCopy_spec cap XW O4 hW4 W ((σ.sets O2 (List.replicate n true)).sets O3 (List.replicate L true))
    (by simp [Function.update_apply, hW2, hW3, hXW]) (by simpa using hXWh)
    (by simp [Function.update_apply, Ne.symm h24, Ne.symm h34, h4]) (by simpa using h4h)
  have h12 : n * (8 * [true].length + 4) = 12 * n := by simp; ring
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) rfl ?_
  rw [h12]; simp only [List.length_replicate]; omega

end TdIn

section ChainB
variable (D : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (cap : ℕ)

/-- The next docks' machine: the front end, the data stage's inputs, the data stage. -/
noncomputable def chainBM (jL j1 : ℕ) :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine (fun j => sTape (nr := nrL) (tfMap D (PrimT.W6.numsW6 alg Dexp).x
      (PrimThrW.TF3Cost.topFront3 alg).x j)) (PrimThrW.TF3Cost.topFront3 alg).M)
    (tdInW (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨2, by decide⟩)
      (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨3, by decide⟩)
      (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨4, by decide⟩)
      (xsN D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x jL)
      (xsN D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x j1)
      (pR 2) ⟨50, by decide⟩ ⟨51, by decide⟩ ⟨52, by decide⟩ :
      WM (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) nrL).toProg.compile)
    (RecoveryFocus.machine (fun j => sTape (nr := nrL) (tdMap D (PrimT.W6.numsW6 alg Dexp).x
      (PrimThrW.TF3Cost.topFront3 alg).x j)) PrimAsm.ThrData.thrDataStage2.M)

/-- The next docks' cost. -/
noncomputable def chainBCost {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (V L W : ℕ) : ℕ :=
  (PrimThrW.TF3Cost.topFront3 alg).cost V + 1 + (40 * n + 12 * L + 12 * W + 30) + 1 +
    PrimAsm.ThrData.thrDataStage2.cost a' Cs carriers L W

theorem chainB_spec (jL j1 : ℕ) (hjL : jL ≤ D) (hj1 : j1 ≤ D)
    (σ : WState (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) nrL)
    (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (tl : List Bool) (V L W : ℕ)
    (hIn : σ.st (sIn D _ _) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
      (carriers.map Stars.Carrier.code) tl))
    (hV : σ.st (tfMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨1, by omega⟩) =
      List.replicate V true)
    (hxL : σ.st (xsN D _ _ jL) = sent L) (hxW : σ.st (xsN D _ _ j1) = sent W)
    (hbl : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1),
      (1 ≤ i.val ∧ i.val ≤ 5) ∨ tfB D (PrimT.W6.numsW6 alg Dexp).x ≤ i.val → σ.st i = [])
    (hsh : ∀ i, σ.sh i = 0) (hn2 : σ.val (pR 2) = P.n) (h50 : σ.val ⟨50, by decide⟩ = 0)
    (h51 : σ.val ⟨51, by decide⟩ = 0) (h52 : σ.val ⟨52, by decide⟩ = 0)
    (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
    (hok : TF2Ok Cs (carriers.map Stars.Carrier.code) V)
    (hk : carriers.length ≤ 2) (hL : ∀ i, (Cs i).descriptionBits ≤ L)
    (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) (h2 : 2 ≤ P.n + L)
    (hcN : natBitLength P.n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ PrimAsm.ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + P.n + L ≤
      2 * W + 2)
    (hcu : 2 * (PrimAsm.Data.unaryList (PrimAsm.ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2)
    (hcap : P.n ≤ cap) :
    ∃ σ6, Step (chainBM D alg Dexp jL j1) (chainBCost alg Cs carriers V L W)
        (wenc cap σ).H (wenc cap σ).A (wenc cap σ6).H (wenc cap σ6).A ∧
      σ6.st (sIn D _ _) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
        (carriers.map Stars.Carrier.code) tl) ∧
      σ6.st (sSlot D _ _ 0) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ (k : ℕ) (hk : k < 4), σ6.st (sSlot D _ _ ⟨k + 1, by omega⟩) =
        tf2OutPorts alg (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
          tl) V Cs ⟨k + 2, by omega⟩) ∧
      (∀ i, 6 ≤ i.val → i.val < tfB D (PrimT.W6.numsW6 alg Dexp).x → i.val ≠ p0B D + 6 → σ6.st i = σ.st i) ∧
      (∀ i, σ6.sh i = 0) ∧ σ6.val = σ.val := by
  have hge := nsL_ge D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x
  have fne : ∀ {a b : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1)},
      a.val ≠ b.val → a ≠ b := fun h e => h (congrArg Fin.val e)
  have tdv := fun j => tdMap_val D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x j
  have tdBv : tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x =
      tfB D (PrimT.W6.numsW6 alg Dexp).x + (10 + (PrimThrW.TF3Cost.topFront3 alg).x) := rfl
  have tfBv : tfB D (PrimT.W6.numsW6 alg Dexp).x = 720 + D + (21 + (PrimT.W6.numsW6 alg Dexp).x) := by
    unfold tfB w6B p0B; omega
  -- 1: the front end
  obtain ⟨J, _, s1⟩ := tf_dock D (PrimT.W6.numsW6 alg Dexp).x cap alg σ Cs (carriers.map Stars.Carrier.code) tl V
    (by rw [show tfMap D _ _ ⟨0, by omega⟩ = sIn D _ _ from Fin.ext (by rw [tfMap_val]; rfl)]; exact hIn) hV
    (fun j h0 h1 => by
      refine hbl _ ?_
      have hv := tfMap_val D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x j
      rw [if_neg h0, if_neg h1] at hv
      rw [hv]; split_ifs <;> omega)
    hsh hn ha hd hok
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = updS (tfMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) σ
      (fun _ => 0) (Fin.addCases (m := 10) (n := (PrimThrW.TF3Cost.topFront3 alg).x) (motive := fun _ => List Bool)
        (tf2OutPorts alg (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
          tl) V Cs) J) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have tfo : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1),
      i.val ≠ 0 → i.val ≠ p0B D + 6 → (i.val < 2 ∨ (5 < i.val ∧ i.val < tfB D (PrimT.W6.numsW6 alg Dexp).x) ∨
        tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ≤ i.val) → σ1.st i = σ.st i :=
    fun i h0 h6 hr => by
      rw [hσ1]
      refine updS_st_out _ _ _ _ i (fun j h => ?_)
      have hv := congrArg Fin.val h; rw [tfMap_val] at hv; rw [tdBv] at hr
      have hj := j.isLt; split_ifs at hv <;> omega
  have sh1 : ∀ i, σ1.sh i = 0 := by rw [hσ1]; exact updS_sh0 _ (tfMap_inj _ _ _) σ _ hsh
  have val1 : σ1.val = σ.val := by rw [hσ1]; rfl
  have tfi : ∀ (k : ℕ) (hk : k < 10), σ1.st (tfMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x
      ⟨k, by omega⟩) = tf2OutPorts alg (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
        (carriers.map Stars.Carrier.code) tl) V Cs ⟨k, hk⟩ := fun k hk => by
    rw [hσ1, show (⟨k, by omega⟩ : Fin (10 + (PrimThrW.TF3Cost.topFront3 alg).x)) = Fin.castAdd _ ⟨k, hk⟩ from rfl,
      updS_st_in _ (tfMap_inj _ _ _), Fin.addCases_left]
  -- 2: the data stage's inputs
  have hxLv := xsN_val D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x jL hjL
  have hxWv := xsN_val D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x j1 hj1
  have hO : ∀ (k : ℕ) (hk : k < TDT), 2 ≤ k → k ≤ 4 → σ1.st (tdMap D (PrimT.W6.numsW6 alg Dexp).x
      (PrimThrW.TF3Cost.topFront3 alg).x ⟨k, hk⟩) = [] := fun k hk h2 h4 => by
    have hv := tdv ⟨k, hk⟩; simp only at hv; rw [if_neg (by omega), if_neg (by omega)] at hv
    rw [tfo _ (by rw [hv]; omega) (by rw [hv, tdBv, tfBv]; unfold p0B; omega) (Or.inr (Or.inr (by rw [hv]; omega)))]
    exact hbl _ (Or.inr (by rw [hv, tdBv]; omega))
  have hxs : ∀ j, j ≤ D → σ1.st (xsN D _ _ j) = σ.st (xsN D _ _ j) := fun j hj => by
    have hv := xsN_val D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x j hj
    exact tfo _ (by rw [hv]; omega) (by rw [hv]; unfold p0B; omega)
      (Or.inr (Or.inl ⟨by rw [hv]; omega, by rw [hv, tfBv]; omega⟩))
  have v0 : (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨0, by decide⟩).val = 0 := by rw [tdv]; simp
  have v2 : (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨2, by decide⟩).val = tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 2 := by rw [tdv]; simp
  have v3 : (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨3, by decide⟩).val = tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 3 := by rw [tdv]; simp
  have v4 : (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨4, by decide⟩).val = tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 4 := by rw [tdv]; simp
  have hBig : 12 + D + 1 < tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x := by rw [tdBv, tfBv]; omega
  have n23 : tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨2, by decide⟩ ≠ tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨3, by decide⟩ := fne (by rw [v2, v3]; omega)
  have n24 : tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨2, by decide⟩ ≠ tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨4, by decide⟩ := fne (by rw [v2, v4]; omega)
  have n34 : tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨3, by decide⟩ ≠ tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨4, by decide⟩ := fne (by rw [v3, v4]; omega)
  have e2 := tdInW_spec cap (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨2, by decide⟩) (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨3, by decide⟩) (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨4, by decide⟩) (xsN D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x jL) (xsN D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x j1)
    (pR 2) ⟨50, by decide⟩ ⟨51, by decide⟩ ⟨52, by decide⟩ n23 n24 n34
    (fne (by rw [hxLv, v3]; omega)) (fne (by rw [hxWv, v4]; omega)) (fne (by rw [hxLv, v2]; omega))
    (fne (by rw [hxWv, v2]; omega)) (fne (by rw [hxWv, v3]; omega))
    (by decide) (by decide) (by decide) (by decide) σ1 P.n L W (by rw [val1]; exact hn2)
    (by rw [val1]; exact h51) (by rw [val1]; exact h52) (by rw [val1]; exact h50)
    (hO 2 (by decide) (by omega) (by omega)) (sh1 _) (hO 3 (by decide) (by omega) (by omega)) (sh1 _)
    (hO 4 (by decide) (by omega) (by omega)) (sh1 _) (by rw [hxs jL hjL]; exact hxL) (sh1 _)
    (by rw [hxs j1 hj1]; exact hxW) (sh1 _) hcap
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = ((σ1.sets (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨2, by decide⟩) (List.replicate P.n true)).sets
      (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨3, by decide⟩) (List.replicate L true)).sets (tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨4, by decide⟩) (List.replicate W true) :=
    ⟨_, rfl⟩
  rw [← hσ2] at e2
  have st2 : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1),
      i.val ≠ tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 2 → i.val ≠ tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 3 → i.val ≠ tdB D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 4 → σ2.st i = σ1.st i :=
    fun i h2 h3 h4 => by
      rw [hσ2]; simp only [WState.sets_st]
      rw [Function.update_of_ne (fne (by rw [v4]; exact h4)), Function.update_of_ne (fne (by rw [v3]; exact h3)),
        Function.update_of_ne (fne (by rw [v2]; exact h2))]
  have sh2 : ∀ i, σ2.sh i = 0 := fun i => by rw [hσ2]; exact sh1 i
  -- 3: the data stage
  obtain ⟨tout, m, hs, _, fIN, fTAB, _, _⟩ := PrimAsm.ThrData.thrDataStage2.run Cs carriers tl L W ha hk hL hLX h2
    hcN hcA hcK hcx hcy hcu
  have s3 := td_dock D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x cap σ2
    (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W
    (by
      rw [show tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨0, by decide⟩ = sIn D _ _ from Fin.ext v0,
        st2 _ (by simp [sIn]) (by simp [sIn]) (by simp [sIn]),
        show sIn D _ _ = tfMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨0, by omega⟩ from
          Fin.ext (by rw [tfMap_val]; rfl), tfi 0 (by decide)]
      rfl)
    (by rw [hσ2]; simp only [WState.sets_st, Function.update_apply, if_neg n24, if_neg n23, ↓reduceIte])
    (by rw [hσ2]; simp only [WState.sets_st, Function.update_apply, if_neg n34, ↓reduceIte])
    (by rw [hσ2]; simp only [WState.sets_st, Function.update_apply, ↓reduceIte])
    (fun j h0 h2 h3 h4 => by
      have hv := tdv j
      rw [if_neg h0] at hv
      rw [st2 _ (by rw [hv]; split_ifs <;> omega) (by rw [hv]; split_ifs <;> omega) (by rw [hv]; split_ifs <;> omega)]
      rw [tfo _ (by rw [hv]; split_ifs <;> omega)
        (by rw [hv, tdBv, tfBv]; unfold p0B; split_ifs <;> omega)
        (by rw [hv]; split_ifs <;> omega)]
      refine hbl _ ?_
      rw [hv, tdBv]; split_ifs <;> omega)
    sh2 hs
  refine ⟨_, Step.seq (Step.seq s1 (Exec.step (WExec.exec cap e2))) s3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show sIn D _ _ = tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x
        (Fin.castAdd 1 ⟨0, by decide⟩) from Fin.ext (by rw [tdv]; rfl),
      updS_st_in _ (tdMap_inj _ _ _), Fin.addCases_left]
    exact fIN
  · rw [show sSlot D _ _ 0 = tdMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x
        (Fin.castAdd 1 ⟨18, by decide⟩) from Fin.ext (by rw [tdv]; rfl),
      updS_st_in _ (tdMap_inj _ _ _), Fin.addCases_left]
    exact fTAB
  · intro k hk
    rw [updS_st_out _ _ _ _ _ (fun j h => by
        have hv := congrArg Fin.val h; rw [tdv] at hv; simp [sSlot] at hv; rw [tdBv, tfBv] at hv
        have hj := j.isLt; split_ifs at hv <;> omega),
      st2 _ (by simp [sSlot]; rw [tdBv, tfBv]; omega) (by simp [sSlot]; rw [tdBv, tfBv]; omega)
        (by simp [sSlot]; rw [tdBv, tfBv]; omega),
      show sSlot D _ _ ⟨k + 1, by omega⟩ = tfMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x
        ⟨k + 2, by omega⟩ from Fin.ext (by rw [tfMap_val]; simp [sSlot]; split_ifs <;> omega), tfi (k + 2) (by omega)]
  · intro i h6 hB hp
    rw [updS_st_out _ _ _ _ _ (fun j h => by
        have hv := congrArg Fin.val h; rw [tdv] at hv; rw [tdBv] at hv
        have hj := j.isLt; split_ifs at hv <;> omega),
      st2 _ (by rw [tdBv]; omega) (by rw [tdBv]; omega) (by rw [tdBv]; omega),
      tfo _ (by omega) hp (Or.inr (Or.inl ⟨by omega, hB⟩))]
  · exact updS_sh0 _ (tdMap_inj _ _ _) σ2 _ sh2
  · show σ2.val = σ.val
    rw [hσ2]; exact val1

end ChainB

end NearCubicWires.WireExponent3_5.FinalPass.S5T
