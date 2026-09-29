import Proof.Wire_3_5.Primitive.SeedFix.W6Q

/-! # W6, part 18: cost-explicit twins of part 1's word phase and proof 1's program docks

P3:2543-2558 (row:threshold-rows: `|𝒢|` and the family's magnitude envelope, computed from the request's words):
part 1's `readM_spec`, `p1_spec`, `metaC_blk`/`metaE_blk`, `progC_dock`/`progE_dock` state their step
counts existentially; the numbers machine's port form (`Nums4.NumsPort4.run`) needs an explicit cost, so these twins
restate them with the count kept (same proofs, the count named):
* **`readM2_spec`** (`readMCost sz`), **`p1_spec2`** (`m ≤ 30·(opU+1)`);
* **`metaC_blk2`**, **`progC_dock2`** (`2·progCost … + 2` steps, `1^{Cv}` on block C's tape `1`), **`metaE_blk2`**,
  **`progE_dock2`** (`1^{clog₂(Fv+1)}` on block E's tape `1`).

Paper quantities of the main types: `|𝒢|`, the magnitude exponent, `M` and the request's numbers, each with its
step count. -/

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
open NearCubicWires.PacketsMeta NearCubicWires.PacketsMeta.Lev NearCubicWires.PacketsMeta.Setup
open NearCubicWires.PacketsMeta.Tail NearCubicWires.PacketsMeta.Prog NearCubicWires.PacketsMeta.Spec
open NearCubicWires.PacketsMeta.Bounds
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_nil appendO_append appendO_setv)
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ)

attribute [local simp] rN rA rM rNc rCap qa qOP qSP qf qc qp qt

/-! ## The word phase with its count -/

/-- The payload fields' count. -/
def readMCost (sz : Fin 4 → ℕ) : ℕ :=
  ((natBitLength (sz 0) + 2) * (40 * 2 ^ natBitLength (sz 0) + 40) + 3) + 1 + (((natBitLength (sz 1) + 2) * (40 * 2 ^ natBitLength (sz 1) + 40) + 3) + 1 + (((natBitLength (sz 2) + 2) * (40 * 2 ^ natBitLength (sz 2) + 40) + 3) + 1 + ((natBitLength (sz 3) + 2) * (40 * 2 ^ natBitLength (sz 3) + 40) + 3)))

theorem readM2_spec (σ : WL) (a' : ℕ) (sz : Fin 4 → ℕ) (Mv : ℕ)
    (hpay : ∀ j : Fin 4, j.val < a' → ∃ r, σ.st (sPay j) = frameP (natWord (sz j)) ++ r)
    (hsh : ∀ j, σ.sh (sPay j) = 0) (hq : σ.val qa = a') (hf : σ.val qf = 0) (hc : σ.val qc = 0)
    (hp : σ.val qp = 0) (ht : σ.val qt = 0) (hM0 : σ.val rM = 0)
    (hMv : Mv = (if (0 : Fin 4).val < a' then sz 0 else 0) + (if (1 : Fin 4).val < a' then sz 1 else 0) +
      (if (2 : Fin 4).val < a' then sz 2 else 0) + (if (3 : Fin 4).val < a' then sz 3 else 0))
    (hcap : ∀ j, 2 ^ (natBitLength (sz j) + 1) + Mv ≤ cap) (hqc : a' ≤ cap) :
    ∃ τ, WExec cap readM σ τ (readMCost sz) ∧ τ.val rM = Mv ∧ τ.val qa = a' - 4 ∧
      (∀ r, r ≠ rM → r ≠ qa → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ (∀ j, (∀ i, j ≠ sPay i) → τ.sh j = σ.sh j) ∧
      τ.cell = σ.cell := by
  have hne : ∀ i j : Fin 4, i ≠ j → sPay i ≠ sPay j := sPay_ne
  have pick : ∀ j : Fin 4, ∃ r, j.val < a' → σ.st (sPay j) = frameP (natWord (sz j)) ++ r := fun j => by
    by_cases h : j.val < a'
    · obtain ⟨r, hr⟩ := hpay j h; exact ⟨r, fun _ => hr⟩
    · exact ⟨[], fun h' => absurd h' h⟩
  obtain ⟨r0, h0⟩ := pick 0
  obtain ⟨r1, h1⟩ := pick 1
  obtain ⟨r2, h2⟩ := pick 2
  obtain ⟨r3, h3⟩ := pick 3
  obtain ⟨τ0, e0, m0, q0, o0, s0, sh0, c0⟩ := gM_spec cap 0 a' (sz 0) r0 σ h0 (hsh 0) (by rw [hq]; rfl) hf hc hp ht
    (by rw [hM0]; have := hcap 0; omega) (by rw [hq]; exact hqc)
  obtain ⟨τ1, e1, m1, q1, o1, s1, sh1, c1⟩ := gM_spec cap 1 a' (sz 1) r1 τ0 (by rw [s0]; exact h1)
    (by rw [sh0 _ (hne 1 0 (by decide))]; exact hsh 1) (by rw [q0]; rfl)
    (by rw [o0 _ (by decide) (by decide)]; exact hf) (by rw [o0 _ (by decide) (by decide)]; exact hc)
    (by rw [o0 _ (by decide) (by decide)]; exact hp) (by rw [o0 _ (by decide) (by decide)]; exact ht)
    (by rw [m0, hM0]; have := hcap 1; omega)
    (by rw [q0]; omega)
  obtain ⟨τ2, e2, m2, q2, o2, s2, sh2, c2⟩ := gM_spec cap 2 a' (sz 2) r2 τ1 (by rw [s1, s0]; exact h2)
    (by rw [sh1 _ (hne 2 1 (by decide)), sh0 _ (hne 2 0 (by decide))]; exact hsh 2) (by rw [q1]; rfl)
    (by rw [o1 _ (by decide) (by decide), o0 _ (by decide) (by decide)]; exact hf)
    (by rw [o1 _ (by decide) (by decide), o0 _ (by decide) (by decide)]; exact hc)
    (by rw [o1 _ (by decide) (by decide), o0 _ (by decide) (by decide)]; exact hp)
    (by rw [o1 _ (by decide) (by decide), o0 _ (by decide) (by decide)]; exact ht)
    (by rw [m1, m0, hM0]; have := hcap 2; omega)
    (by rw [q1]; omega)
  obtain ⟨τ3, e3, m3, q3, o3, s3, sh3, c3⟩ := gM_spec cap 3 a' (sz 3) r3 τ2 (by rw [s2, s1, s0]; exact h3)
    (by rw [sh2 _ (hne 3 2 (by decide)), sh1 _ (hne 3 1 (by decide)), sh0 _ (hne 3 0 (by decide))]; exact hsh 3)
    (by rw [q2]; rfl)
    (by rw [o2 _ (by decide) (by decide), o1 _ (by decide) (by decide), o0 _ (by decide) (by decide)]; exact hf)
    (by rw [o2 _ (by decide) (by decide), o1 _ (by decide) (by decide), o0 _ (by decide) (by decide)]; exact hc)
    (by rw [o2 _ (by decide) (by decide), o1 _ (by decide) (by decide), o0 _ (by decide) (by decide)]; exact hp)
    (by rw [o2 _ (by decide) (by decide), o1 _ (by decide) (by decide), o0 _ (by decide) (by decide)]; exact ht)
    (by rw [m2, m1, m0, hM0]; have := hcap 3; omega)
    (by rw [q2]; omega)
  refine ⟨τ3, WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3)), ?_, ?_, fun r h1 h2 => ?_, ?_, fun j hj => ?_, ?_⟩
  · rw [m3, m2, m1, m0, hM0, hMv]; omega
  · rw [q3]; rfl
  · rw [o3 r h1 h2, o2 r h1 h2, o1 r h1 h2, o0 r h1 h2]
  · rw [s3, s2, s1, s0]
  · rw [sh3 j (hj 3), sh2 j (hj 2), sh1 j (hj 1), sh0 j (hj 0)]
  · rw [c3, c2, c1, c0]

theorem p1_spec2 (σ : WL) (n a' M ncar capT : ℕ) (pl : Fin 4 → List Bool) (sz : Fin 4 → ℕ) (rest : List Bool)
    (ha : a' ≤ 4) (hpl : ∀ j : Fin 4, j.val < a' → ∃ y, pl j = frame y)
    (hpl0 : ∀ j : Fin 4, a' ≤ j.val → pl j = [])
    (hszw : ∀ j : Fin 4, j.val < a' → ∃ r, pl j = frameP (natWord (sz j)) ++ r)
    (hM : M = (if (0 : Fin 4).val < a' then sz 0 else 0) + (if (1 : Fin 4).val < a' then sz 1 else 0) +
      (if (2 : Fin 4).val < a' then sz 2 else 0) + (if (3 : Fin 4).val < a' then sz 3 else 0))
    (hreq : σ.st sReq = frameP (natWord n) ++ ([true, true] ++ (frameP (natWord a') ++ rest)))
    (hpay : ∀ j, σ.st (sPay j) = pl j) (hnc : σ.st sNc = List.replicate ncar true)
    (hcapT : σ.st sCap = List.replicate capT true) (hblkC : ∀ k, σ.st (sBC k) = [])
    (hblkE : ∀ k, σ.st (sBE k) = []) (hsh : ∀ s, σ.sh s = 0) (hv : ∀ r, σ.val r = 0)
    (c1 : 2 ^ (natBitLength n + 1) ≤ cap) (c2 : 2 ^ (natBitLength a' + 1) ≤ cap)
    (c3 : 2 * (pl 0 ++ pl 1 ++ pl 2 ++ pl 3).length + 4 ≤ cap) (c4 : 4 ≤ cap) (c5 : fnw.length ≤ cap)
    (c6 : ∀ j, 2 ^ (natBitLength (sz j) + 1) + M ≤ cap) (c7 : ncar ≤ cap) (c8 : capT ≤ cap) :
    ∃ τ m, WExec cap p1W σ τ m ∧ m ≤ 30 * (opU cap + 1) ∧ P1Post σ τ (pl 0 ++ pl 1 ++ pl 2 ++ pl 3) n a' M ncar capT := by
  have hpayR : ∀ j, sPay j ≠ sReq := fun j h => by
    have := congrArg Fin.val h; simp only [sPay, sReq] at this; omega
  have hcne : ∀ k k', sBC k ≠ sBE k' := fun k k' h => by
    have := congrArg Fin.val h; simp only [sBC, sBE] at this; omega
  have hC0C2 : sBC 0 ≠ sBC 2 := by decide
  have hE0E2 : sBE 0 ≠ sBE 2 := by decide
  have hRblk : ∀ k, sReq ≠ sBC k ∧ sReq ≠ sBE k := fun k => by
    constructor <;> intro h <;> have := congrArg Fin.val h <;> simp only [sReq, sBC, sBE] at this <;> omega
  -- `n`, `a'`
  obtain ⟨σA, eA, hσA⟩ := readReq_spec cap σ n a' rest hreq (hsh _) (hv _) (hv _) (hv _) (hv _) (hv _) (hv _) c1 c2
  have vA : ∀ r, σA.val r = if r = rA then a' else if r = rN then n else σ.val r := fun r => by
    rw [hσA]
    simp only [WState.setv_val, WState.seth_val]
    by_cases h1 : r = rA
    · subst h1; rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne h1, if_neg h1]
      by_cases h2 : r = rN
      · subst h2; rw [Function.update_self, if_pos rfl]
      · rw [Function.update_of_ne h2, if_neg h2]
  -- `qa := a'`, block C's top word
  have eB := wcopyR_spec cap rA qa qt (by decide) (by decide) (by decide) σA (by rw [vA]; simp [hv])
    (by rw [vA]; simp [hv]) (by rw [vA]; simp; omega)
  obtain ⟨τC, eC, hτC⟩ := twW_spec cap (sBC 0) (fun j => (sPay_ne_blk j 0).1) qOP qSP qa (by decide) (by decide)
    (by decide) a' ha pl hpl hpl0 (σA.setv qa (σA.val rA)) (fun j => by rw [hσA]; simp [hpay])
    (fun j => by rw [hσA]; simp [Function.update_of_ne (hpayR j), hsh])
    (by simp [Function.update_of_ne (show qSP ≠ qa by decide), vA, hv])
    (by simp [vA])
    (by rw [hσA]; simp [hblkC]) (by rw [hσA]; simp [Function.update_of_ne (hRblk 0).1.symm, hsh])
    (by simp [Function.update_of_ne (show qOP ≠ qa by decide), vA, hv]) c3 c4
  -- `qa := a'`, block E's top word
  have eD := wcopyR_spec cap rA qa qt (by decide) (by decide) (by decide) τC (by rw [hτC]; simp)
    (by rw [hτC]; simp [Function.update_of_ne (show qt ≠ qa by decide), vA, hv])
    (by rw [hτC]; simp [Function.update_of_ne (show rA ≠ qa by decide), vA]; omega)
  obtain ⟨τE, eE, hτE⟩ := twW_spec cap (sBE 0) (fun j => (sPay_ne_blk j 0).2) qOP qSP qa (by decide) (by decide)
    (by decide) a' ha pl hpl hpl0 (τC.setv qa (τC.val rA))
    (fun j => by rw [hτC, hσA]; simp [Function.update_of_ne (sPay_ne_blk j 0).1, hpay])
    (fun j => by rw [hτC, hσA]; simp [Function.update_of_ne (hpayR j), hsh])
    (by rw [hτC]; simp [Function.update_of_ne (show qSP ≠ qa by decide), vA, hv])
    (by rw [hτC]; simp [Function.update_of_ne (show rA ≠ qa by decide), vA])
    (by rw [hτC, hσA]; simp [Function.update_of_ne (hcne 0 0).symm, hblkE])
    (by rw [hτC, hσA]; simp [Function.update_of_ne (hRblk 0).2.symm, hsh])
    (by rw [hτC]; simp [Function.update_of_ne (show qOP ≠ qa by decide), vA, hv]) c3 c4
  -- the native words
  have eF := nwW_spec cap (sBC 2) fnw τE (by rw [hτE, hτC, hσA]; simp [Function.update_of_ne (hcne 2 0),
      Function.update_of_ne hC0C2.symm, hblkC])
    (by rw [hτE, hτC, hσA]; simp [Function.update_of_ne (hRblk 2).1.symm, hsh])
    (by rw [hτE, hτC]; simp [Function.update_of_ne (show qOP ≠ qa by decide), vA, hv]) c5
  have eG := nwW_spec cap (sBE 2) fnw (τE.sets (sBC 2) fnw) (by rw [hτE, hτC, hσA]; simp [Function.update_of_ne
      (hcne 2 2).symm, Function.update_of_ne hE0E2.symm, Function.update_of_ne (hcne 0 2).symm, hblkE])
    (by rw [hτE, hτC, hσA]; simp [Function.update_of_ne (hRblk 2).2.symm, hsh])
    (by rw [hτE, hτC]; simp [Function.update_of_ne (show qOP ≠ qa by decide), vA, hv]) c5
  obtain ⟨σG, hσG⟩ : ∃ y, y = (τE.sets (sBC 2) fnw).sets (sBE 2) fnw := ⟨_, rfl⟩
  rw [← hσG] at eG
  -- the facts after the words
  have stG : ∀ s, σG.st s = if s = sBC 0 then frame (pl 0 ++ pl 1 ++ pl 2 ++ pl 3) else
      if s = sBE 0 then frame (pl 0 ++ pl 1 ++ pl 2 ++ pl 3) else if s = sBC 2 then fnw else
      if s = sBE 2 then fnw else σ.st s := fun s => by
    rw [hσG, hτE, hτC, hσA]
    by_cases h1 : s = sBE 2
    · subst h1; simp [(hcne 0 2).symm, (hcne 2 2).symm, hE0E2.symm]
    · by_cases h2 : s = sBC 2
      · subst h2; simp [Function.update_of_ne h1, hC0C2.symm, hcne 2 0]
      · by_cases h3 : s = sBE 0
        · subst h3; simp [Function.update_of_ne h1, Function.update_of_ne h2, (hcne 0 0).symm]
        · by_cases h4 : s = sBC 0
          · subst h4; simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
          · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
              Function.update_of_ne h4, h1, h2, h3, h4]
  have shG : ∀ s, σG.sh s = if s = sReq then 2 * (natWord n).length + 2 + 2 * (natWord a').length else σ.sh s :=
    fun s => by
      rw [hσG, hτE, hτC, hσA]
      by_cases h : s = sReq
      · subst h; simp
      · simp [Function.update_of_ne h, h]
  have vG : ∀ r, σG.val r = if r = qa then 0 else if r = rA then a' else if r = rN then n else σ.val r :=
    fun r => by
      rw [hσG, hτE, hτC]
      simp only [WState.sets_val, WState.setv_val]
      by_cases h : r = qa
      · subst h; rw [Function.update_self, if_pos rfl]
      · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h,
          if_neg h, vA]
  have cG : σG.cell = σ.cell := by rw [hσG, hτE, hτC, hσA]; simp
  -- `qa := a'`, `M`
  have eH := wcopyR_spec cap rA qa qt (by decide) (by decide) (by decide) σG (by rw [vG]; simp)
    (by rw [vG]; simp [hv]) (by rw [vG]; simp; omega)
  obtain ⟨τM, eM, rMv, qMv, oM, sM, shM, cM⟩ := readM2_spec cap (σG.setv qa (σG.val rA)) a' sz M
    (fun j hj => by
      obtain ⟨r, hr⟩ := hszw j hj
      refine ⟨r, ?_⟩
      simp only [WState.setv_st]
      rw [stG, if_neg (sPay_ne_blk j 0).1, if_neg (sPay_ne_blk j 0).2, if_neg (sPay_ne_blk j 2).1,
        if_neg (sPay_ne_blk j 2).2, hpay, hr])
    (fun j => by simp only [WState.setv_sh]; rw [shG, if_neg (hpayR j), hsh])
    (by simp [vG]) (by simp [Function.update_of_ne (show qf ≠ qa by decide), vG, hv])
    (by simp [Function.update_of_ne (show qc ≠ qa by decide), vG, hv])
    (by simp [Function.update_of_ne (show qp ≠ qa by decide), vG, hv])
    (by simp [Function.update_of_ne (show qt ≠ qa by decide), vG, hv])
    (by simp [Function.update_of_ne (show rM ≠ qa by decide), vG, hv]) hM c6 (by omega)
  -- `ncar`, `cap_T`
  have hNcP : ∀ i, sNc ≠ sPay i := fun i h => by
    have := congrArg Fin.val h; simp only [sNc, sPay] at this; omega
  have hCapP : ∀ i, sCap ≠ sPay i := fun i h => by
    have := congrArg Fin.val h; simp only [sCap, sPay] at this; omega
  have eN := SymDec.readU_spec cap sNc rNc ncar 0 τM
    (by rw [sM]; simp only [WState.setv_st]; rw [stG, if_neg (by decide), if_neg (by decide), if_neg (by decide),
          if_neg (by decide)]; exact hnc)
    (by rw [shM _ hNcP]; simp only [WState.setv_sh]; rw [shG]; simp [sNc, sReq, hsh])
    (by rw [oM _ (by decide) (by decide)]; simp [Function.update_of_ne (show rNc ≠ qa by decide), vG, hv])
    (by omega)
  have eO := SymDec.readU_spec cap sCap rCap capT 0 ((τM.seth sNc ncar).setv rNc (0 + ncar))
    (by simp only [WState.setv_st, WState.seth_st]; rw [sM]; simp only [WState.setv_st]
        rw [stG, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]; exact hcapT)
    (by simp only [WState.setv_sh, WState.seth_sh]
        rw [Function.update_of_ne (show sCap ≠ sNc by decide), shM _ hCapP]
        simp only [WState.setv_sh]; rw [shG]; simp [sCap, sReq, hsh])
    (by simp only [WState.setv_val, WState.seth_val]
        rw [Function.update_of_ne (show rCap ≠ rNc by decide), oM _ (by decide) (by decide)]
        simp [Function.update_of_ne (show rCap ≠ qa by decide), vG, hv])
    (by omega)
  refine ⟨_, _, WExec.seq eA (WExec.seq eB (WExec.seq eC (WExec.seq eD (WExec.seq eE (WExec.seq eF (WExec.seq eG
    (WExec.seq eH (WExec.seq eM (WExec.seq eN eO))))))))), ?_, ⟨?_, ?_, ?_, ?_, fun s h1 h2 h3 h4 => ?_,
    fun s h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ?_⟩⟩
  · have hU := lin_le_opU cap
    have rb : ∀ x : ℕ, 2 ^ (natBitLength x + 1) ≤ cap →
        (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ opU cap := fun x hx => by
      have h1 : natBitLength x < 2 ^ natBitLength x := Nat.lt_two_pow_self
      have h2 : 2 ^ (natBitLength x + 1) = 2 * 2 ^ natBitLength x := by rw [pow_succ]; ring
      have h3 : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤
          (natBitLength x + 2) * (90 * natBitLength x + 90 * 2 ^ natBitLength x + 60) :=
        Nat.mul_le_mul_left _ (by omega)
      exact h3.trans (quad_le_opU cap _ _ (by omega) (by omega))
    have rN' := rb n c1
    have rA' := rb a' c2
    have r0 := rb (sz 0) (by have := c6 0; omega)
    have r1 := rb (sz 1) (by have := c6 1; omega)
    have r2 := rb (sz 2) (by have := c6 2; omega)
    have r3 := rb (sz 3) (by have := c6 3; omega)
    have hfl : fnw.length = 25 := by
      show (frame PrimThrW.W6Meta.nw0).length = 25
      rw [frame_length, PrimThrW.W6Meta.nw0_len]
    have sA : σA.val rA = a' := by rw [vA]; simp
    have tC : τC.val rA = a' := by rw [hτC]; simp [Function.update_of_ne (show rA ≠ qa by decide), vA]
    have uG : σG.val rA = a' := by rw [vG]; simp
    simp only [readMCost, hfl]
    omega
  · simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh]
    rw [sM, Function.update_of_ne (show sBC 0 ≠ sCap by decide), Function.update_of_ne (show sBC 0 ≠ sNc by decide),
      shM _ (fun i => (sPay_ne_blk i 0).1.symm)]
    simp only [WState.setv_st, WState.setv_sh]
    rw [stG, shG, if_pos rfl, if_neg (hRblk 0).1.symm, hsh]
    exact ⟨rfl, rfl⟩
  · simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh]
    rw [sM, Function.update_of_ne (show sBE 0 ≠ sCap by decide), Function.update_of_ne (show sBE 0 ≠ sNc by decide),
      shM _ (fun i => (sPay_ne_blk i 0).2.symm)]
    simp only [WState.setv_st, WState.setv_sh]
    rw [stG, shG, if_neg (hcne 0 0).symm, if_pos rfl, if_neg (hRblk 0).2.symm, hsh]
    exact ⟨rfl, rfl⟩
  · simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh]
    rw [sM, Function.update_of_ne (show sBC 2 ≠ sCap by decide), Function.update_of_ne (show sBC 2 ≠ sNc by decide),
      shM _ (fun i => (sPay_ne_blk i 2).1.symm)]
    simp only [WState.setv_st, WState.setv_sh]
    rw [stG, shG, if_neg hC0C2.symm, if_neg (hcne 2 0), if_pos rfl, if_neg (hRblk 2).1.symm, hsh]
    exact ⟨rfl, rfl⟩
  · simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh]
    rw [sM, Function.update_of_ne (show sBE 2 ≠ sCap by decide), Function.update_of_ne (show sBE 2 ≠ sNc by decide),
      shM _ (fun i => (sPay_ne_blk i 2).2.symm)]
    simp only [WState.setv_st, WState.setv_sh]
    rw [stG, shG, if_neg (hcne 0 2).symm, if_neg hE0E2.symm, if_neg (hcne 2 2).symm, if_pos rfl,
      if_neg (hRblk 2).2.symm, hsh]
    exact ⟨rfl, rfl⟩
  · simp only [WState.setv_st, WState.seth_st]
    rw [sM]; simp only [WState.setv_st]
    rw [stG, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  · simp only [WState.setv_sh, WState.seth_sh]
    rw [Function.update_of_ne h3, Function.update_of_ne h2, shM _ h4]
    simp only [WState.setv_sh]
    rw [shG, if_neg h1]
  · simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne (show rN ≠ rCap by decide), Function.update_of_ne (show rN ≠ rNc by decide),
      oM _ (by decide) (by decide)]
    simp [Function.update_of_ne (show rN ≠ qa by decide), vG]
  · simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne (show rA ≠ rCap by decide), Function.update_of_ne (show rA ≠ rNc by decide),
      oM _ (by decide) (by decide)]
    simp [Function.update_of_ne (show rA ≠ qa by decide), vG]
  · simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne (show rM ≠ rCap by decide), Function.update_of_ne (show rM ≠ rNc by decide), rMv]
  · simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne (show rNc ≠ rCap by decide), Function.update_self, Nat.zero_add]
  · simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_self, Nat.zero_add]
  · simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne h5, Function.update_of_ne h4]
    by_cases hq : r = qa
    · subst hq
      rw [qMv, hv]; omega
    · rw [oM _ h3 hq]
      simp only [WState.setv_val]
      rw [Function.update_of_ne hq, vG, if_neg hq, if_neg h2, if_neg h1]
  · simp only [WState.setv_cell, WState.seth_cell]
    rw [cM]; simp [cG]

/-! ## Proof 1's program docks with their counts -/

theorem metaC_blk2 (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) :
    ∃ (H : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool) (k : ℕ),
      Step (MaskedReset.machine (PacketsMeta.Prog.prog PacketsMeta.Tail.selTailM) (fun _ => true)) (2 * PrimThrW.W6Meta.progCost (twOf (dsOf a r)) (dsOf a r) (PrimThrW.W6Meta.costC (PrimThrW.W6Meta.metaW (twOf (dsOf a r))) (Cv (dsOf a r))) + 2)
        (Fin.addCases (fun _ : Fin (3 + 57) => (0 : ℕ)) (fun _ : Fin 1 => 0))
        (Fin.addCases (PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame (twOf (dsOf a r)))
          (RepairOrdinary.frame PrimThrW.W6Meta.nw0)) (fun _ : Fin 1 => List.replicate 0 false))
        (Fin.addCases (fun i => if (fun _ : Fin (3 + 57) => true) i = true then 0 else H i) (fun _ : Fin 1 => 0))
        (Fin.addCases A1 (fun _ : Fin 1 => List.replicate k false)) ∧
      A1 ⟨1, by omega⟩ = List.replicate (Cv (dsOf a r)) true :=
  (PrimThrW.W6Meta.metaC a r four).elim fun H1 h => h.elim fun A1 h' =>
    (ListMachine.Row.maskBlank h'.1 (fun _ => true) (fun _ _ => rfl) 0).elim fun k hm => ⟨_, _, k, hm, h'.2⟩

theorem progC_dock2 (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (σ : WL) : σ.st (sBC 0) = RepairOrdinary.frame (twOf (dsOf a r)) →
    σ.st (sBC 2) = RepairOrdinary.frame PrimThrW.W6Meta.nw0 →
    (∀ k : Fin 61, k.val ≠ 0 → k.val ≠ 2 → σ.st (sBC k) = []) → (∀ k, σ.sh (sBC k) = 0) →
    ∃ τ, Step (RecoveryFocus.machine (fun j => sTape (nr := 80) (bC j))
        (MaskedReset.machine (PacketsMeta.Prog.prog PacketsMeta.Tail.selTailM) (fun _ => true))) (2 * PrimThrW.W6Meta.progCost (twOf (dsOf a r)) (dsOf a r) (PrimThrW.W6Meta.costC (PrimThrW.W6Meta.metaW (twOf (dsOf a r))) (Cv (dsOf a r))) + 2) (wenc cap σ).H (wenc cap σ).A
        (wenc cap τ).H (wenc cap τ).A ∧ τ.st (sBC 1) = List.replicate (Cv (dsOf a r)) true ∧
      (∀ k, τ.sh (sBC k) = 0) ∧ (∀ s, (∀ k, s ≠ sBC k) → τ.st s = σ.st s ∧ τ.sh s = σ.sh s) ∧
      τ.val = σ.val ∧ τ.cell = σ.cell :=
  fun h0 h2 hb hsh => (metaC_blk2 a r four).elim fun H h => h.elim fun A1 h => h.elim fun k h =>
    ⟨_, dockS cap bC bC_inj σ ((h.1.congr_in (eHin σ bC (fun j => hsh _))
        (blk_in _ _ (fun k => σ.st (sBC k)) h0 h2 hb)).congr (eHout H) rfl),
      (blk_post σ bC bC_inj A1 k ⟨1, by omega⟩).1.trans h.2,
      fun k' => (blk_post σ bC bC_inj A1 k ⟨0, by omega⟩).2.1 ⟨k'.val, by omega⟩,
      fun s hs => (blk_post σ bC bC_inj A1 k ⟨0, by omega⟩).2.2.1 s
        (fun j hj => hs ⟨j.val, by omega⟩ (by rw [← hj]; rfl)),
      (blk_post σ bC bC_inj A1 k ⟨0, by omega⟩).2.2.2.1, (blk_post σ bC bC_inj A1 k ⟨0, by omega⟩).2.2.2.2⟩

theorem metaE_blk2 (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) :
    ∃ (H : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool) (k : ℕ),
      Step (MaskedReset.machine (PacketsMeta.Prog.prog PrimThrW.W6Meta.tailE) (fun _ => true)) (2 * PrimThrW.W6Meta.progCost (twOf (dsOf a r)) (dsOf a r) (PrimThrW.W6Meta.costE (PrimThrW.W6Meta.metaW (twOf (dsOf a r))) (Fv (dsOf a r))) + 2)
        (Fin.addCases (fun _ : Fin (3 + 57) => (0 : ℕ)) (fun _ : Fin 1 => 0))
        (Fin.addCases (PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame (twOf (dsOf a r)))
          (RepairOrdinary.frame PrimThrW.W6Meta.nw0)) (fun _ : Fin 1 => List.replicate 0 false))
        (Fin.addCases (fun i => if (fun _ : Fin (3 + 57) => true) i = true then 0 else H i) (fun _ : Fin 1 => 0))
        (Fin.addCases A1 (fun _ : Fin 1 => List.replicate k false)) ∧
      A1 ⟨1, by omega⟩ = List.replicate (Nat.clog 2 (Fv (dsOf a r) + 1)) true :=
  (PrimThrW.W6Meta.metaE a r four).elim fun H1 h => h.elim fun A1 h' =>
    (ListMachine.Row.maskBlank h'.1 (fun _ => true) (fun _ _ => rfl) 0).elim fun k hm => ⟨_, _, k, hm, h'.2⟩

theorem progE_dock2 (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (σ : WL) : σ.st (sBE 0) = RepairOrdinary.frame (twOf (dsOf a r)) →
    σ.st (sBE 2) = RepairOrdinary.frame PrimThrW.W6Meta.nw0 →
    (∀ k : Fin 61, k.val ≠ 0 → k.val ≠ 2 → σ.st (sBE k) = []) → (∀ k, σ.sh (sBE k) = 0) →
    ∃ τ, Step (RecoveryFocus.machine (fun j => sTape (nr := 80) (bE j))
        (MaskedReset.machine (PacketsMeta.Prog.prog PrimThrW.W6Meta.tailE) (fun _ => true))) (2 * PrimThrW.W6Meta.progCost (twOf (dsOf a r)) (dsOf a r) (PrimThrW.W6Meta.costE (PrimThrW.W6Meta.metaW (twOf (dsOf a r))) (Fv (dsOf a r))) + 2) (wenc cap σ).H (wenc cap σ).A
        (wenc cap τ).H (wenc cap τ).A ∧ τ.st (sBE 1) = List.replicate (Nat.clog 2 (Fv (dsOf a r) + 1)) true ∧
      (∀ k, τ.sh (sBE k) = 0) ∧ (∀ s, (∀ k, s ≠ sBE k) → τ.st s = σ.st s ∧ τ.sh s = σ.sh s) ∧
      τ.val = σ.val ∧ τ.cell = σ.cell :=
  fun h0 h2 hb hsh => (metaE_blk2 a r four).elim fun H h => h.elim fun A1 h => h.elim fun k h =>
    ⟨_, dockS cap bE bE_inj σ ((h.1.congr_in (eHin σ bE (fun j => hsh _))
        (blk_in _ _ (fun k => σ.st (sBE k)) h0 h2 hb)).congr (eHout H) rfl),
      (blk_post σ bE bE_inj A1 k ⟨1, by omega⟩).1.trans h.2,
      fun k' => (blk_post σ bE bE_inj A1 k ⟨0, by omega⟩).2.1 ⟨k'.val, by omega⟩,
      fun s hs => (blk_post σ bE bE_inj A1 k ⟨0, by omega⟩).2.2.1 s
        (fun j hj => hs ⟨j.val, by omega⟩ (by rw [← hj]; rfl)),
      (blk_post σ bE bE_inj A1 k ⟨0, by omega⟩).2.2.2.1, (blk_post σ bE bE_inj A1 k ⟨0, by omega⟩).2.2.2.2⟩

end NearCubicWires.WireExponent3_5.PrimT.W6
