import Lean
import Proof.Wire_3_5.UnionMachine.FrontSemPathCapsBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Recovery.RecoverySetupTwo
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCallCount
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.FrontCaps
import Proof.Wire_3_5.UnionMachine.FrontSemCap1
import Proof.Wire_3_5.UnionMachine.FrontSemSUE
import Proof.Wire_3_5.UnionMachine.FrontSemSize
import Proof.Wire_3_5.UnionMachine.FrontSemTW
import Proof.Wire_3_5.UnionMachine.PlanW2
import Proof.Wire_3_5.UnionMachine.PlanW3
import Proof.Wire_3_5.UnionMachine.UnionSetup
import Proof.Wire_3_5.UnionMachine.FrontSemEnvSBase


noncomputable section
set_option maxRecDepth 120000


/-! # C6 front, the semantic core (19): the master size bound at the pinned setup (P3:3485-3491, 3669-3691)

At the pinned setup `SUE` a single polynomial **`MS c₀ q`** of the width dominates every size of every guess the
front reads past the onset (**`MS_pq`**): the PCPP output (`Kp`, the size law), the mass and the grid (`Λ̄ ≤ K_Λ(q+2)³`,
`s = C_δ Λ̄²`), the atoms' codes at the description envelope (`Kc`), the atoms' codes words, the carriers' codes
(the fold's writers, `Wc_le`), the translation (`r` codes below `2^s ≤ q+1`), the constant, the description bits,
`c_r`, and a free constant `c₀`. **`genv_of`**: every guess within the size cap that passes the atom test has the
size envelope `GEnv g Λ̄(q) (MS c₀ q)`.

Paper quantity of the main types: the guess's sizes against the width `q`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnvS
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU PQ)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (nvG)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (codesWord)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound (lc)

section SUE
variable (l : Literals) (F : GateFree l) (e coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

/-- The size cap lies below `(w+1)^{capExp l}`. -/
theorem sue_cap : ∀ o w, o ≤ RecoveryScheduleEnvelope.oracleSizeBound (SUE l F e coef A L hL).G w →
    o + 1 ≤ (w + 1) ^ capExp l := fun o w ho => by
  rw [FrontSemSUE.sue_G] at ho
  exact oracleSize_le l w o ho

/-- The size constant of `H_Γ` at the pinned setup (Lemma H.7(b), `UnionCallCount.hsize_pair`). -/
noncomputable def KsS : ℕ :=
  Classical.choose (UnionCallCount.hsize_pair (SUE l F e coef A L hL) (capExp l) (sue_cap l F e coef A L hL))

/-- The size exponent of `H_Γ` at the pinned setup. -/
noncomputable def σS : ℕ := UnionCallCount.eHS (SUE l F e coef A L hL) (capExp l)

theorem KsS_spec : ∀ N (z : BitInput N) (Γ : NearCubicGates.Close.Outer.OuterGuess ((SUE l F e coef A L hL).width N)),
    N = 2 ^ Nat.log 2 N → (SUE l F e coef A L hL).onset ≤ Nat.log 2 N →
    Γ.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (SUE l F e coef A L hL).G ((SUE l F e coef A L hL).width N) →
    ((SUE l F e coef A L hL).request z Γ).circuit.size + 1 ≤
      KsS l F e coef A L hL * ((SUE l F e coef A L hL).width N + 1) ^ σS l F e coef A L hL :=
  Classical.choose_spec (UnionCallCount.hsize_pair (SUE l F e coef A L hL) (capExp l) (sue_cap l F e coef A L hL))

/-- The mass bound's coefficient. -/
noncomputable def KL : ℕ := Classical.choose (rowBLambda_pow16_le (gateZeta_pos l) (gateZeta_lt l) 2)

/-- The mass bound. -/
noncomputable def LamB (q : ℕ) : ℕ := KL l * (q + 2) ^ 3

/-- The grid bound. -/
noncomputable def SpB (q : ℕ) : ℕ := gateCδ1 l * LamB l q ^ 2

theorem lam_le (q : ℕ) : rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q ≤ LamB l q := by
  have h := Classical.choose_spec (rowBLambda_pow16_le (gateZeta_pos l) (gateZeta_lt l) 2) q
  have h1 : rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q ≤ rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q ^ 16 := by
    rcases Nat.eq_zero_or_pos (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q) with h0 | h0
    · rw [h0]; simp
    · exact Nat.le_self_pow (by norm_num) _
  have h2 : Lq q ^ 3 ≤ (q + 2) ^ 3 := Nat.pow_le_pow_left (by have := Lq_le q; omega) 3
  unfold LamB KL
  calc _ ≤ _ := h1
    _ ≤ _ := h
    _ ≤ _ := Nat.mul_le_mul_left _ h2

theorem sp_le (q : ℕ) : rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) q ≤ SpB l q := by
  unfold rowBSparse SpB
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lam_le l q) 2)

/-- The description envelope's exponent (atoms, parities, constant). -/
noncomputable def DD : ℕ := (IUE l F e coef A).descDeg + 4

/-- The atom code bound. -/
noncomputable def KcD (q : ℕ) : ℕ := FrontSemSize.Kc (DD l F e coef A) q

/-- The fold's size parameter: the width and the atoms' codes words. -/
noncomputable def s0 (q : ℕ) : ℕ := q + SpB l q * KcD l F e coef A q

/-- The PCPP output's size bound at the pinned setup. -/
noncomputable def KpS (q : ℕ) : ℕ :=
  FrontSemSize.Kp (SUE l F e coef A L hL) (KsS l F e coef A L hL) (σS l F e coef A L hL) q

/-- **The master size bound.** -/
noncomputable def MS (c0 q : ℕ) : ℕ :=
  q + 3 + 4 * KpS l F e coef A L hL q + LamB l q + SpB l q + SpB l q * KcD l F e coef A q +
    (s0 l F e coef A q + 2) ^ Lc + (2 * q + 3 + q * (2 * q + 5)) + CC + (q + 1) ^ DD l F e coef A + F.cr +
    KcD l F e coef A q + c0

theorem LamB_pq : PQ (LamB l) := by
  unfold LamB
  exact PQ.mul (PQ.const _) (PQ.pow (PQ.add PQ.var (PQ.const 2)) 3)

theorem SpB_pq : PQ (SpB l) := by
  unfold SpB
  exact PQ.mul (PQ.const _) (PQ.pow (LamB_pq l) 2)

theorem MS_pq (c0 : ℕ) : PQ (MS l F e coef A L hL c0) := by
  unfold MS
  have hK : PQ (KcD l F e coef A) := FrontSemSize.Kc_pq _
  have hs0 : PQ (s0 l F e coef A) := by
    unfold s0; exact PQ.add PQ.var (PQ.mul (SpB_pq l) hK)
  have hTr : PQ (fun q => 2 * q + 3 + q * (2 * q + 5)) :=
    PQ.add (PQ.add (PQ.mul (PQ.const 2) PQ.var) (PQ.const 3)) (PQ.mul PQ.var (PQ.add (PQ.mul (PQ.const 2) PQ.var)
      (PQ.const 5)))
  have a1 := PQ.add PQ.var (PQ.const 3)
  have a2 := PQ.add a1 (PQ.mul (PQ.const 4) (FrontSemSize.Kp_pq (S := SUE l F e coef A L hL)
    (Ks := KsS l F e coef A L hL) (σ := σS l F e coef A L hL)))
  have a3 := PQ.add a2 (LamB_pq l)
  have a4 := PQ.add a3 (SpB_pq l)
  have a5 := PQ.add a4 (PQ.mul (SpB_pq l) hK)
  have a6 := PQ.add a5 (PQ.pow (PQ.add hs0 (PQ.const 2)) (Lc))
  have a7 := PQ.add a6 hTr
  have a8 := PQ.add a7 (PQ.const CC)
  have a9 := PQ.add a8 (PQ.pow (PQ.add PQ.var (PQ.const 1)) (DD l F e coef A))
  have a10 := PQ.add a9 (PQ.const F.cr)
  have a11 := PQ.add a10 hK
  exact PQ.add a11 (PQ.const c0)

theorem MS_ge (c0 q : ℕ) :
    q + 3 ≤ MS l F e coef A L hL c0 q ∧ 4 * KpS l F e coef A L hL q ≤ MS l F e coef A L hL c0 q ∧
    LamB l q ≤ MS l F e coef A L hL c0 q ∧ SpB l q ≤ MS l F e coef A L hL c0 q ∧
    SpB l q * KcD l F e coef A q ≤ MS l F e coef A L hL c0 q ∧
    (s0 l F e coef A q + 2) ^ Lc ≤ MS l F e coef A L hL c0 q ∧
    2 * q + 3 + q * (2 * q + 5) ≤ MS l F e coef A L hL c0 q ∧ CC ≤ MS l F e coef A L hL c0 q ∧
    (q + 1) ^ DD l F e coef A ≤ MS l F e coef A L hL c0 q ∧ F.cr ≤ MS l F e coef A L hL c0 q ∧
    KcD l F e coef A q ≤ MS l F e coef A L hL c0 q ∧ c0 ≤ MS l F e coef A L hL c0 q := by
  unfold MS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **Every guess passing the outer step's guards and the atom test has the size envelope** `GEnv g Λ̄(q) (MS c₀ q)`. -/
theorem genv_of (c0 : ℕ) {N : ℕ} (x : BitInput N) (g : UnionGuess (SUE l F e coef A L hL) x)
    (hG : UnionGuards (SUE l F e coef A L hL) x g)
    (hat : PlanW3.AtomsOkG g) (hstar : (IUE l F e coef A).StarAt g.q) :
    FrontSemCap1.GEnv g (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 g.q) (MS l F e coef A L hL c0 g.q) := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12⟩ := MS_ge l F e coef A L hL c0 g.q
  have harity : g.q = (SUE l F e coef A L hL).width N := q_eq_width _ g hG.2.1 hG.2.2.1
  have hr := KsS_spec l F e coef A L hL N x g.pair hG.2.1 hG.2.2.1 hG.2.2.2.2.1
  have hnv := FrontSemSize.nv_le x g.pair _ hr
  have hcb := FrontSemSize.cb_le x g.pair _ hr
  have eK : KpS l F e coef A L hL g.q = FrontSemSize.Kp (SUE l F e coef A L hL) (KsS l F e coef A L hL)
      (σS l F e coef A L hL) ((SUE l F e coef A L hL).width N) := by
    unfold KpS; rw [harity]
  have hpA := FrontSemSUE.sue_parity l F e coef A L hL
  have hcA := FrontSemSUE.sue_const l F e coef A L hL
  have hDD : ∀ k, k ≤ DD l F e coef A → (g.q + 1) ^ k ≤ (g.q + 1) ^ DD l F e coef A :=
    fun k hk => Nat.pow_le_pow_right (by omega) hk
  have hdA : ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ (g.q + 1) ^ DD l F e coef A :=
    fun X a => (hat X a).trans (hDD _ (by unfold DD; omega))
  have hdP : ∀ X, g.mode.descriptionBits (g.parity X) ≤ (g.q + 1) ^ DD l F e coef A := by
    intro X
    show g.mode.descriptionBits ((SUE l F e coef A L hL).parityAtom g.mode g.q (g.support X)) ≤ _
    rw [hpA]
    exact (unionParityAtom_descriptionBits_le _ _ _).trans (hDD 4 (by unfold DD; omega))
  have hwA : ∀ X a, (natWord (g.mode.code (g.atom X a))).length ≤ KcD l F e coef A g.q :=
    fun X a => FrontSemSize.atomWord_le g.mode _ _ (hdA X a)
  have hcw : ∀ X, X < nvG g →
      (codesWord g.mode ((foldOf (g.checkData g.translation)).atoms X)).length ≤ SpB l g.q * KcD l F e coef A g.q := by
    intro X hX
    have hX' : X < FrontFoldSem.nvOf (g.checkData g.translation) := hX
    have hX'' : X < (g.checkData g.translation).pcpp.systematicBits + (g.checkData g.translation).pcpp.auxiliaryBits := hX
    have e1 : (foldOf (g.checkData g.translation)).atoms X =
        List.ofFn ((g.checkData g.translation).atom ⟨X, hX''⟩) := by
      show (if h : X < FrontFoldSem.nvOf (g.checkData g.translation) then
        List.ofFn ((g.checkData g.translation).atom ⟨X, h⟩) else []) = _
      rw [dif_pos hX']
    rw [e1]
    unfold codesWord
    have hs : g.s ≤ SpB l g.q := by
      show (SUE l F e coef A L hL).gridSize g.q ≤ _
      rw [FrontSemSUE.sue_gridSize]; exact sp_le l g.q
    refine le_trans (C1Size.len_flatten_le _ (KcD l F e coef A g.q) ?_) ?_
    · intro w hw
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hw
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hc
      exact hwA ⟨X, hX''⟩ a
    · rw [List.length_map]
      exact Nat.mul_le_mul_right _ (le_trans (le_of_eq List.length_ofFn) hs)
  have hp : (g.checkData g.translation).parityOf =
      unionParityAtom (g.checkData g.translation).mode (g.checkData g.translation).q := by
    show (SUE l F e coef A L hL).parityAtom g.mode g.q = unionParityAtom g.mode g.q; rw [hpA]
  have htr : g.translation = ((IUE l F e coef A).starParams g.q hstar).selectCodes g.pops := by
    unfold UnionGuess.translation; rw [dif_pos hstar]
  have hrq : 4 * (BU l F e coef A).rOf g.q ≤ g.q := hstar.2.2.1
  have hlen : g.translation.length ≤ g.q := by
    rw [htr, Shared.StarParams.selectCodes_length]
    show (BU l F e coef A).rOf g.q ≤ g.q
    omega
  have hcode : ∀ t ∈ g.translation, t ≤ g.q := by
    intro t ht
    have ht' : t ∈ ((IUE l F e coef A).starParams g.q hstar).selectCodes g.pops := htr ▸ ht
    have h1 := Shared.StarParams.selectCodes_lt ((IUE l F e coef A).starParams g.q hstar) g.pops t ht'
    have hs : ((IUE l F e coef A).starParams g.q hstar).s = Nat.log 2 (g.q / (BU l F e coef A).rOf g.q + 1) := rfl
    have h2 : 2 ^ Nat.log 2 (g.q / (BU l F e coef A).rOf g.q + 1) ≤ g.q / (BU l F e coef A).rOf g.q + 1 :=
      Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
    have h3 : g.q / (BU l F e coef A).rOf g.q ≤ g.q := Nat.div_le_self _ _
    rw [hs] at h1
    omega
  have hnv' : g.pcpp.systematicBits + g.pcpp.auxiliaryBits ≤ 2 * KpS l F e coef A L hL g.q := by
    rw [eK]; exact hnv
  have hcb' : 2 ^ g.pcpp.clauseBits ≤ KpS l F e coef A L hL g.q := by rw [eK]; exact hcb
  refine
    { q2 := le_trans (SUE l F e coef A L hL).pcppAlg.minimumArityBound ((SUE l F e coef A L hL).request x g.pair).large
      q := by omega
      nv := by show g.pcpp.systematicBits + g.pcpp.auxiliaryBits ≤ _; omega
      cb := by omega
      s1 := by
        show 1 ≤ (SUE l F e coef A L hL).gridSize g.q
        rw [FrontSemSUE.sue_gridSize]
        exact one_le_gridSize (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCδ1_pos l) g.q
      s := by
        show (SUE l F e coef A L hL).gridSize g.q ≤ _
        rw [FrontSemSUE.sue_gridSize]; exact (sp_le l g.q).trans m4
      lam1 := one_le_lambda (gateZeta_pos l) (gateZeta_lt l) g.q
      lam := (lam_le l g.q).trans m3
      mass := FrontSemSUE.sue_gridMass l F e coef A L hL g.q
      kp := ?_
      circ := ?_
      cw := fun X hX => (hcw X hX).trans m5
      car := ?_
      tr := ?_
      trl := by omega
      cst := ?_ }
  · have e2 : (SUE l F e coef A L hL).pcppAlg.coefficient * (((SUE l F e coef A L hL).request x g.pair).circuit.size + 1) ^
        (SUE l F e coef A L hL).pcppAlg.degree ≤ KpS l F e coef A L hL g.q := by
      rw [eK]; unfold FrontSemSize.Kp
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr _)
    omega
  · intro a
    rcases a with u | ⟨X, b⟩ | X
    · show (natWord (g.mode.code ((SUE l F e coef A L hL).constAtom g.mode g.q))).length ≤ _
      rw [hcA]
      refine (FrontSemSize.atomWord_le g.mode _ (DD l F e coef A) ?_).trans m11
      rw [unionConstAtom_descriptionBits]
      exact Nat.one_le_pow _ _ (by omega)
    · exact (hwA X b).trans m11
    · exact (FrontSemSize.atomWord_le g.mode _ _ (hdP X)).trans m11
  · intro X
    have hq' : g.q ≤ s0 l F e coef A g.q := by unfold s0; omega
    have hA' : (codesWord g.mode ((foldOf (g.checkData g.translation)).atoms X.val)).length ≤ s0 l F e coef A g.q := by
      have := hcw X.val X.isLt; unfold s0; omega
    have hW := FrontFoldBound.Wc_le (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) (foldOf (g.checkData g.translation))
      (s0 l F e coef A g.q) hq' X.val hA'
    have hW' : natBitLength (Stars.Carrier.code ((foldOf (g.checkData g.translation)).car X.val)) + 2 ≤
        (s0 l F e coef A g.q + 2) ^ (lc (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) + 2) := hW
    rw [FrontFoldSem.car_eq hp X] at hW'
    have hLc : (s0 l F e coef A g.q + 2) ^ (lc (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) + 2) ≤
        (s0 l F e coef A g.q + 2) ^ Lc := by
      apply Nat.pow_le_pow_right (by omega)
      unfold Lc
      cases g.mode <;> omega
    show natBitLength (Stars.Carrier.code ((g.checkData g.translation).carrier X)) ≤ _
    omega
  · rw [PrimAsm.CopyNat.natListWord_eq, List.length_append]
    have h1 := C1Size.nw_le g.translation.length
    have h2 := C1Size.len_flatMap_le g.translation natWord (2 * g.q + 3) (fun t ht => (C1Size.nw_le t).trans
      (by have := hcode t ht; omega))
    have h3 : g.translation.length * (2 * g.q + 3) ≤ g.q * (2 * g.q + 5) :=
      Nat.mul_le_mul hlen (by omega)
    omega
  · have : (natWord (CWConst.constCode g.mode)).length ≤ CC := by
      unfold CC; cases g.mode <;> omega
    omega

end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnvS

end
