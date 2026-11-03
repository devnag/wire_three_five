import Lean
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.HashReady4
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.HashFam4Base


noncomputable section
set_option maxRecDepth 4096


/-! # PA2: the HASH writer's family budgets over the v4 data stage

`HashFam`'s run and budget (`hash_fam_run`, `hash_fam_cost`, at the base constants `HB`) with the v4 data stage
(`ThrData.ThrDataStage4`): the machine `hashM4` (the v4 shell `ShellT.shellMGH4` with PA's HASH unit), the run
through `ShellT.hash_ready4`; the data stage's `cost3`, `need`, `Cc3`, `Dc3`, `Kn`, `Dn` are v3's verbatim, so every
numeric step is `HashFam`'s.

* `hashM4`, **`hash_fam_run4`**, **`hash_fam_cost4`**.

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter rows of P3:2220-2226) within the
preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline

section Run
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.HashCall NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.Records
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The HASH writer at one call of the family over the v4 data stage**, within the budget `costH …` at the base
constants. -/
theorem hash_fam_run4
    (S : ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
      (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap))
    (W : PrimT.WalkBank.WalkBankProducer) (FS : FiltSetup.FiltSetupSpec5 W) (h : HB)
    (hS1 : S.Dc3 ≤ h.D0) (hS2 : S.Dn ≤ h.D0) (hS3 : S.Cc3 ≤ h.C0) (hS4 : S.Kn ≤ h.C0)
    (hFS1 : FS.Cn = h.Cn) (hFS2 : FS.Dn = h.Dn) (hFS3 : FS.Cb = h.Cb) (hFS4 : FS.Db = h.Db)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hT : ∀ (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
      (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (capT : ℕ),
      a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) → capT ≤ h.Cc * (n + 1) ^ h.Z →
      ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D capT, v ≤ h.Kt * (n + 1) ^ h.Dt)
    (hfp : ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
      FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
        h.Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ h.Df * (L + 2) ^ (h.Df * (P.errExp + 1)))
    (hZ : h.Z = CallIndexR.capZR l) (hCc : h.Cc = CallIndexR.capK F.cr * 2 ^ h.Z) (hcr : h.cr = F.cr)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    WriterIfaceJ.WriterRun (hashM4 S W FS h)
      (ShellT.costH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH (thrReq n a' ha' Cs carriers translation).word.length n
        (S.cost3 a' Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n))
        (UnaryCalc.value h.D h.Kr (2 ^ NumsXH.mOfH 0 h.KH ((callInputs l F kclk coef A a ha).starParams n hs)) - 1)
        (NumsXH.mOfH 0 h.KH ((callInputs l F kclk coef A a ha).starParams n hs)))
      (ShellT.shellInX4 W.x h.D h.D2 3 1 S.x3) (ShellT.shellOutX4 W.x h.D h.D2 3 1 S.x3)
      (thrReq n a' ha' Cs carriers translation).word (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := by
  -- the length and its logarithm
  have hn8 := fam_n8 l F kclk coef A a ha hs
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLd]; exact Nat.clog_pos (by norm_num) (by omega)
  have hn2 : n + 2 ≤ 2 ^ L := by rw [hLd]; exact Nat.le_pow_clog (by norm_num) _
  -- the call's envelopes
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  have hdesc : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have henv : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hwl : (thrReq n a' ha' Cs carriers translation).word.length ≤ h.Cw * (n + 1) ^ h.Dw :=
    le_trans (CallSize.gate_word_length_le l F kclk coef A a ha _ hcall) (hwb n)
  have hcapT : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤ h.Cc * (n + 1) ^ h.Z := by
    rw [hCc, hZ]; exact fam_capT l F kclk coef A a ha n
  have hnum := hT n hs Cs carriers _ ha' hk2 hdesc hcapT
  -- the THR numbers are at most `2^a`
  obtain ⟨a0, ha0⟩ : ∃ x, x = Nat.clog 2 h.Kt + h.Dt * L := ⟨_, rfl⟩
  have hnum2 : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap, v ≤ 2 ^ a0 := by
    intro v hv
    have := HashSizes.pow_le_two_pow h.Kt h.Dt n
    rw [← hLd, ← ha0] at this
    exact le_trans (hnum v hv) this
  have hee := HashSizes.hashNums_ee_le ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
    (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap a0 hnum2
  rw [hashNums_ee, ← auxP_err] at hee
  have haL : a0 ≤ h.alpha * L := by
    rw [ha0]; unfold HB.alpha
    have : Nat.clog 2 h.Kt ≤ Nat.clog 2 h.Kt * L := Nat.le_mul_of_pos_right _ hL1
    have e : (Nat.clog 2 h.Kt + h.Dt) * L = Nat.clog 2 h.Kt * L + h.Dt * L := by ring
    omega
  -- the carriers' sizes
  have hxs : (carriers.map List.length).sum ≤ 2 * (n + 1) ^ 26 := by
    have hb : ∀ x ∈ carriers.map List.length, x ≤ (n + 1) ^ 26 := by
      intro x hx
      obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      exact (henv X hX).1
    have := List.sum_le_card_nsmul (carriers.map List.length) ((n + 1) ^ 26) hb
    rw [List.length_map, smul_eq_mul] at this
    have := Nat.mul_le_mul_right ((n + 1) ^ 26) hk2
    omega
  have hn1L : n + 1 ≤ 2 ^ L := by omega
  have hp26 : (n + 1) ^ 26 ≤ 2 ^ (26 * L) := by
    rw [show 26 * L = L * 26 by ring, pow_mul]; exact Nat.pow_le_pow_left hn1L 26
  have hlen : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len + 2 ≤ 2 ^ (26 * L + 3) := by
    rw [auxP_len, pow_add]
    have : (1 : ℕ) ≤ 2 ^ (26 * L) := Nat.one_le_two_pow
    omega
  have hcapA : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap + 1 ≤ 2 ^ (h.cA + h.Z * L) := by
    rw [auxP_cap]
    have h1 : (carriers.length + 1) * 4096 * ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤
        12288 * (h.Cc * (n + 1) ^ h.Z) := by
      have := Nat.mul_le_mul (show (carriers.length + 1) * 4096 ≤ 12288 by omega) hcapT
      exact this
    have h2 : (12288 * h.Cc + 1) * (n + 1) ^ h.Z ≤ 2 ^ (h.cA + h.Z * L) := by
      have := HashSizes.pow_le_two_pow (12288 * h.Cc + 1) h.Z n
      rw [← hLd] at this; exact this
    have h3 : 1 ≤ (n + 1) ^ h.Z := Nat.one_le_pow _ _ (by omega)
    have e : (12288 * h.Cc + 1) * (n + 1) ^ h.Z = 12288 * (h.Cc * (n + 1) ^ h.Z) + (n + 1) ^ h.Z := by ring
    omega
  have hkh := HashSizes.kh_cond (Df := h.Df) hL1 haL hee hlen hcapA
    (Filters.seedBits_le (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))
  -- the dimension `m = k + L + K_H L³`
  have hm := fam_mOfH l F kclk coef A a ha hs h.KH
  rw [← hLd] at hm
  have h2kh := fam_two_kh l F kclk coef A a ha hs
  obtain ⟨k, hkd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  rw [← hkd] at hm h2kh
  obtain ⟨m, hmd⟩ : ∃ x, x = NumsXH.mOfH 0 h.KH ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  rw [← hmd] at hm
  have eKH : HashSizes.khOf h.alpha h.cA h.Z h.Df = h.KH := rfl
  rw [eKH] at hkh
  have hL3 : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := Nat.pow_le_pow_right hL1 (by norm_num)
  have hLm : L ≤ m := by omega
  have hsbm : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits + 1 ≤ m := by omega
  have hsbk : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits +
      2 * (((callInputs l F kclk coef A a ha).starParams n hs).s * (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)) ≤ m := by
    omega
  have hkm : 2 * (((callInputs l F kclk coef A a ha).starParams n hs).s * (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)) + 1 ≤ m + 1 := by
    omega
  have hFexp : ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len + 2) ^
      (h.Df * ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp + 1)) ≤ 2 ^ m := by
    have h1 := Nat.le_pow_clog (b := 2) (by norm_num)
      ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len + 2)
    calc ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len + 2) ^
          (h.Df * ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp + 1))
        ≤ (2 ^ Nat.clog 2 ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len + 2)) ^
          (h.Df * ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp + 1)) :=
          Nat.pow_le_pow_left h1 _
      _ = 2 ^ (h.Df * ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp + 1) *
          Nat.clog 2 ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len + 2)) := by
          rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- `Q = 2^m + 1`, `U = Q^{d_N}`
  obtain ⟨Q, hQd⟩ : ∃ x, x = 2 ^ m + 1 := ⟨_, rfl⟩
  have hLmp : 2 ^ L ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hLm
  have hnQ : n + 2 ≤ Q := by omega
  have hdN1 : 1 ≤ h.dN := by unfold HB.dN; omega
  obtain ⟨U, hUd⟩ : ∃ x, x = Q ^ h.dN := ⟨_, rfl⟩
  have hQU : Q ≤ U := by
    rw [hUd]; calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ h.dN := Nat.pow_le_pow_right (by omega) hdN1
  have hpowU : ∀ d, d ≤ h.dN → (n + 1) ^ d ≤ U := fun d hd => by
    rw [hUd]; exact pow_le_pow_of (by omega) (by omega) hd
  have hU1 : 1 ≤ U := by omega
  have h2m : 2 ^ m + 1 = Q := hQd.symm
  -- the atoms: each call size at most `K_atom·U`
  have dDw : h.Dw ≤ h.dN := by unfold HB.dN; omega
  have dDt : h.Dt ≤ h.dN := by unfold HB.dN; omega
  have dZ : h.Z ≤ h.dN := by unfold HB.dN; omega
  have d26 : 26 ≤ h.dN := by unfold HB.dN; omega
  have aW : (thrReq n a' ha' Cs carriers translation).word.length ≤ h.Cw * U :=
    le_trans hwl (Nat.mul_le_mul_left _ (hpowU _ dDw))
  have aN : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap, v ≤ h.Kt * U :=
    fun v hv => le_trans (hnum v hv) (Nat.mul_le_mul_left _ (hpowU _ dDt))
  have aT : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤ h.Cc * U :=
    le_trans hcapT (Nat.mul_le_mul_left _ (hpowU _ dZ))
  have a26 : (n + 1) ^ 26 ≤ U := hpowU 26 d26
  have aX : (carriers.map List.length).sum ≤ 2 * U := by omega
  have aG : (PrimT.ThrTab.tupleG Cs).length ≤ 4 * U := by
    have := PrimT.C4GateSym.tupleG_len_le Cs ((n + 1) ^ 26) hdesc
    have := Nat.mul_le_mul_right ((n + 1) ^ 26) ha'
    omega
  have aC : ∀ v ∈ ThrData.thrCounts Cs carriers, v ≤ 4 * U := by
    intro v hv
    unfold ThrData.thrCounts at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hv
      have := (henv X hX).1
      omega
    · rw [List.mem_singleton] at hv; omega
  have aE : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp ≤ h.Kt * U := by
    rw [auxP_err, ← hashNums_ee]
    exact aN _ (HashSizes.hashNums_getD_mem ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap 13
      (by norm_num))
  have aM : (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 8 0 ≤
        h.Kt * U := aN _ (HashSizes.hashNums_getD_mem ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap 8
      (by norm_num))
  have aP : (thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 4 * U + h.Kt * U := by
    rw [← hash_pool (gate0 l F).alg ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (callInputs l F kclk coef A a ha).D
      ((callInputs l F kclk coef A a ha).filterParams .thr n).cap]
    have := Nat.add_le_add (Nat.mul_le_mul_left 2 aX) aM
    calc _ ≤ 2 * (2 * U) + h.Kt * U := this
      _ = 4 * U + h.Kt * U := by ring
  have aA : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap ≤ 12288 * (h.Cc * U) := by
    rw [auxP_cap]
    exact Nat.mul_le_mul (show (carriers.length + 1) * 4096 ≤ 12288 by omega) aT
  have aLn : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len ≤ 4 * U := by
    rw [auxP_len]; omega
  have aS : 2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits * 2 ≤ Q := by
    rw [← pow_succ]; have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hsbm; omega
  have aK : 2 ^ (2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
      (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)) + 1) ≤ 2 * Q := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hkm
    rw [pow_succ] at this; omega
  have aTOT : 2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits *
      2 ^ (2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
        (((callInputs l F kclk coef A a ha).starParams n hs).r / 2))) * 5 ≤ 5 * Q := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hsbk
    rw [pow_add] at this; omega
  have hKa : h.Cw + h.cr + h.Kt + 12288 * h.Cc + 64 = h.Katom := rfl
  -- `K_atom·U` bounds every size
  have hKatom : 64 ≤ h.Katom := by unfold HB.Katom; omega
  obtain ⟨KU, hKUd⟩ : ∃ x, x = h.Katom * U := ⟨_, rfl⟩
  have hUKU : 64 * U ≤ KU := by rw [hKUd]; exact Nat.mul_le_mul_right _ hKatom
  have kW : (thrReq n a' ha' Cs carriers translation).word.length ≤ KU := by
    have : h.Cw * U ≤ KU := by rw [hKUd]; exact Nat.mul_le_mul_right _ (by unfold HB.Katom; omega)
    omega
  have kKt : h.Kt * U ≤ KU := by rw [hKUd]; exact Nat.mul_le_mul_right _ (by unfold HB.Katom; omega)
  have kCc : 12288 * (h.Cc * U) ≤ KU := by
    rw [hKUd, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by unfold HB.Katom; omega)
  have kP : (thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ KU := by
    have : 4 * U + h.Kt * U ≤ KU := by
      rw [hKUd]
      have e : 4 * U + h.Kt * U = (4 + h.Kt) * U := by ring
      rw [e]; exact Nat.mul_le_mul_right _ (by unfold HB.Katom; omega)
    omega
  have kcr : h.cr ≤ KU := by
    have : h.cr ≤ h.Katom := by unfold HB.Katom; omega
    have : h.Katom ≤ KU := by rw [hKUd]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  -- the register capacity
  have hdcap1 : 1 ≤ h.dcap := by unfold HB.dcap; omega
  obtain ⟨cap, hcapd⟩ : ∃ x, x = h.Kcap * U ^ h.dcap := ⟨_, rfl⟩
  have hUdc : U ≤ U ^ h.dcap := by
    calc U = U ^ 1 := (pow_one U).symm
      _ ≤ U ^ h.dcap := Nat.pow_le_pow_right hU1 hdcap1
  have hcap1 : 100 * KU + 20000 ≤ cap := by
    have a1 : (100 * h.Katom + 20000) * U ≤ h.Kcap * U := Nat.mul_le_mul_right _ (by unfold HB.Kcap; omega)
    have a2 : h.Kcap * U ≤ cap := by rw [hcapd]; exact Nat.mul_le_mul_left _ hUdc
    have e : (100 * h.Katom + 20000) * U = 100 * KU + 20000 * U := by rw [hKUd]; ring
    omega
  have hcapN : h.Cn * (9 * KU) ^ h.Dn ≤ cap := by
    have e1 : (9 * KU) ^ h.Dn = (9 * h.Katom) ^ h.Dn * U ^ h.Dn := by rw [hKUd, ← mul_pow]; ring_nf
    have e2 : U ^ h.dcap = U ^ h.Dn * U := by unfold HB.dcap; rw [pow_succ]
    have a1 : h.Cn * (9 * h.Katom) ^ h.Dn ≤ h.Kcap := by unfold HB.Kcap; omega
    rw [e1, hcapd, e2]
    calc h.Cn * ((9 * h.Katom) ^ h.Dn * U ^ h.Dn) = h.Cn * (9 * h.Katom) ^ h.Dn * U ^ h.Dn := by ring
      _ ≤ h.Kcap * U ^ h.Dn := Nat.mul_le_mul_right _ a1
      _ ≤ h.Kcap * (U ^ h.Dn * U) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hU1)
  -- the aux filter's sizes within `KU`
  have kE : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp ≤ KU := by omega
  have kLn : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len ≤ KU := by omega
  have kA : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap ≤ KU := by omega
  have kT : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤ KU := by
    have : h.Cc * U ≤ 12288 * (h.Cc * U) := Nat.le_mul_of_pos_left _ (by norm_num)
    omega
  have kS : 2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits ≤ U := by omega
  have kQ : Q ≤ U := hQU
  have hclog : ∀ x : ℕ, Nat.clog 2 x ≤ x := fun x => Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have kG5 : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).labelBits +
      (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).fieldBits +
      (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen + 512 ≤ cap := by
    have l1 := hclog (32 * (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap)
    have l2 := hclog (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len
    have l3 : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).labelBits ≤
        32 * (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap +
          (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len := by
      unfold GapParams.labelBits GapParams.prefixBits
      exact max_le (by omega) (by omega)
    have l4 : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).fieldBits ≤
        (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len + 4 := by
      unfold GapParams.fieldBits; omega
    have l5 : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).walkLen ≤
        (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp + 1 := by
      unfold GapParams.walkLen; omega
    omega
  -- the loop's length `b = 5Q`
  have hLp : UnaryCalc.value 1 5 (2 ^ m) = 5 * Q := by rw [value_eq, pow_one, hQd]
  -- the FILTER pipeline's bound
  obtain ⟨BP, hBPd⟩ : ∃ x, x = h.Kf * (10 * KU) ^ h.Df * Q := ⟨_, rfl⟩
  have hPc1 : 1 ≤ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap := by
    rw [auxP_cap]
    have h1 : 1 ≤ ((callInputs l F kclk coef A a ha).filterParams .thr n).cap :=
      ((gate0 l F).budget kclk coef A a ha).capOf_pos .thr n
    have := Nat.mul_le_mul (show 1 ≤ (carriers.length + 1) * 4096 by omega) h1
    omega
  have hFN : ∀ q ≤ UnaryCalc.value 1 5 (2 ^ m),
      FS.need (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len
          (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap
          (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp
          (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len
          (2 * (2 * (q / Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))))
          (thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length 0
          (Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))) ≤ cap ∧
        FiltPipe.filtPipeBound (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (SymDec.hseed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) q)
          (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len
          (2 * (2 * (q / Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))))
          (thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length 0
          (FiltSetup.rulerW (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))
          (FiltSetup.rulerW (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ BP := by
    intro q hq
    rw [hLp] at hq
    have hcard : Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) =
        2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits := card_gapSeed _
    have hr4 : 2 * (2 * (q / Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))) ≤
        20 * U := by
      have := Nat.div_le_self q (Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))
      omega
    refine ⟨?_, ?_⟩
    · have hp := FS.need_poly (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len
        (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap
        (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp
        (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len
        (2 * (2 * (q / Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))))
        (thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length 0
        (Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))
      unfold ValidatorPolynomialDomination.PolyBounded at hp
      rw [hFS1, hFS2] at hp
      refine le_trans hp (le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)) hcapN)
      have kcard : Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ U := by
        rw [hcard]; exact kS
      omega
    · have hb := hfp (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
        (SymDec.hseed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) q)
        (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len
        (2 * (2 * (q / Fintype.card (GapSeed (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))))
        (thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length 0 hPc1
      refine le_trans hb ?_
      rw [hBPd]
      refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)) (le_trans hFexp (by omega))
      omega
  -- the scrub `R = K_r·U^{d_r}`
  obtain ⟨Y, hYd⟩ : ∃ x, x = U ^ h.dr := ⟨_, rfl⟩
  have hRd : UnaryCalc.value h.D h.Kr (2 ^ m) = h.Kr * Y := by
    rw [value_eq, ← hQd, hYd, hUd, ← pow_mul]; rfl
  obtain ⟨hdr1, hdr2, hdr3, hdr4⟩ := h.dr_ge
  have hdcr : h.dcap ≤ h.dr := by omega
  have yU : ∀ d, d ≤ h.dr → U ^ d ≤ Y := fun d hd => by rw [hYd]; exact Nat.pow_le_pow_right hU1 hd
  have fU : U ≤ Y := by have := yU 1 hdr1; rwa [pow_one] at this
  have fKU : KU ≤ h.Katom * Y := by rw [hKUd]; exact Nat.mul_le_mul_left _ fU
  have hKc1 : 1 ≤ h.Kcap := by unfold HB.Kcap; omega
  have fcap : cap ≤ h.Kcap * Y := by rw [hcapd]; exact Nat.mul_le_mul_left _ (yU _ hdcr)
  have fcc : cap * cap ≤ h.Kcap * h.Kcap * Y := by
    have e : cap * cap = h.Kcap * h.Kcap * U ^ (2 * h.dcap) := by rw [hcapd, two_mul, pow_add]; ring
    rw [e]; exact Nat.mul_le_mul_left _ (yU _ hdr2)
  have fcb : FS.bound cap ≤ h.Cb * (2 * h.Kcap) ^ h.Db * Y := by
    have hp := FS.bound_poly cap
    unfold ValidatorPolynomialDomination.PolyBounded at hp
    rw [hFS3, hFS4] at hp
    have e : (2 * h.Kcap) ^ h.Db * U ^ (h.dcap * h.Db) = (2 * cap) ^ h.Db := by
      rw [hcapd, pow_mul, ← mul_pow]; ring_nf
    have a1 : (cap + 1) ^ h.Db ≤ (2 * cap) ^ h.Db := Nat.pow_le_pow_left (by omega) _
    have a2 : (2 * h.Kcap) ^ h.Db * U ^ (h.dcap * h.Db) ≤ (2 * h.Kcap) ^ h.Db * Y :=
      Nat.mul_le_mul_left _ (yU _ hdr3)
    calc FS.bound cap ≤ h.Cb * (cap + 1) ^ h.Db := hp
      _ ≤ h.Cb * ((2 * h.Kcap) ^ h.Db * Y) := Nat.mul_le_mul_left _ (le_trans a1 (e ▸ a2))
      _ = h.Cb * (2 * h.Kcap) ^ h.Db * Y := by ring
  have fBP : BP ≤ h.Kf * (10 * h.Katom) ^ h.Df * Y := by
    rw [hBPd, hKUd]
    have e : h.Kf * (10 * (h.Katom * U)) ^ h.Df * Q = h.Kf * (10 * h.Katom) ^ h.Df * (U ^ h.Df * Q) := by
      rw [show 10 * (h.Katom * U) = (10 * h.Katom) * U by ring, mul_pow]; ring
    rw [e]
    have a1 : U ^ h.Df * Q ≤ U ^ (h.Df + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hQU
    exact Nat.mul_le_mul_left _ (le_trans a1 (yU _ hdr4))
  have eKr : h.Kr * Y = 1000000 * (h.Kcap * h.Kcap * Y) + h.Cb * (2 * h.Kcap) ^ h.Db * Y +
      h.Kf * (10 * h.Katom) ^ h.Df * Y + 1000 * (h.Katom * Y) + 1000000 * Y := by unfold HB.Kr; ring
  have hKcc : h.Kcap * Y ≤ h.Kcap * h.Kcap * Y := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  -- the unit's cost within `R − 1`
  have hcapn : n + 2 ≤ cap := by omega
  have hcapcr : h.cr ≤ cap := by omega
  have fN := HashSizes.hNCost_le n (thrReq n a' ha' Cs carriers translation).word.length h.cr cap hcapn hcapcr
  have fB := HashSizes.hbCost_le cap
  have fc2 : (cap + 2) * (cap + 2) ≤ 9 * (cap * cap) := sq2_le cap (by omega)
  have hul : (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
        ThrData.thrCounts Cs carriers)).length ≤ 19 * (KU + 1) := by
    have hlen2 : (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
        (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
          ThrData.thrCounts Cs carriers).length ≤ 19 := by
      rw [List.length_append, ThrData.hashNums_length]
      simp [ThrData.thrCounts]; omega
    have := PrimT.C4GateSym.unaryList_len_le _ KU (by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact le_trans (aN v hv) kKt
      · exact le_trans (aC v hv) (by omega))
    exact le_trans this (Nat.mul_le_mul_right _ hlen2)
  have hnU : PrimAsm.CellLoopD.cpCost (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs)
        Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
        ThrData.thrCounts Cs carriers)).length + 1 +
      (SymDec.hNCost n (thrReq n a' ha' Cs carriers translation).word.length h.cr cap + 1 +
        (SymDec.hbCost cap + FS.bound cap + 12) + 1 + (BP + 4) + 1 + (3 * UnaryCalc.value 1 5 (2 ^ m) + 3)) ≤
      UnaryCalc.value h.D h.Kr (2 ^ m) - 1 := by
    rw [HashSizes.cpCost_eq, hLp, hRd, eKr]
    omega
  have hcapR : cap + 1 ≤ UnaryCalc.value h.D h.Kr (2 ^ m) := by rw [hRd, eKr]; omega
  have hRR : UnaryCalc.value h.D h.Kr (2 ^ m) - 1 + 1 ≤ UnaryCalc.value h.D h.Kr (2 ^ m) := by
    rw [hRd, eKr]; omega
  have hboot : ShellD.bootCost (thrReq n a' ha' Cs carriers translation).word n 0 0 ≤ UnaryCalc.value h.D h.Kr (2 ^ m) := by
    have := HashSizes.bootCost_le (thrReq n a' ha' Cs carriers translation).word n
    rw [hRd, eKr]; omega
  -- the data width `V = C₂(n+1)^{D₂}`
  have hn1 : 1 ≤ n + 1 := by omega
  have v1 : ∀ d, d ≤ h.D2 → (n + 1) ^ d ≤ (n + 1) ^ h.D2 := fun d hd => Nat.pow_le_pow_right hn1 hd
  have vNW := v1 h.Dnw (by unfold HB.D2; omega)
  have vDt := v1 h.Dt (by unfold HB.D2; omega)
  have vD0 := v1 h.D0 (by unfold HB.D2; omega)
  have vP1 : 1 ≤ (n + 1) ^ h.D2 := Nat.one_le_pow _ _ (by omega)
  have eV : UnaryCalc.value h.D2 h.C2 n = h.Cnw * (n + 1) ^ h.D2 + 16 * (h.Kt * (n + 1) ^ h.D2) +
      32 * (n + 1) ^ h.D2 + h.C0 * (n + 1) ^ h.D2 := by rw [value_eq]; unfold HB.C2; ring
  have hnwV : PrimT.C4GateSym.needW n ≤ UnaryCalc.value h.D2 h.C2 n := by
    have a1 := hnw n
    have a2 : h.Cnw * (n + 1) ^ h.Dnw ≤ h.Cnw * (n + 1) ^ h.D2 := Nat.mul_le_mul_left _ vNW
    rw [eV]; omega
  have td := PrimT.C4GateSym.thr_data_hyps Cs carriers ha' hk2 hdesc henv (UnaryCalc.value h.D2 h.C2 n) hnwV
  have hD : PrimThrW.ShellE.ThrDataOK2 Cs carriers (UnaryCalc.value h.D2 h.C2 n) :=
    ⟨ha', hk2, td.1, td.2.1, td.2.2.1, td.2.2.2.1, td.2.2.2.2.1, td.2.2.2.2.2.1, td.2.2.2.2.2.2.1,
      td.2.2.2.2.2.2.2.1, td.2.2.2.2.2.2.2.2.1⟩
  have td0 := PrimT.C4GateSym.thr_data_hyps Cs carriers ha' hk2 hdesc henv (PrimT.C4GateSym.needW n) le_rfl
  have hu2 := td0.2.2.2.2.2.2.2.2.1
  have hu1 : (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap)).length ≤
        16 * (h.Kt * (n + 1) ^ h.Dt + 1) := by
    have := PrimT.C4GateSym.unaryList_len_le _ (h.Kt * (n + 1) ^ h.Dt) hnum
    rwa [ThrData.hashNums_length] at this
  have hcu3 : 2 * (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
        ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * UnaryCalc.value h.D2 h.C2 n + 2 := by
    unfold Data.unaryList at hu1 hu2 ⊢
    rw [List.flatMap_append, List.length_append]
    have a1 := hnw n
    have a2 : h.Cnw * (n + 1) ^ h.Dnw ≤ h.Cnw * (n + 1) ^ h.D2 := Nat.mul_le_mul_left _ vNW
    have a3 : h.Kt * (n + 1) ^ h.Dt ≤ h.Kt * (n + 1) ^ h.D2 := Nat.mul_le_mul_left _ vDt
    rw [eV]; omega
  have hneed : S.need n ≤ 2 * UnaryCalc.value h.D2 h.C2 n + 2 := by
    have a1 := S.need_le n
    have a2 : S.Kn * (n + 1) ^ S.Dn ≤ h.C0 * (n + 1) ^ h.D0 :=
      Nat.mul_le_mul hS4 (Nat.pow_le_pow_right hn1 hS2)
    have a3 : h.C0 * (n + 1) ^ h.D0 ≤ h.C0 * (n + 1) ^ h.D2 := Nat.mul_le_mul_left _ vD0
    rw [eV]; omega
  -- the dimension stage's fill
  have hW : 2 * n + h.cr + 16 + 0 * (n + 2) ^ 2 + h.KH * (n + 2) ^ 3 ≤ UnaryCalc.value 3 h.Cv n := by
    rw [value_eq]; unfold HB.Cv
    have a1 : (n + 2) ^ 3 ≤ 8 * (n + 1) ^ 3 := by
      have : (n + 2) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      rw [mul_pow] at this; norm_num at this; exact this
    have a2 : n + 1 ≤ (n + 1) ^ 3 := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right hn1 (by norm_num)
    have a3 : h.KH * (n + 2) ^ 3 ≤ h.KH * (8 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ a1
    have a4 : h.cr ≤ h.cr * (n + 1) ^ 3 := Nat.le_mul_of_pos_right _ (by omega)
    have e : (h.cr + 19 + 8 * h.KH) * (n + 1) ^ 3 = h.cr * (n + 1) ^ 3 + 19 * (n + 1) ^ 3 + 8 * (h.KH * (n + 1) ^ 3) := by
      ring
    have e2 : h.KH * (8 * (n + 1) ^ 3) = 8 * (h.KH * (n + 1) ^ 3) := by ring
    rw [e]; omega
  -- the call's sizes
  have hc1 : 2 * (thrReq n a' ha' Cs carriers translation).word.length + 2 ≤ cap := by omega
  have hc2 : 2 ^ (natBitLength n + 1) ≤ cap := by
    have := PrimAsm.CopyNat.two_pow_natBitLength_le n
    rw [pow_succ]; omega
  have hc3 : 4 * (n + 3) + 2 * h.cr + 20 ≤ cap := by omega
  have hcl : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
        ThrData.thrCounts Cs carriers, v ≤ cap := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have := aN v hv; omega
    · have := aC v hv; omega
  have hcs : (carriers.map (·.length)).sum + (PrimT.ThrTab.tupleG Cs).length + 4 ≤ cap := by
    have : (carriers.map (·.length)).sum ≤ 2 * U := aX
    omega
  have hcD1 : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp +
      (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len +
      (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap + (carriers.length + 1) * 4096 +
      ((callInputs l F kclk coef A a ha).filterParams .thr n).cap + 10 ≤ cap := by omega
  have hcG1 : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).cap * 32 + 2 ≤ cap := by omega
  have hcG2 : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).len + 8 ≤ cap := by omega
  have hcG3 : (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).errExp + 4 ≤ cap := by omega
  have hcG4 : 2 ^ ((auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits + 1) ≤ cap := by
    rw [pow_succ]; omega
  have hcD3 : (thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length +
      2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits +
      2 ^ (2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
        (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)) + 1) +
      2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits *
        2 ^ (2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
          (((callInputs l F kclk coef A a ha).starParams n hs).r / 2))) * 5 + 10 ≤ cap := by omega
  have hcJ : 4 * UnaryCalc.value 1 5 (2 ^ m) +
      2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits *
        2 ^ (2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
          (((callInputs l F kclk coef A a ha).starParams n hs).r / 2))) * 5 +
      2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits + 30 ≤ cap := by
    rw [hLp]; omega
  have hTOT : 2 ^ (auxP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).seedBits *
      2 ^ (2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
        (((callInputs l F kclk coef A a ha).starParams n hs).r / 2))) * 5 ≤ UnaryCalc.value 1 5 (2 ^ m) := by
    rw [hLp]; exact aTOT
  -- the run
  subst hmd
  exact ShellT.hash_ready4 (gate0 l F).alg (callInputs l F kclk coef A a ha) S W FS h.cr h.D h.Kr h.D2 h.C2 3 h.Cv 1 5 0 h.KH
    cap _ _ (SymDec.hbCost cap + FS.bound cap) BP hs ha' Cs carriers translation rfl rfl
    (((gate0 l F).budget kclk coef A a ha).capOf_pos .thr n) (by rw [hcr]; rfl) hD hcu3 hdesc hneed hW hcapR hRR hboot
    hTOT hc1 hc2 hc3 hcl hcs hcD1 hcG1 hcG2 hcG3 hcG4 kG5 hcD3 hcJ le_rfl hFN hnU le_rfl

end Run

/-! ## The budget's class link -/

section Cost
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The HASH writer's budget is in the preprocessing class**: `costH … ≤ c_W·classBound E_W .preprocessing n k Ψ`
at every THR call of the family, for every floor with `c_ψ ≥ E_tot` and `C_D ≥ 1`. -/
theorem hash_fam_cost4
    (S : ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
      (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap)) (h : HB)
    (hS1 : S.Dc3 ≤ h.D0) (hS3 : S.Cc3 ≤ h.C0)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hCD : 1 ≤ F.CD) (EW : Envelope) (hcpsi : h.Etot ≤ EW.cpsi)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ShellT.costH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH (thrReq n a' ha' Cs carriers translation).word.length n
        (S.cost3 a' Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n))
        (UnaryCalc.value h.D h.Kr (2 ^ NumsXH.mOfH 0 h.KH ((callInputs l F kclk coef A a ha).starParams n hs)) - 1)
        (NumsXH.mOfH 0 h.KH ((callInputs l F kclk coef A a ha).starParams n hs)) ≤
      h.cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
        (((gate0 l F).budget kclk coef A a ha).psiOf n) := by
  have hn8 := fam_n8 l F kclk coef A a ha hs
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLd]; exact Nat.clog_pos (by norm_num) (by omega)
  have hn2 : n + 2 ≤ 2 ^ L := by rw [hLd]; exact Nat.le_pow_clog (by norm_num) _
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  have hdesc : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have henv : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hwl : (thrReq n a' ha' Cs carriers translation).word.length ≤ h.Cw * (n + 1) ^ h.Dw :=
    le_trans (CallSize.gate_word_length_le l F kclk coef A a ha _ hcall) (hwb n)
  -- the dimension
  have hm := fam_mOfH l F kclk coef A a ha hs h.KH
  rw [← hLd] at hm
  obtain ⟨k, hkd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  rw [← hkd] at hm
  obtain ⟨m, hmd⟩ : ∃ x, x = NumsXH.mOfH 0 h.KH ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  rw [← hmd] at hm ⊢
  obtain ⟨Q, hQd⟩ : ∃ x, x = 2 ^ m + 1 := ⟨_, rfl⟩
  have hL3 : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := Nat.pow_le_pow_right hL1 (by norm_num)
  have hLm : L ≤ m := by omega
  have hnQ : n + 1 ≤ Q := by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hLm; omega
  have hQ1 : 1 ≤ Q := by omega
  have qp : ∀ d d', d ≤ d' → Q ^ d ≤ Q ^ d' := fun d d' hd => Nat.pow_le_pow_right hQ1 hd
  -- the data stage's cost
  have hD21 : 1 ≤ h.D2 := by unfold HB.D2; omega
  have hn1 : 1 ≤ n + 1 := by omega
  have eV : UnaryCalc.value h.D2 h.C2 n = h.C2 * (n + 1) ^ h.D2 := value_eq _ _ _
  have hnwV : PrimT.C4GateSym.needW n ≤ UnaryCalc.value h.D2 h.C2 n := by
    have a1 := hnw n
    have a2 : h.Cnw * (n + 1) ^ h.Dnw ≤ h.C2 * (n + 1) ^ h.D2 :=
      Nat.mul_le_mul (by unfold HB.C2; omega) (Nat.pow_le_pow_right hn1 (by unfold HB.D2; omega))
    omega
  have td := PrimT.C4GateSym.thr_data_hyps Cs carriers ha' hk2 hdesc henv (UnaryCalc.value h.D2 h.C2 n) hnwV
  have hcc := S.cost3_le Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n)
    (UnaryCalc.value h.D2 h.C2 n) ha' hk2 td.1 td.2.1 td.2.2.2.2.2.2.2.2.2.1 td.2.2.2.2.2.2.2.2.2.2 td.2.2.1
  unfold ValidatorPolynomialDomination.PolyBounded at hcc
  have hV3 : UnaryCalc.value h.D2 h.C2 n + n + UnaryCalc.value h.D2 h.C2 n + UnaryCalc.value h.D2 h.C2 n + 1 ≤
      (3 * h.C2 + 1) * (n + 1) ^ h.D2 := by
    have a1 : n + 1 ≤ (n + 1) ^ h.D2 := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ h.D2 := Nat.pow_le_pow_right hn1 hD21
    rw [eV]
    have e : (3 * h.C2 + 1) * (n + 1) ^ h.D2 = 3 * (h.C2 * (n + 1) ^ h.D2) + (n + 1) ^ h.D2 := by ring
    omega
  have hcc2 : S.cost3 a' Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n) ≤
      h.C0 * (3 * h.C2 + 1) ^ h.D0 * (n + 1) ^ (h.D2 * h.D0) := by
    refine le_trans hcc ?_
    have a1 : ((3 * h.C2 + 1) * (n + 1) ^ h.D2) ^ S.Dc3 ≤ ((3 * h.C2 + 1) * (n + 1) ^ h.D2) ^ h.D0 :=
      Nat.pow_le_pow_right (Nat.mul_pos (by omega) (Nat.one_le_pow _ _ (by omega))) hS1
    have a2 := Nat.mul_le_mul hS3 (le_trans (Nat.pow_le_pow_left hV3 _) a1)
    rw [mul_pow, ← pow_mul] at a2
    calc _ ≤ h.C0 * ((3 * h.C2 + 1) ^ h.D0 * (n + 1) ^ (h.D2 * h.D0)) := a2
      _ = _ := by ring
  -- the request side `≤ K₁·Q^{d₁}`
  have hreq : (thrReq n a' ha' Cs carriers translation).word.length + n +
      S.cost3 a' Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n) + 2 ≤ h.K1 * Q ^ h.d1 := by
    have p1 : (n + 1) ^ h.Dw ≤ Q ^ h.d1 := pow_le_pow_of hnQ hQ1 (by unfold HB.d1; omega)
    have p2 : (n + 1) ^ (h.D2 * h.D0) ≤ Q ^ h.d1 := pow_le_pow_of hnQ hQ1 (by unfold HB.d1; omega)
    have p3 : n + 1 ≤ Q ^ h.d1 := by
      calc n + 1 ≤ Q := hnQ
        _ = Q ^ 1 := (pow_one Q).symm
        _ ≤ Q ^ h.d1 := qp _ _ (by unfold HB.d1; omega)
    have a1 : h.Cw * (n + 1) ^ h.Dw ≤ h.Cw * Q ^ h.d1 := Nat.mul_le_mul_left _ p1
    have a2 : h.C0 * (3 * h.C2 + 1) ^ h.D0 * (n + 1) ^ (h.D2 * h.D0) ≤ h.C0 * (3 * h.C2 + 1) ^ h.D0 * Q ^ h.d1 :=
      Nat.mul_le_mul_left _ p2
    have e : h.K1 * Q ^ h.d1 = h.Cw * Q ^ h.d1 + 2 * Q ^ h.d1 + h.C0 * (3 * h.C2 + 1) ^ h.D0 * Q ^ h.d1 := by
      unfold HB.K1; ring
    omega
  -- the budget `≤ K_tot·Q^{E_tot}`
  have hc := ShellT.costH_le h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH
    (thrReq n a' ha' Cs carriers translation).word.length n
    (S.cost3 a' Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n))
    (UnaryCalc.value h.D h.Kr (2 ^ m) - 1) m
  rw [← hQd] at hc
  have eE : ShellT.EcT h.D h.D2 3 1 = h.E := rfl
  rw [eE] at hc
  have f1 : ((thrReq n a' ha' Cs carriers translation).word.length + n +
      S.cost3 a' Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n) + 2) ^ h.E ≤
        h.K1 ^ h.E * Q ^ h.Etot := by
    refine le_trans (Nat.pow_le_pow_left hreq _) ?_
    rw [mul_pow, ← pow_mul]
    exact Nat.mul_le_mul_left _ (qp _ _ (by unfold HB.Etot; omega))
  have f2 : Q ^ h.E ≤ Q ^ h.Etot := qp _ _ (by unfold HB.Etot; omega)
  have eR : UnaryCalc.value h.D h.Kr (2 ^ m) = h.Kr * Q ^ h.D := by rw [value_eq, ← hQd]
  have eL : UnaryCalc.value 1 5 (2 ^ m) = 5 * Q := by rw [value_eq, pow_one, ← hQd]
  have f3 : UnaryCalc.value 1 5 (2 ^ m) * (2 * (UnaryCalc.value h.D h.Kr (2 ^ m) - 1) +
      2 * UnaryCalc.value h.D h.Kr (2 ^ m) + 10) ≤ 5 * (4 * h.Kr + 10) * Q ^ h.Etot := by
    rw [eL, eR]
    have a1 : 2 * (h.Kr * Q ^ h.D - 1) + 2 * (h.Kr * Q ^ h.D) + 10 ≤ (4 * h.Kr + 10) * Q ^ h.D := by
      have : 1 ≤ Q ^ h.D := Nat.one_le_pow _ _ (by omega)
      have e : (4 * h.Kr + 10) * Q ^ h.D = 4 * (h.Kr * Q ^ h.D) + 10 * Q ^ h.D := by ring
      omega
    calc 5 * Q * (2 * (h.Kr * Q ^ h.D - 1) + 2 * (h.Kr * Q ^ h.D) + 10)
        ≤ 5 * Q * ((4 * h.Kr + 10) * Q ^ h.D) := Nat.mul_le_mul_left _ a1
      _ = 5 * (4 * h.Kr + 10) * Q ^ (h.D + 1) := by rw [pow_succ]; ring
      _ ≤ 5 * (4 * h.Kr + 10) * Q ^ h.Etot := Nat.mul_le_mul_left _ (qp _ _ (by unfold HB.Etot; omega))
  have htot : ShellT.costH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH (thrReq n a' ha' Cs carriers translation).word.length n
      (S.cost3 a' Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n))
      (UnaryCalc.value h.D h.Kr (2 ^ m) - 1) m ≤ h.Ktot * Q ^ h.Etot := by
    have g1 := Nat.mul_le_mul_left (ShellT.KcH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH) f1
    have g2 := Nat.mul_le_mul_left (ShellT.KcH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH) f2
    have e : h.Ktot * Q ^ h.Etot = ShellT.KcH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH * (h.K1 ^ h.E * Q ^ h.Etot) +
        ShellT.KcH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH * Q ^ h.Etot + 5 * (4 * h.Kr + 10) * Q ^ h.Etot := by
      unfold HB.Ktot; ring
    omega
  -- the class link
  have hcl := HashSizes.class_link EW h.Etot h.Ktot 0 h.KH F.CD n k L
    (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
    (HashFam.Etot_pos h) hL1 hCD hcpsi (by omega)
  have eQ : 2 ^ (k + L + 0 * L ^ 2 + h.KH * L ^ 3) + 1 = Q := by rw [← hm, hQd]
  rw [eQ] at hcl
  have ecW : h.Ktot * 2 ^ ((h.Etot * (1 + 0 + h.KH)) ^ 2 + h.Etot) = h.cW := rfl
  rw [ecW] at hcl
  have epsi : ((gate0 l F).budget kclk coef A a ha).psiOf n = loadPsi F.CD k L
      (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := by
    rw [hkd, hLd]; rfl
  rw [← hkd, epsi]
  exact le_trans htot hcl

end Cost

end NearCubicWires.WireExponent3_5.PrimAsm.HashFam

end
