import Proof.Wire_3_5.FinalPass.SdPrep2

/-! # S4 (the seeds phase), part 25: the prep (P3:3170-3178)

S4's small numbers `vs = s4Small2 …` arrive as `unaryList vs` on the word stream `i`. **`prepWM i o Rp`**: read
them into `Rp 0 … 15` (`readList`, counter `Rp 16`), rewind the word, `Rp 17 := vs₆ + vs₃·vs₁ + vs₃·vs₁` (PA's
`mulAddW` twice: at `s4Small2` this is `(n − rb) + 2·(r/2)·b = n`), `Rp 18 := 2^{vs₁₁}` (PA's `pow2W`: at `s4Small2`
the seed width, so `|GapSeed| = 2^{seedBits}`), then `reqWM` writes the tables writer's request
`frame (reqT n len cap err L₀ L₁ nE)` onto the empty port `o`. **`prepWM_spec`**: exactly those registers and the port
change.

Paper quantity of the main type: the tables writer's request `ppReq vs` (the call's `n`, the filter parameters, the
carriers' mask lengths, the seed count). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

theorem ppUl_cons (v : ℕ) (vs : List ℕ) :
    Data.unaryList (v :: vs) = List.replicate v true ++ [false] ++ Data.unaryList vs := by
  simp [Data.unaryList]

theorem ppUl_len (v : ℕ) (vs : List ℕ) :
    (Data.unaryList (v :: vs)).length = v + 1 + (Data.unaryList vs).length := by
  rw [ppUl_cons, List.length_append, List.length_append, List.length_replicate, List.length_singleton]

theorem ppUl_mem : ∀ (vs : List ℕ) (v : ℕ), v ∈ vs → v ≤ (Data.unaryList vs).length
  | [], _, h => by simp at h
  | a :: vs, v, h => by
    rw [ppUl_len]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ppUl_mem vs v h'
      omega

theorem ppUl_getD : ∀ (vs : List ℕ) (k : ℕ), vs.getD k 0 ≤ (Data.unaryList vs).length
  | [], k => by simp only [List.getD_nil]; exact Nat.zero_le _
  | a :: vs, 0 => by rw [ppUl_len, List.getD_cons_zero]; omega
  | a :: vs, k + 1 => by
    rw [ppUl_len, List.getD_cons_succ]
    have := ppUl_getD vs k
    omega

section Prep
variable {ns nr : ℕ} (cap : ℕ) (i o : Fin (ns + 1)) (Rp : Fin 30 ↪ Fin nr)

theorem ppv_ne (σ : WState ns nr) (r q : Fin nr) (x : ℕ) (h : q ≠ r) : (σ.setv r x).val q = σ.val q := by
  simp [Function.update_of_ne h]

theorem ppv_eq (σ : WState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).val r = x := by simp

/-- The small numbers' registers `Rp 0 … Rp 15`. -/
def ppRs : List (Fin nr) := List.ofFn fun k : Fin 16 => Rp ⟨k.val, by omega⟩

theorem ppRs_len : (ppRs Rp).length = 16 := by simp [ppRs]

theorem ppRs_get (k : Fin 16) :
    (ppRs Rp).get ⟨k.val, by rw [ppRs_len]; exact k.isLt⟩ = Rp ⟨k.val, by omega⟩ := by
  simp only [ppRs, List.get_eq_getElem, List.getElem_ofFn]

theorem ppRs_mem (q : Fin nr) (hq : q ∈ ppRs Rp) : ∃ k : Fin 16, q = Rp ⟨k.val, by omega⟩ := by
  rw [ppRs, List.mem_ofFn] at hq
  obtain ⟨k, hk⟩ := hq
  exact ⟨k, hk.symm⟩

theorem ppRs_mem' (k : Fin 16) : Rp ⟨k.val, by omega⟩ ∈ ppRs Rp := by
  rw [ppRs, List.mem_ofFn]
  exact ⟨k, rfl⟩

theorem ppRs_nodup : (ppRs Rp).Nodup := by
  rw [ppRs, List.nodup_ofFn]
  intro a b h
  exact Fin.ext (by have := congrArg Fin.val (Rp.injective h); simpa using this)

/-- Read the small numbers into `Rp 0 … 15` (the counter `Rp 16`), the word rewound. -/
def prepR : WM ns nr := .seq (readList i (Rp 16) (ppRs Rp)) (WM.rewind i (Rp 16))

theorem prepR_spec (vs : List ℕ) (hvl : vs.length = 16) (σ : WState ns nr)
    (hst : σ.st i = Data.unaryList vs) (hsh : σ.sh i = 0) (hz : ∀ k : Fin 30, σ.val (Rp k) = 0)
    (hc : (Data.unaryList vs).length ≤ cap) :
    ∃ σ2 : WState ns nr, WExec cap (prepR i Rp) σ σ2 (11 * (Data.unaryList vs).length + 1 +
        (5 * (Data.unaryList vs).length + 1)) ∧ σ2.st = σ.st ∧ σ2.sh = σ.sh ∧
      (∀ k : Fin 16, σ2.val (Rp ⟨k.val, by omega⟩) = vs.getD k.val 0) ∧
      (∀ q, (∀ k : Fin 16, q ≠ Rp ⟨k.val, by omega⟩) → σ2.val q = σ.val q) ∧ σ2.cell = σ.cell := by
  have hcr : ∀ r ∈ ppRs Rp, r ≠ Rp 16 := fun r hr => by
    obtain ⟨k, rfl⟩ := ppRs_mem Rp r hr
    intro h
    have := congrArg Fin.val (Rp.injective h)
    simp at this
    omega
  obtain ⟨σ1, e1, s1, h1, c1, v1, o1, l1⟩ := readList_spec cap i (Rp 16) (ppRs Rp) vs σ [] []
    (by rw [ppRs_len, hvl]) hcr (ppRs_nodup Rp)
    (fun r hr => by obtain ⟨k, rfl⟩ := ppRs_mem Rp r hr; exact hz _)
    (by rw [hst]; simp) (by rw [hsh]; rfl)
    (by rw [hz 16]; omega) (fun v hv => le_trans (ppUl_mem vs v hv) hc)
  have e2 := wrewind_spec cap i (Rp 16) (Data.unaryList vs).length σ1 (by rw [c1, hz 16]; omega)
    (by rw [c1, hz 16]; omega)
  refine ⟨_, WExec.seq e1 e2, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s1]
  · funext j
    by_cases hj : j = i
    · rw [hj]; simp [h1, hsh]
    · simp [h1, Function.update_of_ne hj]
  · intro k
    have hk16 : Rp ⟨k.val, by omega⟩ ≠ Rp 16 := hcr _ (ppRs_mem' Rp k)
    have := v1 ⟨k.val, by rw [ppRs_len]; exact k.isLt⟩
    rw [ppRs_get] at this
    simp [Function.update_of_ne hk16, this]
  · intro q hq
    by_cases hqc : q = Rp 16
    · rw [hqc]; simp [hz 16]
    · have hqr : q ∉ ppRs Rp := fun hm => by
        obtain ⟨k, hk⟩ := ppRs_mem Rp q hm
        exact hq k hk
      simp [Function.update_of_ne hqc, o1 q hqc hqr]
  · simp [l1]

/-- `mulAddW`'s registers: `(vs₃, vs₁, Rp 17, Rp 19, Rp 20)`. -/
def ppC : Fin 5 ↪ Fin 30 := ⟨![3, 1, 17, 19, 20], by decide⟩
/-- `pow2W`'s registers: `(vs₁₁, Rp 18, Rp 19, Rp 20)`. -/
def ppP : Fin 4 ↪ Fin 30 := ⟨![11, 18, 19, 20], by decide⟩
/-- `reqWM`'s registers: `n = Rp 17`, scratch `Rp 21 … 29`, the fields `vs₁₃, vs₁₄, vs₁₅, vs₉, vs₁₀`, `nE = Rp 18`. -/
def ppW : Fin 16 ↪ Fin 30 := ⟨![17, 21, 22, 23, 24, 25, 26, 27, 28, 29, 13, 14, 15, 9, 10, 18], by decide⟩

theorem ppW_hi : ∀ k : Fin 16, 1 ≤ k.val → k.val ≤ 9 → 21 ≤ (ppW k).val := by decide

/-- **The prep**: the small numbers read, `n` and `2^{seed width}` computed, the tables writer's request written. -/
def prepWM : WM ns nr :=
  .seq (prepR i Rp) (.seq (Hash4.wcopyR (Rp 6) (Rp 17) (Rp 19)) (.seq (UnaryArith.mulAddW (ppC.trans Rp))
    (.seq (UnaryArith.mulAddW (ppC.trans Rp)) (.seq (UnaryArith.pow2W (ppP.trans Rp)) (reqWM o (ppW.trans Rp))))))

/-- `vs₆ + vs₃·vs₁ + vs₃·vs₁` (at `s4Small2`: `(n − rb) + 2·(r/2)·b = n`). -/
def ppN (vs : List ℕ) : ℕ := vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0 + vs.getD 3 0 * vs.getD 1 0

/-- The tables writer's request at the small numbers `vs`. -/
def ppReq (vs : List ℕ) : List Bool :=
  TabW.reqT (ppN vs) (vs.getD 13 0) (vs.getD 14 0) (vs.getD 15 0) (vs.getD 9 0) (vs.getD 10 0) (2 ^ vs.getD 11 0)

/-- The prep's step bound. -/
def prepCost (vs : List ℕ) : ℕ :=
  16 * (Data.unaryList vs).length + 2 + (18 * vs.getD 6 0 + 3) +
    2 * (vs.getD 1 0 * (18 * vs.getD 3 0 + 8) + 18 * vs.getD 1 0 + 10) +
    (vs.getD 11 0 * (18 * 2 ^ vs.getD 11 0 + 7) + 18 * vs.getD 11 0 + 20) + reqCost (ppN vs) (ppReq vs).length + 10

theorem prepWM_spec (vs : List ℕ) (hvl : vs.length = 16) (σ : WState ns nr)
    (hst : σ.st i = Data.unaryList vs) (hsh : σ.sh i = 0) (hso : σ.st o = []) (hsho : σ.sh o = 0)
    (hz : ∀ k : Fin 30, σ.val (Rp k) = 0)
    (hc : (Data.unaryList vs).length + ppN vs + 2 ^ (vs.getD 11 0 + 1) + 4 * (ppReq vs).length + 10 ≤ cap) :
    ∃ σ' : WState ns nr, ∃ m, WExec cap (prepWM i o Rp) σ σ' m ∧ m ≤ prepCost vs ∧
      σ'.st = Function.update σ.st o (frame (ppReq vs)) ∧ σ'.sh = σ.sh ∧
      (∀ k : Fin 16, σ'.val (Rp ⟨k.val, by omega⟩) = vs.getD k.val 0) ∧
      σ'.val (Rp 17) = ppN vs ∧ σ'.val (Rp 18) = 2 ^ vs.getD 11 0 ∧
      (∀ q, (∀ k : Fin 16, q ≠ Rp ⟨k.val, by omega⟩) → q ≠ Rp 17 → q ≠ Rp 18 → σ'.val q = σ.val q) ∧
      σ'.cell = σ.cell := by
  have d : ∀ a b : Fin 30, a ≠ b → Rp a ≠ Rp b := fun a b h => Rp.injective.ne h
  have hv : ∀ k : ℕ, vs.getD k 0 ≤ (Data.unaryList vs).length := ppUl_getD vs
  have hN : ppN vs = vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0 + vs.getD 3 0 * vs.getD 1 0 := rfl
  have hQ : ppReq vs = TabW.reqT (ppN vs) (vs.getD 13 0) (vs.getD 14 0) (vs.getD 15 0) (vs.getD 9 0)
      (vs.getD 10 0) (2 ^ vs.getD 11 0) := rfl
  generalize hP : 2 ^ (vs.getD 11 0 + 1) = P at hc
  obtain ⟨σ2, e1, s2, h2, v2, o2, l2⟩ := prepR_spec cap i Rp vs hvl σ hst hsh hz (by omega)
  have g2 : ∀ j : Fin 30, 16 ≤ j.val → σ2.val (Rp j) = 0 := fun j hj => by
    rw [o2 _ (fun k h => by
      have := congrArg Fin.val (Rp.injective h)
      simp at this
      omega), hz]
  have hR1 : σ2.val (Rp 1) = vs.getD 1 0 := v2 ⟨1, by decide⟩
  have hR3 : σ2.val (Rp 3) = vs.getD 3 0 := v2 ⟨3, by decide⟩
  have hR6 : σ2.val (Rp 6) = vs.getD 6 0 := v2 ⟨6, by decide⟩
  have hR9 : σ2.val (Rp 9) = vs.getD 9 0 := v2 ⟨9, by decide⟩
  have hR10 : σ2.val (Rp 10) = vs.getD 10 0 := v2 ⟨10, by decide⟩
  have hR11 : σ2.val (Rp 11) = vs.getD 11 0 := v2 ⟨11, by decide⟩
  have hR13 : σ2.val (Rp 13) = vs.getD 13 0 := v2 ⟨13, by decide⟩
  have hR14 : σ2.val (Rp 14) = vs.getD 14 0 := v2 ⟨14, by decide⟩
  have hR15 : σ2.val (Rp 15) = vs.getD 15 0 := v2 ⟨15, by decide⟩
  have h1 := hv 1
  have h3 := hv 3
  have h6 := hv 6
  -- Rp 17 := vs₆
  have e2 := Hash4.wcopyR_spec cap (Rp 6) (Rp 17) (Rp 19) (d 6 17 (by decide)) (d 6 19 (by decide))
    (d 17 19 (by decide)) σ2 (g2 17 (by decide)) (g2 19 (by decide)) (by rw [hR6]; omega)
  rw [hR6] at e2
  -- Rp 17 += vs₃·vs₁, twice
  have e3 := UnaryArith.mulAddW_spec cap (ppC.trans Rp) (σ2.setv (Rp 17) (vs.getD 6 0))
    (by show (σ2.setv (Rp 17) (vs.getD 6 0)).val (Rp 19) = 0
        rw [ppv_ne _ _ _ _ (d 19 17 (by decide)), g2 19 (by decide)])
    (by show (σ2.setv (Rp 17) (vs.getD 6 0)).val (Rp 20) = 0
        rw [ppv_ne _ _ _ _ (d 20 17 (by decide)), g2 20 (by decide)])
    (by show (σ2.setv (Rp 17) (vs.getD 6 0)).val (Rp 1) ≤ cap
        rw [ppv_ne _ _ _ _ (d 1 17 (by decide)), hR1]; omega)
    (by show (σ2.setv (Rp 17) (vs.getD 6 0)).val (Rp 17) +
          (σ2.setv (Rp 17) (vs.getD 6 0)).val (Rp 3) * (σ2.setv (Rp 17) (vs.getD 6 0)).val (Rp 1) ≤ cap
        rw [ppv_eq, ppv_ne _ _ _ _ (d 3 17 (by decide)), ppv_ne _ _ _ _ (d 1 17 (by decide)), hR3, hR1]; omega)
    (by show (σ2.setv (Rp 17) (vs.getD 6 0)).val (Rp 3) ≤ cap
        rw [ppv_ne _ _ _ _ (d 3 17 (by decide)), hR3]; omega)
  rw [show (ppC.trans Rp) 2 = Rp 17 from rfl, show (ppC.trans Rp) 0 = Rp 3 from rfl,
    show (ppC.trans Rp) 1 = Rp 1 from rfl, ppv_eq, ppv_ne _ _ _ _ (d 3 17 (by decide)),
    ppv_ne _ _ _ _ (d 1 17 (by decide)), hR3, hR1, wsetv_setv] at e3
  have e4 := UnaryArith.mulAddW_spec cap (ppC.trans Rp)
    (σ2.setv (Rp 17) (vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0))
    (by show (σ2.setv (Rp 17) (vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0)).val (Rp 19) = 0
        rw [ppv_ne _ _ _ _ (d 19 17 (by decide)), g2 19 (by decide)])
    (by show (σ2.setv (Rp 17) (vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0)).val (Rp 20) = 0
        rw [ppv_ne _ _ _ _ (d 20 17 (by decide)), g2 20 (by decide)])
    (by show (σ2.setv (Rp 17) (vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0)).val (Rp 1) ≤ cap
        rw [ppv_ne _ _ _ _ (d 1 17 (by decide)), hR1]; omega)
    (by show (σ2.setv (Rp 17) (vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0)).val (Rp 17) +
          (σ2.setv (Rp 17) (vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0)).val (Rp 3) *
          (σ2.setv (Rp 17) (vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0)).val (Rp 1) ≤ cap
        rw [ppv_eq, ppv_ne _ _ _ _ (d 3 17 (by decide)), ppv_ne _ _ _ _ (d 1 17 (by decide)), hR3, hR1]; omega)
    (by show (σ2.setv (Rp 17) (vs.getD 6 0 + vs.getD 3 0 * vs.getD 1 0)).val (Rp 3) ≤ cap
        rw [ppv_ne _ _ _ _ (d 3 17 (by decide)), hR3]; omega)
  rw [show (ppC.trans Rp) 2 = Rp 17 from rfl, show (ppC.trans Rp) 0 = Rp 3 from rfl,
    show (ppC.trans Rp) 1 = Rp 1 from rfl, ppv_eq, ppv_ne _ _ _ _ (d 3 17 (by decide)),
    ppv_ne _ _ _ _ (d 1 17 (by decide)), hR3, hR1, wsetv_setv, ← hN] at e4
  -- Rp 18 := 2^{vs₁₁}
  have e5 := UnaryArith.pow2W_spec cap (ppP.trans Rp) (σ2.setv (Rp 17) (ppN vs))
    (by show (σ2.setv (Rp 17) (ppN vs)).val (Rp 18) = 0
        rw [ppv_ne _ _ _ _ (d 18 17 (by decide)), g2 18 (by decide)])
    (by show (σ2.setv (Rp 17) (ppN vs)).val (Rp 19) = 0
        rw [ppv_ne _ _ _ _ (d 19 17 (by decide)), g2 19 (by decide)])
    (by show (σ2.setv (Rp 17) (ppN vs)).val (Rp 20) = 0
        rw [ppv_ne _ _ _ _ (d 20 17 (by decide)), g2 20 (by decide)])
    (by show 2 ^ ((σ2.setv (Rp 17) (ppN vs)).val (Rp 11) + 1) ≤ cap
        rw [ppv_ne _ _ _ _ (d 11 17 (by decide)), hR11, hP]; omega)
  rw [show (ppP.trans Rp) 1 = Rp 18 from rfl, show (ppP.trans Rp) 0 = Rp 11 from rfl,
    ppv_ne _ _ _ _ (d 11 17 (by decide)), hR11] at e5
  -- the request
  obtain ⟨τ, hτ⟩ : ∃ y : WState ns nr, y = (σ2.setv (Rp 17) (ppN vs)).setv (Rp 18) (2 ^ vs.getD 11 0) :=
    ⟨_, rfl⟩
  rw [← hτ] at e5
  have tv : ∀ q, q ≠ Rp 17 → q ≠ Rp 18 → τ.val q = σ2.val q := fun q h17 h18 => by
    rw [hτ, ppv_ne _ _ _ _ h18, ppv_ne _ _ _ _ h17]
  obtain ⟨m6, e6, hm6⟩ := reqWM_spec cap o (ppW.trans Rp) (ppN vs) (vs.getD 13 0) (vs.getD 14 0) (vs.getD 15 0)
    (vs.getD 9 0) (vs.getD 10 0) (2 ^ vs.getD 11 0) τ (by rw [hτ]; simp [s2, hso]) (by rw [hτ]; simp [h2, hsho])
    (fun k hk1 hk9 => by
      have hk := ppW_hi k hk1 hk9
      have n17 : ppW k ≠ 17 := fun h => by rw [h] at hk; revert hk; decide
      have n18 : ppW k ≠ 18 := fun h => by rw [h] at hk; revert hk; decide
      show τ.val (Rp (ppW k)) = 0
      rw [tv _ (d _ _ n17) (d _ _ n18), g2 _ (by omega)])
    (by show τ.val (Rp 17) = ppN vs
        rw [hτ, ppv_ne _ _ _ _ (d 17 18 (by decide)), ppv_eq])
    (by show τ.val (Rp 13) = vs.getD 13 0
        rw [tv _ (d 13 17 (by decide)) (d 13 18 (by decide)), hR13])
    (by show τ.val (Rp 14) = vs.getD 14 0
        rw [tv _ (d 14 17 (by decide)) (d 14 18 (by decide)), hR14])
    (by show τ.val (Rp 15) = vs.getD 15 0
        rw [tv _ (d 15 17 (by decide)) (d 15 18 (by decide)), hR15])
    (by show τ.val (Rp 9) = vs.getD 9 0
        rw [tv _ (d 9 17 (by decide)) (d 9 18 (by decide)), hR9])
    (by show τ.val (Rp 10) = vs.getD 10 0
        rw [tv _ (d 10 17 (by decide)) (d 10 18 (by decide)), hR10])
    (by show τ.val (Rp 18) = 2 ^ vs.getD 11 0
        rw [hτ, ppv_eq])
    (by rw [← hQ]; omega)
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6)))), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← hQ] at hm6
    unfold prepCost
    omega
  · rw [hQ, hτ]
    simp [s2]
  · rw [hτ]
    simp [h2]
  · intro k
    have h17 : Rp ⟨k.val, by omega⟩ ≠ Rp 17 := d _ _ (fun h => by
      have := congrArg Fin.val h
      simp at this
      omega)
    have h18 : Rp ⟨k.val, by omega⟩ ≠ Rp 18 := d _ _ (fun h => by
      have := congrArg Fin.val h
      simp at this
      omega)
    show τ.val (Rp ⟨k.val, by omega⟩) = vs.getD k.val 0
    rw [tv _ h17 h18, v2 k]
  · show τ.val (Rp 17) = ppN vs
    rw [hτ, ppv_ne _ _ _ _ (d 17 18 (by decide)), ppv_eq]
  · show τ.val (Rp 18) = 2 ^ vs.getD 11 0
    rw [hτ, ppv_eq]
  · intro q hq h17 h18
    show τ.val q = σ.val q
    rw [tv q h17 h18, o2 q hq]
  · show τ.cell = σ.cell
    rw [hτ]
    simp [l2]

end Prep

end NearCubicWires.WireExponent3_5.FinalPass.Sd
