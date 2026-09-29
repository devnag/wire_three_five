import Proof.Wire_3_5.Selection.GateSide

/-! # C1.4: the six key emitters on the gate layout (P3:1345-1356)

Paper: "For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities" (P3:1345-1346),
reduced by C1.1 to `2 + 2(V + 1)` `<`-joins. This module instantiates C1.4's emitters on the gate layout (`G`, `R`)
and discharges `EmitHyp` for each: the right point's two `Y` inner keys (`emYR`), the left point's `Y` query from its
upper or lower key (`emYLh`, `emYLl`), and the level-`ℓ` keys (`emK2` right inner, `emK1`, `emK3` left queries). The
emitters' environment is `EmEnv` (the level `ℓ`, the constants `V + 1`, `W − V − 2`, `W`, `W − 1`, `2V + 3`,
`W − 2V − 3`, the word `HT = 0`, the word `PW = 2^(ℓ+1)`). Paper quantity: a point's tagged keys for each join. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point

variable {ns nr : ℕ}

/-- **The emitters' environment** at level `ℓ`. -/
def EmEnv (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (W V ℓ : ℕ) (σ : WState ns nr) : Prop :=
  σ.val (R 19) = ℓ ∧ σ.val (R 20) = 0 ∧ σ.val (R 5) = V + 1 ∧ σ.val (R 21) = W - V - 2 ∧ σ.val (R 22) = 0 ∧
    σ.val (R 23) = W ∧ σ.val (R 24) = W - 1 ∧ σ.val (R 25) = 2 * V + 3 ∧ σ.val (R 26) = W - (2 * V + 3) ∧
    σ.val (R 6) = 0 ∧ σ.val (R 7) = 0 ∧ σ.val (R 30) = 0 ∧ NumOn σ (G 16) W 0 ∧ NumOn σ (G 17) W (2 ^ (ℓ + 1))

/-- The emitters' register map. -/
def EMr (R : Fin 48 → Fin nr) : Fin 16 → Fin nr := fun i => R (iEM i)

/-- The right `Y` emitter: both keys, tagged inner. -/
def emYR (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (k : Fin 28) (lo hi : Fin (ns + 1)) (Clo Chi : Fin nr) :
    WM ns nr :=
  .seq (EY true lo (G k) Clo (R 27) (R 24) (R 20)) (EY true hi (G k) Chi (R 27) (R 24) (R 20))

/-- The left `Y` emitter from the upper key (a query). -/
def emYLh (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (k : Fin 28) (_lo hi : Fin (ns + 1)) (_Clo Chi : Fin nr) :
    WM ns nr :=
  EY false hi (G k) Chi (R 27) (R 24) (R 20)

/-- The left `Y` emitter from the lower key (a query). -/
def emYLl (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (k : Fin 28) (lo _hi : Fin (ns + 1)) (Clo _Chi : Fin nr) :
    WM ns nr :=
  EY false lo (G k) Clo (R 27) (R 24) (R 20)

/-- The level emitters. -/
def emK1 (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (k : Fin 28) (lo hi : Fin (ns + 1)) (Clo Chi : Fin nr) :
    WM ns nr := EK1 (EMr R) lo hi (G k) Clo Chi

def emK2 (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (k : Fin 28) (lo hi : Fin (ns + 1)) (Clo Chi : Fin nr) :
    WM ns nr := EK2 (EMr R) lo hi (G k) Clo Chi

def emK3 (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (k : Fin 28) (lo hi : Fin (ns + 1)) (Clo _Chi : Fin nr) :
    WM ns nr := EK3 (EMr R) lo hi (G k) (G 16) (G 17) Clo (R 30)

/-- The keys' values. -/
def fYR (W : ℕ) (a b : ℕ) : List Bool := frame (binary W (2 * a + 1)) ++ frame (binary W (2 * b + 1))
def fYLh (W : ℕ) (_a b : ℕ) : List Bool := frame (binary W (2 * b))
def fYLl (W : ℕ) (a _b : ℕ) : List Bool := frame (binary W (2 * a))
def fK1 (W V ℓ : ℕ) (a b : ℕ) : List Bool :=
  frame (binary W (2 * (if b.testBit ℓ then b / 2 ^ (ℓ + 1) * 2 ^ (V + 1) + a else 0) + (false).toNat))
def fK2 (W V ℓ : ℕ) (a b : ℕ) : List Bool :=
  frame (binary W (2 * (if b.testBit ℓ then 2 ^ (2 * (V + 1)) - 1 else b / 2 ^ (ℓ + 1) * 2 ^ (V + 1) + a) + (true).toNat))
def fK3 (W V ℓ : ℕ) (_a b : ℕ) : List Bool :=
  frame (binary W (2 * (if b.testBit ℓ then (b / 2 ^ (ℓ + 1) + 1) * 2 ^ (V + 1) else 0) + (false).toNat))

section Hyps
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (cap W V ℓ : ℕ) (k : Fin 28) (hk : 18 ≤ k.val) (hk' : k.val ≤ 21)
variable (S : Fin 12 → Fin (ns + 1)) (hS6 : S 6 = G 10) (hS7 : S 7 = G 11)
include hG hR hk hk' hS6 hS7


theorem emYR_hyp (hW : 1 ≤ W) :
    EmitHyp cap W V S (G k) (R 27) (R 28) (R 29) (emYR G R k) (EmEnv G R W V ℓ) (fYR W) (2 * (60 * W + 30) + 1) := by
  intro σ L out vlo vhi lo hi Clo Chi hsel hc hlo hhi hClo hChi _ hvhi hcap
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  have hgk : ∀ a : Fin 28, a.val < 18 → G a ≠ G k := fun a ha => hG.ne (by intro h; rw [h] at ha; omega)
  have e24 : σ.val (R 24) = W' := by have := hc.2.2.2.2.2.2.1; simpa using this
  have e20 : σ.val (R 20) = 0 := hc.2.1
  rcases hsel with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [hS6] at hlo ⊢; rw [hS7] at hhi ⊢
    have x1 := EY_spec cap σ (A := G 10) (K := G k) (CA := R 28) (CK := R 27) (N := R 24) (T := R 20) L (hgk 10 (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
      (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) true W' vlo out hlo.1 hlo.2 hClo e24 e20
      (by omega) (by omega)
    have x2 := EY_spec cap σ (A := G 11) (K := G k) (CA := R 29) (CK := R 27) (N := R 24) (T := R 20) L (hgk 11 (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
      (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) true W' vhi
      (out ++ frame (binary (W' + 1) (2 * vlo + (true).toNat))) hhi.1 hhi.2 hChi e24 e20
      (by simp [frame_eq_frameP]; omega) (by omega)
    unfold emYR fYR
    refine WExec.cast cap (WExec.seq x1 x2) ?_ (by omega)
    simp [List.append_assoc]
  · rw [hS7] at hlo ⊢; rw [hS6] at hhi ⊢
    have x1 := EY_spec cap σ (A := G 11) (K := G k) (CA := R 29) (CK := R 27) (N := R 24) (T := R 20) L (hgk 11 (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
      (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) true W' vlo out hlo.1 hlo.2 hClo e24 e20
      (by omega) (by omega)
    have x2 := EY_spec cap σ (A := G 10) (K := G k) (CA := R 28) (CK := R 27) (N := R 24) (T := R 20) L (hgk 10 (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
      (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) true W' vhi
      (out ++ frame (binary (W' + 1) (2 * vlo + (true).toNat))) hhi.1 hhi.2 hChi e24 e20
      (by simp [frame_eq_frameP]; omega) (by omega)
    unfold emYR fYR
    refine WExec.cast cap (WExec.seq x1 x2) ?_ (by omega)
    simp [List.append_assoc]

theorem emYLh_hyp (hW : 1 ≤ W) :
    EmitHyp cap W V S (G k) (R 27) (R 28) (R 29) (emYLh G R k) (EmEnv G R W V ℓ) (fYLh W) (60 * W + 30) := by
  intro σ L out vlo vhi lo hi Clo Chi hsel hc hlo hhi hClo hChi _ hvhi hcap
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  have hgk : ∀ a : Fin 28, a.val < 18 → G a ≠ G k := fun a ha => hG.ne (by intro h; rw [h] at ha; omega)
  have e24 : σ.val (R 24) = W' := by have := hc.2.2.2.2.2.2.1; simpa using this
  have e20 : σ.val (R 20) = 0 := hc.2.1
  rcases hsel with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [hS7] at hhi ⊢
    have x := EY_spec cap σ (A := G 11) (K := G k) (CA := R 29) (CK := R 27) (N := R 24) (T := R 20) L
      (hgk 11 (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
      (hR.ne (by decide)) (hR.ne (by decide)) false W' vhi out hhi.1 hhi.2 hChi e24 e20 (by omega) (by omega)
    unfold emYLh fYLh
    refine WExec.cast cap x ?_ (by omega)
    simp
  · rw [hS6] at hhi ⊢
    have x := EY_spec cap σ (A := G 10) (K := G k) (CA := R 28) (CK := R 27) (N := R 24) (T := R 20) L
      (hgk 10 (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
      (hR.ne (by decide)) (hR.ne (by decide)) false W' vhi out hhi.1 hhi.2 hChi e24 e20 (by omega) (by omega)
    unfold emYLh fYLh
    refine WExec.cast cap x ?_ (by omega)
    simp

theorem emYLl_hyp (hW : 1 ≤ W) :
    EmitHyp cap W V S (G k) (R 27) (R 28) (R 29) (emYLl G R k) (EmEnv G R W V ℓ) (fYLl W) (60 * W + 30) := by
  intro σ L out vlo vhi lo hi Clo Chi hsel hc hlo hhi hClo hChi _ hvhi hcap
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  have hgk : ∀ a : Fin 28, a.val < 18 → G a ≠ G k := fun a ha => hG.ne (by intro h; rw [h] at ha; omega)
  have e24 : σ.val (R 24) = W' := by have := hc.2.2.2.2.2.2.1; simpa using this
  have e20 : σ.val (R 20) = 0 := hc.2.1
  rcases hsel with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [hS6] at hlo ⊢
    have x := EY_spec cap σ (A := G 10) (K := G k) (CA := R 28) (CK := R 27) (N := R 24) (T := R 20) L
      (hgk 10 (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
      (hR.ne (by decide)) (hR.ne (by decide)) false W' vlo out hlo.1 hlo.2 hClo e24 e20 (by omega) (by omega)
    unfold emYLl fYLl
    refine WExec.cast cap x ?_ (by omega)
    simp
  · rw [hS7] at hlo ⊢
    have x := EY_spec cap σ (A := G 11) (K := G k) (CA := R 29) (CK := R 27) (N := R 24) (T := R 20) L
      (hgk 11 (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
      (hR.ne (by decide)) (hR.ne (by decide)) false W' vlo out hlo.1 hlo.2 hClo e24 e20 (by omega) (by omega)
    unfold emYLl fYLl
    refine WExec.cast cap x ?_ (by omega)
    simp

theorem EMr_inj : Function.Injective (EMr R) := hR.comp iEM_inj

theorem EMr_ne (a : Fin 48) (ha : ∀ i, iEM i ≠ a) : ∀ i, EMr R i ≠ R a := fun i => hR.ne (ha i)

theorem emK1_hyp (hW : 2 * V + 3 ≤ W) (hℓ : ℓ ≤ V) :
    EmitHyp cap W V S (G k) (R 27) (R 28) (R 29) (emK1 G R k) (EmEnv G R W V ℓ) (fK1 W V ℓ) (200 * W + 200) := by
  intro σ L out vlo vhi lo hi Clo Chi hsel hc hlo hhi hClo hChi hle hvhi hcap
  have hgk : ∀ a : Fin 28, a.val < 18 → G a ≠ G k := fun a ha => hG.ne (by intro h; rw [h] at ha; omega)
  obtain ⟨c0, c1, c2, c3, c4, c5, -, -, -, -, -, -, -, -⟩ := hc
  rcases hsel with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [hS6] at hlo ⊢; rw [hS7] at hhi ⊢
    exact EK1_spec cap σ (EMr_inj G hG R hR k hk hk' S hS6 hS7) L (hG.ne (by decide)) (hgk 10 (by decide))
      (hgk 11 (by decide)) (hR.ne (by decide)) (EMr_ne G hG R hR k hk hk' S hS6 hS7 28 (by decide))
      (EMr_ne G hG R hR k hk hk' S hS6 hS7 29 (by decide)) W V ℓ vlo vhi out hW hℓ (by omega) hlo.1 hhi.1
      hlo.2 hhi.2 hClo hChi c0 c1 c2 c3 c4 c5 hcap
  · rw [hS7] at hlo ⊢; rw [hS6] at hhi ⊢
    exact EK1_spec cap σ (EMr_inj G hG R hR k hk hk' S hS6 hS7) L (hG.ne (by decide)) (hgk 11 (by decide))
      (hgk 10 (by decide)) (hR.ne (by decide)) (EMr_ne G hG R hR k hk hk' S hS6 hS7 29 (by decide))
      (EMr_ne G hG R hR k hk hk' S hS6 hS7 28 (by decide)) W V ℓ vlo vhi out hW hℓ (by omega) hlo.1 hhi.1
      hlo.2 hhi.2 hClo hChi c0 c1 c2 c3 c4 c5 hcap

theorem emK2_hyp (hW : 2 * V + 3 ≤ W) (hℓ : ℓ ≤ V) :
    EmitHyp cap W V S (G k) (R 27) (R 28) (R 29) (emK2 G R k) (EmEnv G R W V ℓ) (fK2 W V ℓ) (200 * W + 200) := by
  intro σ L out vlo vhi lo hi Clo Chi hsel hc hlo hhi hClo hChi hle hvhi hcap
  have hgk : ∀ a : Fin 28, a.val < 18 → G a ≠ G k := fun a ha => hG.ne (by intro h; rw [h] at ha; omega)
  obtain ⟨c0, c1, c2, c3, -, -, -, c7, c8, -, -, -, -, -⟩ := hc
  rcases hsel with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [hS6] at hlo ⊢; rw [hS7] at hhi ⊢
    exact EK2_spec cap σ (EMr_inj G hG R hR k hk hk' S hS6 hS7) L (hG.ne (by decide)) (hgk 10 (by decide))
      (hgk 11 (by decide)) (hR.ne (by decide)) (EMr_ne G hG R hR k hk hk' S hS6 hS7 28 (by decide))
      (EMr_ne G hG R hR k hk hk' S hS6 hS7 29 (by decide)) W V ℓ vlo vhi out hW hℓ (by omega) hlo.1 hhi.1
      hlo.2 hhi.2 hClo hChi c0 c1 c2 c3 c7 c8 hcap
  · rw [hS7] at hlo ⊢; rw [hS6] at hhi ⊢
    exact EK2_spec cap σ (EMr_inj G hG R hR k hk hk' S hS6 hS7) L (hG.ne (by decide)) (hgk 11 (by decide))
      (hgk 10 (by decide)) (hR.ne (by decide)) (EMr_ne G hG R hR k hk hk' S hS6 hS7 29 (by decide))
      (EMr_ne G hG R hR k hk hk' S hS6 hS7 28 (by decide)) W V ℓ vlo vhi out hW hℓ (by omega) hlo.1 hhi.1
      hlo.2 hhi.2 hClo hChi c0 c1 c2 c3 c7 c8 hcap

theorem emK3_hyp (hW : 2 * V + 3 ≤ W) (hℓ : ℓ ≤ V) :
    EmitHyp cap W V S (G k) (R 27) (R 28) (R 29) (emK3 G R k) (EmEnv G R W V ℓ) (fK3 W V ℓ) (400 * W + 300) := by
  intro σ L out vlo vhi lo hi Clo Chi hsel hc hlo hhi hClo hChi hle hvhi hcap
  have hgk : ∀ a : Fin 28, a.val < 18 → G a ≠ G k := fun a ha => hG.ne (by intro h; rw [h] at ha; omega)
  obtain ⟨c0, c1, c2, c3, c4, c5, -, -, -, c10, c11, c30, cHT, cPW⟩ := hc
  rcases hsel with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rw [hS6] at hlo ⊢; rw [hS7] at hhi ⊢
    exact EK3_spec cap σ (EMr_inj G hG R hR k hk hk' S hS6 hS7) L (hG.ne (by decide))
      (hgk 10 (by decide)) (hgk 16 (by decide)) (hG.ne (by decide)) (hG.ne (by decide)) (hgk 17 (by decide))
      (hgk 11 (by decide)) (hR.ne (by decide)) (EMr_ne G hG R hR k hk hk' S hS6 hS7 28 (by decide))
      (EMr_ne G hG R hR k hk hk' S hS6 hS7 30 (by decide)) W V ℓ vhi out hW hℓ hvhi hhi cHT cPW hlo.2 hClo
      c30 c0 c1 c2 c3 c4 c5 c10 c11 hcap
  · rw [hS7] at hlo ⊢; rw [hS6] at hhi ⊢
    exact EK3_spec cap σ (EMr_inj G hG R hR k hk hk' S hS6 hS7) L (hG.ne (by decide))
      (hgk 11 (by decide)) (hgk 16 (by decide)) (hG.ne (by decide)) (hG.ne (by decide)) (hgk 17 (by decide))
      (hgk 10 (by decide)) (hR.ne (by decide)) (EMr_ne G hG R hR k hk hk' S hS6 hS7 29 (by decide))
      (EMr_ne G hG R hR k hk hk' S hS6 hS7 30 (by decide)) W V ℓ vhi out hW hℓ hvhi hhi cHT cPW hlo.2 hClo
      c30 c0 c1 c2 c3 c4 c5 c10 c11 hcap

end Hyps

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
