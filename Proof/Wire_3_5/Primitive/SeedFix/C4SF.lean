import Proof.Wire_3_5.Primitive.SeedFix.C4SE

/-! # C4 per-call setup (item 3), part 6: the SYM stage's words and the free numbers' interface

C4Dock's entry words (`C4Arm.Nums`'s ten rulers, the seventeen constants `kc` but the batch and the modulus, the
loop counter `word (8ℓ)`), SampStage's inputs (`1^{kh}`, `1^Q`, `1^ℓ`), the modulus search's `1^ℓ` (twice), the C3
request writer's numbers (`1^h`, `1^{Q'}`, `1^m`, `1^{pr}`), the printer child's `1^{Q'}`, and the CapReader sources of
`2^{2·dRow}` and `2^ρ`, as thirty-nine words on the streams `120 … 159` (P3:3011-3016, 2929-2941, 1886-1906).

* `FreeIn`, `FreeRegs`, **`FreeProg`** (the free numbers `TWd, Cap, Q', h, m, pr, ρ`: C4.K's program);
* `SymRegs` (the registers before the words), `opR`, **`symEmits`**, `symEmits_ok`, **`symEmits_val`**.

Paper quantities of the main types: the enumeration's rulers and constants, the generator's inputs, the compiler
request's numbers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-! ## The free numbers -/

/-- The numbers the free program may read. -/
structure FreeIn where
  n : ℕ
  kh : ℕ
  L : ℕ
  capS : ℕ
  a : ℕ
  nc : ℕ
  M : ℕ
  Q : ℕ
  ell : ℕ
  nT : ℕ
  w : ℕ
  dRow : ℕ

/-- Their registers. -/
def FreeRegs (σ : WState (LNS 0) LNR) (x : FreeIn) : Prop :=
  σ.val dN = x.n ∧ σ.val (SGb 8) = x.kh ∧ σ.val (SGb 1) = x.L ∧ σ.val (Hb 13) = x.capS ∧ σ.val dA = x.a ∧
    σ.val dNC = x.nc ∧ σ.val dMS = x.M ∧ σ.val (KB 52) = x.Q ∧ σ.val (X 2) = x.ell ∧ σ.val (N 0) = x.nT ∧
    σ.val (WB 0) = x.w ∧ σ.val (ST 0) = x.dRow

/-- **The free numbers' program** (C4.K's choice): `TWd, Cap, Q', h, m, pr, ρ` into `FB 0 … 6`, from the setup's
numbers, on the scratch `177 … 199` (zero at entry), every other register and the streams unchanged. -/
structure FreeProg where
  prog : WM (LNS 0) LNR
  val : FreeIn → Fin 7 → ℕ
  cost : ℕ → FreeIn → ℕ
  ok : ℕ → FreeIn → Prop
  run : ∀ (cap : ℕ) (σ : WState (LNS 0) LNR) (x : FreeIn), FreeRegs σ x →
    (∀ q : Fin LNR, 130 ≤ q.val → q.val < 137 → σ.val q = 0) → (∀ q : Fin LNR, 177 ≤ q.val → q.val < 200 → σ.val q = 0) →
    ok cap x → ∃ τ, WExec cap prog σ τ (cost cap x) ∧ (∀ j, τ.val (FB j) = val x j) ∧
      (∀ q : Fin LNR, (q.val < 130 ∨ (137 ≤ q.val ∧ q.val < 177) ∨ 200 ≤ q.val) → τ.val q = σ.val q) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell

/-! ## The words -/

/-- The registers before the words. -/
structure SymRegs (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) : Prop where
  x0 : σ.val (X 0) = kh + kh
  x2 : σ.val (X 2) = ell
  k8 : σ.val (SGb 8) = kh
  q : σ.val (KB 52) = Q
  cc : σ.val (CC 0) = cnt
  r2 : σ.val rD2 = d2
  fb : ∀ j, σ.val (FB j) = fr j
  dd : ∀ i, σ.val (DD i) = dd i
  rb0 : σ.val (RB 0) = Q - 1
  rb4 : σ.val (RB 4) = ell
  rb1 : σ.val (RB 1) = 0
  rb2 : σ.val (RB 2) = 0
  rb3 : σ.val (RB 3) = 0
  rb5 : σ.val (RB 5) = 0
  rb6 : σ.val (RB 6) = 0

/-- **The SYM stage's words.** -/
def symEmits : List Emit1 :=
  [⟨sk 0 120, ⟨200, by decide⟩, none, [Part.r (X 2) [true]]⟩,
  ⟨sk 0 121, ⟨201, by decide⟩, none, [Part.r (SGb 8) [true]]⟩,
  ⟨sk 0 122, ⟨202, by decide⟩, none, [Part.r (FB 0) [true]]⟩,
  ⟨sk 0 123, ⟨203, by decide⟩, none, [Part.r (FB 1) [true]]⟩,
  ⟨sk 0 124, ⟨204, by decide⟩, none, [Part.r (X 0) [true]]⟩,
  ⟨sk 0 125, ⟨205, by decide⟩, none, [Part.r (DD 0) [true]]⟩,
  ⟨sk 0 126, ⟨206, by decide⟩, none, [Part.r (DD 1) [true]]⟩,
  ⟨sk 0 127, ⟨207, by decide⟩, none, [Part.r (DD 2) [true]]⟩,
  ⟨sk 0 128, ⟨208, by decide⟩, none, [Part.r (DD 3) [true]]⟩,
  ⟨sk 0 129, ⟨209, by decide⟩, none, [Part.r (DD 4) [true]]⟩,
  ⟨sk 0 130, ⟨210, by decide⟩, none, [Part.c [false]]⟩,
  ⟨sk 0 131, ⟨211, by decide⟩, some RB, [Part.c [false]]⟩,
  ⟨sk 0 132, ⟨212, by decide⟩, none, [Part.c [true]]⟩,
  ⟨sk 0 133, ⟨213, by decide⟩, none, [Part.c (Streaming.marks (List.replicate 8 true) ++ [false])]⟩,
  ⟨sk 0 135, ⟨214, by decide⟩, none, [Part.c (List.replicate 8 true ++ [false])]⟩,
  ⟨sk 0 136, ⟨215, by decide⟩, none, [Part.r (X 2) [true], Part.c [false]]⟩,
  ⟨sk 0 137, ⟨216, by decide⟩, none, [Part.r (SGb 8) [true], Part.c [false]]⟩,
  ⟨sk 0 138, ⟨217, by decide⟩, none, [Part.c [true, false]]⟩,
  ⟨sk 0 139, ⟨218, by decide⟩, none, [Part.c (List.replicate 7 true ++ [false])]⟩,
  ⟨sk 0 140, ⟨219, by decide⟩, none, [Part.r (X 0) [true], Part.c [false]]⟩,
  ⟨sk 0 141, ⟨220, by decide⟩, none, [Part.c [false]]⟩,
  ⟨sk 0 142, ⟨221, by decide⟩, none, [Part.c [false]]⟩,
  ⟨sk 0 143, ⟨222, by decide⟩, none, [Part.c [true, true], Part.r (DD 6) [true, false], Part.c [false]]⟩,
  ⟨sk 0 144, ⟨223, by decide⟩, none, [Part.c [true, false]]⟩,
  ⟨sk 0 145, ⟨224, by decide⟩, none, [Part.r (FB 0) [true], Part.c [false]]⟩,
  ⟨sk 0 146, ⟨225, by decide⟩, none, [Part.c [false], Part.r (CC 0) [true]]⟩,
  ⟨sk 0 147, ⟨226, by decide⟩, none, [Part.r (FB 2) [true]]⟩,
  ⟨sk 0 148, ⟨227, by decide⟩, none, [Part.c [false], Part.r (DD 4) [true]]⟩,
  ⟨sk 0 149, ⟨228, by decide⟩, none, [Part.r (SGb 8) [true]]⟩,
  ⟨sk 0 150, ⟨229, by decide⟩, none, [Part.r (KB 52) [true]]⟩,
  ⟨sk 0 151, ⟨230, by decide⟩, none, [Part.r (X 2) [true]]⟩,
  ⟨sk 0 152, ⟨231, by decide⟩, none, [Part.r (X 2) [true]]⟩,
  ⟨sk 0 153, ⟨232, by decide⟩, none, [Part.r (X 2) [true]]⟩,
  ⟨sk 0 154, ⟨233, by decide⟩, none, [Part.r (FB 3) [true]]⟩,
  ⟨sk 0 155, ⟨234, by decide⟩, none, [Part.r (FB 2) [true]]⟩,
  ⟨sk 0 156, ⟨235, by decide⟩, none, [Part.r (FB 4) [true]]⟩,
  ⟨sk 0 157, ⟨236, by decide⟩, none, [Part.r (FB 5) [true]]⟩,
  ⟨sk 0 158, ⟨237, by decide⟩, none, [Part.c [true], Part.r rD2 [true], Part.c [false], Part.r rD2 [false], Part.c [true]]⟩,
  ⟨sk 0 159, ⟨238, by decide⟩, none, [Part.c [true], Part.r (FB 6) [true], Part.c [false], Part.r (FB 6) [false], Part.c [true]]⟩]


theorem reps_len (n : ℕ) (u : List Bool) : (FiltRec.reps n u).length = n * u.length := by unfold FiltRec.reps; simp

theorem fw_len (w v : ℕ) : (WilliamsPublishedForm.fixedWidthNatBits w v).length = w := by
  simp [WilliamsPublishedForm.fixedWidthNatBits]

/-- **The words' admissibility** at the state before them. -/
theorem symEmits_ok (cap : ℕ) (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)
    (h : SymRegs σ Q kh ell cnt d2 fr dd)
    (hst : ∀ k : Fin 161, 120 ≤ k.val → σ.st (sk 0 k) = []) (hsh : ∀ k : Fin 161, 120 ≤ k.val → σ.sh (sk 0 k) = 0)
    (hop : ∀ q : Fin LNR, 200 ≤ q.val → q.val < 240 → σ.val q = 0)
    (cQl : Q - 1 < 2 ^ ell) (cQ : Q + 1 ≤ cap) (cl : 3 * ell + Q + 3 ≤ cap) (ck : kh + kh + 1 ≤ cap)
    (cfr : ∀ j, fr j + fr j + 3 ≤ cap) (cdd : ∀ i, dd i + dd i + 3 ≤ cap) (cc : cnt + 1 ≤ cap) (cd2 : d2 + d2 + 3 ≤ cap) (c17 : 17 ≤ cap) :
    ∀ e ∈ symEmits, WordOK cap σ e := by
  have cf0 := cfr 0; have cf1 := cfr 1; have cf2 := cfr 2; have cf3 := cfr 3; have cf4 := cfr 4; have cf5 := cfr 5
  have cf6 := cfr 6
  have cd0 := cdd 0; have cd1 := cdd 1; have cd2' := cdd 2; have cd3 := cdd 3; have cd4 := cdd 4; have cd5 := cdd 5
  have cd6 := cdd 6
  have hps_0 : ∀ p ∈ ([Part.r (X 2) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_1 : ∀ p ∈ ([Part.r (SGb 8) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_2 : ∀ p ∈ ([Part.r (FB 0) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_3 : ∀ p ∈ ([Part.r (FB 1) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_4 : ∀ p ∈ ([Part.r (X 0) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_5 : ∀ p ∈ ([Part.r (DD 0) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_6 : ∀ p ∈ ([Part.r (DD 1) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_7 : ∀ p ∈ ([Part.r (DD 2) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_8 : ∀ p ∈ ([Part.r (DD 3) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_9 : ∀ p ∈ ([Part.r (DD 4) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_10 : ∀ p ∈ ([Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_11 : ∀ p ∈ ([Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_12 : ∀ p ∈ ([Part.c [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_13 : ∀ p ∈ ([Part.c (Streaming.marks (List.replicate 8 true) ++ [false])] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_14 : ∀ p ∈ ([Part.c (List.replicate 8 true ++ [false])] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_15 : ∀ p ∈ ([Part.r (X 2) [true], Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_16 : ∀ p ∈ ([Part.r (SGb 8) [true], Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_17 : ∀ p ∈ ([Part.c [true, false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_18 : ∀ p ∈ ([Part.c (List.replicate 7 true ++ [false])] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_19 : ∀ p ∈ ([Part.r (X 0) [true], Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_20 : ∀ p ∈ ([Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_21 : ∀ p ∈ ([Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_22 : ∀ p ∈ ([Part.c [true, true], Part.r (DD 6) [true, false], Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_23 : ∀ p ∈ ([Part.c [true, false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_24 : ∀ p ∈ ([Part.r (FB 0) [true], Part.c [false]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_25 : ∀ p ∈ ([Part.c [false], Part.r (CC 0) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_26 : ∀ p ∈ ([Part.r (FB 2) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_27 : ∀ p ∈ ([Part.c [false], Part.r (DD 4) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_28 : ∀ p ∈ ([Part.r (SGb 8) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_29 : ∀ p ∈ ([Part.r (KB 52) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_30 : ∀ p ∈ ([Part.r (X 2) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_31 : ∀ p ∈ ([Part.r (X 2) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_32 : ∀ p ∈ ([Part.r (X 2) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_33 : ∀ p ∈ ([Part.r (FB 3) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_34 : ∀ p ∈ ([Part.r (FB 2) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_35 : ∀ p ∈ ([Part.r (FB 4) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_36 : ∀ p ∈ ([Part.r (FB 5) [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_37 : ∀ p ∈ ([Part.c [true], Part.r rD2 [true], Part.c [false], Part.r rD2 [false], Part.c [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  have hps_38 : ∀ p ∈ ([Part.c [true], Part.r (FB 6) [true], Part.c [false], Part.r (FB 6) [false], Part.c [true]] : List Part), ∀ A u, p = .r A u → IsRd A ∧ σ.val A ≤ cap := by
    intro p hp A u hpA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only [Part.r.injEq, reduceCtorEq] at hpA <;>
      (obtain ⟨rfl, rfl⟩ := hpA; exact ⟨by unfold IsRd; decide, by simp only [h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd]; omega⟩)
  intro e he
  simp only [symEmits, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_0, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_1, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_2, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_3, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_4, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_5, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_6, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_7, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_8, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_9, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_10, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_11, ⟨rfl, by unfold IsRd; decide, h.rb1, h.rb2, h.rb3, h.rb5, h.rb6, by rw [h.rb0, h.rb4]; exact cQl, by rw [h.rb0, h.rb4]; omega⟩, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_12, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_13, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_14, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_15, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_16, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_17, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_18, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_19, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_20, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_21, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_22, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_23, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_24, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_25, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_26, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_27, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_28, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_29, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_30, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_31, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_32, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_33, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_34, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_35, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_36, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_37, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩
  · exact ⟨hst _ (by decide), hsh _ (by decide), by unfold IsOP; decide, hop _ (by decide) (by decide), hps_38, trivial, by simp only [symEmits, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.length_append, reps_len, Streaming.marks_length, fw_len, List.length_cons, List.length_nil, List.length_replicate, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4]; omega⟩

theorem reps_one (m : ℕ) (b : Bool) : FiltRec.reps m [b] = List.replicate m b := by
  induction m with
  | zero => rfl
  | succ m ih => rw [FiltRec.reps_succ, ih, List.replicate_succ']

theorem symEmits_O_nodup : (symEmits.map (·.O)).Nodup := by decide

theorem symEmits_OP_nodup : (symEmits.map (·.OP)).Nodup := by decide

theorem symEmits_length : symEmits.length = 39 := rfl

theorem symW0 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨0, by decide⟩).O = sk 0 120 ∧ wordVal σ (symEmits.get ⟨0, by decide⟩) = List.replicate ell true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW1 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨1, by decide⟩).O = sk 0 121 ∧ wordVal σ (symEmits.get ⟨1, by decide⟩) = List.replicate kh true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW2 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨2, by decide⟩).O = sk 0 122 ∧ wordVal σ (symEmits.get ⟨2, by decide⟩) = List.replicate (fr 0) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW3 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨3, by decide⟩).O = sk 0 123 ∧ wordVal σ (symEmits.get ⟨3, by decide⟩) = List.replicate (fr 1) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW4 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨4, by decide⟩).O = sk 0 124 ∧ wordVal σ (symEmits.get ⟨4, by decide⟩) = List.replicate (kh + kh) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW5 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨5, by decide⟩).O = sk 0 125 ∧ wordVal σ (symEmits.get ⟨5, by decide⟩) = List.replicate (dd 0) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW6 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨6, by decide⟩).O = sk 0 126 ∧ wordVal σ (symEmits.get ⟨6, by decide⟩) = List.replicate (dd 1) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW7 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨7, by decide⟩).O = sk 0 127 ∧ wordVal σ (symEmits.get ⟨7, by decide⟩) = List.replicate (dd 2) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW8 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨8, by decide⟩).O = sk 0 128 ∧ wordVal σ (symEmits.get ⟨8, by decide⟩) = List.replicate (dd 3) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW9 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨9, by decide⟩).O = sk 0 129 ∧ wordVal σ (symEmits.get ⟨9, by decide⟩) = List.replicate (dd 4) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW10 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨10, by decide⟩).O = sk 0 130 ∧ wordVal σ (symEmits.get ⟨10, by decide⟩) = [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW11 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨11, by decide⟩).O = sk 0 131 ∧ wordVal σ (symEmits.get ⟨11, by decide⟩) = Streaming.marks (WilliamsPublishedForm.fixedWidthNatBits ell (Q - 1)) ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW12 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨12, by decide⟩).O = sk 0 132 ∧ wordVal σ (symEmits.get ⟨12, by decide⟩) = [true] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW13 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨13, by decide⟩).O = sk 0 133 ∧ wordVal σ (symEmits.get ⟨13, by decide⟩) = Streaming.marks (List.replicate 8 true) ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW14 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨14, by decide⟩).O = sk 0 135 ∧ wordVal σ (symEmits.get ⟨14, by decide⟩) = List.replicate 8 true ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW15 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨15, by decide⟩).O = sk 0 136 ∧ wordVal σ (symEmits.get ⟨15, by decide⟩) = List.replicate ell true ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW16 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨16, by decide⟩).O = sk 0 137 ∧ wordVal σ (symEmits.get ⟨16, by decide⟩) = List.replicate kh true ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW17 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨17, by decide⟩).O = sk 0 138 ∧ wordVal σ (symEmits.get ⟨17, by decide⟩) = [true, false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW18 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨18, by decide⟩).O = sk 0 139 ∧ wordVal σ (symEmits.get ⟨18, by decide⟩) = List.replicate 7 true ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW19 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨19, by decide⟩).O = sk 0 140 ∧ wordVal σ (symEmits.get ⟨19, by decide⟩) = List.replicate (kh + kh) true ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW20 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨20, by decide⟩).O = sk 0 141 ∧ wordVal σ (symEmits.get ⟨20, by decide⟩) = [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW21 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨21, by decide⟩).O = sk 0 142 ∧ wordVal σ (symEmits.get ⟨21, by decide⟩) = [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW22 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨22, by decide⟩).O = sk 0 143 ∧ wordVal σ (symEmits.get ⟨22, by decide⟩) = [true, true] ++ FiltRec.reps (dd 6) [true, false] ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW23 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨23, by decide⟩).O = sk 0 144 ∧ wordVal σ (symEmits.get ⟨23, by decide⟩) = [true, false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW24 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨24, by decide⟩).O = sk 0 145 ∧ wordVal σ (symEmits.get ⟨24, by decide⟩) = List.replicate (fr 0) true ++ [false] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW25 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨25, by decide⟩).O = sk 0 146 ∧ wordVal σ (symEmits.get ⟨25, by decide⟩) = [false] ++ List.replicate cnt true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW26 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨26, by decide⟩).O = sk 0 147 ∧ wordVal σ (symEmits.get ⟨26, by decide⟩) = List.replicate (fr 2) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW27 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨27, by decide⟩).O = sk 0 148 ∧ wordVal σ (symEmits.get ⟨27, by decide⟩) = [false] ++ List.replicate (dd 4) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW28 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨28, by decide⟩).O = sk 0 149 ∧ wordVal σ (symEmits.get ⟨28, by decide⟩) = List.replicate kh true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW29 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨29, by decide⟩).O = sk 0 150 ∧ wordVal σ (symEmits.get ⟨29, by decide⟩) = List.replicate Q true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW30 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨30, by decide⟩).O = sk 0 151 ∧ wordVal σ (symEmits.get ⟨30, by decide⟩) = List.replicate ell true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW31 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨31, by decide⟩).O = sk 0 152 ∧ wordVal σ (symEmits.get ⟨31, by decide⟩) = List.replicate ell true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW32 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨32, by decide⟩).O = sk 0 153 ∧ wordVal σ (symEmits.get ⟨32, by decide⟩) = List.replicate ell true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW33 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨33, by decide⟩).O = sk 0 154 ∧ wordVal σ (symEmits.get ⟨33, by decide⟩) = List.replicate (fr 3) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW34 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨34, by decide⟩).O = sk 0 155 ∧ wordVal σ (symEmits.get ⟨34, by decide⟩) = List.replicate (fr 2) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW35 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨35, by decide⟩).O = sk 0 156 ∧ wordVal σ (symEmits.get ⟨35, by decide⟩) = List.replicate (fr 4) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW36 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨36, by decide⟩).O = sk 0 157 ∧ wordVal σ (symEmits.get ⟨36, by decide⟩) = List.replicate (fr 5) true := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW37 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨37, by decide⟩).O = sk 0 158 ∧ wordVal σ (symEmits.get ⟨37, by decide⟩) = [true] ++ List.replicate d2 true ++ [false] ++ List.replicate d2 false ++ [true] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]

theorem symW38 (σ : WState (LNS 0) LNR) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) (h : SymRegs σ Q kh ell cnt d2 fr dd) :
    (symEmits.get ⟨38, by decide⟩).O = sk 0 159 ∧ wordVal σ (symEmits.get ⟨38, by decide⟩) = [true] ++ List.replicate (fr 6) true ++ [false] ++ List.replicate (fr 6) false ++ [true] := by
  refine ⟨rfl, ?_⟩
  simp only [symEmits, List.get, wordVal, headVal, partVal, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, reps_one, h.x2, h.k8, h.x0, h.q, h.cc, h.r2, h.fb, h.dd, h.rb0, h.rb4, List.append_assoc]
end NearCubicWires.WireExponent3_5.PrimT.C4Set
