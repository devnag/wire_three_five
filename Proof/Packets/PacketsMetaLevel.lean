import Proof.Packets.PacketsMetaLevelDefs

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.PacketsMeta.CutoffMath
noncomputable section

/-! ## The child parser at ambient slots -/

theorem Child.at_run {N W : ℕ} (σ : Fin N → TS) (r s m u na kw x a p q f o : Fin N)
    (hi : Function.Injective ![r, s, m, u, na, kw, x, a, p, q, f, o]) (fS fM : ℕ → Bool) (cr : ℕ) {n : ℕ}
    (G : ExactThresholdGate n)
    (hS : ∀ k, k < (exactWord G).length → fS (cr + k) = (exactWord G).getD k false)
    (hn : n < 2 ^ W) (hA : (childRec G).1 < 2 ^ W)
    (hbits : ∀ j (hj : j < n), natBitLength ((Child.ws G)[j]'(by rw [Child.ws_length]; exact hj)).natAbs ≤ W)
    (hT : natBitLength G.target.natAbs ≤ W) (kv xv av pv qv : ℕ) (b : Bool)
    (hr : σ r = .ruler) (hs : σ s = .cells fS cr) (hm : σ m = .cells fM cr) (hu : σ u = .cells blank 0)
    (hna : σ na = .reg n) (hkw : σ kw = .reg kv) (hx : σ x = .reg xv) (ha : σ a = .reg av) (hp : σ p = .reg pv)
    (hq : σ q = .reg qv) (hf : σ f = .flag b) (ho : σ o = .reg 0) :
    LRuns W (RecoveryFocus.machine ![r, s, m, u, na, kw, x, a, p, q, f, o] Child.machine) ((n + 3) * (10 * W + 30)) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update σ s (.cells fS (cr + (exactWord G).length)))
          m (.cells fM (cr + (exactWord G).length))) kw (.reg 0)) x (.reg 0)) a (.reg (childRec G).1))
          p (.reg (childRec G).2.1)) q (.reg (childRec G).2.2)) f (.flag false)) := by
  have h := (Child.childRun W fS fM cr G hS hn hA hbits hT kv xv av pv qv b).dockK
    ![r, s, m, u, na, kw, x, a, p, q, f, o] hi σ
    (by intro j; fin_cases j
        · exact hr
        · exact hs
        · exact hm
        · exact hu
        · exact hna
        · exact hkw
        · exact hx
        · exact ha
        · exact hp
        · exact hq
        · exact hf
        · exact ho) [10, 9, 8, 7, 6, 5, 2, 1]
    (by intro j hj; fin_cases j <;> simp [Child.cst] at hj ⊢)
  exact h

namespace Lev

/-! ## The level's states -/

section States
variable (d : Fin 4 → CD) (c : Fin 4)

/-- The cursor after the two headers. -/
def h0 (e : CD) : ℕ := 1 + (natWord e.1).length + (natWord e.2.length).length
/-- The cursor before child `i`. -/
def cur (e : CD) (i : ℕ) : ℕ := h0 e + ((e.2.take i).flatMap exactWord).length

def hdrS (g : GS) : GS :=
  { g with
    pos := Function.update g.pos c (h0 (d c)), na := Function.update g.na c (d c).1,
    kk := Function.update g.kk c (d c).2.length }
def decS (g : GS) : GS := { g with kk := Function.update g.kk c (g.kk c - 1), fl := false }
def chS {n : ℕ} (G : ExactThresholdGate n) (g : GS) : GS :=
  { g with
    pos := Function.update g.pos c (g.pos c + (exactWord G).length),
    ra := Function.update g.ra c (childRec G).1, ru := Function.update g.ru c (childRec G).2.1,
    rv := Function.update g.rv c (childRec G).2.2, fl := false }
def stepS (innerS : GS → GS) (g : GS) (G : ExactThresholdGate (d c).1) : GS := innerS (chS c G (decS c g))
/-- The state after the first `i` children. -/
def stI (innerS : GS → GS) (g : GS) (i : ℕ) : GS := ((d c).2.take i).foldl (stepS d c innerS) (hdrS d c g)
/-- **The level's exact result.** -/
def levS (innerS : GS → GS) (g : GS) : GS := { stI d c innerS g (d c).2.length with fl := false }

end States

/-! ## The level machine -/

def childSlots (c : Fin 4) : Fin 12 → Fin 60 := ![3, sS c, sM c, 6, sN c, 27, 28, sA c, sP c, sQ c, 4, 5]

def lev (c : Fin 4) {si : ℕ} (inner : Machine 60 si) :=
  Composition.machine
    (Composition.machine (RecoveryFocus.machine ![sM c, sS c] rewind)
      (Composition.machine (ReadNat.at5 3 (sS c) (sM c) 6 (sN c)) (ReadNat.at5 3 (sS c) (sM c) 6 (sK c))))
    (Loop (swAt subF false false 3 5 (sK c) 4)
      (Composition.machine (swAt subF true true 3 (sK c) 5 4)
        (Composition.machine (RecoveryFocus.machine (childSlots c) Child.machine) inner))
      4)

/-! ## Instructions of a level, in `Gv` form -/

section Instr
variable {W : ℕ} (fx : Fin 60 → TS) (d : Fin 4 → CD) (c : Fin 4)

theorem Gv_3 (hfx3 : fx 3 = .ruler) (g : GS) : Gv fx d g 3 = .ruler := hfx3
theorem Gv_5 (hfx5 : fx 5 = .reg 0) (g : GS) : Gv fx d g 5 = .reg 0 := hfx5

theorem lv_rewind (g : GS) (hp1 : 1 ≤ g.pos c) (hp2 : g.pos c ≤ (pay (d c)).length + 1) :
    LRuns W (RecoveryFocus.machine ![sM c, sS c] rewind) ((pay (d c)).length + 5) (Gv fx d g)
      (Gv fx d { g with pos := Function.update g.pos c 1 }) := by
  have h := (rewind_lruns W (pay (d c)).length (g.pos c) (sf (pay (d c))) hp1 hp2).dockK ![sM c, sS c]
    (by fin_cases c <;> decide) (Gv fx d g)
    (by intro j; fin_cases j
        · exact Gv_M fx d g c
        · exact Gv_S fx d g c) [0, 1]
    (by intro j hj; fin_cases j <;> simp at hj)
  refine (h.congr_out ?_).enlarge (by omega)
  rw [← up_SM]
  rfl

theorem lv_readN (hfx3 : fx 3 = .ruler) (g : GS) (x : ℕ) (hW : natBitLength x ≤ W)
    (hS : ∀ k, k < (natWord x).length → sf (pay (d c)) (g.pos c + k) = (natWord x).getD k false) :
    LRuns W (ReadNat.at5 3 (sS c) (sM c) 6 (sN c)) (3 * W + 5) (Gv fx d g)
      (Gv fx d { g with pos := Function.update g.pos c (g.pos c + (natWord x).length),
                        na := Function.update g.na c x }) := by
  have h := ReadNat.at_run (W := W) (Gv fx d g) 3 (sS c) (sM c) 6 (sN c) (by fin_cases c <;> decide) (g.pos c) x
    (g.na c) (sf (pay (d c))) (mk (pay (d c))) hW hS (Gv_3 fx d hfx3 g) (Gv_S fx d g c) (Gv_M fx d g c) rfl
    (Gv_N fx d g c)
  rw [up_SM, up_N] at h
  exact h

theorem lv_readK (hfx3 : fx 3 = .ruler) (g : GS) (x : ℕ) (hW : natBitLength x ≤ W)
    (hS : ∀ k, k < (natWord x).length → sf (pay (d c)) (g.pos c + k) = (natWord x).getD k false) :
    LRuns W (ReadNat.at5 3 (sS c) (sM c) 6 (sK c)) (3 * W + 5) (Gv fx d g)
      (Gv fx d { g with pos := Function.update g.pos c (g.pos c + (natWord x).length),
                        kk := Function.update g.kk c x }) := by
  have h := ReadNat.at_run (W := W) (Gv fx d g) 3 (sS c) (sM c) 6 (sK c) (by fin_cases c <;> decide) (g.pos c) x
    (g.kk c) (sf (pay (d c))) (mk (pay (d c))) hW hS (Gv_3 fx d hfx3 g) (Gv_S fx d g c) (Gv_M fx d g c) rfl
    (Gv_K fx d g c)
  rw [up_SM, up_K] at h
  exact h

theorem lv_test (hfx3 : fx 3 = .ruler) (hfx5 : fx 5 = .reg 0) (g : GS) (hk : g.kk c < 2 ^ W) :
    LRuns W (swAt subF false false 3 5 (sK c) 4) (2 * W + 3) (Gv fx d g)
      (Gv fx d { g with fl := decide (0 < g.kk c) }) := by
  have h := lt_at (W := W) (Gv fx d g) 3 5 (sK c) 4 (by fin_cases c <;> decide) 0 (g.kk c) g.fl
    (Gv_3 fx d hfx3 g) (Gv_5 fx d hfx5 g) (Gv_K fx d g c) rfl (Nat.two_pow_pos W) hk
  rw [up_zo fx d g hfx5, up_fl] at h
  exact h

theorem lv_dec (hfx3 : fx 3 = .ruler) (hfx5 : fx 5 = .reg 0) (g : GS) (hk : g.kk c < 2 ^ W) (h1 : 1 ≤ g.kk c) :
    LRuns W (swAt subF true true 3 (sK c) 5 4) (2 * W + 3) (Gv fx d g) (Gv fx d (decS c g)) := by
  have h := dec_at (W := W) (Gv fx d g) 3 (sK c) 5 4 (by fin_cases c <;> decide) (g.kk c) 0 g.fl
    (Gv_3 fx d hfx3 g) (Gv_K fx d g c) (Gv_5 fx d hfx5 g) rfl rfl hk h1
  rw [up_K, up_fl] at h
  exact h

theorem lv_child (hfx3 : fx 3 = .ruler) (hfx5 : fx 5 = .reg 0) (g : GS) (G : ExactThresholdGate (d c).1)
    (hS : ∀ k, k < (exactWord G).length → sf (pay (d c)) (g.pos c + k) = (exactWord G).getD k false)
    (hn : (d c).1 < 2 ^ W) (hA : (childRec G).1 < 2 ^ W)
    (hbits : ∀ j (hj : j < (d c).1), natBitLength ((Child.ws G)[j]'(by rw [Child.ws_length]; exact hj)).natAbs ≤ W)
    (hT : natBitLength G.target.natAbs ≤ W) (hna : g.na c = (d c).1) :
    LRuns W (RecoveryFocus.machine (childSlots c) Child.machine) (((d c).1 + 3) * (10 * W + 30)) (Gv fx d g)
      (Gv fx d (chS c G g)) := by
  have h := Child.at_run (W := W) (Gv fx d g) 3 (sS c) (sM c) 6 (sN c) 27 28 (sA c) (sP c) (sQ c) 4 5
    (by fin_cases c <;> decide) (sf (pay (d c))) (mk (pay (d c))) (g.pos c) G hS hn hA hbits hT 0 0 (g.ra c)
    (g.ru c) (g.rv c) g.fl (Gv_3 fx d hfx3 g) (Gv_S fx d g c) (Gv_M fx d g c) rfl
    (by rw [Gv_N, hna]) rfl rfl (Gv_A fx d g c) (Gv_P fx d g c) (Gv_Q fx d g c) rfl (Gv_5 fx d hfx5 g)
  rw [up_SM, up_kw, up_x, up_A, up_P, up_Q, up_fl] at h
  exact h

end Instr

end Lev

end
end NearCubicWires.PacketsMeta

