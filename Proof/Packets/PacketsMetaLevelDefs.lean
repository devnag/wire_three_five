import Proof.Packets.PacketsMetaBody

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

namespace Lev

/-- One circuit's data: its arity and its retained top children. -/
abbrev CD := Σ n : ℕ, List (ExactThresholdGate n)

/-- The circuit payload (a `topWord` frame's content). -/
def pay (e : CD) : List Bool := natWord e.1 ++ exactListWord e.2

/-- The record table. -/
def tab (e : CD) : List Rec := e.2.map childRec

/-- Marks of a stream. -/
def mk (w : List Bool) : ℕ → Bool := sf (List.replicate w.length true)

/-- The loop state. -/
structure GS where
  pos : Fin 4 → ℕ
  na : Fin 4 → ℕ
  kk : Fin 4 → ℕ
  ra : Fin 4 → ℕ
  ru : Fin 4 → ℕ
  rv : Fin 4 → ℕ
  f : ℕ
  cnt : ℕ
  fl : Bool

/-- The role map during the loops. -/
def Gv (fx : Fin 60 → TS) (d : Fin 4 → CD) (g : GS) : Fin 60 → TS :=
  ![fx 0, fx 1, fx 2, fx 3, .flag g.fl, fx 5,
    .cells blank 0, fx 7, fx 8, fx 9, fx 10, .cells (sf (pay (d 0))) (g.pos 0),
    .cells (mk (pay (d 0))) (g.pos 0), .cells (sf (pay (d 1))) (g.pos 1), .cells (mk (pay (d 1))) (g.pos 1), .cells (sf (pay (d 2))) (g.pos 2), .cells (mk (pay (d 2))) (g.pos 2), .cells (sf (pay (d 3))) (g.pos 3),
    .cells (mk (pay (d 3))) (g.pos 3), .reg (g.na 0), .reg (g.na 1), .reg (g.na 2), .reg (g.na 3), .reg (g.kk 0),
    .reg (g.kk 1), .reg (g.kk 2), .reg (g.kk 3), .reg 0, .reg 0, .reg (g.ra 0),
    .reg (g.ra 1), .reg (g.ra 2), .reg (g.ra 3), .reg (g.ru 0), .reg (g.ru 1), .reg (g.ru 2),
    .reg (g.ru 3), .reg (g.rv 0), .reg (g.rv 1), .reg (g.rv 2), .reg (g.rv 3), .reg 0,
    .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0,
    .reg g.f, .reg g.cnt, fx 50, fx 51, fx 52, fx 53,
    fx 54, fx 55, fx 56, fx 57, fx 58, fx 59]

/-! ## Slots -/

def sS (c : Fin 4) : Fin 60 := ⟨11 + 2 * c.val, by omega⟩
def sM (c : Fin 4) : Fin 60 := ⟨12 + 2 * c.val, by omega⟩
def sN (c : Fin 4) : Fin 60 := ⟨19 + c.val, by omega⟩
def sK (c : Fin 4) : Fin 60 := ⟨23 + c.val, by omega⟩
def sA (c : Fin 4) : Fin 60 := ⟨29 + c.val, by omega⟩
def sP (c : Fin 4) : Fin 60 := ⟨33 + c.val, by omega⟩
def sQ (c : Fin 4) : Fin 60 := ⟨37 + c.val, by omega⟩

/-! ## Reading the role map -/

section Read
variable (fx : Fin 60 → TS) (d : Fin 4 → CD) (g : GS) (c : Fin 4)
theorem Gv_S : Gv fx d g (sS c) = .cells (sf (pay (d c))) (g.pos c) := by fin_cases c <;> rfl
theorem Gv_M : Gv fx d g (sM c) = .cells (mk (pay (d c))) (g.pos c) := by fin_cases c <;> rfl
theorem Gv_N : Gv fx d g (sN c) = .reg (g.na c) := by fin_cases c <;> rfl
theorem Gv_K : Gv fx d g (sK c) = .reg (g.kk c) := by fin_cases c <;> rfl
theorem Gv_A : Gv fx d g (sA c) = .reg (g.ra c) := by fin_cases c <;> rfl
theorem Gv_P : Gv fx d g (sP c) = .reg (g.ru c) := by fin_cases c <;> rfl
theorem Gv_Q : Gv fx d g (sQ c) = .reg (g.rv c) := by fin_cases c <;> rfl
end Read

/-! ## Updating the role map -/

section Upd
variable (fx : Fin 60 → TS) (d : Fin 4 → CD) (g : GS) (c : Fin 4)

theorem up_fl (b : Bool) : Function.update (Gv fx d g) 4 (.flag b) = Gv fx d { g with fl := b } := by
  funext i; fin_cases i <;> rfl
theorem up_K (v : ℕ) : Function.update (Gv fx d g) (sK c) (.reg v) = Gv fx d { g with kk := Function.update g.kk c v } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem up_N (v : ℕ) : Function.update (Gv fx d g) (sN c) (.reg v) = Gv fx d { g with na := Function.update g.na c v } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem up_A (v : ℕ) : Function.update (Gv fx d g) (sA c) (.reg v) = Gv fx d { g with ra := Function.update g.ra c v } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem up_P (v : ℕ) : Function.update (Gv fx d g) (sP c) (.reg v) = Gv fx d { g with ru := Function.update g.ru c v } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem up_Q (v : ℕ) : Function.update (Gv fx d g) (sQ c) (.reg v) = Gv fx d { g with rv := Function.update g.rv c v } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem up_SM (v : ℕ) : Function.update (Function.update (Gv fx d g) (sS c) (.cells (sf (pay (d c))) v))
    (sM c) (.cells (mk (pay (d c))) v) = Gv fx d { g with pos := Function.update g.pos c v } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
theorem up_F (v : ℕ) : Function.update (Gv fx d g) 48 (.reg v) = Gv fx d { g with f := v } := by
  funext i; fin_cases i <;> rfl
theorem up_C (v : ℕ) : Function.update (Gv fx d g) 49 (.reg v) = Gv fx d { g with cnt := v } := by
  funext i; fin_cases i <;> rfl
theorem up_zo (h5 : fx 5 = .reg 0) : Function.update (Gv fx d g) 5 (.reg 0) = Gv fx d g := by
  funext i; fin_cases i <;> first | rfl | exact h5.symm
theorem up_kw : Function.update (Gv fx d g) 27 (.reg 0) = Gv fx d g := by
  funext i; fin_cases i <;> rfl
theorem up_x : Function.update (Gv fx d g) 28 (.reg 0) = Gv fx d g := by
  funext i; fin_cases i <;> rfl
end Upd

end Lev

end
end NearCubicWires.PacketsMeta

