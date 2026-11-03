import Platform.RecLoop
import Platform.BinW

set_option autoImplicit false

namespace NearCubicGates.Close.Platform
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

/-- `τ` agrees with `σ` outside the streams `S` and the registers `Rg`. -/
def SameExcept (σ τ : WState ns nr) (S : List (Fin (ns + 1))) (Rg : List (Fin nr)) : Prop :=
  (∀ x, x ∉ S → τ.st x = σ.st x ∧ τ.sh x = σ.sh x) ∧ (∀ r, r ∉ Rg → τ.val r = σ.val r) ∧ τ.cell = σ.cell

theorem SameExcept.refl (σ : WState ns nr) (S : List (Fin (ns + 1))) (Rg : List (Fin nr)) : SameExcept σ σ S Rg :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl⟩

theorem SameExcept.trans {σ τ ρ : WState ns nr} {S : List (Fin (ns + 1))} {Rg : List (Fin nr)}
    (h1 : SameExcept σ τ S Rg) (h2 : SameExcept τ ρ S Rg) : SameExcept σ ρ S Rg :=
  ⟨fun x hx => ⟨(h2.1 x hx).1.trans (h1.1 x hx).1, (h2.1 x hx).2.trans (h1.1 x hx).2⟩,
    fun r hr => (h2.2.1 r hr).trans (h1.2.1 r hr), h2.2.2.trans h1.2.2⟩

/-! Programs are opaque to consumers: use the spec theorems. -/

end NearCubicGates.Close.Platform
