import Proof.Wire_3_5.Primitive.Writers.SBFieldA
import Proof.Wire_3_5.Primitive.Writers.SBTau
import Proof.Wire_3_5.Primitive.Writers.ModFull
import Proof.Wire_3_5.Primitive.Writers.DockW
import Proof.Wire_3_5.Filters.GFExists

/-! # SB, part 8: the field phase (S4's words `4` and `5`)

S4's words `4`, `5` are the filter field's trace mask and modulus (`Filt.tauWord FP`, `Filt.modWord FP`: `ℓ`-bit frames
of `GF2.tau p ℓ` and `p = GF.firstPrimitive ℓ`, `ℓ = FP.fieldBits`; P3:2053-2055, 2932-2941). On `23` blank streams
`Fs` and `16` registers `Rb` (`Rb 0 = ℓ`, the rest `0`) of any word layout, the phase

1. writes `1^ℓ` (`copyOnesW`), 2. docks the modulus machine (`Modulus.modM`, `modulus_full`; its answer tape `12` on
`Fs 1`, its other tapes on `Fs 2 … 17`), 3. writes six zero words (`zerosW`: `Fs 0`, `Fs 18 … 22`), 4. runs T's
trace mask program (`tauW`, `SBTau.tauW_spec2`: mask on `Fs 0`, modulus `Fs 1`, work words `Fs 18 … 22`), 5. erases
`Fs 2 … 22` to `0^{4ℓ+6}` (`boundW`, `eraseList`), 6. clears its registers:

* `mIdx`, `mMap`, `smOf`, `rgOf`, `zeroL`, `eraseL`; `w1`, `m2`, `w3`, **`fieldM`**, `fieldCost`;
* **`field_step`**: `Fs 0 = frame (binary ℓ (GF2.tau p ℓ))`, `Fs 1 = frame (binary ℓ p)`, `Fs j = 0^{4ℓ+6}` (`j ≥ 2`),
  every head of `Fs` at `0`, every `Rb` at `0`, the cell and everything outside `Fs`, `Rb` unchanged.

Paper quantity of the main type: the field words `τ` and the modulus (S4's words `4`, `5`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBField
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SBWords
open NearCubicWires.WireExponent3_5.PrimAsm.SBFieldA NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-! ## The layout -/

/-- The modulus machine's tape `j` on the phase's stream index (`12 ↦ 1`, the rest on `2 … 17`). -/
def mIdx (j : Fin 17) : Fin 23 :=
  ⟨if j.val = 12 then 1 else if j.val < 12 then j.val + 2 else j.val + 1, by split_ifs <;> omega⟩

theorem mIdx_val (j : Fin 17) : (mIdx j).val = if j.val = 12 then 1 else if j.val < 12 then j.val + 2 else j.val + 1 :=
  rfl

theorem mIdx_inj : Function.Injective mIdx := by
  intro a b h
  have := congrArg Fin.val h
  simp only [mIdx_val] at this
  apply Fin.ext
  split_ifs at this <;> omega

theorem mIdx_of (k : Fin 23) (h2 : 2 ≤ k.val) (h17 : k.val ≤ 17) :
    mIdx ⟨if k.val ≤ 13 then k.val - 2 else k.val - 1, by split_ifs <;> omega⟩ = k := by
  apply Fin.ext
  simp only [mIdx_val]
  split_ifs <;> omega

section Layout
variable {ns nr : ℕ} (Fs : Fin 23 ↪ Fin (ns + 1)) (Rb : Fin 16 ↪ Fin nr)

def mMap (j : Fin 17) : Fin (ns + 1) := Fs (mIdx j)

theorem mMap_inj : Function.Injective (mMap Fs) := fun a b h => mIdx_inj (Fs.injective h)

/-- The trace program's streams: modulus `Fs 1`, mask `Fs 0`, work words `Fs 18 … 22`. -/
def smIdx : Fin 7 → Fin 23 := ![1, 0, 18, 19, 20, 21, 22]

theorem smIdx_inj : Function.Injective smIdx := by decide

def smOf : Fin 7 ↪ Fin (ns + 1) := ⟨fun j => Fs (smIdx j), fun a b h => smIdx_inj (Fs.injective h)⟩

/-- The trace program's registers `Rb 7 … 15`. -/
def rgOf : Fin 9 ↪ Fin nr := ⟨fun j => Rb ⟨7 + j.val, by omega⟩, fun a b h => by
  have := congrArg Fin.val (Rb.injective h); exact Fin.ext (by simp at this; omega)⟩

def zeroL : List (Fin (ns + 1)) := [Fs 0, Fs 18, Fs 19, Fs 20, Fs 21, Fs 22]

def eraseL : List (Fin (ns + 1)) := ((List.finRange 23).filter fun k => 2 ≤ k.val).map Fs

theorem mem_eraseL (i : Fin (ns + 1)) : i ∈ eraseL Fs ↔ ∃ k : Fin 23, 2 ≤ k.val ∧ Fs k = i := by
  simp [eraseL]

end Layout

/-! ## The program -/

section Prog
variable {ns nr : ℕ} (Fs : Fin 23 ↪ Fin (ns + 1)) (Rb : Fin 16 ↪ Fin nr)

def w1 : WM ns nr := copyOnesW (Fs 2) (Rb 0) (Rb 1) (Rb 3) (Rb 2)

noncomputable def m2 := RecoveryFocus.machine (fun j => sTape (nr := nr) (mMap Fs j)) Modulus.modM

def w3 : WM ns nr :=
  .seq (zerosW (Rb 0) (Rb 1) (Rb 3) (Rb 2) (zeroL Fs))
    (.seq (.seq (FinalPass.Hash4.wcopyR (Rb 0) (rgOf Rb 4) (Rb 3)) (PrimT.tauW (smOf Fs) (rgOf Rb)))
      (.seq (boundW (Rb 0) (Rb 1) (Rb 3) (Rb 4))
        (.seq (eraseList (Rb 4) (Rb 5) (Rb 6) (Rb 3) (eraseL Fs))
          (.seq (WM.clear (Rb 4)) (.seq (WM.clear (Rb 0)) (WM.clear (rgOf Rb 4)))))))

/-- **The field phase.** -/
noncomputable def fieldM := Composition.machine (Composition.machine (w1 Fs Rb).toProg.compile (m2 Fs))
  (w3 Fs Rb).toProg.compile

end Prog

def w3Cost (cap ℓ : ℕ) (l : List ℕ) : ℕ :=
  zerosCost cap ℓ 6 + 1 + ((UnaryPow.sq cap + 1 + PrimT.tauCost ℓ) + 1 +
    ((UnaryPow.sq cap + 1 + (UnaryPow.sq cap + 1 + (19 * ℓ + 1 + 1 + UnaryPow.sq cap))) + 1 +
      (eraseListCost cap (4 * ℓ + 6) l + 1 + ((3 * (4 * ℓ + 6) + 1) + 1 + ((3 * ℓ + 1) + 1 + (3 * ℓ + 1))))))

/-- The phase's cost (`eraseListCost` over the `21` erased streams). -/
def fieldCost (cap ℓ : ℕ) (l : List ℕ) : ℕ :=
  (UnaryPow.sq cap + 1 + (16 * ℓ + 3)) + 1 + Modulus.modCost ℓ + 1 + w3Cost cap ℓ l

end NearCubicWires.WireExponent3_5.PrimAsm.SBField
