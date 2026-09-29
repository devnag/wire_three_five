import Proof.Wire_3_5.UnionMachine.FrontFoldStage

/-! # C6 front, U5, the writers' fold (b): the fold writes the codes and envelope bits

For a parsed guess `D` (`UnionCheckData`) the fold's data (**`foldOf D`**) are the PCPP variables, their
supports and their grid atoms. Its outputs are the table writer's sources (`FrontTW.TWRel`, `TWFlags`):
* **`pcs_get`**: the `X`-th parity code is `natWord (D.mode.code (D.parity X))` (P3:3092-3094), for check data whose
  parity atoms are the setup's (`D.parityOf = unionParityAtom D.mode D.q`);
* **`crs_get`**: the `X`-th carrier code is `natWord (Carrier.code (D.carrier X))` (P3:3409-3410, 3432-3433);
* **`efs_get`**: the `X`-th envelope bit is `envB deg (D.carrier X)`, which is `(D.carrier X).WithinEnvelope deg`
  (**`envB_iff`**, P3:3083-3094).

Paper quantity of the main types: the codes of the setup's parities, of the named carriers, and their envelope bits. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem
open NearCubicWires NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (carrierAtoms carrier_eq carrierOf)
open NearCubicWires.RepairRepresentation (natWord)

variable (D : UnionCheckData)

/-- The number of PCPP variables. -/
def nvOf : ℕ := D.pcpp.systematicBits + D.pcpp.auxiliaryBits

/-- **The fold's data of a parsed guess.** -/
def foldOf : FoldIn D.mode D.q where
  nv := nvOf D
  sys := D.pcpp.systematicBits
  supp := fun X => if h : X < nvOf D then D.support ⟨X, h⟩ else ∅
  atoms := fun X => if h : X < nvOf D then List.ofFn (D.atom ⟨X, h⟩) else []

/-- The envelope bit of a carrier at degree `deg`. -/
def envB (deg : ℕ) (c : Stars.Carrier D.q) : Bool :=
  decide (c.length ≤ (D.q + 1) ^ deg ∧ ∀ g ∈ c, g.encodingBits ≤ (D.q + 1) ^ deg)

theorem envB_iff (deg : ℕ) (c : Stars.Carrier D.q) : envB D deg c = true ↔ c.WithinEnvelope deg :=
  CWEnvSem.envelope_iff c deg

variable {D}

theorem par_eq (hp : D.parityOf = unionParityAtom D.mode D.q) (X : PcppVar D.pcpp) :
    (foldOf D).par X.val = D.parity X := by
  unfold FoldIn.par UnionCheckData.parity
  rw [hp]
  simp [foldOf, X.isLt, nvOf]

theorem cs_eq (hp : D.parityOf = unionParityAtom D.mode D.q) (X : PcppVar D.pcpp) :
    (foldOf D).cs X.val = carrierAtoms D X := by
  unfold FoldIn.cs carrierAtoms
  rw [par_eq hp X]
  have ha : (foldOf D).atoms X.val = List.ofFn (D.atom X) := by simp [foldOf, X.isLt, nvOf]
  rw [ha]
  simp [foldOf, UnionCheckData.sysBit]

theorem car_eq (hp : D.parityOf = unionParityAtom D.mode D.q) (X : PcppVar D.pcpp) :
    (foldOf D).car X.val = D.carrier X := by
  unfold FoldIn.car; rw [cs_eq hp X, carrier_eq]

/-- **The parity codes** are the setup's parity codes. -/
theorem pcs_get (hp : D.parityOf = unionParityAtom D.mode D.q) (X : PcppVar D.pcpp) :
    ((List.range (foldOf D).nv).map (foldOf D).pw).getD X.val [] = natWord (D.mode.code (D.parity X)) := by
  have hX : X.val < (foldOf D).nv := X.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hX]
  simp only [Option.map_some, Option.getD_some, FoldIn.pw]
  rw [par_eq hp X]

/-- **The carrier codes** are the named carriers' codes. -/
theorem crs_get (hp : D.parityOf = unionParityAtom D.mode D.q) (X : PcppVar D.pcpp) :
    ((List.range (foldOf D).nv).map (foldOf D).cw).getD X.val [] = natWord (Stars.Carrier.code (D.carrier X)) := by
  have hX : X.val < (foldOf D).nv := X.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hX]
  simp only [Option.map_some, Option.getD_some, FoldIn.cw]
  rw [car_eq hp X]

/-- **The envelope bits** are the named carriers' envelope bits. -/
theorem efs_get (hp : D.parityOf = unionParityAtom D.mode D.q) (deg : ℕ) (X : PcppVar D.pcpp) :
    ((List.range (foldOf D).nv).map ((foldOf D).eb deg)).getD X.val false = envB D deg (D.carrier X) := by
  have hX : X.val < (foldOf D).nv := X.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hX]
  simp only [Option.map_some, Option.getD_some, FoldIn.eb]
  rw [car_eq hp X]; rfl

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem
