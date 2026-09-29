import Proof.Wire_3_5.Primitive.SeedFix.C4H

/-! # C4HB: the Hb printer's cell and prep bounds at a HASH call (the contract)

`filt:soft`, P3:2262-2268 ("for each product and each `J_j`, the Gaussian-elimination machine counts [...]"), and
`alg:compiler`'s polynomial construction (P3:1887-1888). C4H's side conditions `HashEAt` (the reference one) ask, at every child
prefix, for the Hb printer's global conditions `HbOk`, its per-cell capacities `CellOk` and a cell-cost bound `Kc`,
and bound the child's steps through `hbPrepCost`. These are size bounds of the printer (the reference one). This file fixes their
shape against one size `hbS D` of the call's data:

* `hbS D`: the cell count `2^{2t+2tℓ₀}·(J+1)·|pops|·nE·N²`, `2^{2t+2tℓ₀}`, `2^{ℓ₀+1}`, the words the printer reads
  (`|htWord Fs|`, `|popsWord pops|`, `|wtWord (wsOf MP)|`), `G`, `N²`, `nE`;
* `CapsGe c b` / `CapsLe c v`: every one of the twelve capacities at least `b` / at most `v`;
* `DataOk D`: `1 ≤ t`, `N²·nE ≤ |Fs|`, every population gate `≤ G` (at a HASH call: `hashData_ok`);
* **`HbCellsBound`**: with `DataOk D`, `plen ≤ 2tℓ₀` and `CapsGe c (2^32·(hbS D + 1)^8)`: `HbOk` and, at every cell,
  `CellOk` and `cellCost ≤ 2^32·(hbS D + 1)^8`;
* **`HbPrepBound`**: with `plen ≤ 2tℓ₀` and `CapsLe c v`: `hbPrepCost ≤ 2^32·(hbS D + v + 1)^3`.

The constants are literals: `CH = CK = CP = 2^32`, `eH = eK = 8`, `eP = 3`.

Paper quantity of the main types: the Hb printer's step counts and capacities at the call's data size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires NearCubicWires.WireExponent3_5

/-- **The Hb data's size**: the cell count, the odometer's radix, the words the printer reads, its small numbers. -/
def hbS (D : HashData) : ℕ :=
  2 ^ (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) * (D.MP.J + 1) * D.pops.length * D.nE * D.N ^ 2 +
    2 ^ (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) + 2 ^ (D.MP.ell0 + 1) + (HbM.htWord D.Fs).length +
    (HbM.popsWord D.pops).length + (HbM.wtWord (HbM.wsOf D.MP)).length + D.G + D.N ^ 2 + D.nE

/-- Every capacity at least `b`. -/
def CapsGe (c : HbCaps) (b : ℕ) : Prop :=
  b ≤ c.cap ∧ b ≤ c.capL ∧ b ≤ c.m ∧ b ≤ c.c1 ∧ b ≤ c.c2 ∧ b ≤ c.c3 ∧ b ≤ c.c4 ∧ b ≤ c.RV ∧ b ≤ c.cL ∧
    b ≤ c.cE ∧ b ≤ c.cK ∧ b ≤ c.cC

/-- Every capacity at most `v`. -/
def CapsLe (c : HbCaps) (v : ℕ) : Prop :=
  c.cap ≤ v ∧ c.capL ≤ v ∧ c.m ≤ v ∧ c.c1 ≤ v ∧ c.c2 ≤ v ∧ c.c3 ≤ v ∧ c.c4 ≤ v ∧ c.RV ≤ v ∧ c.cL ≤ v ∧
    c.cE ≤ v ∧ c.cK ≤ v ∧ c.cC ≤ v

/-- The data facts the printer needs. -/
structure DataOk (D : HashData) : Prop where
  ht : 1 ≤ D.MP.t
  hF : D.N ^ 2 * D.nE ≤ D.Fs.length
  hG : ∀ pop ∈ D.pops, ∀ gi ∈ pop.2, gi ≤ D.G

/-- **The Hb printer's cell bounds** (`HashEAt`'s first clause): the global conditions, and at every cell the
capacities and the cost bound `2^32·(hbS D + 1)^8`. -/
def HbCellsBound : Prop :=
  ∀ (D : HashData), DataOk D → ∀ (c : HbCaps) (plen pfx : ℕ), plen ≤ 2 * D.MP.t * D.MP.ell0 →
    CapsGe c (2 ^ 32 * (hbS D + 1) ^ 8) →
    (hbX D c plen pfx).HbOk ∧ ∀ cc < (hbX D c plen pfx).n,
      (hbX D c plen pfx).CellOk cc ∧ (hbX D c plen pfx).cellCost cc ≤ 2 ^ 32 * (hbS D + 1) ^ 8

/-- **The Hb unit's prep bound** (`hCoreCost`'s first term). -/
def HbPrepBound : Prop :=
  ∀ (D : HashData) (c : HbCaps) (plen pfx v : ℕ), plen ≤ 2 * D.MP.t * D.MP.ell0 → CapsLe c v →
    hbPrepCost (hbX D c plen pfx) ≤ 2 ^ 32 * (hbS D + v + 1) ^ 3

end NearCubicWires.WireExponent3_5.PrimT.C4H
