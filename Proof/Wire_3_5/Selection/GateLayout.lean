import Proof.Wire_3_5.Selection.PointBridge
import Proof.Wire_3_5.Selection.GatePlan

/-! # C1.4: the gate routine's layout (P3:1339-1358)

Paper: "Enumerate its `2^k` error rows. For each gate and row [...] Sum its exact count" (P3:1339-1358). The gate
routine runs on one injective map of streams `G : Fin 28 → Fin (ns + 1)` and one of registers `R : Fin 48 → Fin nr`;
this module fixes the roles (C1.4's interface `GateLayout`, with `NS := G 0`, `GA := G 1`, `OF := G 2`, `TX := G 3`,
`Rh := R 0`, `Rb := R 1`, `Rs := R 2`, `RfL := R 3`, `RfR := R 4`, `RV := R 5`) and the sub-maps of the point routine
(`SL`, `SR`, `QL`, `QR`) and of the key emitters (`EM`), with their injectivity.
Streams: `4` X, `5` U, `6` WTL, `7` WTR, `8` CI, `9` SY, `10` AC, `11` AC', `12` WV, `13` TK, `14` XP, `15` UP, `16` HT,
`17` PW, `18` KY, `19` KY', `20` KL, `21` KL', `22` CNT, `23` JT, `24` ACC, `25` EW, `26`, `27` spare.
Registers: `6`–`14` the routine's (F, R, OK, FL, SG, CX, CW, CU, CN), `15` RO (left), `16`, `17` loop scratch,
`19`–`27` the emitters' (LV, ET, RQ, RZ, RW, RW1, RS1, RS0, CK), `28`–`30` the key words' counters, `31` `2^lw`,
`32` `2^(s·h)`, `33`, `34` loop scratch, `35` `2^rw`, `36` RO (right), `37`–`47` the joins' and the preamble's.
Paper quantity: none (the layout); every map is checked injective by `decide`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- The left point routine's streams. -/
def iSL : Fin 12 → Fin 28 := ![4, 5, 0, 6, 8, 9, 10, 11, 12, 13, 14, 15]
/-- The right point routine's streams (its initial word is `OF`, `2^V`). -/
def iSR : Fin 12 → Fin 28 := ![4, 5, 0, 7, 8, 9, 10, 11, 12, 2, 14, 15]
/-- The left point routine's registers. -/
def iQL : Fin 20 → Fin 48 := ![6, 7, 8, 9, 10, 11, 12, 13, 14, 1, 0, 2, 3, 15, 16, 17, 31, 33, 32, 34]
/-- The right point routine's registers. -/
def iQR : Fin 20 → Fin 48 := ![6, 7, 8, 9, 10, 11, 12, 13, 14, 1, 0, 2, 4, 36, 16, 17, 35, 33, 32, 34]
/-- The emitters' registers. -/
def iEM : Fin 16 → Fin 48 := ![19, 20, 5, 21, 22, 23, 24, 25, 26, 27, 6, 7, 40, 41, 42, 43]

theorem iSL_inj : Function.Injective iSL := by decide
theorem iSR_inj : Function.Injective iSR := by decide
theorem iQL_inj : Function.Injective iQL := by decide
theorem iQR_inj : Function.Injective iQR := by decide
theorem iEM_inj : Function.Injective iEM := by decide

/-- **The gate routine's layout** (C1.4's interface) on the maps `G`, `R`. -/
def gateLayout (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : GateLayout ns nr where
  NS := G 0
  GA := G 1
  OF := G 2
  TX := G 3
  Rh := R 0
  Rb := R 1
  Rs := R 2
  RfL := R 3
  RfR := R 4
  RV := R 5
  scS := (List.finRange 24).map fun i => G ⟨i.val + 4, by omega⟩
  scR := (List.finRange 42).map fun i => R ⟨i.val + 6, by omega⟩

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
