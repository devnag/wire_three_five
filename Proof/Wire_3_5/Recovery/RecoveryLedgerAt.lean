import Proof.Wire_3_5.Recovery.RecoveryBudget

/-! # The Case-2 ledger at one source length (P3:3399-3430, 3616-3626, 3669-3697; D1.5)

Realizes `tr:completeness`'s conditions at the union machine's width `q = q(N)` of one source length, at the gate's
constants: the grid (P3:3399-3403), the star hypotheses (P3:1188-1189), the fit conditions (P3:3106-3107), the name
count (P3:3078), the envelopes (P3:3068-3072), the parity (P3:3409-3410), the cap `tr:B` (P3:3425-3430), the endpoint
and propagated errors (P3:3075-3076, 3616-3624), and the guess budget (P3:3675-3680).

Paper quantities: the gate relations the recovery needs (**`GateRel l G`**: `A_pad`, the grid `s = C_δΛ̄²` at `C_Λ = 2`,
`C_par = 2`, `1/β⁻¹ ≤ β`, positive native coefficients, name count `≥ 2`, `kDeg ≥ 2`, `descDeg, carrierDeg ≥ 26`) and
the record `CaseTwoLedger` at one source length (**`ledger_at`**), from the per-length facts. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)

/-- **The gate relations of the recovery leaf** (the gate constants the union's completeness reads). -/
structure GateRel (l : Literals) (G : Split.Gate) : Prop where
  apad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad
  sp : G.row.sp = rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l)
  cpar : G.row.cap.Cpar = 2
  betaInv : 1 ≤ G.row.cap.betaInv
  beta : 1 / (G.row.cap.betaInv : ℝ) ≤ ((gateCParams1 l).β : ℝ)
  aT : 1 ≤ G.row.cap.aT
  aS : 1 ≤ G.row.cap.aS
  name : 2 ≤ G.nameCount
  kdeg : 2 ≤ G.kDeg
  desc : 26 ≤ G.descDeg
  carrier : 26 ≤ G.carrierDeg

section LedgerAt

