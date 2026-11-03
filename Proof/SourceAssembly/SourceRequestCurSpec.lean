import Proof.SourceAssembly.SourceRequestSelSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.CurSpec
open NearCubicWires NearCubicWires.SourceRequest.SelSpec
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

/-! ## Per-slot data -/

def fSys : Option Fac → Bool
  | some (.sys _) => true
  | _ => false
def fTerm : Option Fac → Bool
  | some (.term _ _) => true
  | _ => false
def fSide : Option Fac → Bool
  | some (.sys r) => r
  | some (.term r _) => r
  | none => false
def fIdx : Option Fac → Nat
  | some (.term _ i) => i
  | _ => 0

/-- Monomial `m`'s symbolic record (`none` past the end). -/
def selAt (ph : Phase) (sL sR nL nR : Bool) (JL JR m : Nat) : Option Sel := (siteSel ph sL sR nL nR JL JR)[m]?

def facAt (σ : Option Sel) (i : Nat) : Option Fac := σ.bind (fun s => s.facs[i]?)

/-! ## Index algebra of the symbolic operations -/



/-! ## The moment phase: `T_L × T_L` -/

/-! ## The penalty phase: two sides, `½ · (penSide sL L ++ penSide sR R)` -/

/-! ## The clause phase: `litL ++ (litR ++ -(litL × litR))` -/

end NearCubicWires.SourceRequest.CurSpec

