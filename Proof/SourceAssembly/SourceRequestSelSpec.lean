import Proof.SourceAssembly.SourceRequestMonomialSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SelSpec
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceRequest.MonomialSpec

/-- Provenance of one factor: the systematic parity atom of the left (`false`) / right (`true`) literal, or term `idx`
of that literal's guessed sum. -/
inductive Fac where
  | sys (right : Bool)
  | term (right : Bool) (idx : Nat)
  deriving DecidableEq

/-- A symbolic monomial: factor provenances in order, and the constant multiplier. -/
structure Sel where
  facs : List Fac
  rho : ℚ

def smul1 (a b : Sel) : Sel := ⟨a.facs ++ b.facs, a.rho * b.rho⟩
def sadd (A B : List Sel) : List Sel := A ++ B
def smul (A B : List Sel) : List Sel := A.flatMap fun a => B.map (smul1 a)
def sscale (q : ℚ) (A : List Sel) : List Sel := A.map fun a => ⟨a.facs, q * a.rho⟩
def sconst : List Sel := [⟨[], 1⟩]
def satom (r : Bool) : List Sel := [⟨[.sys r], 1⟩]
def scoord (r : Bool) (J : Nat) : List Sel := (List.range J).map fun i => ⟨[.term r i], 1⟩

section real

end real

/-! ## The three site lists, symbolically -/

def litSel (neg r : Bool) (J : Nat) : List Sel :=
  if neg then sadd sconst (sscale (-1) (scoord r J)) else scoord r J

def penSide (sys r : Bool) (J : Nat) : List Sel :=
  if sys then sadd (satom r) (sadd (sscale (-2) (smul (satom r) (scoord r J))) (smul (scoord r J) (scoord r J)))
  else sadd (smul (scoord r J) (scoord r J))
    (sadd (sscale (-2) (smul (smul (scoord r J) (scoord r J)) (scoord r J)))
      (smul (smul (scoord r J) (scoord r J)) (smul (scoord r J) (scoord r J))))

open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule in
/-- **The site list, symbolically** (before the uniform `1/2^clauseBits`). -/
def siteSel : Phase → Bool → Bool → Bool → Bool → Nat → Nat → List Sel
  | .penalty, sL, sR, _, _, JL, JR => sscale (1 / 2) (sadd (penSide sL false JL) (penSide sR true JR))
  | .moment, _, _, _, _, JL, _ => smul (scoord false JL) (scoord false JL)
  | .clause, _, _, nL, nR, JL, JR =>
    sadd (litSel nL false JL) (sadd (litSel nR true JR) (sscale (-1) (smul (litSel nL false JL) (litSel nR true JR))))

section site

end site

section site2
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape

end site2

end NearCubicWires.SourceRequest.SelSpec

