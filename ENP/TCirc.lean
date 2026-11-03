import Statement
import Outer.CircuitEval

/-!
# Stage 2 (semantic part): the stage-2 circuit `c_T`

The near-cubic-gates paper's uniform recovery (sec:all-lengths, E^NP paragraph): "Second, the algorithm of imp:short-pcp is run deterministically on
`⟨B*_src⟩_ν` …; a formula with one variable per oracle address and the constraints `C^O_{⟨B*_src⟩_ν}(R) = 0` for all
`2^{ℓ_out}` inputs `R`, of size `2^{ℓ_out} q^{O_G(1)}`, finds the first oracle `O*`." the extraction of the hard table: "Let `O*` be the first such
oracle, viewed as a truth table".

`tCircuit C` is a Boolean circuit on the `T = 2^ℓ` table bits `t` (one input per oracle address, address order) with
`tCircuit C`(t) = ⋀_{z < T} ¬ C^{O_t}(bin(z))` (`tCircuit_eval`), where `O_t(a) = t(binaryAddress a)`. Its
`circuitInputFormula` is the stage-2 formula; the prefix search over its first `T` variables returns the first honest
table. Layout (uniform blocks, so that the emitter needs only unary arithmetic): node `0` is `false`, nodes
`1..T` the table inputs, node `T+1` is `true`; then for each seed `z` a block of `m·K + 2` nodes (`m` = size of `C`,
`K = T(2ℓ+1)`): node `c` of `C` becomes `K` nodes whose last carries its value (an oracle gate becomes the multiplexer
`⋁_a (t_a ∧ [args = bin(a)])`; any other node is `K−1` constants and its translation), then `¬C(z)` and the running
conjunction.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TCirc

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.SourceInterfaces

variable {ℓ : ℕ} (C : OracleCircuit ℓ ℓ)

/-- `T = 2^ℓ`, the number of oracle addresses (= seeds). -/
abbrev T (ℓ : ℕ) : ℕ := 2 ^ ℓ
/-- The block size. -/
abbrev K (ℓ : ℕ) : ℕ := T ℓ * (2 * ℓ + 1)
/-- The start region: zero wire, `T` inputs, the constant `true`. -/
abbrev S (ℓ : ℕ) : ℕ := T ℓ + 2
/-- The seed length. -/
abbrev L : ℕ := C.nodes.length * K ℓ + 2
/-- The first node of seed `z`. -/
abbrev base (z : ℕ) : ℕ := S ℓ + z * L C
/-- The image of node `c` of `C` at seed `z`. -/
abbrev img (z c : ℕ) : ℕ := base C z + c * K ℓ + (K ℓ - 1)
/-- The first node of the block of node `c` at seed `z`. -/
abbrev bs (z c : ℕ) : ℕ := base C z + c * K ℓ
/-- The first node of group `a` in an oracle block. -/
abbrev gs (z c a : ℕ) : ℕ := bs C z c + a * (2 * ℓ + 1)

/-- The literal `[w = b]`. -/
def lit (b : Bool) (w : ℕ) : BooleanNode (T ℓ) := if b then .or w w else .not w

/-- The node holding `t_a ∧ ⋀_{j' < j} [args_{j'} = a_{j'}]`. -/
def gIdx (z c a j : ℕ) : ℕ := if j = 0 then 1 + a else gs C z c a + 2 * j - 1

/-- The previous running disjunction (`0`, the zero wire, before group `0`). -/
def oPrev (z c a : ℕ) : ℕ := if a = 0 then 0 else gs C z c a - 1

/-- Group `a` of the multiplexer of an oracle gate with arguments `args` (the near-cubic-gates paper's uniform recovery, stage 2: one variable per
oracle address). -/
def group (z c : ℕ) (args : Fin ℓ → ℕ) (a : ℕ) : List (BooleanNode (T ℓ)) :=
  (List.range ℓ).flatMap (fun j =>
    [lit (a.testBit j) (img C z (if h : j < ℓ then args ⟨j, h⟩ else 0)),
      .and (gIdx C z c a j) (gs C z c a + 2 * j)]) ++
    [.or (oPrev C z c a) (gIdx C z c a ℓ)]

/-- A non-oracle node of `C` at seed `z`. -/
def translate (z : ℕ) : OracleNode ℓ ℓ → BooleanNode (T ℓ)
  | .const b => .const b
  | .input i => .const (z.testBit i.val)
  | .not c => .not (img C z c)
  | .and l r => .and (img C z l) (img C z r)
  | .or l r => .or (img C z l) (img C z r)
  | .oracle _ => .const false

/-- The block of node `c` (with value `nd`) at seed `z`. -/
def block (z c : ℕ) : OracleNode ℓ ℓ → List (BooleanNode (T ℓ))
  | .oracle args => (List.range (T ℓ)).flatMap (group C z c args)
  | nd => List.replicate (K ℓ - 1) (.const false) ++ [translate C z nd]

/-- Seed `z`: every node's block, then `¬C(z)` and the running conjunction. -/
def seed (z : ℕ) : List (BooleanNode (T ℓ)) :=
  (List.range C.nodes.length).flatMap (fun c => block C z c (C.nodes.getD c (.const false))) ++
    [.not (img C z C.output.val), .and (base C z - 1) (base C z + C.nodes.length * K ℓ)]

/-- The start region. -/
def start (ℓ : ℕ) : List (BooleanNode (T ℓ)) :=
  [.const false] ++ List.ofFn (fun a : Fin (T ℓ) => .input a) ++ [.const true]

/-- All nodes of `c_T`. -/
def nodes : List (BooleanNode (T ℓ)) := start ℓ ++ (List.range (T ℓ)).flatMap (seed C)

end NearCubicGates.Close.ENP.TCirc
