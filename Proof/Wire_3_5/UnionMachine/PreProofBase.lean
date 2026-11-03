import Proof.Wire_3_5.Primitive.Writers.PreLinkBase

/-! # PA (e), proved: the writers' class link `∀ l, PreLinkT l`

"The additive preprocessing of a call costs `2^{O(Ψ)}q^{O(1)}`" (P3:3108, 3112-3114) at the load
`Ψ = max{Ψ_T, Ψ_S, Ψ_aux}` (P3:3094-3102), `Ψ_aux = C_D[k + L² + (k+L³)L²(k+L)]`. The batch writers run over the star
cells, `2^{k+L}·poly(n)` units, with the writers' fixed polynomial `C·(2^{k+L} + n + 1)^D` (PA's `PreLinkT`).
With the floor envelope `2^{D·Ψ}` (**`envW D`**: `cpsi = D`, `Apre = 0`), the load-constant floor `C_D ≥ 1` and
`c_W = C·2^D`: `Ψ ≥ Ψ_aux ≥ k + L` (**`kL_le_loadPsi`**) and `n + 2 ≤ 2^L`, so `2^{k+L} + n + 1 ≤ 2^{Ψ+1}` and
`C·(2^{k+L} + n + 1)^D ≤ C·2^D·2^{D·Ψ}` (**`link_le`**); **`preLink`**: `∀ l, PreLinkT l`.

Paper quantity of the main type: the preprocessing class `2^{cpsi·Ψ}q^{Apre}` at the load `Ψ` against the star cells'
count `2^{k+L}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.PreProof
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ
open NearCubicWires.WireExponent3_5.PrimAsm.PreLink

/-- **The writers' floor envelope**: preprocessing `2^{D·Ψ}`, every other exponent `0`. -/
def envW (D : ℕ) : Envelope := ⟨0, 0, 0, 0, 0, 0, 0, D⟩

/-- **The load dominates the star cells' exponent**: `k + L ≤ Ψ` once `C_D ≥ 1` (through `Ψ_aux`). -/
theorem kL_le_loadPsi (CD k L BT BS : ℕ) (hCD : 1 ≤ CD) : k + L ≤ loadPsi CD k L BT BS := by
  have h1 : loadAux CD k L ≤ loadPsi CD k L BT BS := by
    unfold loadPsi
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h2 : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) L
  have h3 : k + L ≤ k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L) := by omega
  have h4 : k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L) ≤ loadAux CD k L := by
    unfold loadAux
    have h := Nat.mul_le_mul hCD (le_refl (k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L)))
    simpa using h
  omega

/-- **The link at one call**: `C·(2^{k+L} + n + 1)^D ≤ C·2^D · classBound (envW D) .preprocessing n k Ψ`. -/
theorem link_le (D C CD k n BT BS : ℕ) (hCD : 1 ≤ CD) :
    C * (2 ^ (k + Nat.clog 2 (n + 2)) + n + 1) ^ D ≤
      C * 2 ^ D * classBound (envW D) .preprocessing n k (loadPsi CD k (Nat.clog 2 (n + 2)) BT BS) := by
  obtain ⟨L, hLdef⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLdef]
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = loadPsi CD k L BT BS := ⟨_, rfl⟩
  rw [← hΨdef]
  have hΨ : k + L ≤ Ψ := by rw [hΨdef]; exact kL_le_loadPsi CD k L BT BS hCD
  have hL : n + 2 ≤ 2 ^ L := by rw [hLdef]; exact Nat.le_pow_clog (by norm_num) _
  have h1 : 2 ^ (k + L) ≤ 2 ^ Ψ := Nat.pow_le_pow_right (by norm_num) hΨ
  have h2 : 2 ^ L ≤ 2 ^ Ψ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (k + L) + n + 1 ≤ 2 ^ (Ψ + 1) := by rw [pow_succ]; omega
  have h4 : (2 ^ (k + L) + n + 1) ^ D ≤ (2 ^ (Ψ + 1)) ^ D := Nat.pow_le_pow_left h3 D
  have h5 : (2 ^ (Ψ + 1)) ^ D = 2 ^ D * 2 ^ (D * Ψ) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have e : classBound (envW D) .preprocessing n k Ψ = 2 ^ (D * Ψ) := by simp [classBound, envW]
  rw [e, mul_assoc, ← h5]
  exact Nat.mul_le_mul le_rfl h4

end NearCubicWires.WireExponent3_5.UnionMachine.PreProof
