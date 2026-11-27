import OMAStatements.S_oeis_a090826
import Mathlib.Tactic.LinearCombination

/-!
# Mathar's four-term recurrence for the Catalan–Fibonacci convolution

Derive McGarvey's inhomogeneous recurrence from the convolution and apply
the Catalan ratio to two successive indices. Ekhad and Yang proved the
four-term recurrence by a generating function in 2017 (their Theorem 19).
This direct Lean formalization is by @anmolspace, assisted by Codex.
-/

namespace OMA.A090826Proof

open OMA.S_oeis_a090826

private theorem conv_step (n : ℕ) : a (n+2) = a (n+1) + a n + catalan (n+1) := by
  calc
    a (n+2) = (∑ j ∈ Finset.range (n+1), catalan j * Nat.fib (n+2-j)) + catalan (n+1) := by
      simp [a, Finset.sum_range_succ]
    _ = ((∑ j ∈ Finset.range (n+1), catalan j * Nat.fib (n+1-j)) +
        (∑ j ∈ Finset.range (n+1), catalan j * Nat.fib (n-j))) + catalan (n+1) := by
      rw [← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [show n+2-j = (n-j)+2 by omega, Nat.fib_add_two,
        show n+1-j = (n-j)+1 by omega, Nat.mul_add, Nat.add_comm]
    _ = _ := by simp [a, Finset.sum_range_succ]

private theorem catalan_step (n : ℕ) :
    (n+2)*catalan (n+1) = 2*(2*n+1)*catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1), ← succ_mul_catalan_eq_centralBinom n] at h
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < n+1)
  calc
    _ = 2*(2*n+1)*((n+1)*catalan n) := h
    _ = _ := by ring

end OMA.A090826Proof

open OMA.S_oeis_a090826 in
theorem OMA.solution : type_of% @OMA.S_oeis_a090826.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  have h₁ : (a (k+3) : ℤ) = a (k+2) + a (k+1) + catalan (k+2) := by
    exact_mod_cast A090826Proof.conv_step (k+1)
  have h₂ : (a (k+2) : ℤ) = a (k+1) + a k + catalan (k+1) := by
    exact_mod_cast A090826Proof.conv_step k
  have h₃ : ((k : ℤ)+3)*(catalan (k+2) : ℤ) =
      2*(2*((k : ℤ)+1)+1)*(catalan (k+1) : ℤ) := by
    exact_mod_cast A090826Proof.catalan_step (k+1)
  rw [show k+3-1 = k+2 by omega, show k+3-2 = k+1 by omega, show k+3-3 = k by omega]
  push_cast
  linear_combination ((k : ℤ)+3)*h₁ + (-4*((k : ℤ)+3)+6)*h₂ + h₃
