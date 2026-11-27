import OMAStatements.S_oeis_a188486
import Mathlib.Tactic

-- Credit: @anmolspace. Eric W. Weisstein lists the known witness 550564 in OEIS A188486.

open ArithmeticFunction

private lemma sigma_prime_sq {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private lemma sigma_family {p : ℕ} (hp : p.Prime) (hc : Nat.Coprime 196 p) :
    sigma 1 (196 * p ^ 2) = 399 * (p ^ 2 + p + 1) := by
  have h196 : sigma 1 196 = 399 := by
    rw [show 196 = 2 ^ 2 * 7 ^ 2 by decide,
      isMultiplicative_sigma.map_mul_of_coprime (by decide),
      sigma_prime_sq (by decide), sigma_prime_sq (by decide)]
    decide
  rw [isMultiplicative_sigma.map_mul_of_coprime (hc.pow_right 2), h196, sigma_prime_sq hp]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188486.main) := by
  intro h
  apply h 550564 (by decide) 203 (by decide) (by decide)
  have witness := sigma_family (p := 53) (by decide) (by decide)
  norm_num at witness ⊢
  exact witness
