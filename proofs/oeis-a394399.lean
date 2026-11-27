import OMAStatements.S_oeis_a394399
import Mathlib.Tactic

/-!
A proof for Aied Sulaiman's OEIS A394399.
Credit: @anmolspace. The geometric sum, midpoint and factorization lemmas adapt the
same contributor's companion proof of OEIS A394757.
-/

namespace A394399Proof

open Finset ArithmeticFunction OMA.S_oeis_a394399

private lemma paired_sum (p d j : ℕ) (hd : d ∣ 1+p) :
    d ∣ ∑ i ∈ range (2*j+2), p^i := by
  induction j with
  | zero => simpa [sum_range_succ, Nat.add_comm] using hd
  | succ j ih =>
    have pair : (∑ i ∈ range (2*(j+1)+2), p^i) =
        (∑ i ∈ range (2*j+2), p^i) + p^(2*j+2)*(1+p) := by
      rw [show 2*(j+1)+2=(2*j+2)+1+1 by omega, sum_range_succ, sum_range_succ, pow_succ p (2*j+2)]
      ring
    rw [pair]
    exact dvd_add ih (dvd_mul_of_dvd_right hd _)

/-- For an odd exponent of p in k, every divisor of 1+p divides sigma(k). -/
private lemma divisor_of_odd_exponent {k p d : ℕ} (hk : k ≠ 0) (hp : p.Prime)
    (he : k.factorization p % 2 = 1) (hd : d ∣ 1+p) : d ∣ sigma 1 k := by
  have localDiv : d ∣ sigma 1 (p ^ k.factorization p) := by
    rw [sigma_one_apply_prime_pow hp]
    obtain ⟨j,hj⟩ : ∃ j, k.factorization p + 1 = 2*j+2 := ⟨k.factorization p/2, by omega⟩
    rw [hj]
    exact paired_sum p d j hd
  have factor := Nat.ordProj_mul_ordCompl_eq_self k p
  have cop := (Nat.coprime_ordCompl (p := p) hp hk).pow_left (k.factorization p)
  calc
    d ∣ sigma 1 (p ^ k.factorization p) * sigma 1 (ordCompl[p] k) :=
      dvd_mul_of_dvd_left localDiv _
    _ = sigma 1 (p ^ k.factorization p * ordCompl[p] k) :=
      (isMultiplicative_sigma.map_mul_of_coprime cop).symm
    _ = sigma 1 k := congrArg (sigma 1) factor

private lemma midpoint_facts {k : ℕ} (large : 6 ≤ k) (left : (k-1).Prime)
    (right : (k+1).Prime) : 2 ∣ k ∧ 3 ∣ k ∧ ¬ IsSquare k := by
  have parity := left.eq_two_or_odd
  have leftThree : ¬ 3 ∣ k-1 := by
    intro h
    have := (Nat.dvd_prime left).mp h
    omega
  have rightThree : ¬ 3 ∣ k+1 := by
    intro h
    have := (Nat.dvd_prime right).mp h
    omega
  refine ⟨by omega, by omega, ?_⟩
  rintro ⟨r, hr⟩
  have rlarge : 3 ≤ r := by
    by_contra! small
    interval_cases r <;> omega
  have mul : k-1 = (r-1)*(r+1) := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s+1 := ⟨r-1, by omega⟩
    rw [show s+1-1=s by omega]
    have exactProduct : k = s*(s+1+1)+1 := by rw [hr]; ring
    omega
  rw [mul] at left
  exact Nat.not_prime_mul (by omega) (by omega) left

private lemma square_of_even_exponents {k : ℕ} (hk : k ≠ 0)
    (h : ∀ p : ℕ, p.Prime → k.factorization p % 2 = 0) : IsSquare k := by
  refine ⟨∏ p ∈ k.primeFactors, p ^ (k.factorization p / 2), ?_⟩
  calc
    k = ∏ p ∈ k.primeFactors, p ^ k.factorization p := Nat.prod_primeFactors_pow_factorization hk
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_add]
      have hv := h p (Nat.prime_of_mem_primeFactors hp)
      congr 1
      omega

private theorem twice_square_of_gcd_three {k : ℕ} (hk : k ≠ 0) (evenK : 2 ∣ k)
    (nonsquare : ¬ IsSquare k) (hg : divisorGcd k = 3) : ∃ m : ℕ, k = 2 * m^2 := by
  have oddSigma : ¬ 2 ∣ sigma 1 k := by
    intro hs
    have h : 2 ∣ divisorGcd k := Nat.dvd_gcd evenK hs
    rw [hg] at h
    omega
  have other (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : k.factorization p % 2 = 0 := by
    by_contra h
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
    exact oddSigma (divisor_of_odd_exponent hk hp (by omega) ⟨j + 1, by omega⟩)
  have twoOdd : k.factorization 2 % 2 = 1 := by
    by_contra h
    apply nonsquare (square_of_even_exponents hk ?_)
    intro p hp
    by_cases heq : p = 2
    · subst p; omega
    · exact other p hp heq
  obtain ⟨r, rfl⟩ := evenK
  have hr : r ≠ 0 := by omega
  have hsq : IsSquare r := square_of_even_exponents hr (by
    intro p hp
    by_cases heq : p = 2
    · subst p
      have he : (2 * r).factorization 2 = 1 + r.factorization 2 := by
        simp [Nat.factorization_mul (by decide : 2 ≠ 0) hr, Nat.prime_two.factorization]
      rw [he] at twoOdd
      omega
    · have he : (2 * r).factorization p = r.factorization p := by
        simp [Nat.factorization_mul (by decide : 2 ≠ 0) hr, Nat.prime_two.factorization, heq]
      simpa only [he] using other p hp heq)
  obtain ⟨m, hm⟩ := hsq
  exact ⟨m, by rw [hm, pow_two]⟩

private theorem gcd_three_of_twice_square {k m : ℕ} (hk : k ≠ 0) (hm : k = 2 * m^2)
    (threeK : 3 ∣ k) (hg : (divisorGcd k).Prime) : divisorGcd k = 3 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp_all
  have h2 : k.factorization 2 = 1 + 2 * m.factorization 2 := by
    rw [hm, Nat.factorization_mul (by decide) (pow_ne_zero _ hm0), Nat.factorization_pow]
    simp [Nat.prime_two.factorization]
  have hsig : 3 ∣ sigma 1 k := divisor_of_odd_exponent hk Nat.prime_two (by omega) (by decide)
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hg).mp (Nat.dvd_gcd threeK hsig)).symm

end A394399Proof

open A394399Proof OMA.S_oeis_a394399 in
theorem OMA.solution : type_of% @OMA.S_oeis_a394399.main := by
  intro k ht
  by_cases large : 6 ≤ k
  · obtain ⟨evenK, threeK, nonSquare⟩ := midpoint_facts large ht.1 ht.2
    have hk : k ≠ 0 := by omega
    constructor
    · intro hg
      exact ⟨hg ▸ Nat.prime_three, twice_square_of_gcd_three hk evenK nonSquare hg⟩
    · rintro ⟨hg, m, hm⟩
      exact gcd_three_of_twice_square hk hm threeK hg
  · have hnot : ¬ (divisorGcd k).Prime := by interval_cases k <;> decide +kernel
    have hne : divisorGcd k ≠ 3 := by intro h; exact hnot (h ▸ Nat.prime_three)
    simp [hnot, hne]
