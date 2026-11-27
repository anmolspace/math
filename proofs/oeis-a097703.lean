import OMAStatements.S_oeis_a097703

/-!
Source: https://oeis.org/A097703
Credit: @anmolspace (Lean formalization). Ralf Stephan posed the progression
conjecture in 2004. Amiram Eldar gave the mathematical proof and full
classification in 2024. The unitary multiplicativity and prime-power lemmas
adapt our formalization of A034448.
-/

namespace OMA.A097703Proof

open Finset ArithmeticFunction OMA.S_oeis_a097703

private theorem quotient_product {a b m n : ℕ} (ha : a ∣ m) (hb : b ∣ n)
    (hpa : 0 < a) (hpb : 0 < b) : m * n / (a * b) = (m / a) * (n / b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left x hpa, Nat.mul_div_cancel_left y hpb,
    show a * x * (b * y) = a * b * (x * y) by ring,
    Nat.mul_div_cancel_left (x * y) (mul_pos hpa hpb)]

/-- Unitary divisors of coprime numbers multiply independently. -/
private theorem unitary_mul {m n : ℕ} (hmn : m.Coprime n) :
    unitarySum (m * n) = unitarySum m * unitarySum n := by
  simp only [unitarySum, Finset.sum_filter]
  rw [sum_mul_sum, ← sum_product', hmn.divisors_mul, sum_map]
  calc
    _ = ∑ v ∈ (m.divisors ×ˢ n.divisors).attach,
        (if v.val.1.Coprime (m / v.val.1) then v.val.1 else 0) *
        (if v.val.2.Coprime (n / v.val.2) then v.val.2 else 0) := by
      apply sum_congr rfl
      rintro ⟨⟨x, y⟩, hxy⟩ _
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      have hxm := Nat.dvd_of_mem_divisors hx
      have hyn := Nat.dvd_of_mem_divisors hy
      have hcross₁ : x.Coprime (n / y) :=
        (hmn.coprime_dvd_left hxm).coprime_dvd_right (Nat.div_dvd_of_dvd hyn)
      have hcross₂ : y.Coprime (m / x) :=
        (hmn.symm.coprime_dvd_left hyn).coprime_dvd_right (Nat.div_dvd_of_dvd hxm)
      change (if (x * y).Coprime (m * n / (x * y)) then x * y else 0) = _
      rw [quotient_product hxm hyn (Nat.pos_of_mem_divisors hx) (Nat.pos_of_mem_divisors hy)]
      simp only [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
      split_ifs <;> simp_all
    _ = _ := Finset.sum_attach _ (fun v : ℕ × ℕ =>
      (if v.1.Coprime (m / v.1) then v.1 else 0) * (if v.2.Coprime (n / v.2) then v.2 else 0))

private theorem unitary_prime_power {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    unitarySum (p ^ e) = 1 + p ^ e := by
  have hs : (p ^ e).divisors.filter (fun d => d.Coprime (p ^ e / d)) = {1, p ^ e} := by
    ext d
    rw [mem_filter, Nat.mem_divisors_prime_pow hp, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hc⟩
      by_cases hzero : j = 0
      · left; simp [hzero]
      by_cases htop : j = e
      · exact Or.inr (congrArg (p ^ ·) htop)
      exfalso
      rw [Nat.pow_div hj hp.pos] at hc
      have ha : p ∣ p ^ j := dvd_pow_self _ hzero
      have hb : p ∣ p ^ (e - j) := dvd_pow_self _ (by omega)
      exact hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd ha hb)
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by omega, by simp⟩, by simp⟩
      · exact ⟨⟨e, le_rfl, rfl⟩, by simp [pow_pos hp.pos]⟩
  have hne : 1 ≠ p ^ e := (one_lt_pow₀ hp.one_lt he.ne').ne
  simp [unitarySum, hs, hne]

private def nonunitarySum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with ¬ d.Coprime (n / d), d

private theorem split_sum (n : ℕ) : unitarySum n + nonunitarySum n = sigma 1 n := by
  rw [sigma_one_apply]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

private theorem unitary_le (n : ℕ) : unitarySum n ≤ sigma 1 n := by
  have h := split_sum n
  omega

private theorem all_unitary {n : ℕ} (hn : n ≠ 0) : sigma 1 n = unitarySum n ↔ Squarefree n := by
  constructor
  · intro heq
    have hzero : nonunitarySum n = 0 := by have h := split_sum n; omega
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hpp
    have hpn : p ∣ n := (dvd_mul_right p p).trans hpp
    obtain ⟨x, hx⟩ := hpp
    have hdiv : n / p = p * x := by
      rw [hx, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    have hbad : ¬p.Coprime (n / p) := by
      rw [hp.coprime_iff_not_dvd, hdiv]
      simp
    have hmem : p ∈ n.divisors.filter (fun d => ¬ d.Coprime (n / d)) :=
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hpn, hn⟩, hbad⟩
    exact hp.ne_zero ((Finset.sum_eq_zero_iff_of_nonneg (fun (i : ℕ) _ => Nat.zero_le i)).mp hzero p hmem)
  · intro hs
    rw [sigma_one_apply, unitarySum]
    congr 1
    symm
    apply filter_true_of_mem
    intro d hd
    apply Nat.coprime_of_squarefree_mul
    simpa [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] using hs

/-- Once the exponent of 3 is at least four, the ordinary divisor sum of
`4 * 3^e` strictly exceeds twice its unitary divisor sum. -/
private theorem three_power_strict (e : ℕ) (he : 4 ≤ e) :
    2 * unitarySum (4 * 3 ^ e) < sigma 1 (4 * 3 ^ e) := by
  have hc : (4 : ℕ).Coprime (3 ^ e) := (show Nat.Coprime 4 3 by decide).pow_right e
  rw [unitary_mul hc, isMultiplicative_sigma.map_mul_of_coprime hc,
    unitary_prime_power Nat.prime_three (by omega : 0 < e), sigma_one_apply_prime_pow Nat.prime_three]
  have hu : unitarySum 4 = 5 := by decide
  have hs : sigma 1 4 = 7 := by rw [sigma_one_apply]; decide
  rw [hu, hs]
  have geom : (∑ i ∈ range (e + 1), 3 ^ i) * 2 + 1 = 3 ^ e * 3 := by
    simpa only [show (2 : ℕ) + 1 = 3 by decide, pow_succ] using geom_sum_mul_add (2 : ℕ) (e + 1)
  have hpow : (3 : ℕ) ^ 4 ≤ 3 ^ e := Nat.pow_le_pow_right (by decide) he
  omega

private theorem classification (j : ℕ) : occurs j ↔ 3 ∣ 2 * j + 1 ∨ ¬ Squarefree (2 * j + 1) := by
  let t := 2 * j + 1
  have ht : t ≠ 0 := by dsimp [t]; omega
  have htOdd : Odd t := ⟨j, rfl⟩
  have hbase : 216 * j + 108 = 108 * t := by dsimp [t]; ring
  change (sigma 1 (216 * j + 108) ≠ 2 * unitarySum (216 * j + 108)) ↔ 3 ∣ t ∨ ¬ Squarefree t
  rw [hbase]
  by_cases h3 : 3 ∣ t
  · simp only [h3, true_or, iff_true]
    let e := t.factorization 3
    let r := ordCompl[3] t
    have he : 0 < e := Nat.prime_three.factorization_pos_of_dvd ht h3
    have hr : 0 < r := Nat.ordCompl_pos 3 ht
    have hf : 3 ^ e * r = t := Nat.ordProj_mul_ordCompl_eq_self t 3
    have hsplit : 108 * t = (4 * 3 ^ (3 + e)) * r := by rw [← hf, pow_add]; ring
    have hc₄ : (4 : ℕ).Coprime r := by
      exact (htOdd.coprime_two_left.coprime_dvd_right (Nat.ordCompl_dvd t 3)).pow_left 2
    have hc := hc₄.mul_left ((Nat.coprime_ordCompl Nat.prime_three ht).pow_left (3 + e))
    rw [hsplit, unitary_mul hc, isMultiplicative_sigma.map_mul_of_coprime hc]
    have hl := three_power_strict (3 + e) (by omega)
    have hrpos := sigma_pos 1 r hr.ne'
    apply ne_of_gt
    calc
      2 * (unitarySum (4 * 3 ^ (3 + e)) * unitarySum r) ≤
          (2 * unitarySum (4 * 3 ^ (3 + e))) * sigma 1 r := by
            rw [← Nat.mul_assoc]
            exact Nat.mul_le_mul_left _ (unitary_le r)
      _ < sigma 1 (4 * 3 ^ (3 + e)) * sigma 1 r := Nat.mul_lt_mul_of_pos_right hl hrpos
  · have hc : (108 : ℕ).Coprime t :=
      (htOdd.coprime_two_left.pow_left 2).mul_left ((Nat.prime_three.coprime_iff_not_dvd.mpr h3).pow_left 3)
    rw [unitary_mul hc, isMultiplicative_sigma.map_mul_of_coprime hc]
    have hu : unitarySum 108 = 140 := by decide
    have hs : sigma 1 108 = 280 := by rw [sigma_one_apply]; decide
    rw [hu, hs]
    have eq := all_unitary ht
    simp only [h3, false_or]
    rw [← eq]
    omega

end OMA.A097703Proof

open OMA.A097703Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a097703.main := by
  refine ⟨fun k => (classification (3 * k + 1)).mpr (Or.inl ?_), classification⟩
  exact ⟨2 * k + 1, by ring⟩

