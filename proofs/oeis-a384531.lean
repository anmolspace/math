import OMAStatements.S_oeis_a384531
import Mathlib.Tactic

/-!
The mathematical identity is due to Werner Schulte and was proved by David
Radcliffe. We first use the Chinese remainder theorem to separate coprime
moduli, then count the gcd values at a prime power.
-/

namespace AdjacentGcd

open Finset

private def term (n i : ℕ) := (i+1).gcd n * (i+2).gcd n

private def total (n : ℕ) := ∑ i ∈ range n, term n i

private lemma residue_sum (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n)
    (f : ℕ → ℕ → ℕ) :
    (∑ i ∈ range (m*n), f (i%m) (i%n)) = ∑ i ∈ range m, ∑ j ∈ range n, f i j := by
  let pack : Fin (m*n) → Fin m × Fin n :=
    fun x => (⟨x.val%m, Nat.mod_lt _ hm⟩, ⟨x.val%n, Nat.mod_lt _ hn⟩)
  have bij : Function.Bijective pack := by
    constructor
    · intro x y he
      have hm' : x.val ≡ y.val [MOD m] := congrArg (fun t : Fin m × Fin n => t.1.val) he
      have hn' : x.val ≡ y.val [MOD n] := congrArg (fun t : Fin m × Fin n => t.2.val) he
      exact Fin.ext (((Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hm', hn'⟩).eq_of_lt_of_lt x.isLt y.isLt)
    · rintro ⟨a,b⟩
      let x := Nat.chineseRemainder h a.val b.val
      refine ⟨⟨x.val, Nat.chineseRemainder_lt_mul h _ _ hm.ne' hn.ne'⟩, ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · exact Eq.trans x.property.1 (Nat.mod_eq_of_lt a.isLt)
      · exact Eq.trans x.property.2 (Nat.mod_eq_of_lt b.isLt)
  let e := Equiv.ofBijective pack bij
  have eq := e.sum_comp (fun t : Fin m × Fin n => f t.1.val t.2.val)
  calc
    _ = ∑ i : Fin (m*n), f (i.val%m) (i.val%n) :=
      (Fin.sum_univ_eq_sum_range (fun i => f (i%m) (i%n)) _).symm
    _ = ∑ i : Fin m, ∑ j : Fin n, f i.val j.val := by simpa [e, pack, Fintype.sum_prod_type] using eq
    _ = ∑ i : Fin m, ∑ j ∈ range n, f i.val j := by
      apply sum_congr rfl
      intro i _
      exact Fin.sum_univ_eq_sum_range (fun j => f i.val j) n
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, f i j) m

private lemma term_mod (n i : ℕ) : term n (i%n) = term n i := by
  have h := Nat.mod_modEq i n
  exact congrArg₂ (· * ·) ((h.add_right 1).gcd_eq) ((h.add_right 2).gcd_eq)

private lemma total_mul (m n : ℕ) (h : m.Coprime n) : total (m*n) = total m * total n := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [total]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [total]
  calc
    _ = ∑ i ∈ range (m*n), term m (i%m) * term n (i%n) := by
      apply sum_congr rfl
      intro i _
      rw [term_mod m i, term_mod n i]
      simp only [term, Nat.Coprime.gcd_mul _ h]
      ring
    _ = ∑ i ∈ range m, ∑ j ∈ range n, term m i * term n j :=
      residue_sum m n hm hn h (fun i j => term m i * term n j)
    _ = _ := by
      change _ = (∑ i ∈ range m, term m i) * total n
      rw [sum_mul]
      refine sum_congr rfl fun i _ => ?_
      exact (mul_sum ..).symm

private lemma rotate {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (h : f n = f 0) :
    (∑ i ∈ range n, f (i+1)) = ∑ i ∈ range n, f i := by
  cases n with
  | zero => simp
  | succ n => rw [sum_range_succ (fun i => f (i+1)) n, sum_range_succ' f n, h]

private lemma gcd_sum (n : ℕ) :
    (∑ i ∈ range n, (i+1).gcd n) = ∑ r ∈ n.divisors, r.totient * (n/r) := by
  rw [rotate (fun i => i.gcd n) n (by simp)]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have within (k : ℕ) (_ : k ∈ range n) : n.gcd k ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn.ne'⟩
  calc
    _ = ∑ i ∈ range n, n.gcd i := by simp only [Nat.gcd_comm]
    _ = ∑ d ∈ n.divisors, (n/d).totient * d := by
      rw [← sum_fiberwise_of_maps_to' within (fun d : ℕ => d)]
      apply sum_congr rfl
      intro d hd
      rw [sum_const, ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd), nsmul_eq_mul]
      rfl
    _ = _ := by
      calc
        _ = ∑ d ∈ n.divisors, (n/d).totient * (n/(n/d)) := by
          apply sum_congr rfl
          intro d hd
          rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn.ne']
        _ = _ := Nat.sum_div_divisors n (fun d => d.totient * (n/d))

private lemma gcd_sum_pow (p e : ℕ) (hp : p.Prime) :
    (∑ i ∈ range (p^(e+1)), (i+1).gcd (p^(e+1))) =
      p^(e+1) + (e+1) * (p^e * (p-1)) := by
  rw [gcd_sum, Nat.sum_divisors_prime_pow hp, sum_range_succ']
  simp only [pow_zero, Nat.totient_one, Nat.div_one, one_mul]
  rw [add_comm]
  congr 1
  calc
    _ = ∑ j ∈ range (e+1), p^e * (p-1) := by
      apply sum_congr rfl
      intro j hj
      have le : j ≤ e := by simpa using hj
      have quotient : p^(e+1) / p^(j+1) = p^(e-j) := by
        simpa using Nat.pow_div (x := p) (show j+1 ≤ e+1 by omega) hp.pos
      rw [Nat.totient_prime_pow_succ hp, quotient]
      calc
        _ = (p^j * p^(e-j)) * (p-1) := by ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le le]
    _ = _ := by simp

private lemma total_pow (p e : ℕ) (hp : p.Prime) :
    total (p^(e+1)) = ((2*(e+1)+1)*p - 2*(e+1))*p^e := by
  let q := p^(e+1)
  have pointwise (i : ℕ) : term q i + 1 = (i+1).gcd q + (i+2).gcd q := by
    by_cases h : p ∣ i+1
    · have hn : ¬p ∣ i+2 := by
        intro hd
        exact hp.not_dvd_one (by simpa using Nat.dvd_sub hd h)
      have cop : (i+2).gcd q = 1 := ((hp.coprime_iff_not_dvd.mpr hn).pow_left (e+1)).symm
      simp [term, cop]
    · have cop : (i+1).gcd q = 1 := ((hp.coprime_iff_not_dvd.mpr h).pow_left (e+1)).symm
      simp [term, cop, Nat.add_comm]
  have rotate_gcd : (∑ i ∈ range q, (i+2).gcd q) = ∑ i ∈ range q, (i+1).gcd q := by
    exact rotate (fun i => (i+1).gcd q) q (by simp)
  have summed := sum_congr (s₁ := range q) rfl (fun i _ => pointwise i)
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one, rotate_gcd] at summed
  change total q + q = _ at summed
  dsimp [q] at summed ⊢
  rw [gcd_sum_pow p e hp] at summed
  have hsub : 2*(e+1) ≤ (2*(e+1)+1)*p := by nlinarith only [hp.one_lt, Nat.zero_le e]
  have hp' := Nat.sub_add_cancel (show 1 ≤ p by have := hp.one_lt; omega)
  have hs := Nat.sub_add_cancel hsub
  rw [pow_succ] at summed ⊢
  nlinarith only [summed, congrArg (· * p^e) hs,
    congrArg (fun x : ℕ => (e+1)*p^e*x) hp']

end AdjacentGcd

open Finset AdjacentGcd OMA.S_oeis_a384531

theorem OMA.solution : type_of% @OMA.S_oeis_a384531.main := by
  intro n hn
  change a n = total n
  rw [Nat.multiplicative_factorization total total_mul (by simp [total, term]) hn.ne']
  unfold a Finsupp.prod
  apply prod_congr rfl
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have pos := prime.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  rw [he]
  exact (total_pow p e prime).symm
