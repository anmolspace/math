import OMAStatements.S_oeis_a350900
import Mathlib.Tactic

namespace SchulteConvolution

open Finset ArithmeticFunction OMA.S_oeis_a350900

private lemma rotate {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (h : f n = f 0) :
    (∑ i ∈ range n, f (i + 1)) = ∑ i ∈ range n, f i := by
  cases n with
  | zero => simp
  | succ n => rw [sum_range_succ (fun i => f (i+1)) n, sum_range_succ' f n, h]

/-- Exactly φ(n/d) residues have gcd d with n. -/
private lemma group_gcd {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    (∑ k ∈ range n, f (n.gcd (k + 1))) = ∑ d ∈ n.divisors, (n / d).totient • f d := by
  rw [rotate (fun k => f (n.gcd k)) n (by simp)]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have within (k : ℕ) (_ : k ∈ range n) : n.gcd k ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn.ne'⟩
  rw [← sum_fiberwise_of_maps_to' within f]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_const, ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]

/-- The complementary gcd quotient takes value r exactly φ(r) times in one period. -/
private lemma one_period {M : Type*} [AddCommMonoid M] (f : ℕ → M) (d : ℕ) :
    (∑ k ∈ range d, f (d / d.gcd (k+1))) = ∑ r ∈ d.divisors, r.totient • f r := by
  calc
    _ = ∑ e ∈ d.divisors, (d / e).totient • f (d / e) := group_gcd (fun e => f (d/e)) d
    _ = _ := Nat.sum_div_divisors d (fun r => r.totient • f r)

private lemma repeat_period {M : Type*} [AddCommMonoid M] (f : ℕ → M) (d q : ℕ) :
    (∑ k ∈ range (q*d), f (d / d.gcd (k+1))) =
      q • ∑ r ∈ d.divisors, r.totient • f r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add, ih, succ_nsmul]
    congr 1
    calc
      _ = ∑ k ∈ range d, f (d / d.gcd (k+1)) := by
        apply sum_congr rfl
        intro k _
        rw [Nat.add_assoc, Nat.gcd_mul_right_add_right]
      _ = _ := one_period f d

private lemma expand_sum {R : Type*} [CommSemiring R] (f : ArithmeticFunction R) (n : ℕ) :
    triangleSum f n = ∑ d ∈ n.divisors, (n/d).totient • ((n/d) •
      (∑ r ∈ d.divisors, r.totient • f r)) := by
  change (∑ i ∈ range n, ∑ k ∈ range n, f (n.gcd (i+1) / (n.gcd (i+1)).gcd (k+1))) = _
  rw [group_gcd (fun d => ∑ k ∈ range n, f (d / d.gcd (k+1))) n]
  refine sum_congr rfl fun d hd => ?_
  have hp := repeat_period (fun x => f x) d (n/d)
  rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)] at hp
  rw [hp]

private lemma companion : orderSum = weight * ArithmeticFunction.zeta := by
  ext n
  rw [mul_zeta_apply]
  change (∑ k ∈ range n, n / n.gcd (k+1)) = _
  change (∑ k ∈ range n, n / n.gcd (k+1)) = ∑ i ∈ n.divisors, i * i.totient
  simpa [nsmul_eq_mul, Nat.mul_comm] using one_period (fun x : ℕ => x) n

private lemma convolution {R : Type*} [CommSemiring R] (f : ArithmeticFunction R) :
    triangleSum f = f.pmul (phi : ArithmeticFunction R) * (orderSum : ArithmeticFunction R) := by
  let b := f.pmul (phi : ArithmeticFunction R)
  let z : ArithmeticFunction R := ArithmeticFunction.zeta
  have hcomp : (orderSum : ArithmeticFunction R) = z * (weight : ArithmeticFunction R) := by
    rw [companion, natCoe_mul, mul_comm]
  rw [hcomp, ← mul_assoc]
  ext n
  rw [expand_sum, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => (b*z) d * (weight : ArithmeticFunction R) e)]
  refine sum_congr rfl fun d _ => ?_
  change (n/d).totient • ((n/d) • (∑ r ∈ d.divisors, r.totient • f r)) =
    (b * (ArithmeticFunction.zeta : ArithmeticFunction R)) d * (weight : ArithmeticFunction R) (n/d)
  rw [coe_mul_zeta_apply]
  have inner : (∑ r ∈ d.divisors, r.totient • f r) = ∑ r ∈ d.divisors, b r := by
    refine sum_congr rfl fun r _ => ?_
    rw [nsmul_eq_mul]
    change (r.totient : R) * f r = f r * (r.totient : R)
    exact mul_comm _ _
  rw [inner]
  simp only [nsmul_eq_mul]
  change ((n/d).totient : R) * ((n/d : ℕ) * (∑ r ∈ d.divisors, b r)) =
    (∑ r ∈ d.divisors, b r) * (((n/d) * (n/d).totient : ℕ) : R)
  rw [Nat.cast_mul]
  ring

private lemma phi_mult : phi.IsMultiplicative :=
  ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩

end SchulteConvolution

open ArithmeticFunction OMA.S_oeis_a350900 SchulteConvolution

theorem OMA.solution : type_of% @OMA.S_oeis_a350900.main := by
  refine ⟨fun _ _ f => convolution f, ?_, ?_⟩
  · intro R _ f hf
    rw [convolution]
    have ho : orderSum.IsMultiplicative := by
      rw [companion]
      exact (isMultiplicative_id.pmul phi_mult).mul isMultiplicative_zeta
    exact (hf.pmul phi_mult.natCast).mul ho.natCast
  · simpa [weight] using convolution ArithmeticFunction.id
