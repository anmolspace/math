import OMAStatements.S_oeis_a350900
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace SchulteConvolution

open Finset ArithmeticFunction OMA.S_oeis_a350900


/-- Euler's totient as an arithmetic function. -/
private def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

/-- A002618 is n times its totient. -/
private def weight : ArithmeticFunction ℕ := ArithmeticFunction.id.pmul phi

/-- A057660 sums the orders of the elements of the cyclic group of size n. -/
private def cycleSum : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ k ∈ range n, n / n.gcd (k + 1), by simp⟩

/-- Schulte's double sum, with the identity function giving the triangle's row sum. -/
private def triangleSum {R : Type*} [CommSemiring R] (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => ∑ i ∈ range n, ∑ k ∈ range n,
    f (n.gcd (i + 1) / (n.gcd (i + 1)).gcd (k + 1)), by simp⟩



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

private lemma companion : cycleSum = weight * ArithmeticFunction.zeta := by
  ext n
  rw [mul_zeta_apply]
  change (∑ k ∈ range n, n / n.gcd (k+1)) = _
  change (∑ k ∈ range n, n / n.gcd (k+1)) = ∑ i ∈ n.divisors, i * i.totient
  simpa [nsmul_eq_mul, Nat.mul_comm] using one_period (fun x : ℕ => x) n

private lemma convolution {R : Type*} [CommSemiring R] (f : ArithmeticFunction R) :
    triangleSum f = f.pmul (phi : ArithmeticFunction R) * (cycleSum : ArithmeticFunction R) := by
  let b := f.pmul (phi : ArithmeticFunction R)
  let z : ArithmeticFunction R := ArithmeticFunction.zeta
  have hcomp : (cycleSum : ArithmeticFunction R) = z * (weight : ArithmeticFunction R) := by
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

private def normalized (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

private lemma shifted_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ i ∈ Icc 1 n, g i = ∑ i ∈ range n, g (i + 1) := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private lemma convert_rows (f : ℕ → ℂ) (n : ℕ) :
    weightedRowSum f n = triangleSum (normalized f) n := by
  unfold weightedRowSum
  rw [shifted_sum]
  change _ = ∑ i ∈ range n, ∑ k ∈ range n, normalized f
    (n.gcd (i+1) / (n.gcd (i+1)).gcd (k+1))
  refine sum_congr rfl fun i hi => ?_
  rw [shifted_sum]
  refine sum_congr rfl fun k _ => ?_
  have hd : 0 < n.gcd (i+1) := Nat.gcd_pos_of_pos_right _ (by omega)
  have den := Nat.gcd_pos_of_pos_right (n.gcd (i+1)) (Nat.succ_pos k)
  have positive : 0 < n.gcd (i+1) / (n.gcd (i+1)).gcd (k+1) :=
    Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_left _ _)) den
  let q := n.gcd (i+1) / (n.gcd (i+1)).gcd (k+1)
  change f _ = if q = 0 then 0 else f q
  rw [if_neg positive.ne']
  simp only [q, Nat.gcd_assoc, Nat.gcd_comm, Nat.gcd_left_comm]

private lemma order_value (m : ℕ) : cycleSum m = OMA.S_oeis_a350900.orderSum m := by
  rw [companion, mul_zeta_apply]
  rfl

private lemma divisor_formula (f : ℕ → ℂ) (n : ℕ) :
    weightedRowSum f n = ∑ d ∈ n.divisors, f d * (d.totient : ℂ) * (orderSum (n / d) : ℂ) := by
  rw [convert_rows, convolution, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e =>
      ((normalized f).pmul (phi : ArithmeticFunction ℂ)) d * (cycleSum : ArithmeticFunction ℂ) e)]
  refine sum_congr rfl fun d hd => ?_
  have hpos := Nat.pos_of_mem_divisors hd
  change (if d = 0 then 0 else f d) * (d.totient : ℂ) * (cycleSum (n / d) : ℂ) = _
  rw [if_neg hpos.ne', order_value]

private lemma normalized_mult (f : ℕ → ℂ) (hf : OMA.S_oeis_a350900.IsMultiplicative f) :
    (normalized f).IsMultiplicative := by
  refine ⟨by simpa [normalized] using hf.1, ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · subst a; simp [normalized]
  by_cases hb : b = 0
  · subst b; simp [normalized]
  simp [normalized, ha, hb, hf.2 a b hab]

private lemma rows_mult (f : ℕ → ℂ) (hf : OMA.S_oeis_a350900.IsMultiplicative f) :
    OMA.S_oeis_a350900.IsMultiplicative (weightedRowSum f) := by
  have ho : cycleSum.IsMultiplicative := by
    rw [companion]
    exact (isMultiplicative_id.pmul phi_mult).mul isMultiplicative_zeta
  have hm : (triangleSum (normalized f)).IsMultiplicative := by
    rw [convolution]
    exact ((normalized_mult f hf).pmul phi_mult.natCast).mul ho.natCast
  exact ⟨by simpa only [convert_rows] using hm.1,
    fun a b hab => by simpa only [convert_rows] using hm.2 hab⟩

private lemma square_totient {d : ℕ} (hd : 0 < d) : (d ^ 2).totient = d * d.totient := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hd)
  simpa [pow_two, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using
    Nat.totient_gcd_mul_totient_mul d d

end SchulteConvolution

open Finset OMA.S_oeis_a350900 SchulteConvolution

theorem OMA.solution : type_of% @OMA.S_oeis_a350900.main := by
  refine ⟨fun f n _ => divisor_formula f n, rows_mult, ?_⟩
  intro n _
  rw [divisor_formula]
  refine sum_congr rfl fun d hd => ?_
  rw [square_totient (Nat.pos_of_mem_divisors hd), Nat.cast_mul]
