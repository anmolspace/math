import OMAStatements.S_oeis_a339387
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace ModularDivisorSums

open Finset OMA.S_oeis_a339387

private def leftTerm (n k : ℕ) := quotient n k % k
private def rightTerm (n k : ℕ) := quotient n k % n

/-- Write n = m g and k = t g, where g is their gcd. The common quotient is m t. -/
private lemma residues {n k g m t : ℕ} (hg : 0 < g) (hd : n.gcd k = g)
    (hn : n = m * g) (hk : k = t * g) :
    leftTerm n k = (m % g) * t ∧ rightTerm n k = m * (t % g) := by
  have hq : quotient n k = m * t := by
    unfold quotient
    rw [Nat.lcm_eq_mul_div, hd, hn, hk,
      show m * g * (t * g) = (m * t * g) * g by ring,
      Nat.mul_div_cancel _ hg, Nat.mul_div_cancel _ hg]
  constructor
  · unfold leftTerm
    rw [hq, hk, Nat.mul_comm t g, Nat.mul_mod_mul_right]
  · unfold rightTerm
    rw [hq, hn, Nat.mul_mod_mul_left]

/-- The reflection k ↦ n − k preserves g, and the two reduced indices sum to m. -/
private lemma paired {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    let g := n.gcd k
    let m := n / g
    let t := k / g
    let u := (n - k) / g
    leftTerm n k + leftTerm n (n - k) = m * (m % g) ∧
    rightTerm n k + rightTerm n (n - k) = m * (t % g + u % g) ∧ m = t + u := by
  let g := n.gcd k
  let m := n / g
  let t := k / g
  let u := (n - k) / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have href : n.gcd (n - k) = g := Nat.gcd_self_sub_right hk
  have hn' : n = m * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left n k)).symm
  have hk' : k = t * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right n k)).symm
  have hu : n - k = u * g := (Nat.div_mul_cancel (href ▸ Nat.gcd_dvd_right n (n-k))).symm
  have parts : m = t + u := by
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [add_mul, ← hn', ← hk', ← hu]
    omega
  obtain ⟨lk, rk⟩ := residues hg rfl hn' hk'
  obtain ⟨lu, ru⟩ := residues hg href hn' hu
  exact ⟨by rw [lk, lu, ← mul_add, ← parts, mul_comm],
    by rw [rk, ru, ← mul_add], parts⟩

private lemma pair_le {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    leftTerm n k + leftTerm n (n-k) ≤ rightTerm n k + rightTerm n (n-k) := by
  obtain ⟨hl, hr, hsum⟩ := paired hn hk
  rw [hl, hr]
  apply Nat.mul_le_mul_left
  rw [hsum, Nat.add_mod]
  exact Nat.mod_le _ _

/-- If p² divides n, then k = p has reduced index one and both left residues vanish. -/
private lemma strict_at_prime {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hsq : p * p ∣ n) :
    leftTerm n p + leftTerm n (n-p) < rightTerm n p + rightTerm n (n-p) := by
  have hd : p ∣ n := (dvd_mul_right p p).trans hsq
  have hle := Nat.le_of_dvd hn hd
  have hd' : p ∣ n / p := (Nat.dvd_div_iff_mul_dvd hd).mpr hsq
  obtain ⟨hl, hr, _⟩ := paired hn hle
  rw [hl, hr, Nat.gcd_eq_right hd, Nat.mod_eq_zero_of_dvd hd', Nat.mul_zero,
    Nat.div_self hp.pos, Nat.mod_eq_of_lt hp.one_lt]
  exact Nat.mul_pos (Nat.div_pos hle hp.pos) (by omega)

private lemma reflect_sum (f : ℕ → ℕ) (n : ℕ) :
    (∑ k ∈ Ico 1 n, f (n - k)) = ∑ k ∈ Ico 1 n, f k := by
  simpa using sum_Ico_reflect f 1 (show n ≤ n + 1 by omega)

end ModularDivisorSums

open Finset OMA.S_oeis_a339387 ModularDivisorSums

theorem OMA.solution : type_of% @OMA.S_oeis_a339387.main := by
  intro n hn hequal
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hsq
  have hpn : p < n := by
    have h := Nat.le_of_dvd hn hsq
    nlinarith [hp.two_le]
  have strict := Finset.sum_lt_sum
    (s := Ico 1 n) (f := fun k => leftTerm n k + leftTerm n (n-k))
    (g := fun k => rightTerm n k + rightTerm n (n-k))
    (fun k hk => pair_le hn (mem_Ico.mp hk).2.le)
    ⟨p, mem_Ico.mpr ⟨hp.pos, hpn⟩, strict_at_prime hn hp hsq⟩
  simp only [sum_add_distrib, reflect_sum] at strict
  change (∑ k ∈ Ico 1 (n + 1), leftTerm n k) = ∑ k ∈ Ico 1 (n + 1), rightTerm n k at hequal
  rw [sum_Ico_succ_top hn, sum_Ico_succ_top hn] at hequal
  have same : leftTerm n n = rightTerm n n := rfl
  rw [same] at hequal
  have eqsum : (∑ k ∈ Ico 1 n, leftTerm n k) = ∑ k ∈ Ico 1 n, rightTerm n k :=
    Nat.add_right_cancel hequal
  rw [eqsum] at strict
  exact (Nat.lt_irrefl _) strict
