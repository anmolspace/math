import OMAStatements.S_oeis_a273400
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Growth of the decimal length of the third Catalan iterate

The Catalan recurrence implies doubling from index one. Thus `C(t+1) ≥ 2^t`.
For `t ≥ 12`, this gives `C(t) ≥ 4*t^2+1` and `C(C(t)) ≥ 10^(t^2)`.
It follows that the decimal length of the triple iterate eventually exceeds
every constant multiple of `C(n)`, as well as satisfying Puszkarz's explicit
finite-exception formulation. Proof by @anmolspace, assisted by Codex.
-/

namespace OMA.A273400Proof

open OMA.S_oeis_a273400

private theorem double_step (n : ℕ) (hn : 1 ≤ n) :
    2 * catalan n ≤ catalan (n+1) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1), ← succ_mul_catalan_eq_centralBinom n] at h
  have h' : (n+1)*((n+2)*catalan (n+1)) = (n+1)*(2*(2*n+1)*catalan n) := by
    calc
      _ = 2*(2*n+1)*((n+1)*catalan n) := h
      _ = _ := by ring
  have hstep := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n+1) h'
  have hb : (n+2)*(2*catalan n) ≤ (n+2)*catalan (n+1) := by
    rw [hstep]
    calc
      (n+2)*(2*catalan n) = (2*(n+2))*catalan n := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  exact Nat.le_of_mul_le_mul_left hb (by omega)

private theorem exponential_lower (n : ℕ) : 2^n ≤ catalan (n+1) := by
  induction n with
  | zero => simp [catalan_one]
  | succ n ih =>
    calc
      2^(n+1) = 2*2^n := by rw [pow_succ, Nat.mul_comm]
      _ ≤ 2*catalan (n+1) := Nat.mul_le_mul_left 2 ih
      _ ≤ _ := double_step (n+1) (by omega)

private theorem index_lower (n : ℕ) : n ≤ catalan n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact (Nat.lt_two_pow_self (n := n)).trans_le (exponential_lower n)

private theorem square_lower (u : ℕ) : 4*(u+12)^2+1 ≤ 2^(u+11) := by
  induction u with
  | zero => decide
  | succ u ih =>
    rw [show u+1+11 = (u+11)+1 by omega, pow_succ 2 (u+11)]
    nlinarith [Nat.zero_le (u*u)]

private theorem digit_lower {t : ℕ} (ht : 12 ≤ t) :
    t^2 < (Nat.digits 10 (catalan (catalan t))).length := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u+12 := ⟨t-12, by omega⟩
  have e1 := exponential_lower (u+11)
  have hcat : 4*(u+12)^2+1 ≤ catalan (u+12) := (square_lower u).trans e1
  have e2 := exponential_lower (catalan (u+12)-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ catalan (u+12))] at e2
  apply (Nat.lt_digits_length_iff (b := 10) (by decide) _).mpr
  calc
    10^((u+12)^2) ≤ (2^4)^((u+12)^2) := Nat.pow_le_pow_left (by decide) _
    _ = 2^(4*(u+12)^2) := (pow_mul _ _ _).symm
    _ ≤ 2^(catalan (u+12)-1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ _ := e2

/-- A stronger reading of the asymptotic claim: every fixed multiple is exceeded. -/
theorem dominates_every_multiple (m : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, m*catalan n < (Nat.digits 10 (a n)).length := by
  refine ⟨max m 12, ?_⟩
  intro n hn
  have hcn := index_lower n
  have h1 : m ≤ catalan n := (le_max_left _ _).trans (hn.trans hcn)
  have h2 : 12 ≤ catalan n := (le_max_right _ _).trans (hn.trans hcn)
  have hm : m*catalan n ≤ (catalan n)^2 := by
    simpa [pow_two] using Nat.mul_le_mul_right (catalan n) h1
  exact hm.trans_lt (digit_lower h2)

end OMA.A273400Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a273400.main := by
  obtain ⟨N, h⟩ := A273400Proof.dominates_every_multiple 1
  apply (Set.finite_lt_nat N).subset
  intro n hn
  change (Nat.digits 10 (S_oeis_a273400.a n)).length < catalan n at hn
  change n < N
  by_contra! hN
  have hd := h n hN
  omega
