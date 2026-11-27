import OMAStatements.S_oeis_a290443
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The published middle coefficient contains `-2*-n`. The first admissible
index gives the nonzero residual 600. The negative middle coefficient
instead gives a recurrence valid at every admissible index. These conclusions
follow from the Catalan and Motzkin recurrence formulas. Proof by @anmolspace.
-/

namespace OMA.CatalanMotzkin
open OMA.S_oeis_a290443

private theorem catalan_step (k : ℕ) :
    ((k : ℚ)+2) * (catalan (k+1) : ℚ) = 2*(2*(k : ℚ)+1)*(catalan k : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [← succ_mul_catalan_eq_centralBinom (k+1), ← succ_mul_catalan_eq_centralBinom k] at h
  have z : ((k : ℚ)+1)*(((k : ℚ)+2)*(catalan (k+1) : ℚ)) =
      2*(2*(k : ℚ)+1)*(((k : ℚ)+1)*(catalan k : ℚ)) := by
    exact_mod_cast h
  have product : ((k : ℚ)+1) *
      (((k : ℚ)+2)*(catalan (k+1) : ℚ) - 2*(2*(k : ℚ)+1)*(catalan k : ℚ)) = 0 := by
    linear_combination z
  exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left (by positivity))

private theorem motzkin_step (k : ℕ) :
    ((k : ℚ)+4)*motzkin (k+2) =
      (2*(k : ℚ)+5)*motzkin (k+1) + 3*((k : ℚ)+1)*motzkin k := by
  rw [motzkin]
  have h : (k : ℚ)+4 ≠ 0 := by positivity
  field_simp

/-- Replacing the published `-2*-n` by `-2*n` gives an identity for all `n ≥ 3`. -/
theorem corrected (n : ℕ) (hn : 3 ≤ n) :
    (n : ℚ)*((n : ℚ)+1)^2*a n - 2*(n : ℚ)*(2*(n : ℚ)-1)^2*a (n-1)
      - 12*((n : ℚ)-2)*(2*(n : ℚ)-1)*(2*(n : ℚ)-3)*a (n-2) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have top := catalan_step (k+2)
  have mid := catalan_step (k+1)
  have mot := motzkin_step k
  simp only [a, show k+3-1 = k+2 by omega, show k+3-2 = k+1 by omega,
    show k+2-1 = k+1 by omega, show k+1-1 = k by omega]
  push_cast at top mid ⊢
  linear_combination ((k : ℚ)+3)*((k : ℚ)+4)*motzkin (k+2)*top
    + 2*((k : ℚ)+3)*(2*(k : ℚ)+5)*(catalan (k+2) : ℚ)*mot
    + 6*((k : ℚ)+1)*(2*(k : ℚ)+5)*motzkin k*mid

end OMA.CatalanMotzkin

open OMA.S_oeis_a290443 OMA.CatalanMotzkin in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290443.main) := by
  intro claimed
  have published := claimed 3 (by decide)
  have correct := corrected 3 (by decide)
  have term : a 2 = 2 := by norm_num [a, motzkin, catalan_two]
  norm_num at published correct
  linarith
