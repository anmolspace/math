import OMAStatements.S_oeis_a151341
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The recurrence for the Catalan–Motzkin excursion counts

Combine the Motzkin recurrence with two consecutive Catalan identities.
The walk decomposition that gives their product is recorded in the statement.
Proof and formalization by @anmolspace, assisted by Codex.
-/

namespace OMA.QuarterPlaneExcursions
open OMA.S_oeis_a151341

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

end OMA.QuarterPlaneExcursions

open OMA.S_oeis_a151341 OMA.QuarterPlaneExcursions in
theorem OMA.solution : type_of% @OMA.S_oeis_a151341.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have top := catalan_step (k+1)
  have mid := catalan_step k
  have mot := motzkin_step k
  simp only [a, show k+2-1 = k+1 by omega, show k+2-2 = k by omega]
  push_cast at top ⊢
  linear_combination ((k : ℚ)+2)*((k : ℚ)+4)*motzkin (k+2)*top
    + 2*((k : ℚ)+2)*(2*(k : ℚ)+3)*(catalan (k+1) : ℚ)*mot
    + 6*((k : ℚ)+1)*(2*(k : ℚ)+3)*motzkin k*mid
