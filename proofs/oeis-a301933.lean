import OMAStatements.S_oeis_a301933
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-!
Paul D. Hanna's differential equation simplifies modulo two. Its derivative
then forces Y′=1, proving both the conjecture and the observation about Y·Y′.
-/


namespace OMA.HannaDyadic

theorem support_two (c : ℕ → ZMod 2) (hone : c 1 = 1)
    (step : ∀ n, 1 < n → c n = if 2 ∣ n then c (n/2) else 0) :
    ∀ n : ℕ, 0 < n → (c n = 1 ↔ ∃ k : ℕ, n = 2^k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      exact ⟨fun _ => ⟨0,rfl⟩, fun _ => hone⟩
    have h2 : 1 < n := by omega
    rw [step n h2]
    by_cases he : 2 ∣ n
    · rw [if_pos he, ih (n/2) (by omega) (by omega)]
      constructor
      · rintro ⟨k,hk⟩
        exact ⟨k+1, by rw [pow_succ, ← hk]; omega⟩
      · rintro ⟨k,hk⟩
        cases k with
        | zero => exact (h1 (hk.trans (pow_zero 2))).elim
        | succ k => exact ⟨k, by rw [hk,pow_succ]; omega⟩
    · rw [if_neg he]
      constructor
      · intro h
        contradiction
      · rintro ⟨k,hk⟩
        cases k with
        | zero => exact (h1 (hk.trans (pow_zero 2))).elim
        | succ k => exact (he ⟨2^k, by rw [hk,pow_succ,Nat.mul_comm]⟩).elim

end OMA.HannaDyadic


namespace OMA.DifferentialFrobenius
open PowerSeries
abbrev Series := PowerSeries (ZMod 2)

private theorem square (f : Series) : f^2 = expand 2 (by decide) f := by
  have hf := MvPowerSeries.map_frobenius_expand 2 (by decide : 2 ≠ 0) (f := f)
  have hid : frobenius (ZMod 2) 2 = RingHom.id _ := Subsingleton.elim _ _
  simpa [hid, PowerSeries.expand] using hf.symm

end OMA.DifferentialFrobenius

namespace OMA.HannaDifferential
open PowerSeries

abbrev Series := PowerSeries (ZMod 2)
private abbrev red := Int.castRingHom (ZMod 2)

private theorem reduce_derivative (A : PowerSeries ℤ) :
    (d⁄dX ℤ A).map red = d⁄dX (ZMod 2) (A.map red) := by
  ext n
  simp [coeff_map,coeff_derivative,red]

private theorem derivative_twice (Y : Series) : d⁄dX (ZMod 2) (d⁄dX (ZMod 2) Y) = 0 := by
  ext n
  have h : ∀ v : ZMod 2, (v+1)*v = 0 := by decide
  simp only [coeff_derivative, Nat.cast_add, Nat.cast_one, map_zero, mul_assoc, h, mul_zero]

theorem parity (A : PowerSeries ℤ) (ha : OMA.S_oeis_a301933.Defines A) : ∀ n : ℕ, 0 < n →
    (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k) ∧
    (Odd (coeff n (A * d⁄dX ℤ A)) ↔ ∃ k : ℕ, n = 2^k) := by
  let Y := A.map red
  have oneC : coeff 1 Y = 1 := by simp [Y, coeff_map, red, ha.2.1]
  have two : (2 : Series) = 0 := by
    simpa only [map_ofNat,map_zero] using
      congrArg (PowerSeries.C : ZMod 2 →+* Series) (by decide : (2 : ZMod 2) = 0)
  have four : (4 : Series) = 0 := by linear_combination 2*two
  have eq1 := congrArg (PowerSeries.map red) ha.2.2
  simp only [map_mul,map_one,map_add,map_ofNat,PowerSeries.map_X,reduce_derivative,
    four,zero_mul,add_zero,mul_one] at eq1
  change Y*(1+Y*d⁄dX (ZMod 2) Y) = X at eq1
  have relation : Y = X + Y^2*d⁄dX (ZMod 2) Y := by
    linear_combination eq1 - Y^2*(d⁄dX (ZMod 2) Y)*two
  have derivative_one : d⁄dX (ZMod 2) Y = 1 := by
    have hd := congrArg (d⁄dX (ZMod 2)) relation
    simpa [map_add,derivative_X,Derivation.leibniz,derivative_pow,derivative_twice,two] using hd
  rw [derivative_one,mul_one] at relation
  have step (n : ℕ) (hn : 1 < n) :
      coeff n Y = if 2 ∣ n then coeff (n/2) Y else 0 := by
    have h := congrArg (coeff n) relation
    rw [map_add, OMA.DifferentialFrobenius.square, coeff_expand] at h
    simpa [coeff_X, show n ≠ 1 by omega] using h
  have factor : (A * d⁄dX ℤ A).map red = Y := by
    rw [map_mul,reduce_derivative]
    change Y * d⁄dX (ZMod 2) Y = Y
    rw [derivative_one,mul_one]
  intro n hn
  have ans := OMA.HannaDyadic.support_two (fun i => coeff i Y) oneC step n hn
  constructor
  · simpa only [Y, coeff_map, red, Int.coe_castRingHom, ZMod.intCast_eq_one_iff_odd] using ans
  · rw [← factor] at ans
    simpa only [coeff_map, red, Int.coe_castRingHom, ZMod.intCast_eq_one_iff_odd] using ans

end OMA.HannaDifferential


namespace OMA.HannaDifferentialExistence

open PowerSeries

private abbrev Series := PowerSeries ℤ

private def Agree (k : ℕ) (f g : Series) : Prop := (X : Series)^k ∣ f-g

private theorem agree_iff {k : ℕ} {f g : Series} :
    Agree k f g ↔ ∀ i < k, coeff i f = coeff i g := by
  simp [Agree, X_pow_dvd_iff, sub_eq_zero]

private theorem agree_mul {k : ℕ} {a b c d : Series}
    (hab : Agree k a b) (hcd : Agree k c d) : Agree k (a*c) (b*d) := by
  change X^k ∣ a*c-b*d
  rw [show a*c-b*d = (a-b)*c+b*(c-d) by ring]
  exact dvd_add (dvd_mul_of_dvd_left hab _) (dvd_mul_of_dvd_right hcd _)

/-- The Euler derivative multiplies the ith coefficient by i. -/
private noncomputable def euler (b : Series) : Series := X * d⁄dX ℤ b

private theorem euler_agree {k : ℕ} {b c : Series} (h : Agree k b c) :
    Agree k (euler b) (euler c) := by
  apply agree_iff.mpr
  intro i hi
  cases i with
  | zero => simp [euler, coeff_zero_eq_constantCoeff]
  | succ n =>
    simp only [euler, coeff_succ_X_mul, coeff_derivative, agree_iff.mp h (n+1) hi]

/-- After writing A = XB, the differential equation becomes B = step B. -/
private noncomputable def term (b : Series) : Series := b*(4-b)*(b+euler b)
private noncomputable def step (b : Series) : Series := 1+X*term b

private theorem step_zero (b : Series) : (step b).constantCoeff = 1 := by simp [step]

/-- The outer factor X allows the next coefficient to be recovered integrally. -/
private theorem step_agree {k : ℕ} {b c : Series} (h : Agree k b c) :
    Agree (k+1) (step b) (step c) := by
  have sub : Agree k (4-b) (4-c) := by
    apply agree_iff.mpr
    intro i hi
    simp only [map_sub, agree_iff.mp h i hi]
  have add : Agree k (b+euler b) (c+euler c) := by
    apply agree_iff.mpr
    intro i hi
    simp only [map_add, agree_iff.mp h i hi, agree_iff.mp (euler_agree h) i hi]
  have ht : Agree k (term b) (term c) := agree_mul (agree_mul h sub) add
  obtain ⟨t, hterm⟩ := ht
  refine ⟨t, ?_⟩
  calc
    _ = X*(term b-term c) := by dsimp [step]; ring
    _ = _ := by rw [hterm, pow_succ]; ring

private noncomputable def approx : ℕ → Series
  | 0 => 1
  | n+1 => step (approx n)

private theorem approx_zero (n : ℕ) : (approx n).constantCoeff = 1 := by
  cases n with
  | zero => simp [approx]
  | succ n => exact step_zero _

private theorem successive (n : ℕ) : Agree (n+1) (approx n) (approx (n+1)) := by
  induction n with
  | zero =>
    apply agree_iff.mpr
    intro i hi
    have : i = 0 := by omega
    simp [this, coeff_zero_eq_constantCoeff, approx_zero]
  | succ n ih => exact step_agree ih

private theorem stabilized (i n : ℕ) (hin : i ≤ n) :
    coeff i (approx i) = coeff i (approx n) := by
  induction n, hin using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact ih.trans (agree_iff.mp (successive n) i (by omega))

private noncomputable def limit : Series := mk fun i => coeff i (approx i)

private theorem limit_zero : limit.constantCoeff = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, limit, coeff_mk, coeff_zero_eq_constantCoeff_apply]
  exact approx_zero 0

private theorem fixed : step limit = limit := by
  ext i
  have h : Agree (i+1) limit (approx i) := by
    apply agree_iff.mpr
    intro j hj
    rw [limit, coeff_mk]
    exact stabilized j i (by omega)
  have hh := agree_iff.mp (step_agree h) i (by omega)
  change coeff i (step limit) = coeff i (approx (i+1)) at hh
  rw [limit, coeff_mk]
  exact hh.trans (stabilized i (i+1) (by omega)).symm

/-- Stabilized integer coefficients give a normalized solution of Hanna's equation. -/
theorem existence : ∃ A, S_oeis_a301933.Defines A := by
  let b := limit
  have hf : 1+X*(b*(4-b)*(b+euler b)) = b := fixed
  have hd : d⁄dX ℤ (X*b) = b+euler b := by
    rw [(derivative ℤ).leibniz, derivative_X]
    simp [euler, smul_eq_mul, add_comm]
  refine ⟨X*b, by simp, ?_, ?_⟩
  · simpa only [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] using limit_zero
  · rw [hd]
    linear_combination -X * hf

end OMA.HannaDifferentialExistence

theorem OMA.solution : type_of% @OMA.S_oeis_a301933.main :=
  ⟨OMA.HannaDifferentialExistence.existence, OMA.HannaDifferential.parity⟩
