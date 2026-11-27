import OMAStatements.S_oeis_a003625
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.NormNum

open Polynomial

namespace OMA.P_oeis_a003625

private instance seven_prime : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem no_root_iff (p : ℕ) [Fact p.Prime] :
    Irreducible ((X : (ZMod p)[X]) ^ 2 + X + 2) ↔
      ¬ ∃ x : ZMod p, x*x + x + 2 = 0 := by
  let f := (X : (ZMod p)[X]) ^ 2 + X + 2
  have hd : f.natDegree = 2 := by
    simpa only [f, map_one, one_mul, map_ofNat] using
      (natDegree_quadratic (b := (1:ZMod p)) (c := 2) one_ne_zero)
  have hn : f ≠ 0 := by intro h; simp [h] at hd
  change Irreducible f ↔ _
  have hi : Irreducible f ↔ f.roots = 0 := irreducible_iff_roots_eq_zero_of_degree_le_three
    (by omega : 2 ≤ f.natDegree) (by omega : f.natDegree ≤ 3)
  have hv (x : ZMod p) : f.eval x = x*x + x + 2 := by
    calc f.eval x = x^2+x+2 := by
           simp only [f, eval_add, eval_pow, eval_X, eval_ofNat]
         _ = x*x+x+2 := by rw [pow_two]
  constructor
  · rintro hirr ⟨x,hx⟩
    have hr : x ∈ f.roots := (mem_roots hn).2 ((hv x).trans hx)
    rw [hi.1 hirr] at hr
    exact Multiset.notMem_zero _ hr
  · intro h
    apply hi.2
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    exact h ⟨x,(hv x).symm.trans ((mem_roots hn).1 hx)⟩

private theorem odd_discriminant (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∃ x : ZMod p, x*x+x+2 = 0) ↔ IsSquare (-7:ZMod p) := by
  letI : NeZero (2:ZMod p) := ⟨by simpa using ZMod.prime_ne_zero p 2 hp2⟩
  have hd : discrim (1:ZMod p) 1 2 = -7 := by norm_num [discrim]
  constructor
  · rintro ⟨x,hx⟩
    have h : (1:ZMod p)*(x*x) + 1*x + 2 = 0 := by simpa using hx
    refine ⟨2*1*x+1, ?_⟩
    rw [← hd, discrim_eq_sq_of_quadratic_eq_zero h, pow_two]
  · rintro ⟨s,hs⟩
    have h := exists_quadratic_eq_zero (a := (1:ZMod p)) (b := 1) (c := 2) one_ne_zero
      ⟨s,hd.trans hs⟩
    simpa using h

private theorem reciprocity (p : ℕ) [h : Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p (-7) = legendreSym 7 p := by
  have odd := h.out.eq_two_or_odd.resolve_left hp2
  have sign : (-1:ℤ) ^ (p/2 * (7/2)) = (-1:ℤ) ^ (p/2) := by
    rw [Nat.mul_comm, pow_mul]
    norm_num
  rw [legendreSym.at_neg hp2, ZMod.χ₄_eq_neg_one_pow odd]
  simpa only [sign, Nat.cast_ofNat] using
    (legendreSym.quadratic_reciprocity' (p := p) (q := 7) hp2 (by decide)).symm

theorem criterion (p : ℕ) [Fact p.Prime] :
    (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) ↔
      Irreducible ((X : (ZMod p)[X]) ^ 2 + X + 2) := by
  rw [no_root_iff]
  by_cases h2 : p = 2
  · subst p
    have h : ∃ x : ZMod 2, x*x+x+2=0 := ⟨0,by decide +revert⟩
    simp [h]
  rw [odd_discriminant p h2]
  have hn : ¬ IsSquare (-7:ZMod p) ↔ legendreSym p (-7) = -1 := by
    simpa using (legendreSym.eq_neg_one_iff (p:=p) (a:=(-7:ℤ))).symm
  rw [hn,reciprocity p h2,legendreSym.eq_neg_one_iff']
  have tab : ∀ r : ZMod 7, (¬ IsSquare r) ↔ r.val = 3 ∨ r.val = 5 ∨ r.val = 6 := by
    change ∀ r : ZMod 7, (¬ ∃ y : ZMod 7, r = y*y) ↔ _
    decide +kernel
  simpa using (tab (p:ZMod 7)).symm

end OMA.P_oeis_a003625

-- Federico Provvedi proposed the criterion. Jianing Song recorded the nonresidue equivalence.
theorem OMA.solution : type_of% @OMA.S_oeis_a003625.main := by
  intro p hp
  exact OMA.P_oeis_a003625.criterion p
