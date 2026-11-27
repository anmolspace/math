import OMAStatements.S_oeis_a253975
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Every positive multiplicity occurs in A253975

For `k = 3^(2*n+1)-1`, a representation amounts to `(x+1)*(y+1)=3^(2*n+1)`.
The smaller factor must be `3^j` for a unique `j` from `1` through `n`.
This is a bijection, which counts all the representations including the
ordering and lower-bound conditions in Alex Ratushnyak's conjecture.
Proof by @anmolspace, assisted by Codex.
-/

namespace OMA.A253975Proof

open OMA.S_oeis_a253975

private theorem factor_iff (x y k : ℕ) :
    x*y+x+y = k ↔ (x+1)*(y+1) = k+1 := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

private theorem add_one (e : ℕ) : 3^e-1+1 = (3:ℕ)^e :=
  Nat.sub_add_cancel (Nat.one_le_pow e 3 (by decide))

private def indexed (n : ℕ) (i : Fin n) : Representations (3^(2*n+1)-1) := by
  refine ⟨(3^(2*n-i.val)-1, 3^(i.val+1)-1), ?_, ?_, ?_⟩
  · change 1 < 3^(i.val+1)-1
    have h := Nat.pow_le_pow_right (by decide : 0 < 3) (show 1 ≤ i.val+1 by omega)
    simp only [pow_one] at h
    omega
  · change 3^(i.val+1)-1 ≤ 3^(2*n-i.val)-1
    exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega)) 1
  · apply (factor_iff _ _ _).mpr
    change (3^(2*n-i.val)-1+1) * (3^(i.val+1)-1+1) = 3^(2*n+1)-1+1
    rw [add_one, add_one, add_one, ← pow_add]
    congr 1
    omega

private theorem indexed_injective (n : ℕ) : Function.Injective (indexed n) := by
  intro i j hij
  have hy := congrArg (fun p : Representations (3^(2*n+1)-1) => p.val.2 + 1) hij
  change 3^(i.val+1)-1+1 = 3^(j.val+1)-1+1 at hy
  rw [add_one, add_one] at hy
  have he := Nat.pow_right_injective (by decide : 2 ≤ 3) hy
  exact Fin.ext (by omega)

private theorem indexed_surjective (n : ℕ) : Function.Surjective (indexed n) := by
  rintro ⟨⟨x,y⟩, hy, hyx, hk⟩
  change 1 < y at hy
  change y ≤ x at hyx
  change x*y+x+y = 3^(2*n+1)-1 at hk
  have hprod := (factor_iff _ _ _).mp hk
  rw [add_one] at hprod
  have dx : x+1 ∣ 3^(2*n+1) := ⟨y+1, hprod.symm⟩
  have dy : y+1 ∣ 3^(2*n+1) := ⟨x+1, by simpa [Nat.mul_comm] using hprod.symm⟩
  obtain ⟨a, _, hx⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp dx
  obtain ⟨b, _, hyy⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp dy
  rw [hx, hyy, ← pow_add] at hprod
  have hab := Nat.pow_right_injective (by decide : 2 ≤ 3) hprod
  have hba : b ≤ a := (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp (by omega)
  have hb : 0 < b := by
    by_contra! h
    have hz : b = 0 := by omega
    rw [hz, pow_zero] at hyy
    omega
  let i : Fin n := ⟨b-1, by omega⟩
  refine ⟨i, Subtype.ext ?_⟩
  have hi : i.val = b-1 := rfl
  have ha : 2*n-i.val = a := by omega
  have hb' : i.val+1 = b := by omega
  change (3^(2*n-i.val)-1, 3^(i.val+1)-1) = (x,y)
  rw [ha, hb', ← hx, ← hyy]
  simp

end OMA.A253975Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a253975.main := by
  intro n _
  exact ⟨3^(2*n+1)-1, ⟨Equiv.ofBijective _
    ⟨A253975Proof.indexed_injective n, A253975Proof.indexed_surjective n⟩⟩⟩
