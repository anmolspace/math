import OMAStatements.S_oeis_a254074

/-!
Source: https://oeis.org/A254074
Credit: @anmolspace. Felix Fröhlich defined the sequence. Chai Wah Wu posed
the nondivisibility conjecture in 2017. A number ending in five has a square
ending in twenty-five, which violates the lower digit bound.
-/

namespace OMA.A254074Proof

private theorem units_mem {n : ℕ} (hn : n ≠ 0) : n % 10 ∈ Nat.digits 10 n := by
  rw [Nat.digits_eq_cons_digits_div (by decide) hn]
  exact List.mem_cons_self

private theorem tens_mem {n : ℕ} (hn : n / 10 ≠ 0) : n / 10 % 10 ∈ Nat.digits 10 n := by
  rw [Nat.digits_eq_cons_digits_div (by decide) (show n ≠ 0 by omega)]
  exact List.mem_cons_of_mem _ (units_mem hn)

end OMA.A254074Proof

open OMA.S_oeis_a254074 OMA.A254074Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a254074.main := by
  rintro n ⟨hn, hs⟩ h5
  have hn0 : n ≠ 0 := by
    intro hz
    simpa [hz] using hn.1
  have hlast := (hn.2.2 _ (units_mem hn0)).1
  have hrem : n % 10 = 5 := by omega
  obtain ⟨t, hform⟩ : ∃ t : ℕ, n = 10 * t + 5 := ⟨n / 10, by omega⟩
  have hsquare : n ^ 2 = 100 * (t ^ 2 + t) + 25 := by rw [hform]; ring
  have htens : n ^ 2 / 10 % 10 = 2 := by rw [hsquare]; omega
  have hmem := tens_mem (n := n ^ 2) (by rw [hsquare]; omega)
  have hbound := (hs.2.2 _ hmem).1
  omega
