import OMAReductions.R_oeis_a105403_R1

/-!
The four indices in this finite direction of Schoenfield's conjecture are
checked by counting primes below their two endpoints. Mathlib's square-root
criterion supplies a short bounded primality decision. The prime-index
identity is `Nat.nth_count`, as in the earlier proofs in PRs 9868 and 10156.
-/
open OMA.S_oeis_a105403

private def trialPrime (n : ℕ) : Decidable (Nat.Prime n) :=
  decidable_of_iff (2 ≤ n ∧ ∀ d < n.sqrt + 1, 2 ≤ d → ¬ d ∣ n) (by
    rw [Nat.prime_def_le_sqrt]
    constructor
    · rintro ⟨hn, h⟩
      exact ⟨hn, fun d hd hs => h d (by omega) hd⟩
    · rintro ⟨hn, h⟩
      exact ⟨hn, fun d hs hd => h d hd (by omega)⟩)

private theorem checkPair {n : ℕ} (a b : ℕ)
    (ranks : 1 ≤ n ∧ a.Prime ∧ b.Prime ∧
      @Nat.count Nat.Prime trialPrime a = n - 1 ∧ @Nat.count Nat.Prime trialPrime b = n)
    (factors : gpf (a - 1) = gpf (b - 1)) :
    n ∈ {k : ℕ | 1 ≤ k ∧ gpf (prime k - 1) = gpf (prime (k + 1) - 1)} := by
  obtain ⟨hn, ha, hb, ca, cb⟩ := ranks
  refine ⟨hn, ?_⟩
  simp only [prime, Nat.add_sub_cancel]
  rw [← ca, @Nat.nth_count Nat.Prime trialPrime a ha,
    ← cb, @Nat.nth_count Nat.Prime trialPrime b hb]
  exact factors

set_option maxRecDepth 8192 in
theorem OMA.solution : OMA.R_oeis_a105403_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact checkPair 3 5 (by decide +kernel) (by simp [gpf, Nat.primeFactors])
  · exact checkPair 113 127 (by decide +kernel) (by simp [gpf, Nat.primeFactors])
  · exact checkPair 241 251 (by decide +kernel) (by simp [gpf, Nat.primeFactors])
  · exact checkPair 1327 1361 (by decide +kernel) (by simp [gpf, Nat.primeFactors])
