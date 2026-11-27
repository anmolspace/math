import OMAStatements.S_oeis_a264100

open Finset OMA.S_oeis_a264100

private theorem diff_total (n : ℕ) :
    totalLength (n+1) - totalLength n = endingWeight n := by
  simp [totalLength, Finset.sum_range_succ]

private theorem upper_endpoint (n : ℕ) :
    ∑ k ∈ Icc 1 (n+1), (k+1)*(n/k) = ∑ k ∈ Icc 1 n, (k+1)*(n/k) := by
  have h : Icc 1 (n+1) = insert (n+1) (Icc 1 n) := by ext k; simp; omega
  rw [h,sum_insert (by simp)]
  simp

private theorem divisor_jump (n : ℕ) :
    ∑ k ∈ Icc 1 (n+1), (if k ∣ n+1 then k+1 else 0) =
      (∑ d ∈ (n+1).divisors, d)+(n+1).divisors.card := by
  have eq : (Icc 1 (n+1)).filter (fun k => k ∣ n+1) = (n+1).divisors := by
    ext k
    constructor
    · intro hk
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hk).2,by omega⟩
    · intro hk
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hk,Nat.divisor_le hk⟩,
        (Nat.mem_divisors.mp hk).1⟩
  rw [← sum_filter,eq,sum_add_distrib]
  simp

theorem OMA.solution : type_of% @OMA.S_oeis_a264100.main := by
  intro n
  rw [show n+2 = (n+1)+1 by omega, diff_total, diff_total]
  have update :
      ∑ k ∈ Icc 1 (n+1), (k+1)*((n+1)/k) =
        (∑ k ∈ Icc 1 n, (k+1)*(n/k)) +
        ((∑ d ∈ (n+1).divisors, d)+(n+1).divisors.card) := by
    rw [← upper_endpoint n,← divisor_jump n,← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    rw [Nat.succ_div,Nat.mul_add]
    by_cases h : k ∣ n+1 <;> simp [h]
  unfold endingWeight
  rw [update]
  omega
