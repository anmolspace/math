import OMAStatements.S_oeis_a334765

-- Credit: @anmolspace. Thomas König posed the conjecture and found the first run of three.

open OMA.S_oeis_a334765

private lemma trit_parity (n : ℕ) : balancedSum n % 2 = (n : ℤ) % 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [balancedSum]
    split
    · rename_i h
      subst n
      decide
    · have hq := ih ((n+1)/3) (by omega)
      dsimp only
      omega

private lemma parity_of_match (n : ℕ) (hm : digitMatch n = true) :
    ((Nat.digits 2 n).sum : ℤ) % 2 = (n : ℤ) % 2 := by
  have h : ((Nat.digits 2 n).sum : ℤ) = -balancedSum n := of_decide_eq_true hm
  have hp := trit_parity n
  omega

private def ones (n : ℕ) := (Nat.digits 2 n).sum

private lemma ones_last (q r : ℕ) (hr : r < 2) : ones (2*q+r) = ones q+r := by
  by_cases h : r=0 ∧ q=0
  · obtain ⟨rfl,rfl⟩ := h
    simp [ones]
  · have hn : r≠0 ∨ q≠0 := by omega
    unfold ones
    rw [Nat.add_comm (2*q), Nat.digits_add 2 (by decide) r q hr hn]
    simp [Nat.add_comm]

private lemma binary_pair (q : ℕ) : ones (4*q+1) = ones (4*q+2) := by
  have h₀ := ones_last q 0 (by decide)
  have h₁ := ones_last q 1 (by decide)
  have h₂ := ones_last (2*q) 1 (by decide)
  have h₃ := ones_last (2*q+1) 0 (by decide)
  simp only [Nat.add_zero] at h₀ h₃
  calc
    ones (4*q+1) = ones (2*q)+1 := by rw [show 4*q+1 = 2*(2*q)+1 by omega, h₂]
    _ = ones q+1 := by rw [h₀]
    _ = ones (2*q+1) := h₁.symm
    _ = ones (4*q+2) := by rw [show 4*q+2 = 2*(2*q+1) by omega, h₃]

private lemma binary_even (n : ℕ) (he : n%2=0) : ones (n+1) = ones n+1 := by
  have h₀ := ones_last (n/2) 0 (by decide)
  have h₁ := ones_last (n/2) 1 (by decide)
  have hz : ones n = ones (n/2) := by
    calc
      ones n = ones (2*(n/2)+0) := congrArg ones (by omega)
      _ = ones (n/2) := by simpa using h₀
  calc
    ones (n+1) = ones (2*(n/2)+1) := congrArg ones (by omega)
    _ = ones (n/2)+1 := h₁
    _ = ones n+1 := by rw [hz]

private lemma trit_no_carry (n : ℕ) (hm : n%3 ≠ 1) :
    balancedSum (n+1) = balancedSum n+1 := by
  by_cases hn : n=0
  · subst n
    decide +kernel
  · have hq : (n+1+1)/3 = (n+1)/3 := by omega
    rw [balancedSum.eq_def (n+1), balancedSum.eq_def n]
    simp only [if_neg (by omega : n+1 ≠ 0), if_neg hn]
    rw [hq]
    omega

private lemma force_carry (n : ℕ) (he : n%2=0)
    (hm : digitMatch n = true) (hm' : digitMatch (n+1) = true) : n%3=1 := by
  have h₁ : (ones n : ℤ) = -balancedSum n := of_decide_eq_true hm
  have h₂ : (ones (n+1) : ℤ) = -balancedSum (n+1) := of_decide_eq_true hm'
  have hb := binary_even n he
  by_contra h
  have ht := trit_no_carry n h
  omega

private lemma no_four (n : ℕ) : ¬ (∀ i : Fin 4, digitMatch (n+i.val) = true) := by
  intro hall
  have take (m : ℕ) (hl : n ≤ m) (hh : m < n+4) : digitMatch m = true := by
    simpa [Nat.add_sub_of_le hl] using hall ⟨m-n, by omega⟩
  by_cases he : n%2=0
  · have h₁ := force_carry n he (take n (by omega) (by omega)) (take (n+1) (by omega) (by omega))
    have h₂ := force_carry (n+2) (by omega) (take (n+2) (by omega) (by omega))
      (take (n+2+1) (by omega) (by omega))
    omega
  · let q := (n+2)/4
    have hlo : n ≤ 4*q+1 := by dsimp [q]; omega
    have hhi : 4*q+2 < n+4 := by dsimp [q]; omega
    have h₁ := parity_of_match _ (take (4*q+1) hlo (by omega))
    have h₂ := parity_of_match _ (take (4*q+2) (by omega) hhi)
    have hp := binary_pair q
    unfold ones at hp
    omega

-- Bounded, structurally recursive digit sums for the finite prefix.
private def bitPrefix : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f+1, n => n%2 + bitPrefix f (n/2)

private def tritPrefix : ℕ → ℕ → ℤ
  | 0, _ => 0
  | f+1, n =>
    let q := (n+1)/3
    (n : ℤ) - 3*(q : ℤ) + tritPrefix f q

private lemma bitPrefix_eq (f n : ℕ) (hn : n < 2^f) : bitPrefix f n = ones n := by
  induction f generalizing n with
  | zero =>
    have h : n = 0 := by simpa using hn
    subst n
    decide +kernel
  | succ f ih =>
    rw [pow_succ] at hn
    rw [bitPrefix, ih (n/2) (by omega)]
    have h := ones_last (n/2) (n%2) (by omega)
    rw [show 2*(n/2)+n%2=n by omega] at h
    omega

private lemma tritPrefix_eq (f n : ℕ) (hn : n < 2^f) : tritPrefix f n = balancedSum n := by
  induction f generalizing n with
  | zero =>
    have h : n = 0 := by simpa using hn
    subst n
    decide +kernel
  | succ f ih =>
    rw [pow_succ] at hn
    have hp : 0 < 2^f := by positivity
    rw [tritPrefix, ih ((n+1)/3) (by omega)]
    by_cases hz : n=0
    · subst n
      decide +kernel
    · rw [balancedSum.eq_def n, if_neg hz]

private def quick (n : ℕ) : Bool := decide ((bitPrefix 16 n : ℤ) = -tritPrefix 16 n)

private lemma quick_eq (n : ℕ) (hn : n < 65536) : quick n = digitMatch n := by
  unfold quick digitMatch
  rw [bitPrefix_eq _ _ hn, tritPrefix_eq _ _ hn, ones]

private def triple (n : ℕ) : Bool := quick n && quick (n+1) && quick (n+2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private lemma checked_no_triple : (List.range 32770).all (fun n => !(triple n)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private lemma checked_count : (List.range 32770).countP quick = 115 := by
  decide +kernel

theorem OMA.solution : type_of% @OMA.S_oeis_a334765.main := by
  refine ⟨no_four, by decide +kernel, ?_, ?_⟩
  · intro n h
    have bad := List.all_eq_true.mp checked_no_triple n.val (List.mem_range.mpr n.isLt)
    have h₀ := h ⟨0,by decide⟩
    have h₁ := h ⟨1,by decide⟩
    have h₂ := h ⟨2,by decide⟩
    simp only [Nat.add_zero] at h₀ h₁ h₂
    have hn := n.isLt
    simp [triple, quick_eq _ (by omega : n.val < 65536),
      quick_eq _ (by omega : n.val+1 < 65536), quick_eq _ (by omega : n.val+2 < 65536),
      h₀, h₁, h₂] at bad
  · rw [← checked_count]
    apply List.countP_congr
    intro n hn
    have hb := List.mem_range.mp hn
    rw [quick_eq n (by omega)]
