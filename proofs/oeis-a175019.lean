import OMAStatements.S_oeis_a175019

-- Credit: @anmolspace. The recurrence is by José María Grau Ribas and the conjectures are by Chai Wah Wu.

open OMA.S_oeis_a175019

private def idx (t s r : ℕ) : ℕ := 4 * (t ^ 2 + s) + r

-- The four columns in the interval from 4t² to 4(t+1)².
private def val (t s r : ℕ) : ℕ :=
  if r = 0 then (if s = 2 * t then 2 * t else 2 * t - 1)
  else if r = 1 then (if s + 1 < t then 2 * t - 2 else if s < t then 2 * t - 1 else 2 * t)
  else if r = 2 then 2 * t + 1
  else if s < t then 2 * t else 2 * t + 2

private def expected (n : ℕ) : ℕ :=
  let t := (n / 4).sqrt
  val t (n / 4 - t ^ 2) (n % 4)

private lemma coords (n : ℕ) :
    ∃ t s r, s ≤ 2 * t ∧ r < 4 ∧ n = idx t s r := by
  let q := n / 4
  let t := q.sqrt
  have h₁ : t ^ 2 ≤ q := Nat.sqrt_le' q
  have h₂ : q ≤ t ^ 2 + 2 * t := by
    simpa [t, pow_two, two_mul, Nat.add_assoc] using Nat.sqrt_le_add q
  refine ⟨t, q - t ^ 2, n % 4, by omega, Nat.mod_lt _ (by decide), ?_⟩
  simp only [idx, Nat.add_sub_of_le h₁]
  dsimp [q]
  omega

private lemma expected_idx {t s r : ℕ} (hs : s ≤ 2 * t) (hr : r < 4) :
    expected (idx t s r) = val t s r := by
  have hdiv : idx t s r / 4 = t ^ 2 + s := by unfold idx; omega
  have hmod : idx t s r % 4 = r := by unfold idx; omega
  have hroot : (t ^ 2 + s).sqrt = t := Nat.sqrt_add_eq' _ (by omega)
  simp [expected, hdiv, hmod, hroot]

private lemma idx_bounds {t s r : ℕ} (hs : s ≤ 2 * t) (hr : r < 4) :
    4 * t ^ 2 ≤ idx t s r ∧ idx t s r < 4 * (t + 1) ^ 2 := by
  unfold idx
  constructor <;> nlinarith

private lemma row_near {j u s r i : ℕ} (hs : s ≤ 2 * u) (hr : r < 4)
    (hi : i = idx u s r) (hlo : 4 * j ^ 2 ≤ i) (hhi : i < 4 * (j + 2) ^ 2) :
    u = j ∨ u = j + 1 := by
  obtain ⟨h₁,h₂⟩ := idx_bounds hs hr
  rw [← hi] at h₁ h₂
  by_contra! h
  by_cases hl : u < j
  · have hm := Nat.pow_le_pow_left (by omega : u+1 ≤ j) 2
    omega
  · have hm := Nat.pow_le_pow_left (by omega : j+2 ≤ u) 2
    omega

private lemma val_bound (t s r : ℕ) : val t s r ≤ 2 * t + 2 := by
  unfold val
  split_ifs <;> omega

-- When both recursive arguments lie in one of two adjacent square intervals,
-- their relative coordinates reduce to finitely many linear arithmetic cases.
set_option maxHeartbeats 6000000 in
private lemma step_numeric {j s r u v w t a b : ℕ} (hj : 2 ≤ j)
    (hs : s ≤ 2 * (j+1)) (hr : r < 4)
    (hu : u = j ∨ u = j+1) (hv : v ≤ 2*u) (hw : w < 4)
    (ht : t = j ∨ t = j+1) (ha : a ≤ 2*t) (hb : b < 4)
    (hpre : idx (j+1) s r = idx u v w + 2)
    (htar : idx (j+1) s r = idx t a b + (2 * val u v w + 1)) :
    val (j+1) s r = val t a b + 1 := by
  rcases hu with rfl | rfl <;> rcases ht with rfl | rfl <;>
    unfold idx at hpre htar <;> ring_nf at hpre htar
  all_goals interval_cases r <;> interval_cases w <;> try omega
  all_goals interval_cases b <;> simp [val] at htar ⊢ <;> (try split_ifs at *) <;> omega

private lemma small : ∀ n : Fin 36, half n = expected n := by decide +kernel

-- Strong induction identifies the proposed block values with the nested recurrence.
private lemma half_eq (n : ℕ) : half n = expected n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 36
    · exact small ⟨n, hn⟩
    obtain ⟨t,s,r,hs,hr,coord⟩ := coords n
    obtain ⟨lo,hi⟩ := idx_bounds hs hr
    rw [← coord] at lo hi
    have ht : 3 ≤ t := by
      by_contra! hlt
      have hsq := Nat.pow_le_pow_left (by omega : t+1 ≤ 3) 2
      omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    change n = idx (j+1) s r at coord
    change 4*(j+1)^2 ≤ n at lo
    change n < 4*((j+1)+1)^2 at hi
    have upper : n < 4*(j+2)^2 := hi
    have hj : 2 ≤ j := by omega
    obtain ⟨u,v,w,hv,hw,pre⟩ := coords (n-2)
    have et : 4 * j ^ 2 + 4 * j + 8 ≤ n := by nlinarith only [lo,hj]
    have hu := row_near hv hw pre (by omega : 4*j^2 ≤ n-2)
      ((Nat.sub_le _ _).trans_lt upper)
    have epre : half (n-2) = val u v w := by
      rw [ih (n-2) (by omega), pre, expected_idx hv hw]
    have bound := val_bound u v w
    have hu' : u ≤ j+1 := by omega
    let d := 2 * val u v w + 1
    have hd : 0 < d := by dsimp [d]; omega
    have hd' : d ≤ 4*j+9 := by dsimp [d]; omega
    obtain ⟨t,a,b,ha,hb,tar⟩ := coords (n-d)
    have eb : 4*j^2 + (4*j+9) ≤ n := by nlinarith only [lo,hj]
    have ht' := row_near ha hb tar (by omega : 4*j^2 ≤ n-d)
      ((Nat.sub_le _ _).trans_lt upper)
    have etar : half (n-d) = val t a b := by
      rw [ih (n-d) (by omega), tar, expected_idx ha hb]
    have hrec : half n = half (n-d) + 1 := by
      conv_lhs => rw [show n = (n-2)+2 by omega, half]
      rw [show n-2+2 = n by omega, epre]
    rw [hrec, etar, coord, expected_idx hs hr]
    symm
    apply step_numeric hj hs hr hu hv hw ht' ha hb
    · omega
    · change idx (j+1) s r = idx t a b + d
      omega

private lemma mem_positions_idx {t s r k : ℕ} (hs : s ≤ 2*t) (hr : r < 4) :
    idx t s r ∈ positions k ↔ val t s r = k := by
  change 2 * half (idx t s r) + 1 = 2*k+1 ↔ _
  rw [half_eq, expected_idx hs hr]
  omega

private lemma odd_value {t s r : ℕ} (hs : s ≤ 2*t) (hr : r < 4) (h : ℕ) :
    val t s r = 2*h+1 ↔
    (t = h ∧ r = 2) ∨ (t = h+1 ∧ r = 0 ∧ s < 2*t) ∨
    (t = h+1 ∧ r = 1 ∧ s+1 = t) := by
  interval_cases r <;> simp [val] <;> (try split_ifs) <;> omega

private lemma even_value {t s r : ℕ} (hs : s ≤ 2*t) (hr : r < 4) (h : ℕ) :
    val t s r = 2*h ↔
    (t = h ∧ r = 3 ∧ s < t) ∨ (t+1 = h ∧ r = 3 ∧ t ≤ s) ∨
    (t = h ∧ r = 1 ∧ t ≤ s) ∨ (t = h+1 ∧ r = 1 ∧ s+1 < t) ∨
    (t = h ∧ r = 0 ∧ s = 2*t) := by
  interval_cases r <;> simp [val] <;> (try split_ifs) <;> omega

private lemma idx_injective {t s r u v w : ℕ} (hs : s ≤ 2*t) (hr : r < 4)
    (hv : v ≤ 2*u) (hw : w < 4) (h : idx t s r = idx u v w) :
    t = u ∧ s = v ∧ r = w := by
  obtain ⟨h₁,h₂⟩ := idx_bounds hs hr
  obtain ⟨h₃,h₄⟩ := idx_bounds hv hw
  have htu : t = u := by
    rcases lt_trichotomy t u with hlt | he | hgt
    · have hp := Nat.pow_le_pow_left (by omega : t+1 ≤ u) 2
      omega
    · exact he
    · have hp := Nat.pow_le_pow_left (by omega : u+1 ≤ t) 2
      omega
  subst u
  unfold idx at h
  omega

-- A segment in one column of one square interval.
private def row (t r first len : ℕ) : Finset ℕ :=
  (Finset.range len).image (fun j => idx t (first+j) r)

private lemma mem_row {t s r u z first len : ℕ} (hs : s ≤ 2*t) (hr : r < 4)
    (hseg : first+len ≤ 2*u+1) (hz : z < 4) :
    idx t s r ∈ row u z first len ↔
      t = u ∧ r = z ∧ first ≤ s ∧ s < first+len := by
  simp only [row, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x,hx,eq⟩
    have hc := idx_injective hs hr (by omega : first+x ≤ 2*u) hz eq.symm
    omega
  · rintro ⟨rfl,rfl,h₁,h₂⟩
    exact ⟨s-first, by omega, by rw [Nat.add_sub_of_le h₁]⟩

private lemma card_row (t r first len : ℕ) : (row t r first len).card = len := by
  unfold row
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro x y h
  change idx t (first+x) r = idx t (first+y) r at h
  unfold idx at h
  omega

private lemma rows_disjoint {t r first len u z start count : ℕ}
    (hend : first+len ≤ 2*t+1) (hend' : start+count ≤ 2*u+1)
    (hr : r < 4) (hz : z < 4) (hd : t ≠ u ∨ r ≠ z) :
    Disjoint (row t r first len) (row u z start count) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  obtain ⟨m,hm,em⟩ := Finset.mem_image.mp hi
  obtain ⟨n,hn,en⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_range] at hm hn
  have hc := idx_injective (by omega : first+m ≤ 2*t) hr (by omega : start+n ≤ 2*u) hz
    (em.trans en.symm)
  omega

private def oddHits (h : ℕ) : Finset ℕ :=
  row h 2 0 (2*h+1) ∪ row (h+1) 0 0 (2*h+2) ∪ row (h+1) 1 h 1

private def evenHits (h : ℕ) : Finset ℕ :=
  row h 3 0 h ∪ row (h-1) 3 (h-1) h ∪ row h 1 h (h+1) ∪
  row (h+1) 1 0 h ∪ row h 0 (2*h) 1

private lemma positions_odd (h : ℕ) : positions (2*h+1) = (oddHits h : Set ℕ) := by
  ext i
  obtain ⟨t,s,r,hs,hr,rfl⟩ := coords i
  simp only [Finset.mem_coe, oddHits, Finset.mem_union, mem_positions_idx hs hr,
    odd_value hs hr h]
  simp (disch := omega) only [mem_row hs hr]
  omega

private lemma positions_even (h : ℕ) : positions (2*h) = (evenHits h : Set ℕ) := by
  ext i
  obtain ⟨t,s,r,hs,hr,rfl⟩ := coords i
  simp only [Finset.mem_coe, evenHits, Finset.mem_union, mem_positions_idx hs hr,
    even_value hs hr h]
  simp (disch := omega) only [mem_row hs hr]
  omega

private lemma card_odd (h : ℕ) : (oddHits h).card = 4*h+4 := by
  unfold oddHits
  repeat' rw [Finset.card_union_of_disjoint (by
    try simp only [Finset.disjoint_union_left]
    repeat' apply And.intro
    all_goals apply rows_disjoint <;> omega)]
  simp only [card_row]
  omega

private lemma card_even (h : ℕ) : (evenHits h).card = 4*h+2 := by
  cases h with
  | zero => decide +kernel
  | succ h =>
    unfold evenHits
    repeat' rw [Finset.card_union_of_disjoint (by
      try simp only [Finset.disjoint_union_left]
      repeat' apply And.intro
      all_goals apply rows_disjoint <;> omega)]
    simp only [card_row]
    omega

private lemma greatest_odd (h : ℕ) :
    IsGreatest (positions (2*h+1)) ((2*h+1+3)^2-8) := by
  have endidx : (2*h+1+3)^2-8 = idx (h+1) (2*h+1) 0 := by
    unfold idx
    apply Nat.sub_eq_of_eq_add
    ring
  rw [endidx]
  constructor
  · rw [mem_positions_idx (by omega) (by decide), odd_value (by omega) (by decide)]
    omega
  · intro i hi
    obtain ⟨t,s,r,hs,hr,rfl⟩ := coords i
    rw [mem_positions_idx hs hr, odd_value hs hr] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl,ha⟩ | ⟨rfl,rfl,ha⟩ <;>
      unfold idx <;> nlinarith

private lemma least_odd (h : ℕ) :
    IsLeast (positions (2*h+1)) ((2*h+1-1)^2+2) := by
  have firstidx : (2*h+1-1)^2+2 = idx h 0 2 := by
    rw [show 2*h+1-1 = 2*h by omega]
    unfold idx
    ring
  rw [firstidx]
  constructor
  · rw [mem_positions_idx (by omega) (by decide), odd_value (by omega) (by decide)]
    omega
  · intro i hi
    obtain ⟨t,s,r,hs,hr,rfl⟩ := coords i
    rw [mem_positions_idx hs hr, odd_value hs hr] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl,ha⟩ | ⟨rfl,rfl,ha⟩ <;>
      unfold idx <;> nlinarith

private lemma greatest_even_zero : IsGreatest (positions 0) 1 := by
  constructor
  · change 2 * half 1 + 1 = 2 * 0 + 1
    decide +kernel
  · intro i hi
    obtain ⟨t,s,r,hs,hr,rfl⟩ := coords i
    change idx t s r ∈ positions (2*0) at hi
    rw [mem_positions_idx hs hr, even_value hs hr] at hi
    have hc : t = 0 ∧ s = 0 ∧ (r = 0 ∨ r = 1) := by omega
    rcases hc with ⟨rfl,rfl,rfl|rfl⟩ <;> decide

private lemma greatest_even_succ (h : ℕ) :
    IsGreatest (positions (2*(h+1))) ((2*(h+1)+3)^2-8) := by
  have endidx : (2*(h+1)+3)^2-8 = idx (h+2) h 1 := by
    unfold idx
    apply Nat.sub_eq_of_eq_add
    ring
  rw [endidx]
  constructor
  · rw [mem_positions_idx (by omega) (by decide), even_value (by omega) (by decide)]
    omega
  · intro i hi
    obtain ⟨t,s,r,hs,hr,rfl⟩ := coords i
    rw [mem_positions_idx hs hr, even_value hs hr] at hi
    rcases hi with c | c | c | c | c <;> rcases c with ⟨hu,rfl,ha⟩
    all_goals first
      | subst t
      | have eqt : t = h := by omega
        subst t
    all_goals unfold idx
    all_goals nlinarith

private lemma least_even_succ (h : ℕ) :
    IsLeast (positions (2*(h+1))) ((2*(h+1)-1)^2+2) := by
  have firstidx : (2*(h+1)-1)^2+2 = idx h h 3 := by
    rw [show 2*(h+1)-1 = 2*h+1 by omega]
    unfold idx
    ring
  rw [firstidx]
  constructor
  · rw [mem_positions_idx (by omega) (by decide), even_value (by omega) (by decide)]
    omega
  · intro i hi
    obtain ⟨t,s,r,hs,hr,rfl⟩ := coords i
    rw [mem_positions_idx hs hr, even_value hs hr] at hi
    rcases hi with c | c | c | c | c <;> rcases c with ⟨hu,rfl,ha⟩
    all_goals first
      | subst t
      | have eqt : t = h := by omega
        subst t
    all_goals unfold idx
    all_goals nlinarith

theorem OMA.solution : type_of% @OMA.S_oeis_a175019.main := by
  have par (n : ℕ) : ∃ h, n = 2*h ∨ n = 2*h+1 := ⟨n/2, by omega⟩
  have greatest (n : ℕ) : IsGreatest (positions n) ((n+3)^2-8) := by
    obtain ⟨h,rfl|rfl⟩ := par n
    · cases h with
      | zero => exact greatest_even_zero
      | succ h => exact greatest_even_succ h
    · exact greatest_odd h
  refine ⟨fun n => ⟨_,(greatest n).1⟩, ?_, greatest, ?_⟩
  · intro n
    obtain ⟨h,rfl|rfl⟩ := par n
    · rw [positions_even, Set.encard_coe_eq_coe_finsetCard, card_even]
      congr 1
      omega
    · rw [positions_odd, Set.encard_coe_eq_coe_finsetCard, card_odd]
      congr 1
      omega
  · intro n hn
    obtain ⟨h,rfl|rfl⟩ := par n
    · cases h with
      | zero => omega
      | succ h => exact least_even_succ h
    · exact least_odd h
