import OMAStatements.S_oeis_a081201
import Mathlib.Tactic


/-!
R. H. Hardin proposed this geometric interpretation of A081201. József Beck's
Theorem 3.4(a) in Combinatorial Games: Tic-Tac-Toe Theory gives the general
winning-line count. Here collinearity is stated in terms of integer minors.
The proof first counts codes for oriented lines, then reconstructs such a code
from an arbitrary collinear six-point subset of the actual grid.
-/

namespace OMA.GridSix
open OMA.S_oeis_a081201

abbrev Mode := Fin 6 ⊕ Bool
abbrev Code (n : ℕ) := Fin n → Mode

def value (m : Mode) (t : Fin 6) : Fin 6 :=
  match m with
  | .inl a => a
  | .inr true => t
  | .inr false => Fin.rev t

def point {n : ℕ} (c : Code n) (t : Fin 6) : Grid n := fun j => value (c j) t

def points {n : ℕ} (c : Code n) : Finset (Grid n) := Finset.univ.image (point c)

def active {n : ℕ} (c : Code n) : Prop := ∃ j b, c j = Sum.inr b

def reverseMode : Mode → Mode
  | .inl a => .inl a
  | .inr b => .inr (!b)

def reverseCode {n : ℕ} (c : Code n) : Code n := fun j => reverseMode (c j)

private theorem value_reverse : ∀ m : Mode, ∀ t, value (reverseMode m) t = value m (Fin.rev t) := by
  decide

private theorem endpoints_determine : ∀ m m' : Mode,
    value m 0 = value m' 0 → value m 5 = value m' 5 → m = m' := by decide

private theorem endpoint_minors : ∀ m m' : Mode, ∀ t : Fin 6,
    ((value m t : ℤ) - value m 0) * ((value m' 5 : ℤ) - value m' 0) =
    ((value m' t : ℤ) - value m' 0) * ((value m 5 : ℤ) - value m 0) := by decide

private theorem moving_injective (b : Bool) : Function.Injective (value (.inr b)) := by
  cases b <;> decide

private theorem point_injective {n} {c : Code n} (hc : active c) : Function.Injective (point c) := by
  obtain ⟨i,b,hi⟩ := hc
  intro t u h
  apply moving_injective b
  simpa [point,hi] using congrFun h i

private theorem mem_points {n} (c : Code n) (t : Fin 6) : point c t ∈ points c :=
  Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩

private theorem six_line {n} {c : Code n} (hc : active c) :
    (points c).card = 6 ∧ Collinear (points c) := by
  constructor
  · rw [points, Finset.card_image_of_injective _ (point_injective hc)]
    simp
  · refine ⟨point c 0, mem_points _ _, point c 5, mem_points _ _,
      fun h => (by decide : (0 : Fin 6) ≠ 5) (point_injective hc h), ?_⟩
    intro z hz i j
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
    exact endpoint_minors _ _ _

private theorem points_reverse {n} (c : Code n) : points (reverseCode c) = points c := by
  have hr (t : Fin 6) : point (reverseCode c) t = point c (Fin.rev t) :=
    funext (fun i => value_reverse (c i) t)
  ext z
  constructor <;> intro hz <;> obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
  · rw [hr]
    exact mem_points _ _
  · exact Finset.mem_image.mpr ⟨Fin.rev t, Finset.mem_univ _, by simp [hr]⟩

private theorem active_reverse {n} {c : Code n} (hc : active c) : active (reverseCode c) := by
  obtain ⟨i,b,h⟩ := hc
  exact ⟨i,!b, by simp [reverseCode,h,reverseMode]⟩

private theorem reverse_ne {n} {c : Code n} (hc : active c) : reverseCode c ≠ c := by
  obtain ⟨i,b,hi⟩ := hc
  intro heq
  have h := congrFun heq i
  cases b <;> simp [reverseCode,hi,reverseMode] at h

private theorem code_eq_of_pivot {n} {c d : Code n} {i : Fin n} {b : Bool}
    (hc : c i = Sum.inr b) (hd : d i = Sum.inr b) (h : points c = points d) : c = d := by
  have values (t : Fin 6) : point c t = point d t := by
    have hm := mem_points c t
    rw [h] at hm
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hm
    have hut : u = t := moving_injective b (by simpa [point,hc,hd] using congrFun hu i)
    simpa [hut] using hu.symm
  exact funext fun j => endpoints_determine _ _ (congrFun (values 0) j) (congrFun (values 5) j)

private theorem fiber_pair {n} {c d : Code n} (hc : active c) (heq : points c = points d) :
    d = c ∨ d = reverseCode c := by
  obtain ⟨i,b,hi⟩ := hc
  cases hd : d i with
  | inl a =>
    have collide (t : Fin 6) : value (Sum.inr b) t = a := by
      have hm := mem_points c t
      rw [heq] at hm
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hm
      simpa [point,hi,hd,value] using (congrFun hu i).symm
    have bad := moving_injective b ((collide 0).trans (collide 5).symm)
    exact False.elim ((by decide : (0 : Fin 6) ≠ 5) bad)
  | inr e =>
    by_cases hb : b = e
    · subst e
      exact Or.inl (code_eq_of_pivot hi hd heq).symm
    · have hbe : (!b) = e := by cases b <;> cases e <;> simp_all
      have hr : reverseCode c i = Sum.inr e := by rw [reverseCode, hi, reverseMode, hbe]
      exact Or.inr (code_eq_of_pivot hr hd ((points_reverse c).trans heq)).symm

private theorem active_iff_six {n} (c : Code n) : active c ↔ (points c).card = 6 := by
  constructor
  · exact fun h => (six_line h).1
  · intro h
    by_contra hnone
    have flat (t : Fin 6) : point c t = point c 0 := by
      funext j
      cases h : c j with
      | inl a => simp [point,h,value]
      | inr b => exact (hnone ⟨j,b,h⟩).elim
    have singleton : points c = {point c 0} := by
      ext z
      constructor
      · intro hz
        obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
        simp [flat t]
      · intro hz
        rw [Finset.mem_singleton.mp hz]
        exact mem_points _ _
    simp [singleton] at h

open Classical in
private theorem count_active (n : ℕ) :
    (Finset.univ.filter (fun c : Code n => active c)).card = 8^n - 6^n := by
  classical
  let embed (g : Grid n) : Code n := fun i => Sum.inl (g i)
  have hi : Function.Injective embed := by
    intro g k h
    exact funext (fun i => Sum.inl.inj (congrFun h i))
  have constants :
      (Finset.univ.filter (fun c : Code n => ¬ active c)) = Finset.univ.image embed := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hc
      have hex (j : Fin n) : ∃ a : Fin 6, c j = Sum.inl a := by
        cases h : c j with
        | inl a => exact ⟨a,rfl⟩
        | inr b => exact (hc ⟨j,b,h⟩).elim
      choose g hg using hex
      exact ⟨g, by funext i; exact (hg i).symm⟩
    · rintro ⟨g,rfl⟩ ⟨j,b,h⟩
      simp [embed] at h
  have total := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Code n))) active
  rw [constants, Finset.card_image_of_injective _ hi] at total
  have gridSize : (Finset.univ : Finset (Grid n)).card = 6^n := by simp [Grid]
  have spaceSize : (Finset.univ : Finset (Code n)).card = 8^n := by
    simp [Code, Mode]
  rw [gridSize, spaceSize] at total
  rw [← total, Nat.add_sub_cancel]

private theorem count_from_classification (n : ℕ)
    (classify : ∀ s : Finset (Grid n), s.card = 6 → Collinear s → ∃ c : Code n, points c = s) :
    lineCount n = (8^n - 6^n)/2 := by
  classical
  let codes := Finset.univ.filter (fun c : Code n => active c)
  let lines := Finset.univ.filter (fun s : Finset (Grid n) => s.card = 6 ∧ Collinear s)
  have land : (codes : Set (Code n)).MapsTo points lines := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, six_line (Finset.mem_filter.mp hc).2⟩
  have size (s : Finset (Grid n)) (hs : s ∈ lines) :
      (codes.filter (fun c => points c = s)).card = 2 := by
    obtain ⟨hsix, hline⟩ := (Finset.mem_filter.mp hs).2
    obtain ⟨c, rfl⟩ := classify s hsix hline
    have hc := (active_iff_six c).mpr hsix
    have eqPair : codes.filter (fun d => points d = points c) = {c, reverseCode c} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun hd => fiber_pair hc hd.2.symm
      · rintro (rfl | rfl)
        · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,rfl⟩
        · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,active_reverse hc⟩,points_reverse _⟩
    rw [eqPair, Finset.card_pair (Ne.symm (reverse_ne hc))]
  have count := Finset.card_eq_sum_card_fiberwise land
  rw [Finset.sum_congr rfl size] at count
  simp only [Finset.sum_const, smul_eq_mul] at count
  have hc : codes.card = 8^n - 6^n := count_active n
  change lines.card = _
  omega


private lemma geometry_int_bounds (v : Fin 6) : 0 ≤ (v : ℤ) ∧ (v : ℤ) ≤ 5 := by
  have h := v.isLt
  omega

private lemma geometry_axis (f : Fin 6 → Fin 6)
    (hf : ∀ t : Fin 6, (f t : ℤ) = (f 0 : ℤ) + (t : ℤ) * ((f 1 : ℤ) - f 0)) :
    ∃ m : Mode, ∀ t : Fin 6, f t =
      match m with | .inl a => a | .inr true => t | .inr false => Fin.rev t := by
  have he : (f 5 : ℤ) = (f 0 : ℤ) + 5 * ((f 1 : ℤ) - f 0) := hf 5
  have h0 := geometry_int_bounds (f 0)
  have h5 := geometry_int_bounds (f 5)
  have sl : (f 1 : ℤ)-(f 0 : ℤ) = 0 ∨ (f 1 : ℤ)-(f 0 : ℤ) = 1 ∨
      (f 1 : ℤ)-(f 0 : ℤ) = -1 := by omega
  rcases sl with h | h | h
  · refine ⟨.inl (f 0), ?_⟩
    intro t
    have ht := hf t
    rw [h, mul_zero, add_zero] at ht
    apply Fin.ext
    exact_mod_cast ht
  · refine ⟨.inr true, ?_⟩
    intro t
    have ht := hf t
    rw [h, mul_one] at ht
    apply Fin.ext
    change (f t).val = t.val
    omega
  · refine ⟨.inr false, ?_⟩
    intro t
    have ht := hf t
    rw [h, mul_neg_one] at ht
    apply Fin.ext
    change (f t).val = (Fin.rev t).val
    rw [Fin.val_rev]
    have hb := geometry_int_bounds t
    omega

private lemma code_of_collinear {n : ℕ} {s : Finset (Grid n)}
    (hs : s.card = 6) (hcol : Collinear s) : ∃ c : Code n, points c = s := by
  classical
  obtain ⟨a, ha, b, hb, hab, h⟩ := hcol
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
    by_contra! hn
    exact hab (funext hn)
  have hn : (b i : ℤ) - (a i : ℤ) ≠ 0 := by
    intro he
    apply hi
    apply Fin.ext
    omega
  let proj (v : ↥s) : Fin 6 := v.val i
  have inj : Function.Injective proj := by
    intro x y he
    change x.val i = y.val i at he
    apply Subtype.ext
    funext j
    have hx := h x.val x.property j i
    have hy := h y.val y.property j i
    rw [he] at hx
    have hz := mul_right_cancel₀ hn (hx.trans hy.symm)
    apply Fin.ext
    omega
  have hcard : Fintype.card (↥s) = Fintype.card (Fin 6) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using hs
  have sur := ((Fintype.bijective_iff_injective_and_card proj).mpr ⟨inj,hcard⟩).2
  choose g hg using sur
  have hgi (t : Fin 6) : (g t).val i = t := hg t
  have affine (j : Fin n) (t : Fin 6) :
      ((g t).val j : ℤ) = ((g 0).val j : ℤ) +
        (t : ℤ) * (((g 1).val j : ℤ) - (g 0).val j) := by
    have rect (u : Fin 6) := h (g u).val (g u).property j i
    have ht := rect t
    have h0 := rect 0
    have h1 := rect 1
    rw [hgi t] at ht
    rw [hgi 0] at h0
    rw [hgi 1] at h1
    apply mul_right_cancel₀ hn
    change (((g 0).val j : ℤ) - a j) * ((b i : ℤ) - a i) =
      (0 - (a i : ℤ)) * ((b j : ℤ) - a j) at h0
    change (((g 1).val j : ℤ) - a j) * ((b i : ℤ) - a i) =
      (1 - (a i : ℤ)) * ((b j : ℤ) - a j) at h1
    linear_combination ht + ((t : ℤ)-1) * h0 - (t : ℤ) * h1
  have cfs (j : Fin n) := geometry_axis (fun t => (g t).val j) (affine j)
  choose c hc using cfs
  have point_eq (t : Fin 6) : point c t = (g t).val := by
    funext j
    exact (hc j t).symm
  refine ⟨c, Finset.ext fun p => ⟨?_, ?_⟩⟩
  · intro hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hp
    rw [point_eq]
    exact (g t).property
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨p i, Finset.mem_univ _, ?_⟩
    rw [point_eq]
    exact congrArg Subtype.val (inj (show proj (g (p i)) = proj ⟨p,hp⟩ from hg (p i)))


end OMA.GridSix

open OMA.GridSix in
theorem OMA.solution : type_of% @OMA.S_oeis_a081201.main := by
  intro n
  exact count_from_classification n (fun _ => code_of_collinear)
