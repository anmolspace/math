import FormalConjecturesForMathlib.Combinatorics.Additive.Convolution
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A finite Erdős–Turán bound for digit descriptions of bounded width

For every ordered representation cap and every number of states this file derives
an explicit finite cutoff for bases whose initial segment has a digit reader
of that width. The machine can have a different transition at every position
and a different description for every length. Accepting paths partition the
digits into boxes. Reflecting the variable coordinates gives many ordered pairs
at the same sum.

Seda Albayrak, Sparse Automatic Sets, University of Waterloo, 2020, Chapter 5,
proves a quantitative Erdős–Turán theorem for automatic additive bases.
This finite calculation also allows nonuniform transitions. The unrestricted
worksheet permits arbitrary finite sets; that case is still open.
The last theorem permits false positives and false negatives and gives an explicit
cutoff in terms of their counts. The proof reuses the one-element insertion
lemma proved by Claude for @anmolspace in PR 5250 and the finite-edit
induction by TheWaler in PR 4711.

Formalization for @anmolspace with OpenAI Codex.
-/

namespace OMA.Erdos28DigitBoxes

open Finset AdditiveCombinatorics

/-- Allowed digits at each position, lowest position first. -/
def words (B : ℕ) : List (Finset ℕ) → Finset ℕ
  | [] => {0}
  | D :: ds => (D ×ˢ words B ds).image (fun p => p.1+B*p.2)

def varied : List (Finset ℕ) → ℕ
  | [] => 0
  | D :: ds => (if 1 < D.card then 1 else 0) + varied ds

def valid (B : ℕ) (ds : List (Finset ℕ)) :=
  ∀ D ∈ ds, D.Nonempty ∧ D ⊆ range B

private theorem append_inj {B : ℕ} {D X : Finset ℕ}
    (hb : 0 < B) (hd : D ⊆ range B) :
    Set.InjOn (fun p : ℕ × ℕ => p.1+B*p.2) (D ×ˢ X : Finset _) := by
  rintro ⟨a,x⟩ hx ⟨b,y⟩ hy e
  have ha : a < B := mem_range.mp (hd (mem_product.mp hx).1)
  have hb' : b < B := mem_range.mp (hd (mem_product.mp hy).1)
  change a+B*x=b+B*y at e
  have eqab : a=b := by
    have z := congrArg (· % B) e
    simpa [Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb'] using z
  subst b
  have hxy : x=y := Nat.eq_of_mul_eq_mul_left hb (Nat.add_left_cancel e)
  simp [hxy]

theorem card_words_le (B : ℕ) (ds : List (Finset ℕ)) (good : valid B ds) :
    (words B ds).card ≤ B ^ varied ds := by
  induction ds with
  | nil => simp [words,varied]
  | cons D ds ih =>
    have hd := good D (by simp)
    have prev := ih (fun E he => good E (by simp [he]))
    have bound := (card_image_le (s := D ×ˢ words B ds)
      (f := fun p : ℕ × ℕ => p.1+B*p.2))
    rw [card_product] at bound
    change _ ≤ B ^ ((if 1 < D.card then 1 else 0) + varied ds)
    apply bound.trans
    rw [pow_add]
    apply Nat.mul_le_mul _ prev
    split
    · simpa using (card_le_card hd.2)
    · simp_all

theorem words_lt (B : ℕ) (ds : List (Finset ℕ)) (good : valid B ds)
    {x : ℕ} (hx : x ∈ words B ds) : x < B^ds.length := by
  induction ds generalizing x with
  | nil => simpa [words] using hx
  | cons D ds ih =>
    obtain ⟨⟨a,y⟩,hp,rfl⟩ := mem_image.mp hx
    have ha := mem_range.mp ((good D (by simp)).2 (mem_product.mp hp).1)
    have hy := ih (fun E he => good E (by simp [he])) (mem_product.mp hp).2
    have h := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hy)
    simp only [List.length_cons, pow_succ, Nat.mul_succ] at *
    rw [Nat.mul_comm (B ^ ds.length) B]
    omega

/-- The box contains at least 2^t first coordinates, with partners in the
same box giving a common integer sum, if t positions have two digits. -/
theorem reflection (B : ℕ) (hb : 0 < B) (ds : List (Finset ℕ)) (good : valid B ds) :
    ∃ m : ℕ, ∃ X : Finset ℕ, 2^varied ds ≤ X.card ∧ X ⊆ words B ds ∧
      ∀ x ∈ X, ∃ y ∈ words B ds, x+y=m := by
  induction ds with
  | nil => exact ⟨0,{0},by simp [varied],by simp [words],by simp [words]⟩
  | cons D ds ih =>
    obtain ⟨m,X,hcount,hX,href⟩ := ih (fun E he => good E (by simp [he]))
    obtain ⟨hne,hD⟩ := good D (by simp)
    obtain ⟨a,ha⟩ := hne
    have select : ∃ b ∈ D, 2 ^ (if 1 < D.card then 1 else 0) ≤ ({a,b} : Finset ℕ).card := by
      split
      · rename_i h
        obtain ⟨b,hb,ne⟩ := Finset.exists_mem_ne h a
        exact ⟨b,hb,by simp [Ne.symm ne]⟩
      · exact ⟨a,ha,by simp⟩
    obtain ⟨b,hb',hsize⟩ := select
    let digits : Finset ℕ := {a,b}
    have small : digits ⊆ D := by
      intro c hc
      simp only [digits,mem_insert,mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ha
      · exact hb'
    let f (p : ℕ × ℕ) := p.1+B*p.2
    let Y := (digits ×ˢ X).image f
    refine ⟨a+b+B*m,Y,?_,?_,?_⟩
    · change 2 ^ ((if 1 < D.card then 1 else 0) + varied ds) ≤ _
      rw [pow_add]
      change _ ≤ ((digits ×ˢ X).image f).card
      rw [card_image_of_injOn (append_inj hb (small.trans hD)),card_product]
      exact Nat.mul_le_mul hsize hcount
    · intro w hw
      obtain ⟨⟨c,x⟩,hp,rfl⟩ := mem_image.mp hw
      exact mem_image.mpr ⟨(c,x),mem_product.mpr ⟨small (mem_product.mp hp).1,hX (mem_product.mp hp).2⟩,rfl⟩
    · intro w hw
      obtain ⟨⟨c,x⟩,hp,rfl⟩ := mem_image.mp hw
      obtain ⟨hc,hx⟩ := mem_product.mp hp
      obtain ⟨y,hy,he⟩ := href x hx
      have oth : ∃ d ∈ D, c+d=a+b := by
        change c ∈ ({a,b} : Finset ℕ) at hc
        simp only [mem_insert,mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact ⟨b,hb',rfl⟩
        · exact ⟨a,ha,Nat.add_comm _ _⟩
      obtain ⟨d,hd,hs⟩ := oth
      refine ⟨d+B*y, mem_image.mpr ⟨(d,y),mem_product.mpr ⟨hd,hy⟩,rfl⟩,?_⟩
      dsimp [f]
      calc c + B*x + (d+B*y) = (c+d) + B*(x+y) := by ring
           _ = a+b+B*m := by rw [hs,he]

private theorem witnessed_count (S : Set ℕ) (X : Finset ℕ) (m : ℕ)
    (incl : (X : Set ℕ) ⊆ S) (refl : ∀ x ∈ X, ∃ y ∈ S, x+y=m) :
    X.card ≤ sumRep S m := by
  classical
  let f (x : ℕ) := (x,m-x)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  rw [sumRep_def, ← card_image_of_injective X hf]
  apply card_le_card
  intro p hp
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
  obtain ⟨y,hy,he⟩ := refl x hx
  apply mem_filter.mpr
  have hy' : m-x=y := by omega
  refine ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr ?_,incl hx,?_⟩
  · change x+(m-x)=m
    omega
  · change m-x ∈ S
    rwa [hy']

/-- If a capped set is described on k digits by a union of boxes, each
nonempty box has only h variable digit positions when g < 2^(h+1).
Consequently this many boxes are necessary to cover an initial interval. -/
theorem box_count_obstruction (B k g h : ℕ) (hb : 0 < B) (hg : g < 2^(h+1))
    (boxes : Finset (List (Finset ℕ))) (S : Set ℕ)
    (good : ∀ ds ∈ boxes, valid B ds ∧ ds.length=k)
    (eqn : ∀ x < B^k, x ∈ S ↔ x ∈ boxes.biUnion (words B))
    (cover : ∀ n < B^k, ∃ a ∈ S, ∃ b ∈ S, a+b=n)
    (cap : ∀ n ≤ 2*B^k-2, sumRep S n ≤ g) :
    B^k ≤ (boxes.card * B^h)^2 := by
  classical
  let T := boxes.biUnion (words B)
  have incl : range (B^k) ⊆ (T ×ˢ T).image (fun p => p.1+p.2) := by
    intro n hn
    have hl := mem_range.mp hn
    obtain ⟨a,ha,b,hb',he⟩ := cover n hl
    exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨(eqn a (by omega)).mp ha,
      (eqn b (by omega)).mp hb'⟩,he⟩
  have lower := (card_le_card incl).trans card_image_le
  rw [card_range,card_product] at lower
  have each (ds) (hd : ds ∈ boxes) : (words B ds).card ≤ B^h := by
    obtain ⟨valids,len⟩ := good ds hd
    have bound (x) (hx : x ∈ words B ds) : x < B^k := len ▸ words_lt B ds valids hx
    have inside (x) (hx : x ∈ words B ds) : x ∈ S :=
      (eqn x (bound x hx)).mpr (mem_biUnion.mpr ⟨ds,hd,hx⟩)
    obtain ⟨m,X,hsize,hX,refl⟩ := reflection B hb ds valids
    have pos : 0 < X.card := lt_of_lt_of_le (by positivity : 0 < 2 ^ varied ds) hsize
    obtain ⟨x,hx⟩ := card_pos.mp pos
    obtain ⟨y,hy,he⟩ := refl x hx
    have boundX := bound x (hX hx)
    have boundY := bound y hy
    have capm := cap m (by omega)
    have hc := witnessed_count S X m (fun w hw => inside w (hX hw)) (by
      intro w hw
      obtain ⟨v,hv,e⟩ := refl w hw
      exact ⟨v,inside v hv,e⟩)
    have lt := Nat.lt_of_le_of_lt (hsize.trans (hc.trans capm)) hg
    have hv : varied ds ≤ h := by
      by_contra! hh
      exact (Nat.not_le_of_gt lt) (Nat.pow_le_pow_right (by decide) hh)
    exact (card_words_le B ds valids).trans (Nat.pow_le_pow_right hb hv)
  have total : T.card ≤ boxes.card * B^h := card_biUnion_le_card_mul _ _ _ each
  simpa [pow_two] using lower.trans (Nat.mul_le_mul total total)

end OMA.Erdos28DigitBoxes


namespace OMA.Erdos28DigitBoxes

open Finset AdditiveCombinatorics

section Machine

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A position-dependent machine reads exactly k digits, including padding. -/
def accepts (B : ℕ) (step : ℕ → σ → ℕ → σ) (finish : σ → Prop) :
    ℕ → ℕ → σ → ℕ → Prop
  | 0, _, s, _ => finish s
  | k+1, i, s, x => accepts B step finish k (i+1) (step i s (x%B)) (x/B)

open scoped Classical in
noncomputable def states (B : ℕ) (step : ℕ → σ → ℕ → σ) (finish : σ → Prop) :
    ℕ → ℕ → σ → Finset (List (Finset ℕ))
  | 0, _, s => if finish s then {[]} else ∅
  | k+1, i, s => univ.biUnion (fun t : σ =>
      let D := (range B).filter (fun d => step i s d=t)
      if D.Nonempty then (states B step finish k (i+1) t).image (List.cons D) else ∅)

theorem states_card (B k i : ℕ) (step : ℕ → σ → ℕ → σ) (finish : σ → Prop) (s : σ) :
    (states B step finish k i s).card ≤ Fintype.card σ ^ k := by
  classical
  induction k generalizing i s with
  | zero => simp only [states,pow_zero]; split <;> simp
  | succ k ih =>
    rw [states]
    calc
      _ ≤ univ.card * (Fintype.card σ ^ k) := card_biUnion_le_card_mul _ _ _ (by
        intro t _
        dsimp only
        split
        · exact card_image_le.trans (ih (i+1) t)
        · simp)
      _ = _ := by simp [pow_succ, Nat.mul_comm]

theorem states_valid (B k i : ℕ) (step : ℕ → σ → ℕ → σ) (finish : σ → Prop) (s : σ)
    {ds : List (Finset ℕ)} (hd : ds ∈ states B step finish k i s) :
    valid B ds ∧ ds.length=k := by
  classical
  induction k generalizing i s ds with
  | zero =>
    simp only [states] at hd
    split at hd
    · obtain rfl := mem_singleton.mp hd
      simp [valid]
    · simp at hd
  | succ k ih =>
    rw [states] at hd
    obtain ⟨t,_,hds⟩ := mem_biUnion.mp hd
    dsimp only at hds
    split at hds
    · rename_i hn
      obtain ⟨tail,ht,rfl⟩ := mem_image.mp hds
      obtain ⟨hv,hl⟩ := ih _ _ ht
      refine ⟨?_,by simp [hl]⟩
      intro E he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨hn,filter_subset _ _⟩
      · exact hv E he
    · simp at hds

private theorem words_cons_mem (B : ℕ) (hb : 0 < B) (D : Finset ℕ) (ds : List (Finset ℕ))
    (bound : D ⊆ range B) (x : ℕ) :
    x ∈ words B (D::ds) ↔ x%B ∈ D ∧ x/B ∈ words B ds := by
  constructor
  · intro hx
    obtain ⟨⟨a,y⟩,h,rfl⟩ := mem_image.mp hx
    obtain ⟨ha,hy⟩ := mem_product.mp h
    have al := mem_range.mp (bound ha)
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt al,Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt al,Nat.zero_add]
    exact ⟨ha,hy⟩
  · rintro ⟨ha,hy⟩
    exact mem_image.mpr ⟨(x%B,x/B),mem_product.mpr ⟨ha,hy⟩,Nat.mod_add_div x B⟩

theorem states_correct (B k i : ℕ) (hb : 0 < B) (step : ℕ → σ → ℕ → σ)
    (finish : σ → Prop) (s : σ) (x : ℕ) (hx : x < B^k) :
    accepts B step finish k i s x ↔ x ∈ (states B step finish k i s).biUnion (words B) := by
  classical
  induction k generalizing i s x with
  | zero =>
    have hz : x=0 := by simpa using hx
    subst x
    simp only [accepts,states]
    split <;> simp_all [words]
  | succ k ih =>
    have hquot : x/B < B^k := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [pow_succ] using hx)
    let t := step i s (x%B)
    let D := (range B).filter (fun d => step i s d=t)
    have digit : x%B ∈ D := mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hb),rfl⟩
    rw [accepts, ih (i+1) t _ hquot]
    constructor
    · intro h
      obtain ⟨ds,hds,hy⟩ := mem_biUnion.mp h
      refine mem_biUnion.mpr ⟨D::ds,?_,(words_cons_mem B hb D ds (filter_subset _ _) x).mpr ⟨digit,hy⟩⟩
      rw [states]
      apply mem_biUnion.mpr
      refine ⟨t,mem_univ _,?_⟩
      change D::ds ∈ (if D.Nonempty then _ else _)
      rw [if_pos ⟨_,digit⟩]
      exact mem_image.mpr ⟨ds,hds,rfl⟩
    · intro h
      obtain ⟨ds,hds,hxds⟩ := mem_biUnion.mp h
      rw [states] at hds
      obtain ⟨t',_,hh⟩ := mem_biUnion.mp hds
      dsimp only at hh
      split at hh
      · obtain ⟨tail,ht,rfl⟩ := mem_image.mp hh
        obtain ⟨hdigit,htail⟩ := (words_cons_mem B hb _ tail (filter_subset _ _) x).mp hxds
        have e : t=t' := (mem_filter.mp hdigit).2
        subst t'
        exact mem_biUnion.mpr ⟨tail,ht,htail⟩
      · simp at hh

theorem machine_count_obstruction (B k g h : ℕ) (hb : 0 < B) (hg : g < 2^(h+1))
    (step : ℕ → σ → ℕ → σ) (finish : σ → Prop) (start : σ) (S : Set ℕ)
    (model : ∀ x < B^k, x ∈ S ↔ accepts B step finish k 0 start x)
    (cover : ∀ n < B^k, ∃ a ∈ S, ∃ b ∈ S, a+b=n)
    (cap : ∀ n ≤ 2*B^k-2, sumRep S n ≤ g) :
    B^k ≤ (Fintype.card σ ^ k * B^h)^2 := by
  have old := box_count_obstruction B k g h hb hg (states B step finish k 0 start) S
    (fun _ hd => states_valid B k 0 step finish start hd)
    (fun x hx => (model x hx).trans (states_correct B k 0 hb step finish start x hx)) cover cap
  exact old.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (states_card B k 0 step finish start)) _)

end Machine
end OMA.Erdos28DigitBoxes


namespace OMA.Erdos28DigitBoxes

open AdditiveCombinatorics

/-- An explicit cutoff for every cap, provided the digit description has
bounded width. The transitions can change at every digit position. -/
theorem finite_width_cutoff {σ : Type*} [Fintype σ] [DecidableEq σ]
    (M g h : ℕ) (hg : g < 2^(h+1)) (width : 4*(Fintype.card σ)^2 ≤ 2^M)
    (step : ℕ → σ → ℕ → σ) (finish : σ → Prop) (start : σ) (S : Set ℕ) :
    let B := 2^M
    let k := M*h+1
    (∀ x < B^k, x ∈ S ↔ accepts B step finish k 0 start x) →
    (∀ n < B^k, ∃ a ∈ S, ∃ b ∈ S, a+b=n) →
    ∃ n ≤ 2*B^k-2, g < sumRep S n := by
  classical
  let B := 2^M
  let k := M*h+1
  let q := Fintype.card σ
  change (∀ x < B^k, x ∈ S ↔ accepts B step finish k 0 start x) →
    (∀ n < B^k, ∃ a ∈ S, ∃ b ∈ S, a+b=n) →
    ∃ n ≤ 2*B^k-2, g < sumRep S n
  intro recog cover
  by_contra! cap
  have hbound := machine_count_obstruction B k g h (by dsimp [B]; positivity) hg
    step finish start S recog cover cap
  change B^k ≤ (q^k*B^h)^2 at hbound
  have qq : 0 < q := Fintype.card_pos_iff.mpr ⟨start⟩
  have low : (4*q^2)^k ≤ B^k := Nat.pow_le_pow_left width k
  have align : (B^h)^2 = 4^(M*h) := by
    change ((2^M)^h)^2 = (2^2)^(M*h)
    simp only [← pow_mul]
    rw [Nat.mul_comm (M*h) 2]
  have alignq : (q^k)^2=(q^2)^k := by simp only [←pow_mul,Nat.mul_comm k 2]
  have grow : 4^(M*h) < 4^k := Nat.pow_lt_pow_right (by decide : 1<4) (Nat.lt_succ_self _)
  have bigger : (q^k*B^h)^2 < (4*q^2)^k := by
    rw [mul_pow,alignq,align,mul_pow,Nat.mul_comm (4^k)]
    exact Nat.mul_lt_mul_of_pos_left grow (by positivity)
  exact (Nat.not_lt_of_ge (low.trans hbound)) bigger

end OMA.Erdos28DigitBoxes

-- Single-insertion proof from the accepted PR 5250 by @anmolspace (Claude).
namespace OMA.Erdos28DigitEdits
open Finset

lemma key (A : Set ℕ) (a n : ℕ)
    {i1 : DecidablePred (fun p : ℕ × ℕ => p.1 ∈ insert a A ∧ p.2 ∈ insert a A)}
    {i2 : DecidablePred (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)} :
    ((Finset.HasAntidiagonal.antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ insert a A ∧ p.2 ∈ insert a A)).card
      ≤ ((Finset.HasAntidiagonal.antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)).card + 2 := by
  classical
  have hsub : (Finset.HasAntidiagonal.antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ insert a A ∧ p.2 ∈ insert a A)
      ⊆ (Finset.HasAntidiagonal.antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)
        ∪ {(a, n - a), (n - a, a)} := by
    intro p hp
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_insert_iff,
      Set.mem_insert_iff] at hp
    obtain ⟨hsum, h1, h2⟩ := hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases ha1 : p.1 = a
    · right; left
      exact Prod.ext ha1 (by simp only; omega)
    · by_cases ha2 : p.2 = a
      · right; right
        exact Prod.ext (by simp only; omega) ha2
      · left
        exact ⟨hsum, h1.resolve_left ha1, h2.resolve_left ha2⟩
  have h2 : ({(a, n - a), (n - a, a)} : Finset (ℕ × ℕ)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left h2 _


open AdditiveCombinatorics

private theorem insert_bound (A : Set ℕ) (a n : ℕ) : sumRep (insert a A) n ≤ sumRep A n + 2 := by
  rw [sumRep_def, sumRep_def]
  exact key A a n


open OMA.Erdos28DigitBoxes Finset

private theorem count_mono (A B : Set ℕ) (sub : A ⊆ B) (n : ℕ) : sumRep A n ≤ sumRep B n := by
  classical
  rw [sumRep_def,sumRep_def]
  apply card_le_card
  intro p hp
  obtain ⟨he,ha,hb⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨he,sub ha,sub hb⟩

-- Induction on the inserted set is the finite-edit argument of TheWaler, PR 4711.
private theorem add_bound (A : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    sumRep ((F : Set ℕ) ∪ A) n ≤ sumRep A n + 2*F.card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    rw [Finset.coe_insert,Set.insert_union,Finset.card_insert_of_notMem ha]
    have h := insert_bound ((F : Set ℕ) ∪ A) a n
    omega

private theorem singleton_box (B k x : ℕ) (hb : 0 < B) (hx : x < B^k) :
    ∃ ds : List (Finset ℕ), valid B ds ∧ ds.length=k ∧ words B ds={x} := by
  induction k generalizing x with
  | zero =>
    have hx' : x=0 := by simpa using hx
    subst x
    exact ⟨[],by simp [valid],rfl,rfl⟩
  | succ k ih =>
    have hquot : x/B < B^k := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [pow_succ] using hx)
    obtain ⟨ds,hv,hl,hw⟩ := ih (x/B) hquot
    let D : Finset ℕ := {x%B}
    refine ⟨D::ds,?_,by simp [hl],?_⟩
    · intro E he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨⟨x%B, by simp [D]⟩, by simpa [D] using Nat.mod_lt x hb⟩
      · exact hv E he
    · simp [words,D,hw,Nat.mod_add_div]

/-- A bounded representation function forces an exact basis to be far even
from finite-state descriptions that make false-positive and false-negative
errors. Only the errors within the tested prefix need to be listed. -/
theorem approximate_machine_bound {σ : Type*} [Fintype σ] [DecidableEq σ]
    (B k g h : ℕ) (hb : 0 < B) (step : ℕ → σ → ℕ → σ) (finish : σ → Prop)
    (start : σ) (S : Set ℕ) (miss extra : Finset ℕ)
    (hg : g+2*extra.card < 2^(h+1))
    (omits : ∀ x < B^k, x∈S → accepts B step finish k 0 start x ∨ x∈miss)
    (adds : ∀ x < B^k, accepts B step finish k 0 start x → x∈S ∨ x∈extra)
    (cover : ∀ n < B^k, ∃ a∈S, ∃ b∈S, a+b=n)
    (cap : ∀ n ≤ 2*B^k-2, sumRep S n ≤ g) :
    B^k ≤ ((Fintype.card σ ^ k + miss.card)*B^h)^2 := by
  classical
  let pool := states B step finish k 0 start
  let M := miss.filter (fun x => x < B^k ∧ x∈S)
  have singleton (x) (hx : x ∈ M) :
      ∃ ds : List (Finset ℕ), valid B ds ∧ ds.length=k ∧ words B ds={x} :=
    singleton_box B k x hb (mem_filter.mp hx).2.1
  let box (x : ℕ) := if hx : x∈M then (singleton x hx).choose else []
  have spec (x) (hx : x∈M) : valid B (box x) ∧ (box x).length=k ∧ words B (box x)={x} := by
    simpa [box,hx] using (singleton x hx).choose_spec
  let bs := pool ∪ M.image box
  let T : Set ℕ := (bs.biUnion (words B) : Finset ℕ)
  have exactAt (x) (hx : x < B^k) :
      x ∈ T ↔ accepts B step finish k 0 start x ∨ x∈M := by
    change x ∈ bs.biUnion (words B) ↔ _
    rw [states_correct B k 0 hb step finish start x hx]
    constructor
    · intro hx'
      obtain ⟨ds,hd,hw⟩ := mem_biUnion.mp hx'
      rcases mem_union.mp hd with h | h
      · exact Or.inl (mem_biUnion.mpr ⟨ds,h,hw⟩)
      · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
        rw [(spec y hy).2.2] at hw
        simpa [mem_singleton.mp hw] using Or.inr hy
    · rintro (hc | hm)
      · obtain ⟨ds,hd,hw⟩ := mem_biUnion.mp hc
        exact mem_biUnion.mpr ⟨ds,mem_union_left _ hd,hw⟩
      · exact mem_biUnion.mpr ⟨box x,mem_union_right _ (mem_image_of_mem _ hm),by simp [(spec x hm).2.2]⟩
  have ins (x) (hx : x<B^k) (hs : x∈S) : x∈T := by
    apply (exactAt x hx).mpr
    exact (omits x hx hs).imp_right (fun hm => mem_filter.mpr ⟨hm,hx,hs⟩)
  have good : ∀ ds ∈ bs, valid B ds ∧ ds.length=k := by
    intro ds hd
    rcases mem_union.mp hd with hp | hm
    · exact states_valid B k 0 step finish start hp
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hm
      exact ⟨(spec y hy).1,(spec y hy).2.1⟩
  have sub : T ⊆ (extra : Set ℕ) ∪ S := by
    intro x hx
    obtain ⟨ds,hds,hw⟩ := mem_biUnion.mp hx
    obtain ⟨hv,hl⟩ := good ds hds
    have small : x<B^k := hl ▸ OMA.Erdos28DigitBoxes.words_lt B ds hv hw
    rcases (exactAt x small).mp hx with h | h
    · exact (adds x small h).symm
    · exact Or.inr (mem_filter.mp h).2.2
  have capT (n : ℕ) (hn : n ≤ 2*B^k-2) : sumRep T n ≤ g+2*extra.card := by
    exact (count_mono T _ sub n).trans ((add_bound S extra n).trans (Nat.add_le_add_right (cap n hn) _))
  have ob := box_count_obstruction B k (g+2*extra.card) h hb hg bs T good (fun _ _ => Iff.rfl)
    (by intro n hn; obtain ⟨a,ha,b,hb',he⟩ := cover n hn
        exact ⟨a,ins a (by omega) ha,b,ins b (by omega) hb',he⟩) capT
  have size : bs.card ≤ Fintype.card σ^k + miss.card := (card_union_le ..).trans
    (Nat.add_le_add (states_card B k 0 step finish start) (card_image_le.trans (card_filter_le ..)))
  exact ob.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ size) _)

end OMA.Erdos28DigitEdits


namespace OMA.Erdos28DigitEdits

open OMA.Erdos28DigitBoxes AdditiveCombinatorics

/-- Even an inexact reader is impossible for a capped cover when the
prefix is long enough. M fixes the block width and d bounds false
negatives. False positives enter only through the representation budget. -/
theorem finite_width_cutoff_with_errors {σ : Type*} [Fintype σ] [DecidableEq σ]
    (M g h d : ℕ) (miss extra : Finset ℕ) (hm : miss.card ≤ d)
    (hg : g+2*extra.card < 2^(h+1)) (width : (2*Fintype.card σ)^2 ≤ 2^M)
    (step : ℕ → σ → ℕ → σ) (finish : σ → Prop) (start : σ) (S : Set ℕ) :
    let B := 2^M
    let k := M*h+(d+1)
    (∀ x < B^k, x ∈ S → accepts B step finish k 0 start x ∨ x∈miss) →
    (∀ x < B^k, accepts B step finish k 0 start x → x∈S ∨ x∈extra) →
    (∀ n < B^k, ∃ a∈S, ∃ b∈S, a+b=n) →
    ∃ n ≤ 2*B^k-2, g < sumRep S n := by
  classical
  let B := 2^M
  let k := M*h+(d+1)
  let q := Fintype.card σ
  change (∀ x < B^k, x ∈ S → accepts B step finish k 0 start x ∨ x∈miss) →
    (∀ x < B^k, accepts B step finish k 0 start x → x∈S ∨ x∈extra) →
    (∀ n < B^k, ∃ a∈S, ∃ b∈S, a+b=n) →
    ∃ n ≤ 2*B^k-2, g < sumRep S n
  intro om ad cv
  by_contra! cap
  have upper := approximate_machine_bound B k g h (by dsimp [B]; positivity)
    step finish start S miss extra hg om ad cv cap
  change B^k ≤ ((q^k+miss.card)*B^h)^2 at upper
  have pq : 0<q := Fintype.card_pos_iff.mpr ⟨start⟩
  have pqk : 1≤q^k := Nat.one_le_pow _ _ pq
  have multiple : miss.card ≤ q^k*d := hm.trans (by simpa using Nat.mul_le_mul_right d pqk)
  have first : q^k+miss.card ≤ q^k*(d+1) := by rw [Nat.mul_succ]; omega
  have scale : (d+1)*B^h < 2^k := by
    have pb : 0 < B^h := pow_pos (pow_pos (by decide : 0 < (2:ℕ)) M) h
    calc
      (d+1)*B^h < 2^(d+1)*B^h := Nat.mul_lt_mul_of_pos_right (Nat.lt_pow_self (by decide : 1<2)) pb
      _ = 2^k := by
        change 2^(d+1)*(2^M)^h = 2^(M*h+(d+1))
        rw [← pow_mul, ← pow_add, Nat.add_comm (d+1) (M*h)]
  have compare : (q^k+miss.card)*B^h < (2*q)^k := calc
    _ ≤ (q^k*(d+1))*B^h := Nat.mul_le_mul_right _ first
    _ = q^k*((d+1)*B^h) := Nat.mul_assoc .. 
    _ < q^k*2^k := Nat.mul_lt_mul_of_pos_left scale pqk
    _ = (2*q)^k := by rw [mul_pow,Nat.mul_comm]
  have low : ((2*q)^k)^2 ≤ B^k := by
    rw [←pow_mul,Nat.mul_comm k 2,pow_mul]
    exact Nat.pow_le_pow_left width k
  have sq : ((q^k+miss.card)*B^h)^2 < ((2*q)^k)^2 := by
    exact Nat.pow_lt_pow_left compare (by decide)
  exact (Nat.not_lt_of_ge (low.trans upper)) sq

end OMA.Erdos28DigitEdits

