import OMAStatements.S_oeis_a384270
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
Paul D. Hanna proposed this parity question for OEIS A384270. The proof treats
the actual integer generating-series equation. Reduction modulo two forces the
binary series to satisfy Y = X + Y². A separate coefficientwise fixed-point
construction produces a normalized solution over the integers.
-/
namespace OMA.HannaReduction
open PowerSeries
abbrev Series := PowerSeries (ZMod 2)

private theorem square (f : Series) : f^2 = expand 2 (by decide) f := by
  have hf := MvPowerSeries.map_frobenius_expand 2 (by decide : 2 ≠ 0) (f := f)
  have hid : frobenius (ZMod 2) 2 = RingHom.id _ := Subsingleton.elim _ _
  simpa [hid, PowerSeries.expand] using hf.symm

private theorem fourth (f : Series) : f.subst ((X : Series)^4) = f^4 := by
  calc
    f.subst ((X : Series)^4) = expand 4 (by decide) f := (expand_apply 4 (by decide) f).symm
    _ = expand 2 (by decide) (expand 2 (by decide) f) := expand_mul 2 (by decide) 2 (by decide) f
    _ = (f^2)^2 := by rw [← square f, ← square]
    _ = f^4 := by ring

private theorem reduced (A : PowerSeries ℤ) (h : S_oeis_a384270.Defines A) :
    let Y := A.map (Int.castRingHom (ZMod 2))
    Y.subst ((X : Series)^3 + X*Y^3) = Y^3 := by
  obtain ⟨h0,h1,heq⟩ := h
  let red := Int.castRingHom (ZMod 2)
  let Y := A.map red
  let V := (X : PowerSeries ℤ)^3 + 3*X*A^3
  let W := (X : PowerSeries ℤ)^4 + 4*X*A^4
  have hv : HasSubst V := HasSubst.of_constantCoeff_zero (by
    change PowerSeries.constantCoeff V = 0
    simp [V])
  have hw : HasSubst W := HasSubst.of_constantCoeff_zero (by
    change PowerSeries.constantCoeff W = 0
    simp [W])
  have htwo : (2 : Series) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C : ZMod 2 →+* Series) (by decide : (2 : ZMod 2) = 0)
  have hthree : (3 : Series) = 1 := by linear_combination htwo
  have hfour : (4 : Series) = 0 := by linear_combination 2*htwo
  have hy : Y ≠ 0 := by
    intro hz
    have hcy := congrArg (coeff 1) hz
    simp [Y,red,coeff_map,h1] at hcy
  have eq1 := congrArg (PowerSeries.map red) heq
  change (PowerSeries.map red) (A * A.subst V) = (PowerSeries.map red) (A.subst W) at eq1
  have v : PowerSeries.map red (A.subst V) = Y.subst (PowerSeries.map red V) :=
    PowerSeries.map_subst (h:=red) hv A
  have w : PowerSeries.map red (A.subst W) = Y.subst (PowerSeries.map red W) :=
    PowerSeries.map_subst (h:=red) hw A
  rw [map_mul, v, w] at eq1
  change Y * Y.subst (PowerSeries.map red V) = Y.subst (PowerSeries.map red W) at eq1
  simp only [V, W, map_add, map_pow, map_mul, map_ofNat, PowerSeries.map_X,
    hthree,hfour,one_mul,zero_mul,add_zero] at eq1
  rw [fourth, show Y^4 = Y*Y^3 by ring] at eq1
  exact mul_left_cancel₀ (M₀ := Series) hy eq1

end OMA.HannaReduction

namespace OMA.HannaParity
open PowerSeries

abbrev Series := PowerSeries (ZMod 2)

private theorem vanish (Y : Series) (h0 : Y.constantCoeff = 0) (h1 : coeff 1 Y = 1)
    (eqn : Y.subst ((X : Series)^3 + X*Y^3) = Y^3) :
    (X : Series) + (Y + Y^2) = 0 := by
  let T := Y + Y^2
  let F := (X : Series) + T
  let Q := (X : Series)^3 + X*Y^3
  let K := (X : Series)^2 + (T*F + Y^3)
  have oy : Y.order = 1 := by
    apply (order_eq_nat (n := 1)).mpr
    exact ⟨by simp [h1], fun i hi => by interval_cases i; simpa [coeff_zero_eq_constantCoeff] using h0⟩
  have oy2 : (Y^2).order = 2 := by rw [order_pow, oy]; norm_num
  have oy3 : (Y^3).order = 3 := by rw [order_pow, oy]; norm_num
  have ot : T.order = 1 := by
    change (Y+Y^2).order = _
    rw [order_add_of_order_ne _ _ (by rw [oy,oy2]; decide),oy,oy2]; rfl
  have ofl : 2 ≤ F.order := by
    apply nat_le_order F 2
    intro i hi
    have hz := coeff_of_lt_order (φ:=Y^2) i (by rw [oy2]; exact_mod_cast hi)
    interval_cases i <;> simp [F,T, map_add, coeff_zero_eq_constantCoeff, h0,h1,hz] <;> decide
  have oq : Q.order = 3 := by
    have o4 : ((X : Series)*Y^3).order = 4 := by rw [order_mul,order_X,oy3]; rfl
    change ((X : Series)^3 + X*Y^3).order = _
    rw [order_add_of_order_ne _ _ (by rw [order_X_pow,o4]; decide),order_X_pow,o4]; rfl
  have ok : K.order = 2 := by
    have lower : 3 ≤ (T*F + Y^3).order := by
      apply le_trans _ (min_order_le_order_add _ _)
      apply le_min
      · rw [order_mul,ot]
        exact (show (1 : ℕ∞)+2 ≤ 1 + F.order from add_le_add le_rfl ofl)
      · rw [oy3]
    change ((X : Series)^2 + (T*F + Y^3)).order = _
    have smaller : ((X : Series)^2).order < (T*F + Y^3).order :=
      lt_of_lt_of_le (by rw [order_X_pow]; decide) lower
    rw [order_add_of_order_ne _ _ smaller.ne, min_eq_left smaller.le, order_X_pow]
    rfl
  have hq : HasSubst Q := HasSubst.of_constantCoeff_zero (by
    change PowerSeries.constantCoeff Q = 0
    simp [Q])
  have identity : F.subst Q = F*K := by
    change ((X : Series)+(Y+Y^2)).subst Q = _
    rw [subst_add hq, subst_add hq, subst_X hq, subst_pow hq, show Y.subst Q = _ from eqn]
    dsimp [Q,K,F,T]
    have two : (2 : Series) = 0 := by
      simpa only [map_ofNat, map_zero] using
        congrArg (PowerSeries.C : ZMod 2 →+* Series) (by decide : (2 : ZMod 2) = 0)
    grind
  by_contra h
  have hn : F ≠ 0 := h
  have bound : Q.order * F.order ≤ PowerSeries.order (F.subst Q : Series) := by
    simpa only [PowerSeries.order_eq_order] using le_order_subst Q hq F
  rw [identity, order_mul, ok, oq, ← coe_toNat_order hn] at bound
  rw [← coe_toNat_order hn] at ofl
  have b : 3 * F.order.toNat ≤ F.order.toNat + 2 := by exact_mod_cast bound
  have f : 2 ≤ F.order.toNat := by exact_mod_cast ofl
  omega

end OMA.HannaParity

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

namespace OMA.HannaParity
open PowerSeries

theorem parity (A : PowerSeries ℤ) (ha : OMA.S_oeis_a384270.Defines A) :
    ∀ n : ℕ, 0 < n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k) := by
  let Y := A.map (Int.castRingHom (ZMod 2))
  have zeroC : Y.constantCoeff = 0 := by
    dsimp only [Y]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, ha.1, map_zero]
  have oneC : coeff 1 Y = 1 := by simp [Y, coeff_map, ha.2.1]
  have equation := OMA.HannaReduction.reduced A ha
  have binary := vanish Y zeroC oneC equation
  have two : (2 : Series) = 0 := by
    simpa only [map_ofNat,map_zero] using
      congrArg (PowerSeries.C : ZMod 2 →+* Series) (by decide : (2 : ZMod 2) = 0)
  have relation : Y = X + Y^2 := by linear_combination -binary + Y * two
  have step (n : ℕ) (hn : 1 < n) :
      coeff n Y = if 2 ∣ n then coeff (n/2) Y else 0 := by
    have h := congrArg (coeff n) relation
    rw [map_add, OMA.HannaReduction.square, coeff_expand] at h
    simpa [coeff_X, show n ≠ 1 by omega] using h
  intro n hn
  have ans := OMA.HannaDyadic.support_two (fun i => coeff i Y) oneC step n hn
  simpa only [Y, coeff_map, Int.coe_castRingHom, ZMod.intCast_eq_one_iff_odd] using ans

end OMA.HannaParity

namespace OMA.HannaExistence

open PowerSeries

private abbrev Series := PowerSeries ℤ

/-- Agreement of all coefficients strictly below degree k. -/
private def Agree (k : ℕ) (f g : Series) : Prop := (X : Series)^k ∣ f - g

private theorem agree_iff {k : ℕ} {f g : Series} :
    Agree k f g ↔ ∀ i < k, coeff i f = coeff i g := by
  simp [Agree, X_pow_dvd_iff, sub_eq_zero]

private theorem agree_trans {k : ℕ} {f g h : Series} (hf : Agree k f g)
    (hg : Agree k g h) : Agree k f h :=
  agree_iff.mpr (fun i hi => (agree_iff.mp hf i hi).trans (agree_iff.mp hg i hi))

private theorem agree_mul {k : ℕ} {a b c d : Series}
    (hab : Agree k a b) (hcd : Agree k c d) : Agree k (a*c) (b*d) := by
  change X^k ∣ a*c-b*d
  rw [show a*c-b*d = (a-b)*c+b*(c-d) by ring]
  exact dvd_add (dvd_mul_of_dvd_left hab _) (dvd_mul_of_dvd_right hcd _)

private theorem agree_inner {k : ℕ} {u v : Series} (hu : HasSubst u) (hv : HasSubst v)
    (h : Agree k u v) (f : Series) : Agree k (f.subst u) (f.subst v) := by
  apply agree_iff.mpr
  intro i hi
  rw [coeff_subst' hu, coeff_subst' hv]
  apply finsum_congr
  intro j
  have hp : Agree k (u^j) (v^j) := Dvd.dvd.trans h (sub_dvd_pow_sub_pow u v j)
  rw [agree_iff.mp hp i hi]

private theorem agree_outer {k : ℕ} (hk : 0 < k) {u f g : Series}
    (hu : HasSubst u) (h2 : (X : Series)^2 ∣ u) (h : Agree k f g) :
    Agree (k+1) (f.subst u) (g.subst u) := by
  obtain ⟨a, ha⟩ := h
  change X^(k+1) ∣ f.subst u - g.subst u
  rw [← subst_sub hu, ha, subst_mul hu, subst_pow hu, subst_X hu]
  apply dvd_mul_of_dvd_left
  obtain ⟨b, hb⟩ := h2
  rw [hb, mul_pow, ← pow_mul]
  exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _

private noncomputable def factor (j : ℕ) (b : Series) : Series := 1 + (j : Series)*X*b^j
private noncomputable def arg (j : ℕ) (b : Series) : Series := X^j * factor j b
private noncomputable def weight (j : ℕ) (b : Series) : Series :=
  factor j b * b.subst (arg j b)
private noncomputable def step (b : Series) : Series := weight 4 b - b*(weight 3 b - 1)

private theorem arg_zero {j : ℕ} (hj : 2 ≤ j) (b : Series) :
    (arg j b).constantCoeff = 0 := by simp [arg, show j ≠ 0 by omega]

private theorem weight_zero {j : ℕ} (hj : 2 ≤ j) (b : Series) :
    (weight j b).constantCoeff = b.constantCoeff := by
  have hq := arg_zero hj b
  have hz : ((b-C b.constantCoeff).subst (arg j b) : Series).constantCoeff = 0 :=
    constantCoeff_subst_eq_zero hq _ (by simp)
  rw [subst_sub (HasSubst.of_constantCoeff_zero' hq)] at hz
  change constantCoeff (b.subst (arg j b) - (C b.constantCoeff).subst (arg j b) : Series) = 0 at hz
  rw [map_sub, subst_C] at hz
  change constantCoeff (b.subst (arg j b) : Series) - b.constantCoeff = 0 at hz
  simp [weight, factor, sub_eq_zero.mp hz]

private theorem step_zero (b : Series) (hb : b.constantCoeff = 1) :
    (step b).constantCoeff = 1 := by
  simp [step, weight_zero (j:=3) (by decide), weight_zero (j:=4) (by decide), hb]

private theorem weight_agree {k j : ℕ} (hk : 0 < k) (hj : 2 ≤ j) {b c : Series}
    (h : Agree k b c) : Agree (k+1) (weight j b) (weight j c) := by
  have hp : (X : Series)^k ∣ b^j-c^j := Dvd.dvd.trans h (sub_dvd_pow_sub_pow b c j)
  obtain ⟨t, ht⟩ := hp
  have hf : Agree (k+1) (factor j b) (factor j c) := by
    refine ⟨(j : Series)*t, ?_⟩
    change 1+(j : Series)*X*b^j-(1+(j : Series)*X*c^j) = _
    calc
      _ = (j : Series)*X*(b^j-c^j) := by ring
      _ = _ := by rw [ht, pow_succ]; ring
  have ha : Agree (k+1) (arg j b) (arg j c) :=
    agree_mul (show Agree (k+1) (X^j) (X^j) by simp [Agree]) hf
  have h2 : (X : Series)^2 ∣ arg j b := dvd_mul_of_dvd_left (pow_dvd_pow _ hj) _
  have hb := HasSubst.of_constantCoeff_zero' (arg_zero hj b)
  have hc := HasSubst.of_constantCoeff_zero' (arg_zero hj c)
  exact agree_mul hf (agree_trans (agree_outer hk hb h2 h) (agree_inner hb hc ha c))

private theorem step_agree {k : ℕ} (hk : 0 < k) {b c : Series}
    (hb : b.constantCoeff = 1) (h : Agree k b c) : Agree (k+1) (step b) (step c) := by
  have h3 := weight_agree hk (j:=3) (by decide) h
  have h4 := weight_agree hk (j:=4) (by decide) h
  have h1 : (X : Series) ∣ weight 3 b - 1 := by
    rw [X_dvd_iff, map_sub, weight_zero (by decide), hb, map_one, sub_self]
  have hh : (X : Series)^(k+1) ∣ (b-c)*(weight 3 b-1) := by
    simpa [pow_succ] using mul_dvd_mul (show X^k ∣ b-c from h) h1
  change X^(k+1) ∣ (weight 4 b-b*(weight 3 b-1))-(weight 4 c-c*(weight 3 c-1))
  rw [show (weight 4 b-b*(weight 3 b-1))-(weight 4 c-c*(weight 3 c-1)) =
      (weight 4 b-weight 4 c)-(b-c)*(weight 3 b-1)-c*(weight 3 b-weight 3 c) by ring]
  exact dvd_sub (dvd_sub h4 hh) (dvd_mul_of_dvd_right h3 _)

private noncomputable def approx : ℕ → Series
  | 0 => 1
  | n+1 => step (approx n)

private theorem approx_zero (n : ℕ) : (approx n).constantCoeff = 1 := by
  induction n with
  | zero => simp [approx]
  | succ n ih => exact step_zero _ ih

private theorem successive (n : ℕ) : Agree (n+1) (approx n) (approx (n+1)) := by
  induction n with
  | zero =>
    apply agree_iff.mpr
    intro i hi
    have : i = 0 := by omega
    simp [this, coeff_zero_eq_constantCoeff, approx_zero]
  | succ n ih => exact step_agree (by omega) (approx_zero n) ih

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
  have hh := agree_iff.mp (step_agree (by omega) limit_zero h) i (by omega)
  change coeff i (step limit) = coeff i (approx (i+1)) at hh
  rw [limit, coeff_mk] at ⊢
  exact hh.trans (stabilized i (i+1) (by omega)).symm

/-- The recursively stabilized integral series solves Hanna's equation. -/
theorem existence : ∃ A, S_oeis_a384270.Defines A := by
  let b := limit
  have hf : weight 4 b - b*(weight 3 b-1) = b := fixed
  have he : b*weight 3 b = weight 4 b := by linear_combination -hf
  refine ⟨X*b, by simp, ?_, ?_⟩
  · simpa only [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] using limit_zero
  · have q3 : (X : Series)^3+3*X*(X*b)^3 = arg 3 b := by dsimp [arg,factor]; ring
    have q4 : (X : Series)^4+4*X*(X*b)^4 = arg 4 b := by dsimp [arg,factor]; ring
    have h3 := HasSubst.of_constantCoeff_zero' (arg_zero (j:=3) (by decide) b)
    have h4 := HasSubst.of_constantCoeff_zero' (arg_zero (j:=4) (by decide) b)
    rw [q3, q4, subst_mul h3, subst_mul h4, subst_X h3, subst_X h4]
    calc
      _ = X^4*(b*weight 3 b) := by dsimp [weight,arg]; ring
      _ = X^4*weight 4 b := by rw [he]
      _ = _ := by dsimp [weight,arg]; ring

end OMA.HannaExistence

theorem OMA.solution : type_of% @OMA.S_oeis_a384270.main :=
  ⟨OMA.HannaExistence.existence, OMA.HannaParity.parity⟩
