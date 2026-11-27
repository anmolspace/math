import OMAStatements.S_oeis_a392525
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

namespace OMA.CubicFifteenFive
open PowerSeries
private abbrev Series := PowerSeries (ZMod 5)

/-- Reducing the given cubic-substitution equation modulo five leaves only X. -/
theorem linear_mod_five (A : PowerSeries ℤ) (ha : OMA.S_oeis_a392525.Defines A) :
    A.map (Int.castRingHom (ZMod 5)) = X := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let red := Int.castRingHom (ZMod 5)
  let Y := A.map red
  let V := (X : PowerSeries ℤ)^3 + 15*X*A^3
  let E := Y-(X : Series)
  have hc : Y.constantCoeff = 0 := by
    dsimp only [Y]
    rw [← coeff_zero_eq_constantCoeff,coeff_map,coeff_zero_eq_constantCoeff,ha.1,map_zero]
  have hl : coeff 1 Y = 1 := by simp [Y,red,coeff_map,ha.2.1]
  have low : 2 ≤ E.order := by
    apply nat_le_order E 2
    intro i hi
    interval_cases i <;> simp [E, coeff_zero_eq_constantCoeff, hc, hl]
  have hv : HasSubst V := HasSubst.of_constantCoeff_zero (by
    change PowerSeries.constantCoeff V = 0
    simp [V])
  have sub : PowerSeries.map red (A.subst V) = Y.subst (PowerSeries.map red V) :=
    PowerSeries.map_subst (h:=red) hv A
  have h15 : (15 : Series) = 0 := by
    simpa only [map_ofNat,map_zero] using congrArg (PowerSeries.C : ZMod 5 →+* Series)
      (by decide : (15 : ZMod 5)=0)
  have mapped := congrArg (PowerSeries.map red) ha.2.2
  change PowerSeries.map red (A^3) = PowerSeries.map red (A.subst V) at mapped
  rw [map_pow,sub] at mapped
  simp only [V,map_add,map_mul,map_pow,map_ofNat,PowerSeries.map_X,h15,zero_mul,add_zero] at mapped
  have cube : Y.subst ((X : Series)^3) = Y^3 := mapped.symm
  have hq : HasSubst ((X : Series)^3) := HasSubst.X_pow (by decide)
  let K := 3*(X : Series)^2 + E*(3*X+E)
  have ident : E.subst ((X : Series)^3) = E*K := by
    rw [show E = Y-X from rfl, subst_sub hq, cube, subst_X hq]
    dsimp [K,E]
    ring
  have o3 : (3 : Series).order = 0 := by
    apply (order_eq_nat (n:=0)).mpr
    constructor
    · rw [coeff_zero_eq_constantCoeff, map_ofNat]
      decide
    · omega
  have left : (3*(X : Series)^2).order = 2 := by rw [order_mul,o3,order_X_pow]; rfl
  have rest : 3 ≤ (E*(3*X+E)).order := by
    rw [order_mul]
    have positive : 1 ≤ (3*X+E).order := by
      apply le_trans _ (min_order_le_order_add _ _)
      apply le_min
      · rw [order_mul,o3,order_X]; rfl
      · exact le_trans (by decide) low
    exact (show (2 : ℕ∞)+1 ≤ _ from add_le_add low positive)
  have small : (3*(X : Series)^2).order < (E*(3*X+E)).order :=
    lt_of_lt_of_le (by rw [left]; decide) rest
  have ok : K.order = 2 := by
    change (3*X^2+E*(3*X+E)).order = _
    rw [order_add_of_order_ne _ _ small.ne,min_eq_left small.le,left]
  change Y = X
  by_contra h
  have ne : E ≠ 0 := sub_ne_zero.mpr h
  have bound : ((X : Series)^3).order * E.order ≤ PowerSeries.order (E.subst ((X : Series)^3) : Series) := by
    simpa only [PowerSeries.order_eq_order] using le_order_subst ((X : Series)^3) hq E
  rw [ident,order_mul,ok,order_X_pow,← coe_toNat_order ne] at bound
  rw [← coe_toNat_order ne] at low
  have b : 3*E.order.toNat ≤ E.order.toNat+2 := by exact_mod_cast bound
  have g : 2 ≤ E.order.toNat := by exact_mod_cast low
  omega

end OMA.CubicFifteenFive


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


namespace OMA.CubicFrobenius
open PowerSeries
abbrev Series := PowerSeries (ZMod 2)

private theorem square (f : Series) : f^2 = expand 2 (by decide) f := by
  have hf := MvPowerSeries.map_frobenius_expand 2 (by decide : 2 ≠ 0) (f := f)
  have hid : frobenius (ZMod 2) 2 = RingHom.id _ := Subsingleton.elim _ _
  simpa [hid, PowerSeries.expand] using hf.symm

end OMA.CubicFrobenius

namespace OMA.CubicFifteen
open PowerSeries
private abbrev Binary := PowerSeries (ZMod 2)

private theorem binary_equation (A : PowerSeries ℤ) (ha : OMA.S_oeis_a392525.Defines A) :
    let Y := A.map (Int.castRingHom (ZMod 2))
    Y.subst ((X : Binary)^3+X*Y^3) = Y^3 := by
  let red := Int.castRingHom (ZMod 2)
  let V := (X : PowerSeries ℤ)^3+15*X*A^3
  let Y := A.map red
  have hv : HasSubst V := HasSubst.of_constantCoeff_zero (by
    change PowerSeries.constantCoeff V = 0
    simp [V])
  have sub : PowerSeries.map red (A.subst V) = Y.subst (PowerSeries.map red V) :=
    PowerSeries.map_subst (h:=red) hv A
  have h15 : (15 : Binary) = 1 := by
    simpa only [map_ofNat,map_one] using congrArg (PowerSeries.C : ZMod 2 →+* Binary)
      (by decide : (15 : ZMod 2)=1)
  have eq1 := congrArg (PowerSeries.map red) ha.2.2
  change PowerSeries.map red (A^3) = PowerSeries.map red (A.subst V) at eq1
  rw [map_pow,sub] at eq1
  simp only [V,map_add,map_pow,map_mul,map_ofNat,PowerSeries.map_X,h15,one_mul] at eq1
  exact eq1.symm

theorem residues (A : PowerSeries ℤ) (ha : OMA.S_oeis_a392525.Defines A) :
    ∀ n : ℕ, 0 < n →
      (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k) ∧
      (coeff n A % 10 = 5 ↔ ∃ k : ℕ, n = 2^(k+1)) := by
  let Y := A.map (Int.castRingHom (ZMod 2))
  have zeroC : Y.constantCoeff = 0 := by
    dsimp only [Y]
    rw [← coeff_zero_eq_constantCoeff,coeff_map,coeff_zero_eq_constantCoeff,ha.1,map_zero]
  have oneC : coeff 1 Y = 1 := by simp [Y,coeff_map,ha.2.1]
  have binary := OMA.HannaParity.vanish Y zeroC oneC (binary_equation A ha)
  have two : (2 : Binary) = 0 := by
    simpa only [map_ofNat,map_zero] using congrArg (PowerSeries.C : ZMod 2 →+* Binary)
      (by decide : (2 : ZMod 2)=0)
  have relation : Y = X + Y^2 := by linear_combination -binary + Y*two
  have step (n : ℕ) (hn : 1 < n) :
      coeff n Y = if 2 ∣ n then coeff (n/2) Y else 0 := by
    have h := congrArg (coeff n) relation
    rw [map_add, OMA.CubicFrobenius.square,coeff_expand] at h
    simpa [coeff_X,show n ≠ 1 by omega] using h
  intro n hn
  have binaryAns := OMA.HannaDyadic.support_two (fun i => coeff i Y) oneC step n hn
  have hp : Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k := by
    simpa only [Y, coeff_map, Int.coe_castRingHom, ZMod.intCast_eq_one_iff_odd] using binaryAns
  refine ⟨hp,?_⟩
  by_cases h1 : n = 1
  · subst n
    rw [ha.2.1]
    constructor
    · norm_num
    · rintro ⟨k,hk⟩
      rw [pow_succ] at hk
      omega
  have reduced := congrArg (coeff n) (OMA.CubicFifteenFive.linear_mod_five A ha)
  have hdiv : (5 : ℤ) ∣ coeff n A := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    simpa [coeff_map, coeff_X, h1] using reduced
  have last : coeff n A % 10 = 5 ↔ Odd (coeff n A) := by
    obtain ⟨k,hk⟩ := hdiv
    rw [hk,Int.odd_iff]
    omega
  rw [last,hp]
  constructor
  · rintro ⟨k,hk⟩
    cases k with
    | zero => exact (h1 (hk.trans (pow_zero 2))).elim
    | succ k => exact ⟨k,hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k+1,hk⟩

end OMA.CubicFifteen


namespace OMA.CubicFifteenExistence

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

/-- Substituting congruent arguments preserves their degree of agreement. -/
private theorem agree_inner {k : ℕ} {u v : Series} (hu : HasSubst u) (hv : HasSubst v)
    (h : Agree k u v) (f : Series) : Agree k (f.subst u) (f.subst v) := by
  apply agree_iff.mpr
  intro i hi
  rw [coeff_subst' hu, coeff_subst' hv]
  apply finsum_congr
  intro j
  have hp : Agree k (u^j) (v^j) := Dvd.dvd.trans h (sub_dvd_pow_sub_pow u v j)
  rw [agree_iff.mp hp i hi]

/-- An argument divisible by X² makes congruent outer series agree one degree further. -/
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

/-- After writing A = XB, the two substitution arguments are Xʲ times this factor. -/
private noncomputable def factor (j : ℕ) (b : Series) : Series := 1 + (15 : Series)*X*b^j
private noncomputable def arg (j : ℕ) (b : Series) : Series := X^j * factor j b
private noncomputable def weight (j : ℕ) (b : Series) : Series :=
  factor j b * b.subst (arg j b)
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

private theorem weight_agree {k j : ℕ} (hk : 0 < k) (hj : 2 ≤ j) {b c : Series}
    (h : Agree k b c) : Agree (k+1) (weight j b) (weight j c) := by
  have hp : (X : Series)^k ∣ b^j-c^j := Dvd.dvd.trans h (sub_dvd_pow_sub_pow b c j)
  obtain ⟨t, ht⟩ := hp
  have hf : Agree (k+1) (factor j b) (factor j c) := by
    refine ⟨(15 : Series)*t, ?_⟩
    change 1+(15 : Series)*X*b^j-(1+(15 : Series)*X*c^j) = _
    calc
      _ = (15 : Series)*X*(b^j-c^j) := by ring
      _ = _ := by rw [ht, pow_succ]; ring
  have ha : Agree (k+1) (arg j b) (arg j c) :=
    agree_mul (show Agree (k+1) (X^j) (X^j) by simp [Agree]) hf
  have h2 : (X : Series)^2 ∣ arg j b := dvd_mul_of_dvd_left (pow_dvd_pow _ hj) _
  have hb := HasSubst.of_constantCoeff_zero' (arg_zero hj b)
  have hc := HasSubst.of_constantCoeff_zero' (arg_zero hj c)
  exact agree_mul hf (agree_trans (agree_outer hk hb h2 h) (agree_inner hb hc ha c))

/-- The residual of the normalized cubic equation after cancelling X³. -/
private noncomputable def residual (b : Series) : Series := weight 3 b - b^3

/-- Frobenius in characteristic three makes every coefficient of the residual divisible by three. -/
private theorem residual_dvd (b : Series) (i : ℕ) : (3 : ℤ) ∣ coeff i (residual b) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let red := Int.castRingHom (ZMod 3)
  let Y := b.map red
  have h15 : (15 : PowerSeries (ZMod 3)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C : ZMod 3 →+* PowerSeries (ZMod 3)) (by decide : (15 : ZMod 3) = 0)
  have hf : PowerSeries.map red (factor 3 b) = 1 := by
    simp only [factor, map_add, map_one, map_mul, map_pow, map_ofNat, PowerSeries.map_X,
      h15, zero_mul, add_zero]
  have ha : PowerSeries.map red (arg 3 b) = X^3 := by simp [arg, hf]
  have hs : PowerSeries.map red (b.subst (arg 3 b)) = Y.subst (PowerSeries.map red (arg 3 b)) :=
    PowerSeries.map_subst (h := red) (HasSubst.of_constantCoeff_zero' (arg_zero (by decide) b)) b
  have hpow : Y.subst ((X : PowerSeries (ZMod 3))^3) = Y^3 := by
    have he := MvPowerSeries.map_frobenius_expand 3 (by decide : 3 ≠ 0) (f := Y)
    have hi : frobenius (ZMod 3) 3 = RingHom.id _ := Subsingleton.elim _ _
    calc
      _ = expand 3 (by decide) Y := (expand_apply 3 (by decide) Y).symm
      _ = _ := by simpa [hi, PowerSeries.expand] using he
  have hz : PowerSeries.map red (residual b) = 0 := by
    change PowerSeries.map red (factor 3 b * b.subst (arg 3 b) - b^3) = 0
    rw [map_sub, map_mul, map_pow, hf, one_mul, hs, ha]
    exact sub_eq_zero.mpr hpow
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  have hc := congrArg (coeff i) hz
  simpa [red, coeff_map] using hc

/-- Divide the integral residual coefficientwise to correct the approximation. -/
private noncomputable def step (b : Series) : Series :=
  mk fun i => coeff i b + coeff i (residual b) / 3

private theorem coeff_step (b : Series) (i : ℕ) :
    3 * coeff i (step b) = 3*coeff i b + coeff i (residual b) := by
  rw [step, coeff_mk]
  have h := Int.ediv_mul_cancel (residual_dvd b i)
  omega

private theorem step_zero (b : Series) (hb : b.constantCoeff = 1) :
    (step b).constantCoeff = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, step, coeff_mk]
  simp [coeff_zero_eq_constantCoeff, residual, weight_zero (j := 3) (by decide), hb]

private theorem coeff_triple (b : Series) (i : ℕ) : coeff i (3*b) = 3*coeff i b := by
  rw [show (3 : Series) = C (3 : ℤ) by simp, coeff_C_mul]

private theorem step_agree {k : ℕ} (hk : 0 < k) {b c : Series}
    (hb : b.constantCoeff = 1) (h : Agree k b c) : Agree (k+1) (step b) (step c) := by
  have hc : c.constantCoeff = 1 := by
    have h₀ := agree_iff.mp h 0 hk
    rw [coeff_zero_eq_constantCoeff] at h₀
    exact h₀.symm.trans hb
  have hw := weight_agree hk (j := 3) (by decide) h
  have hp : (X : Series) ∣ 3-(b^2+b*c+c^2) := by
    rw [X_dvd_iff]
    simp [hb, hc, map_ofNat]
  have hprod : (X : Series)^(k+1) ∣ (b-c)*(3-(b^2+b*c+c^2)) := by
    simpa [pow_succ] using mul_dvd_mul (show X^k ∣ b-c from h) hp
  have hall : Agree (k+1) (3*b+residual b) (3*c+residual c) := by
    change X^(k+1) ∣ (3*b+(weight 3 b-b^3))-(3*c+(weight 3 c-c^3))
    rw [show (3*b+(weight 3 b-b^3))-(3*c+(weight 3 c-c^3)) =
      (weight 3 b-weight 3 c)+(b-c)*(3-(b^2+b*c+c^2)) by ring]
    exact dvd_add hw hprod
  apply agree_iff.mpr
  intro i hi
  have eq := agree_iff.mp hall i hi
  simp only [map_add, coeff_triple] at eq
  have := coeff_step b i
  have := coeff_step c i
  omega

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

/-- At degree i the coefficient has stabilized by the ith iterate. -/
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

/-- The stabilized integral series solves Hanna's cubic substitution equation. -/
theorem existence : ∃ A, S_oeis_a392525.Defines A := by
  let b := limit
  have hf : step b = b := fixed
  have hr : residual b = 0 := by
    ext i
    have h := coeff_step b i
    rw [hf] at h
    simp only [map_zero]
    omega
  have he : weight 3 b = b^3 := sub_eq_zero.mp hr
  refine ⟨X*b, by simp, ?_, ?_⟩
  · simpa only [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] using limit_zero
  · have q : (X : Series)^3+15*X*(X*b)^3 = arg 3 b := by dsimp [arg, factor]; ring
    have hq := HasSubst.of_constantCoeff_zero' (arg_zero (j := 3) (by decide) b)
    rw [q, subst_mul hq, subst_X hq]
    calc
      (X*b)^3 = X^3*b^3 := by ring
      _ = X^3*weight 3 b := by rw [he]
      _ = _ := by dsimp [weight, arg]; ring

end OMA.CubicFifteenExistence

theorem OMA.solution : type_of% @OMA.S_oeis_a392525.main :=
  ⟨OMA.CubicFifteenExistence.existence, OMA.CubicFifteen.residues⟩
