import OMAStatements.S_oeis_a363309
import Mathlib.Tactic

/-!
Source: https://oeis.org/A363309
Credit: @anmolspace. Paul D. Hanna gave the series and the integer-root
conjecture in 2023. The explicit root is B times F evaluated at X B^(n−1).
-/

namespace OMA.A363309Proof

open PowerSeries

private abbrev Series := PowerSeries ℤ
private def Agree (k : ℕ) (f g : Series) : Prop := (X : Series)^k ∣ f-g

private theorem agree_iff {k : ℕ} {f g : Series} :
    Agree k f g ↔ ∀ i < k, coeff i f = coeff i g := by
  simp [Agree, X_pow_dvd_iff, sub_eq_zero]

private theorem shift_pow {k : ℕ} {b c : Series} (h : Agree k b c) (n : ℕ) :
    Agree (k+1) (X*b^n) (X*c^n) := by
  obtain ⟨a, ha⟩ := Dvd.dvd.trans (show (X : Series)^k ∣ b-c from h) (sub_dvd_pow_sub_pow b c n)
  refine ⟨a, ?_⟩
  calc
    _ = X*(b^n-c^n) := by ring
    _ = _ := by rw [ha, pow_succ]; ring

private theorem agree_inner {k : ℕ} {u v : Series} (hu : HasSubst u) (hv : HasSubst v)
    (h : Agree k u v) (f : Series) : Agree k (f.subst u) (f.subst v) := by
  apply agree_iff.mpr
  intro i hi
  rw [coeff_subst' hu, coeff_subst' hv]
  apply finsum_congr
  intro j
  have hp : Agree k (u^j) (v^j) := Dvd.dvd.trans h (sub_dvd_pow_sub_pow u v j)
  rw [agree_iff.mp hp i hi]

private noncomputable def approx (f : Series → Series) : ℕ → Series
  | 0 => 0
  | n+1 => f (approx f n)

/-- A map that fixes one more coefficient at every iteration has an integral fixed point. -/
private theorem fixed_of_agree (f : Series → Series)
    (hf : ∀ {k u v}, Agree k u v → Agree (k+1) (f u) (f v)) : ∃ u, f u = u := by
  have adjacent (n : ℕ) : Agree n (approx f n) (approx f (n+1)) := by
    induction n with
    | zero => exact agree_iff.mpr (fun _ hi => (Nat.not_lt_zero _ hi).elim)
    | succ n ih => exact hf ih
  have stable (i n : ℕ) (hin : i+1 ≤ n) :
      coeff i (approx f (i+1)) = coeff i (approx f n) := by
    induction n, hin using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact ih.trans (agree_iff.mp (adjacent n) i (by omega))
  let u : Series := mk fun i => coeff i (approx f (i+1))
  refine ⟨u, ?_⟩
  ext i
  have h : Agree (i+1) u (approx f (i+1)) := by
    apply agree_iff.mpr
    intro j hj
    simp only [u, coeff_mk]
    exact stable j (i+1) (by omega)
  have hh := agree_iff.mp (hf h) i (by omega)
  change coeff i (f u) = coeff i (approx f (i+2)) at hh
  exact hh.trans (by simpa only [u, coeff_mk] using (stable i (i+2) (by omega)).symm)

private theorem exists_series (n : ℕ) : ∃ F A B, S_oeis_a363309.Defines n F A B := by
  have hFstep {k : ℕ} {u v : Series} (h : Agree k u v) :
      Agree (k+1) (1+X*u^n) (1+X*v^n) := by
    simpa [Agree] using shift_pow h n
  obtain ⟨F, hF⟩ := fixed_of_agree (fun u => 1+X*u^n) hFstep
  let A : Series := F.subst (X*F^(2*n-1))
  have hBstep {k : ℕ} {u v : Series} (h : Agree k u v) :
      Agree (k+1) (A.subst (X*u^(n-1))) (A.subst (X*v^(n-1))) :=
    agree_inner (HasSubst.of_constantCoeff_zero' (by simp))
      (HasSubst.of_constantCoeff_zero' (by simp)) (shift_pow h (n-1)) A
  obtain ⟨B, hB⟩ := fixed_of_agree (fun u => A.subst (X*u^(n-1))) hBstep
  exact ⟨F, A, B, hF.symm, rfl, hB.symm⟩

private theorem subst_constant {q : Series} (hq : q.constantCoeff = 0) (f : Series) :
    PowerSeries.constantCoeff (f.subst q : Series) = PowerSeries.constantCoeff f := by
  have hz : ((f-C f.constantCoeff).subst q : Series).constantCoeff = 0 :=
    constantCoeff_subst_eq_zero hq _ (by simp)
  rw [subst_sub (HasSubst.of_constantCoeff_zero' hq)] at hz
  change constantCoeff (f.subst q - (C f.constantCoeff).subst q : Series) = 0 at hz
  rw [map_sub, subst_C] at hz
  exact sub_eq_zero.mp hz

private theorem integer_root (n : ℕ) (hn : 1 ≤ n) (F A B : Series)
    (h : S_oeis_a363309.Defines n F A B) :
    ∃ R : Series, R.constantCoeff = 1 ∧ B = 1+X*R^(2*n-1) := by
  obtain ⟨hF, hA, hB⟩ := h
  let m := 2*n-1
  let T : Series := X*B^(n-1)
  let H : Series := F.subst T
  have hq : HasSubst (X*F^m : Series) := HasSubst.of_constantCoeff_zero' (by simp)
  have hT0 : T.constantCoeff = 0 := by simp [T]
  have hT := HasSubst.of_constantCoeff_zero' hT0
  have hF0 := congrArg constantCoeff hF
  have fzero : F.constantCoeff = 1 := by simpa using hF0
  have azero : A.constantCoeff = 1 := by
    rw [hA]
    exact (subst_constant (q:=X*F^(2*n-1)) (by simp) F).trans fzero
  have hb : B = A.subst T := hB
  have bzero : B.constantCoeff = 1 := by
    rw [hb]
    exact (subst_constant hT0 A).trans azero
  have hAF : (substAlgHom hq) F = A := by simpa only [coe_substAlgHom] using hA.symm
  have hBA : (substAlgHom hT) A = B := by simpa only [coe_substAlgHom] using hb.symm
  have hHF : (substAlgHom hT) F = H := by simp only [coe_substAlgHom]; rfl
  have aeq : A = 1+(X*F^m)*A^n := by
    calc
      A = (substAlgHom hq) F := hAF.symm
      _ = (substAlgHom hq) (1+X*F^n) := congrArg _ hF
      _ = _ := by simp only [map_add, map_one, map_mul, map_pow, substAlgHom_X, hAF]
  have beq : B = 1+(T*H^m)*B^n := by
    calc
      B = (substAlgHom hT) A := hBA.symm
      _ = (substAlgHom hT) (1+(X*F^m)*A^n) := congrArg _ aeq
      _ = _ := by
        simp only [map_add, map_one, map_mul, map_pow, substAlgHom_X, hHF, hBA]
  refine ⟨B*H, ?_, ?_⟩
  · rw [map_mul, bzero]
    rw [one_mul]
    exact (subst_constant hT0 F).trans fzero
  · calc
      B = 1+(X*B^(n-1)*H^m)*B^n := beq
      _ = 1+X*(B*H)^m := by
        rw [mul_pow, show m = (n-1)+n by dsimp [m]; omega, pow_add, pow_add]
        ring

end OMA.A363309Proof

open OMA.A363309Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a363309.main :=
  fun n hn => ⟨exists_series n, integer_root n hn⟩
