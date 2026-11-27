import FormalConjecturesForMathlib.Combinatorics.Additive.Convolution
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Data.Finset.MulAntidiagonal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Six ordered representations in an asymptotic basis of order two

Anmol Sahu and OpenAI Codex formalized the cofinite case of Ioannis
Konstantoulas’s 2013 theorem on sets whose missing sums have upper density below
1/10. Huixi Li and Zihan Zhang improved that density threshold to 7/32 and
identified the role of the sparse odd representation counts. This proof adapts
Csaba Sándor’s spectral method using finite generating polynomials and Parseval’s
identity. The theorem counts ordered pairs and allows all nonnegative integers.

* Ioannis Konstantoulas, *Lower bounds for a conjecture of Erdős and Turán*,
  Acta Arith. 159 (2013), 301–313, https://doi.org/10.4064/aa159-4-1.
* Huixi Li and Zihan Zhang, *An improvement of Konstantoulas’ density constant*,
  Acta Arith. 225 (2026), 187–197, https://doi.org/10.4064/aa260528-23-7.
* Csaba Sándor, *A note on a conjecture of Erdős–Turán*, Integers 8 (2008), A30,
  https://math.bme.hu/~csandor/Publications/ErdosTuran.pdf.
-/

open scoped Classical
open scoped Classical

namespace OMA.Erdos28Six

open AdditiveCombinatorics

/-- Away from diagonal sums, swapping the components pairs all ordered representations. -/
theorem even_away_from_diagonal (A : Set ℕ) (n : ℕ)
    (off : ¬∃ a∈A, a+a=n) : Even (sumRep A n) := by
  classical
  let P := (Finset.HasAntidiagonal.antidiagonal n).filter (fun p : ℕ × ℕ => p.1∈A ∧ p.2∈A)
  let L := P.filter (fun p => p.1<p.2)
  let R := P.filter (fun p => ¬p.1<p.2)
  have swap_mem (x y : ℕ) (h : (x,y)∈P) : (y,x)∈P := by
    obtain ⟨hxy,hx,hy⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by
      simpa [Nat.add_comm] using Finset.HasAntidiagonal.mem_antidiagonal.mp hxy),hy,hx⟩
  have distinct (x y : ℕ) (h : (x,y)∈P) : x ≠ y := by
    rintro rfl
    obtain ⟨hn,hx,_⟩ := Finset.mem_filter.mp h
    exact off ⟨x,hx,Finset.HasAntidiagonal.mem_antidiagonal.mp hn⟩
  have equal : L.card=R.card := by
    refine Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨x,y⟩ hp
      obtain ⟨hm,ho⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨swap_mem x y hm, (Nat.le_of_lt ho).not_gt⟩
    · rintro ⟨x,y⟩ hp
      obtain ⟨hm,ho⟩ := Finset.mem_filter.mp hp
      have ne := distinct x y hm
      change ¬x<y at ho
      exact Finset.mem_filter.mpr ⟨swap_mem x y hm, by change y<x; omega⟩
    · rintro ⟨x,y⟩ _; rfl
    · rintro ⟨x,y⟩ _; rfl
  have split : L.card+R.card=P.card := Finset.card_filter_add_card_filter_not (s := P) (fun p => p.1<p.2)
  rw [sumRep_def]
  change Even P.card
  exact ⟨L.card,by omega⟩

/-- In the range one through five, the squared deviation from three costs at most
half a representation except at a diagonal sum. The extra cost there is at most four. -/
theorem deviation (A : Set ℕ) (n : ℕ) (pos : 0 < sumRep A n)
    (cap : sumRep A n ≤ 5) :
    ((sumRep A n : ℝ)-3)^2 ≤ (sumRep A n : ℝ)/2+
      4*(if ∃ a∈A, a+a=n then (1:ℝ) else 0) := by
  classical
  set k := sumRep A n
  change 0<k at pos
  change k≤5 at cap
  by_cases diag : ∃ a∈A, a+a=n
  · rw [if_pos diag]
    interval_cases k <;> norm_num
  · rw [if_neg diag]
    obtain ⟨t,ht⟩ := even_away_from_diagonal A n diag
    change k=t+t at ht
    have small : k=2 ∨ k=4 := by omega
    rcases small with h|h <;> rw [h] <;> norm_num

end OMA.Erdos28Six

namespace OMA.Erdos28Six

open Polynomial

/-- Young's inequality twice converts the circle estimate into three polynomial energies. -/
theorem pointwise_energy (X g h d b C : ℝ) (hX : 0≤X) (_hg : 0≤g)
    (hh : 0≤h) (h1 : h≤1) (hd : 0≤d) (tri : g≤d+b) (base : (1-h)*b≤C) :
    X*g ≤ g^2/100+25*X^2*h+3*d^2/4+X^2/3+C*X := by
  have hu : X*g*h ≤ g^2/100+25*X^2*h := by
    nlinarith [sq_nonneg (g-50*X*h), mul_nonneg (sq_nonneg X) (mul_nonneg hh (sub_nonneg.mpr h1))]
  have hv : X*d ≤ 3*d^2/4+X^2/3 := by nlinarith [sq_nonneg (3*d-2*X)]
  have htri := mul_le_mul_of_nonneg_left tri (sub_nonneg.mpr h1)
  have hm : (1-h)*g ≤ d+C := by nlinarith [mul_nonneg hd hh]
  have hm2 := mul_le_mul_of_nonneg_left hm hX
  linarith only [show X*g = X*g*h + X*((1-h)*g) by ring, hu, hv, hm2, mul_comm C X]


noncomputable def energy (P : ℂ[X]) : ℝ :=
  ∑ i ∈ P.support, ‖P.coeff i‖^2

/-- A polynomial that is small near 1 removes the geometric baseline B. The result
compares only finite coefficient energies; all appearances of the circle disappear. -/
theorem spectral_estimate (G H B : ℂ[X]) (X C : ℝ) (hX : 0≤X)
    (bound : ∀ z : ℂ, ‖z‖=1 → ‖H.eval z‖≤1)
    (base : ∀ z : ℂ, ‖z‖=1 → (1-‖H.eval z‖^2)*‖B.eval z‖≤C) :
    X*energy G ≤ (1/100)*energy (G^2)+(25*X^2)*energy H+
      (3/4)*energy (G^2-B)+(X^2/3+C*X) := by
  let q (P : ℂ[X]) (z : ℂ) := ‖P.eval z‖^2
  let avg (f : ℂ → ℝ) := Real.circleAverage f 0 1
  have qcon (P : ℂ[X]) : Continuous (q P) := P.continuous.norm.pow 2
  have qm (P : ℂ[X]) : avg (q P) = energy P := P.sum_sq_norm_coeff_eq_circleAverage.symm
  have ci (f : ℂ→ℝ) (hf : Continuous f) : CircleIntegrable f 0 1 :=
    ContinuousOn.circleIntegrable' hf.continuousOn
  have add (f g : ℂ→ℝ) (hf : Continuous f) (hg : Continuous g) :
      avg (fun z => f z+g z)=avg f+avg g :=
    Real.circleAverage_fun_add (ci _ hf) (ci _ hg)
  have mul (a : ℝ) (f : ℂ→ℝ) : avg (fun z => a*f z)=a*avg f :=
    by simpa only [avg,smul_eq_mul] using
      (Real.circleAverage_fun_smul (a:=a) (f:=f) (c:=(0:ℂ)) (R:=(1:ℝ)))
  have const (a : ℝ) : avg (fun _ => a)=a := Real.circleAverage_const a 0 1
  let u := fun z => (1/100:ℝ)*q (G^2) z
  let v := fun z => (25*X^2)*q H z
  let w := fun z => (3/4:ℝ)*q (G^2-B) z
  let k := fun (_:ℂ) => X^2/3+C*X
  have cu : Continuous u := continuous_const.mul (qcon _)
  have cv : Continuous v := continuous_const.mul (qcon _)
  have cw : Continuous w := continuous_const.mul (qcon _)
  have ck : Continuous k := continuous_const
  have hp : avg (fun z => X*q G z) ≤ avg (fun z => u z+v z+w z+k z) := by
    apply Real.circleAverage_mono (ci _ (continuous_const.mul (qcon _)))
      (ci _ (((cu.add cv).add cw).add ck))
    intro z hz
    have hz' : ‖z‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hz
    have hH := bound z hz'
    have tri : q G z ≤ ‖(G^2-B).eval z‖+‖B.eval z‖ := by
      have h := norm_add_le ((G.eval z)^2-B.eval z) (B.eval z)
      rw [sub_add_cancel] at h
      simpa only [q,Polynomial.eval_sub,Polynomial.eval_pow,norm_pow] using h
    have pt := pointwise_energy X (q G z) (q H z) ‖(G^2-B).eval z‖ ‖B.eval z‖ C
      hX (sq_nonneg _) (sq_nonneg _) (by dsimp [q]; nlinarith [norm_nonneg (H.eval z)])
      (norm_nonneg _) tri (base z hz')
    change X*q G z ≤ u z+v z+w z+k z
    simp only [u,v,w,k,q,Polynomial.eval_pow,norm_pow] at pt ⊢
    linarith only [pt]
  rw [mul, add (fun z => u z+v z+w z) k ((cu.add cv).add cw) ck,
    add (fun z => u z+v z) w (cu.add cv) cw, add u v cu cv] at hp
  dsimp only [u,v,w,k] at hp
  rwa [mul,mul,mul,const,qm,qm,qm,qm] at hp

end OMA.Erdos28Six

namespace OMA.Erdos28Six

open Finset Polynomial

/-- The unnormalized finite geometric sum. -/
noncomputable def geom (z : ℂ) (k : ℕ) := ∑ j ∈ range k,z^j

theorem norm_geom_le (z : ℂ) (k : ℕ) (hz : ‖z‖≤1) : ‖geom z k‖≤k := by
  calc
    ‖geom z k‖ ≤ ∑ j ∈ range k,‖z^j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range k,(1:ℝ) := sum_le_sum fun j _ => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hz
    _ = k := by simp

theorem norm_one_sub_pow (z : ℂ) (k : ℕ) (hz : ‖z‖≤1) :
    ‖1-z^k‖≤k*‖1-z‖ := by
  rw [← geom_sum_mul_neg z k,norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_geom_le z k hz) (norm_nonneg _)

/-- The normalized average of the first m circle characters. -/
noncomputable def kernel (m : ℕ) (z : ℂ) := (m:ℂ)⁻¹*geom z m

theorem norm_kernel_le (m : ℕ) (hm : 0<m) (z : ℂ) (hz : ‖z‖≤1) :
    ‖kernel m z‖≤1 := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  simp only [kernel,norm_mul,norm_inv,Complex.norm_natCast]
  rw [← div_eq_inv_mul]
  exact (div_le_one hm').mpr (norm_geom_le z m hz)

theorem kernel_vanish (m : ℕ) (hm : 0<m) (z : ℂ) (hz : ‖z‖≤1) :
    1-‖kernel m z‖^2 ≤ (2*m)*‖1-z‖ := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have hn : ((m:ℂ)⁻¹)*(∑ _j∈range m,(1:ℂ)) = 1 := by
    simp [Nat.ne_of_gt hm]
  have eq : 1-kernel m z = (m:ℂ)⁻¹*∑ j∈range m, (1-z^j) := by
    rw [sum_sub_distrib,mul_sub,hn]
    rfl
  have sumLim : ‖∑ j∈range m, (1-z^j)‖ ≤ m*((m:ℝ)*‖1-z‖) := by
    calc
      _ ≤ ∑ j∈range m, ‖1-z^j‖ := norm_sum_le _ _
      _ ≤ ∑ _j∈range m, (m:ℝ)*‖1-z‖ := by
        apply sum_le_sum
        intro j hj
        exact (norm_one_sub_pow z j hz).trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Nat.le_of_lt (mem_range.mp hj))) (norm_nonneg _))
      _ = _ := by simp [nsmul_eq_mul]
  have close : ‖1-kernel m z‖≤m*‖1-z‖ := by
    rw [eq,norm_mul,norm_inv,Complex.norm_natCast,← div_eq_inv_mul]
    apply (div_le_iff₀ hm').mpr
    simpa [mul_comm] using sumLim
  have low : 1-‖kernel m z‖≤‖1-kernel m z‖ := by
    simpa using norm_sub_norm_le (1:ℂ) (kernel m z)
  have ker := norm_kernel_le m hm z hz
  nlinarith [sq_nonneg (1-‖kernel m z‖)]

theorem kernel_geometric_bound (m : ℕ) (hm : 0<m) (z : ℂ) (hz : ‖z‖=1)
    (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (k : ℕ) :
    (1-‖kernel m z‖^2)*‖(3:ℂ)*geom ((r:ℂ)*z) k‖ ≤ 24*m := by
  let t := (r:ℂ)*z
  have ht : ‖t‖=r := by simp [t,hz,Real.norm_eq_abs,abs_of_nonneg hr]
  have dist : ‖z-t‖=1-r := by
    have h : z-t=((1-r:ℝ):ℂ)*z := by dsimp [t]; push_cast; ring
    rw [h,norm_mul,hz,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  have lower : 1-r≤‖1-t‖ := by simpa [ht] using norm_sub_norm_le (1:ℂ) t
  have detour : ‖1-z‖≤2*‖1-t‖ := by
    have ht1 : ‖1-z‖ ≤ ‖1-t‖+‖t-z‖ := by
      calc
        ‖1-z‖ = ‖(1-t)+(t-z)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev t z,dist] at ht1
    linarith
  have van : 1-‖kernel m z‖^2 ≤ (4*m)*‖1-t‖ := by
    have a := kernel_vanish m hm z hz.le
    have b := mul_le_mul_of_nonneg_left detour (by positivity : (0:ℝ)≤2*m)
    linarith
  have prod : ‖1-t‖*‖geom t k‖≤2 := by
    rw [mul_comm,← norm_mul]
    change ‖(∑ j∈range k,t^j)*(1-t)‖≤2
    rw [geom_sum_mul_neg]
    have : ‖t^k‖≤1 := by rw [norm_pow,ht]; exact pow_le_one₀ hr hr1
    have h := norm_sub_le (1:ℂ) (t^k)
    rw [norm_one] at h
    linarith
  change (1-‖kernel m z‖^2)*‖(3:ℂ)*geom t k‖≤24*m
  rw [norm_mul,show ‖(3:ℂ)‖=(3:ℝ) by norm_num]
  have a := mul_le_mul_of_nonneg_right van (norm_nonneg (geom t k))
  have b := mul_le_mul_of_nonneg_left prod (by positivity : (0:ℝ)≤4*m)
  nlinarith only [a,b]

end OMA.Erdos28Six

namespace OMA.Erdos28Six

open Finset Polynomial AdditiveCombinatorics

/-- Generating polynomial of a finite set of exponents after dilation. -/
noncomputable def gen (T : Finset ℕ) (r : ℝ) : ℂ[X] :=
  ∑ a∈T, monomial a ((r:ℂ)^a)

theorem coeff_gen (T : Finset ℕ) (r : ℝ) (n : ℕ) :
    (gen T r).coeff n = if n∈T then (r:ℂ)^n else 0 := by
  classical
  simp [gen,finsetSum_coeff,coeff_monomial]

theorem eval_gen (T : Finset ℕ) (r : ℝ) (z : ℂ) :
    (gen T r).eval z=∑ a∈T,((r:ℂ)*z)^a := by
  classical
  simp [gen,eval_finsetSum,eval_monomial,mul_pow]

theorem sumRep_fiber (T : Finset ℕ) (n : ℕ) :
    sumRep (T : Set ℕ) n = ((T ×ˢ T).filter (fun p => p.1+p.2=n)).card := by
  classical
  rw [sumRep_def]
  congr 1
  ext p
  simp [and_comm]

theorem coeff_gen_sq (T : Finset ℕ) (r : ℝ) (n : ℕ) :
    ((gen T r)^2).coeff n = (sumRep (T : Set ℕ) n:ℂ)*(r:ℂ)^n := by
  classical
  let P := (Finset.HasAntidiagonal.antidiagonal n).filter (fun p : ℕ × ℕ => p.1∈T ∧ p.2∈T)
  have countP : sumRep (T:Set ℕ) n=P.card := by
    rw [sumRep_fiber]
    congr 1
    ext p
    simp [P,and_comm]
  rw [sq,coeff_mul,countP]
  calc
    _ = ∑ p∈Finset.HasAntidiagonal.antidiagonal n, if p.1∈T ∧ p.2∈T then (r:ℂ)^n else 0 := by
      apply sum_congr rfl
      intro p hp
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases ha : p.1∈T <;> by_cases hb : p.2∈T <;>
        simp [coeff_gen,ha,hb,←pow_add,he]
    _ = ∑ _p∈P,(r:ℂ)^n := by simp only [P,sum_filter]
    _ = _ := by simp [nsmul_eq_mul]

theorem mass_sq (T : Finset ℕ) (D : ℕ) (sub : T⊆Finset.Iic D) (t : ℝ) :
    ∑ n∈range (2*D+1), (sumRep (T : Set ℕ) n:ℝ)*t^n = (∑ a∈T,t^a)^2 := by
  classical
  let E := T×ˢT
  let f := fun p : ℕ × ℕ => p.1+p.2
  have rng : ∀p∈E,f p∈range (2*D+1) := by
    intro p hp
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    have ha' := mem_Iic.mp (sub ha)
    have hb' := mem_Iic.mp (sub hb)
    apply mem_range.mpr
    change p.1+p.2<2*D+1
    omega
  calc
    _ = ∑ n∈range (2*D+1), ∑ p∈E with f p=n, t^(f p) := by
      apply sum_congr rfl
      intro n hn
      rw [sumRep_fiber]
      calc
        _ = ∑ _p∈E.filter (fun p=>f p=n),t^n := by simp [E,f,nsmul_eq_mul]
        _ = _ := sum_congr rfl fun p hp => by rw [(mem_filter.mp hp).2]
    _ = ∑ p∈E,t^(f p) := sum_fiberwise_of_maps_to rng _
    _ = _ := by simp [E,f,sum_product,pow_add,sq,sum_mul,mul_sum,mul_comm]

theorem energy_over (P : ℂ[X]) (S : Finset ℕ) (hs : ∀i∉S,P.coeff i=0) :
    energy P = ∑ i∈S, ‖P.coeff i‖^2 := by
  unfold energy
  have sub : P.support ⊆ S := by
    intro i hi
    by_contra h
    exact (mem_support_iff.mp hi) (hs i h)
  exact sum_subset sub fun i _ hi => by simp [notMem_support_iff.mp hi]

theorem energy_gen (T : Finset ℕ) (r : ℝ) (hr : 0≤r) :
    energy (gen T r) = ∑ a∈T,(r^2)^a := by
  rw [energy_over _ T (by intro i hi; simp [coeff_gen,hi])]
  apply sum_congr rfl
  intro a ha
  simp [coeff_gen,ha,norm_pow,Real.norm_eq_abs,abs_of_nonneg hr,← pow_mul,Nat.mul_comm]


theorem energy_const_mul (c : ℂ) (P : ℂ[X]) :
    energy (C c * P) = ‖c‖^2 * energy P := by
  rw [energy_over _ P.support (by intro i hi; simp [coeff_C_mul,notMem_support_iff.mp hi])]
  simp [energy,coeff_C_mul,mul_pow,mul_sum]

noncomputable def baseline (D : ℕ) (r : ℝ) : ℂ[X] := C 3 * gen (range (2*D+1)) r

/-- The only analytic step of the six-representation argument, with all Fourier terms
expressed as finite sums of squares of coefficients. -/
theorem finite_spectral (T : Finset ℕ) (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (D : ℕ) :
    let G := gen T r
    let B := baseline D r
    let X := ∑ a∈T,(r^2)^a
    X^2 ≤ energy (G^2)/100+(1/40)*X^2+3*energy (G^2-B)/4+X^2/3+24000*X := by
  dsimp only
  let m : ℕ := 1000
  let H : ℂ[X] := C ((m:ℂ)⁻¹)*gen (range m) 1
  have hm : 0<m := by decide
  have hval (z : ℂ) : H.eval z= kernel m z := by
    simp [H,kernel,geom,eval_gen]
  have hE : energy H = 1/1000 := by
    rw [energy_const_mul,energy_gen _ 1 (by norm_num)]
    norm_num [m]
  have hB (z : ℂ) : (baseline D r).eval z=3*geom ((r:ℂ)*z) (2*D+1) := by
    simp [baseline,eval_gen,geom]
  have hnon : 0 ≤ ∑ a∈T,(r^2)^a := sum_nonneg fun a _ => pow_nonneg (sq_nonneg r) a
  have h := spectral_estimate (gen T r) H (baseline D r) _ 24000 hnon
    (fun z hz => by rw [hval]; exact norm_kernel_le m hm z hz.le)
    (fun z hz => by
      rw [hval,hB]
      exact (kernel_geometric_bound m hm z hz r hr hr1 (2*D+1)).trans_eq (by norm_num [m]))
  rw [energy_gen _ _ hr,hE] at h
  linarith only [h]

end OMA.Erdos28Six

namespace OMA.Erdos28Six

open Finset
open scoped Classical

/-- A finite initial part of an infinite set can have arbitrarily large geometric
mass while its right endpoint makes the remaining geometric series negligible. -/
theorem large_mass (A : Set ℕ) (inf : A.Infinite) (Y K : ℕ) :
    ∃ (r : ℝ) (D : ℕ), 0<r ∧ r<1 ∧ K≤D ∧
      (r^2)^D≤1-r^2 ∧
      (Y:ℝ)<∑ a∈(Iic D).filter (·∈A), (r^2)^a := by
  classical
  obtain ⟨S,hSA,card⟩ := inf.exists_subset_card_eq (2*Y+1)
  let V := S.sup id
  let u : ℝ := 4*(V:ℝ)+4
  have hu : 1<u := by dsimp [u]; linarith [Nat.cast_nonneg (α:=ℝ) V]
  let r := 1-1/u
  have hr : 0<r := by
    dsimp [r]
    have := (div_lt_one (by linarith : 0<u)).mpr hu
    linarith
  have hr1 : r<1 := by dsimp [r]; have := one_div_pos.mpr (by linarith : 0<u); linarith
  have wpos : 0<r^2 := sq_pos_of_pos hr
  have wlt : r^2<1 := by nlinarith [mul_pos hr (sub_pos.mpr hr1)]
  obtain ⟨d,hd⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr wlt) wlt
  let D := max d (max K V)
  have dD : d≤D := le_max_left _ _
  have kD : K≤D := (le_max_left _ _).trans (le_max_right _ _)
  have vD : V≤D := (le_max_right _ _).trans (le_max_right _ _)
  have tail : (r^2)^D≤1-r^2 := (pow_le_pow_of_le_one wpos.le wlt.le dD).trans hd.le
  have inD : S⊆(Iic D).filter (·∈A) := by
    intro a ha
    exact mem_filter.mpr ⟨mem_Iic.mpr ((show a≤V from le_sup (f:=id) ha).trans vD),hSA ha⟩
  have half (a : ℕ) (ha : a∈S) : (1/2:ℝ)≤(r^2)^a := by
    have hav : (a:ℝ)≤V := by exact_mod_cast (show a≤V from le_sup (f:=id) ha)
    have rat : (2*a:ℝ)/u ≤ 1/2 := by
      apply (div_le_iff₀ (by linarith : 0<u)).mpr
      dsimp [u]
      linarith
    have hb := one_add_mul_sub_le_pow (by linarith : (-1:ℝ)≤r) (2*a)
    have he : r-1= -(1/u) := by dsimp [r]; ring
    rw [he] at hb
    norm_num at hb
    rw [← pow_mul]
    rw [div_eq_mul_inv] at rat
    linarith
  have sumS := sum_le_sum half
  have full := sum_le_sum_of_subset_of_nonneg inD (fun i _ _ => pow_nonneg wpos.le i)
  have lb : (Y:ℝ)<∑ _a∈S,(1/2:ℝ) := by
    simp only [sum_const,nsmul_eq_mul,card]
    push_cast
    linarith
  exact ⟨r,D,hr,hr1,kD,tail,lb.trans_le (sumS.trans full)⟩

end OMA.Erdos28Six

namespace OMA.Erdos28Six

open Finset AdditiveCombinatorics Polynomial

theorem rep_limit (A : Set ℕ) (n : ℕ) : sumRep A n≤n+1 := by
  classical
  rw [sumRep_def]
  simpa using (card_filter_le (Finset.HasAntidiagonal.antidiagonal n) (fun p : ℕ × ℕ => p.1∈A ∧ p.2∈A))

theorem rep_subset {A B : Set ℕ} (h : A⊆B) (n : ℕ) : sumRep A n≤sumRep B n := by
  classical
  rw [sumRep_def,sumRep_def]
  apply card_le_card
  intro p hp
  obtain ⟨hn,ha,hb⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hn,h ha,h hb⟩

theorem rep_initial (A : Set ℕ) (D n : ℕ) (hn : n≤D) :
    sumRep (↑((Iic D).filter (·∈A)) : Set ℕ) n=sumRep A n := by
  classical
  rw [sumRep_fiber,sumRep_def]
  congr 1
  ext p
  simp only [mem_filter,mem_product,mem_Iic,Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨⟨⟨_,ha⟩,⟨_,hb⟩⟩,he⟩
    exact ⟨he,ha,hb⟩
  · rintro ⟨he,ha,hb⟩
    exact ⟨⟨⟨by omega,ha⟩,⟨by omega,hb⟩⟩,he⟩

theorem rep_outside (T : Finset ℕ) (D n : ℕ) (hT : T⊆Iic D) (hn : 2*D<n) :
    sumRep (T:Set ℕ) n=0 := by
  rw [sumRep_fiber]
  rw [card_eq_zero,eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨hm,he⟩ := mem_filter.mp hp
  obtain ⟨ha,hb⟩ := mem_product.mp hm
  have h1 := mem_Iic.mp (hT ha)
  have h2 := mem_Iic.mp (hT hb)
  omega

theorem norm_real_power_coeff (c r : ℝ) (n : ℕ) :
    ‖(c:ℂ)*(r:ℂ)^n‖^2 = c^2*(r^2)^n := by
  rw [norm_mul,norm_pow,mul_pow,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    sq_abs, ←pow_mul, Nat.mul_comm, pow_mul, sq_abs]

theorem energy_forms (T : Finset ℕ) (D : ℕ) (sub : T⊆Iic D) (r : ℝ) :
    energy ((gen T r)^2) = ∑ n∈range (2*D+1), (sumRep (T:Set ℕ) n:ℝ)^2*(r^2)^n ∧
    energy ((gen T r)^2-baseline D r) =
      ∑ n∈range (2*D+1), ((sumRep (T:Set ℕ) n:ℝ)-3)^2*(r^2)^n := by
  let G := gen T r
  have out (n : ℕ) (hn : n∉range (2*D+1)) : (G^2).coeff n=0 := by
    rw [coeff_gen_sq,rep_outside T D n sub (by simpa [not_lt] using hn)]
    simp
  have bcoeff (n : ℕ) : (baseline D r).coeff n =
      3*(if n∈range (2*D+1) then (r:ℂ)^n else 0) := by
    simp [baseline,coeff_C_mul,coeff_gen]
  constructor
  · rw [energy_over _ _ out]
    apply sum_congr rfl
    intro n hn
    rw [coeff_gen_sq]
    simpa using norm_real_power_coeff (sumRep (T:Set ℕ) n) r n
  · rw [energy_over _ (range (2*D+1)) (by
        intro i hi
        rw [coeff_sub,out i hi,bcoeff,if_neg hi]
        ring)]
    apply sum_congr rfl
    intro n hn
    rw [coeff_sub,coeff_gen_sq,bcoeff,if_pos hn,←sub_mul]
    simpa using norm_real_power_coeff ((sumRep (T:Set ℕ) n:ℝ)-3) r n

/-- Each diagonal exception contributes r^(4a), at most its share r^(2a) of X. -/
theorem diag_mass (T : Finset ℕ) (L : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    ∑ n∈range L, (if ∃a∈T,a+a=n then t^n else 0) ≤ ∑ a∈T,t^a := by
  classical
  let Z := T.image (fun a => a+a)
  have memZ (n : ℕ) : (∃ a∈T, a+a=n) ↔ n∈Z := mem_image.symm
  simp only [memZ,←sum_filter]
  have sub : (range L).filter (·∈Z) ⊆ Z := fun _ h => (mem_filter.mp h).2
  calc
    _ ≤ ∑ n∈Z,t^n := sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => pow_nonneg ht n)
    _ = ∑ a∈T, t^(a+a) := sum_image (fun x _ y _ h => by omega)
    _ ≤ _ := sum_le_sum fun a _ => pow_le_pow_of_le_one ht ht1 (by omega)

theorem small_prefix_mass (K L : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    ∑ n∈range L, (if n<K then t^n else 0) ≤ K := by
  rw [←sum_filter]
  have sub : (range L).filter (·<K)⊆range K := fun _ h=>mem_range.mpr (mem_filter.mp h).2
  calc
    _ ≤ ∑ n∈range K,t^n := sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => pow_nonneg ht n)
    _ ≤ ∑ _n∈range K,(1:ℝ) := sum_le_sum fun _ _ => pow_le_one₀ ht ht1
    _ = _ := by simp

end OMA.Erdos28Six

namespace OMA.Erdos28Six

open Finset AdditiveCombinatorics

theorem late_mass (D : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t<1) (tail : t^D≤1-t) :
    ∑ n∈range (2*D+1), (if D<n then t^n else 0) ≤1 := by
  rw [←sum_filter]
  have sub : (range (2*D+1)).filter (D<·) ⊆ Ico D (2*D+1) := by
    intro n hn
    obtain ⟨hL,hD⟩ := mem_filter.mp hn
    exact mem_Ico.mpr ⟨hD.le,mem_range.mp hL⟩
  apply (sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => pow_nonneg ht n)).trans
  have hgeom := geom_sum_Ico_mul_neg t (m:=D) (n:=2*D+1) (by omega)
  apply (le_of_mul_le_mul_right · (by linarith : 0<1-t))
  simpa only [one_mul] using (hgeom.le.trans (by linarith [pow_nonneg ht (2*D+1)]))

/-- Under an ordered cap of five, the squared error has diagonal, prefix, and
truncation corrections with respective total weights at most X, K, and one. -/
theorem error_bounds (T : Finset ℕ) (D K : ℕ) (sub : T⊆Iic D)
    (cap : ∀ n, K≤n → sumRep (T:Set ℕ) n≤5)
    (cover : ∀ n, K≤n → n≤D → 0<sumRep (T:Set ℕ) n)
    (t : ℝ) (ht : 0≤t) (ht1 : t<1) (tail : t^D≤1-t) :
    let X := ∑ a∈T,t^a
    let L := range (2*D+1)
    (∑ n∈L, (sumRep (T:Set ℕ) n:ℝ)^2*t^n) ≤ 5*X^2+((K:ℝ)+3)^2*K ∧
    (∑ n∈L, ((sumRep (T:Set ℕ) n:ℝ)-3)^2*t^n) ≤ X^2/2+4*X+((K:ℝ)+3)^2*K+9 := by
  classical
  let v (n : ℕ) := (sumRep (T:Set ℕ) n:ℝ)
  let M := ((K:ℝ)+3)^2
  let L := range (2*D+1)
  let f (n : ℕ) := if n<K then t^n else 0
  let g (n : ℕ) := if D<n then t^n else 0
  let h (n : ℕ) := if ∃a∈T, a+a=n then t^n else 0
  let X := ∑ a∈T,t^a
  have vpos (n : ℕ) : 0≤v n := Nat.cast_nonneg _
  have wt (n : ℕ) : 0≤t^n := pow_nonneg ht n
  have mass : (∑ n∈L, v n*t^n)=X^2 := mass_sq T D sub t
  have pref : (∑ n∈L,f n)≤K := small_prefix_mass K _ t ht ht1.le
  have ztail : (∑ n∈L,g n)≤1 := late_mass D t ht ht1 tail
  have diag : (∑ n∈L,h n)≤X := diag_mass T _ t ht ht1.le
  have Mp : M*(∑ n∈L,f n) ≤ M*K := mul_le_mul_of_nonneg_left pref (sq_nonneg ((K:ℝ)+3))
  have prv (n : ℕ) (hn : n<K) : v n≤K := by
    dsimp only [v]
    exact_mod_cast (show sumRep (T:Set ℕ) n≤K from (rep_limit _ _).trans (by omega))
  have last (n : ℕ) (hn : K≤n) : v n≤5 := by
    dsimp only [v]
    exact_mod_cast cap n hn
  have bound4 (n : ℕ) : (v n)^2*t^n ≤5*(v n*t^n)+M*f n := by
    by_cases p : n<K
    · have hk := prv n p
      have raw : (v n)^2≤5*v n+M := by
        dsimp [M]
        nlinarith [vpos n,mul_nonneg (by linarith : 0≤(K:ℝ)+3-v n)
          (by nlinarith [vpos n] : 0≤(K:ℝ)+3+v n)]
      have m := mul_le_mul_of_nonneg_right raw (wt n)
      simp only [f,if_pos p]
      linarith
    · have hk := last n (by omega)
      have raw : (v n)^2≤5*v n := by nlinarith [mul_nonneg (by linarith : 0≤5-v n) (vpos n)]
      have m := mul_le_mul_of_nonneg_right raw (wt n)
      simp [f,p]
      linarith
  have boundE (n : ℕ) :
      (v n-3)^2*t^n ≤ (1/2)*(v n*t^n)+4*h n+M*f n+9*g n := by
    have hh : 0≤h n := by dsimp [h]; split <;> positivity
    have hf : 0≤f n := by dsimp [f]; split <;> positivity
    have hg : 0≤g n := by dsimp [g]; split <;> positivity
    by_cases p : n<K
    · have hk := prv n p
      have raw : (v n-3)^2≤M := by
        dsimp [M]
        nlinarith [mul_nonneg (by linarith : 0≤(K:ℝ)+3-(v n-3))
          (by nlinarith [vpos n] : 0≤(K:ℝ)+3+(v n-3))]
      have m := mul_le_mul_of_nonneg_right raw (wt n)
      simp only [f,if_pos p]
      nlinarith [mul_nonneg (vpos n) (wt n)]
    · have hn : K≤n := by omega
      by_cases q : D<n
      · have hk := last n hn
        have raw : (v n-3)^2≤9 := by nlinarith [mul_nonneg (by linarith : 0≤6-v n) (vpos n)]
        have m := mul_le_mul_of_nonneg_right raw (wt n)
        simp only [f,g,p,q,if_false,if_true,mul_zero,add_zero]
        nlinarith [mul_nonneg (vpos n) (wt n)]
      · have raw := deviation (T:Set ℕ) n (cover n hn (by omega)) (cap n hn)
        have m := mul_le_mul_of_nonneg_right raw (wt n)
        by_cases w : ∃ a∈T, a+a=n
        · have ws : ∃ a∈(T:Set ℕ),a+a=n := w
          rw [if_pos ws] at m
          change (v n-3)^2*t^n≤(v n/2+4*1)*t^n at m
          simp only [h,f,g,if_pos w,if_neg p,if_neg q,mul_zero,add_zero]
          linarith
        · have ws : ¬∃ a∈(T:Set ℕ),a+a=n := w
          rw [if_neg ws] at m
          change (v n-3)^2*t^n≤(v n/2+4*0)*t^n at m
          simp only [h,f,g,if_neg w,if_neg p,if_neg q,mul_zero,add_zero]
          linarith
  dsimp only
  constructor
  · change (∑ n∈L,(v n)^2*t^n) ≤5*X^2+M*K
    have a := sum_le_sum (fun n (_:n∈L) => bound4 n)
    rw [sum_add_distrib,←mul_sum,←mul_sum,mass] at a
    linarith only [a,Mp]
  · change (∑ n∈L,(v n-3)^2*t^n) ≤ X^2/2+4*X+M*K+9
    have a := sum_le_sum (fun n (_:n∈L) => boundE n)
    simp only [sum_add_distrib,←mul_sum,mass] at a
    linarith only [a,Mp,diag,ztail]

end OMA.Erdos28Six

namespace OMA.Erdos28Six

open Finset AdditiveCombinatorics
open scoped Classical Pointwise

/-- Every asymptotic basis of order two has arbitrarily large integers with
at least six ordered representations as a sum of two members. -/
theorem six_frequently (A : Set ℕ) (cof : (A+A)ᶜ.Finite) (K₀ : ℕ) :
    ∃ n≥K₀, 6≤sumRep A n := by
  classical
  by_contra! bad
  let F := cof.toFinset
  let K := K₀+F.sup id+1
  have old (n : ℕ) (h : K≤n) : K₀≤n := by dsimp [K] at h; omega
  have cap (n : ℕ) (h : K≤n) : sumRep A n≤5 := by have := bad n (old n h); omega
  have cov (n : ℕ) (h : K≤n) : 0<sumRep A n := by
    have good : n∈A+A := by
      by_contra missing
      have fail : n∈F := cof.mem_toFinset.mpr missing
      have hm : n≤F.sup id := le_sup (f:=id) fail
      dsimp [K] at h
      omega
    obtain ⟨a,ha,b,hb,he⟩ := good
    rw [sumRep_def]
    exact card_pos.mpr ⟨(a,b),mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr he,ha,hb⟩⟩
  have inf : A.Infinite := by
    intro fA
    exact (Set.infinite_of_finite_compl cof) (fA.add fA)
  let C := (K+3)^2*K
  obtain ⟨r,D,hr,hr1,hKD,tail,hX⟩ := large_mass A inf (300000+C) K
  let T := (Iic D).filter (·∈A)
  have sub : T⊆Iic D := filter_subset _ _
  have sa : (T:Set ℕ)⊆A := fun n hn => (mem_filter.mp hn).2
  have cT (n : ℕ) (hn : K≤n) : sumRep (T:Set ℕ) n≤5 := (rep_subset sa n).trans (cap n hn)
  have pT (n : ℕ) (hn : K≤n) (hnD : n≤D) : 0<sumRep (T:Set ℕ) n := by
    rw [rep_initial A D n hnD]
    exact cov n hn
  have hq : r^2<1 := by nlinarith [mul_pos hr (sub_pos.mpr hr1)]
  let X := ∑ a∈T,(r^2)^a
  let U := energy ((gen T r)^2)
  let V := energy ((gen T r)^2-baseline D r)
  have effects := error_bounds T D K sub cT pT (r^2) (sq_nonneg r) hq tail
  obtain ⟨u,v⟩ := energy_forms T D sub r
  dsimp only at effects
  rw [←u,←v] at effects
  have cR : (C:ℝ)=((K:ℝ)+3)^2*K := by simp [C]
  have bounds : U≤5*X^2+C ∧ V≤X^2/2+4*X+C+9 := by simpa only [U,V,X,cR] using effects
  have wave := finite_spectral T r hr.le hr1.le D
  change X^2≤U/100+(1/40)*X^2+3*V/4+X^2/3+24000*X at wave
  change ((300000+C:ℕ):ℝ)<X at hX
  push_cast at hX
  have nonneg : 0≤(C:ℝ) := by positivity
  have large : 300000≤X := by linarith
  nlinarith only [wave,bounds.1,bounds.2,hX,nonneg,
    mul_nonneg (show 0≤X by linarith) (sub_nonneg.mpr large)]

end OMA.Erdos28Six

/-!
# Lower density of the six-fold sums under any eventual cap

Extending the finite six-representation argument, Anmol Sahu and OpenAI Codex
keep the contribution of all higher representation counts in the estimated
fourth moment and variance. The resulting lower bound applies to every large
integer N. No natural density limit is assumed to exist. The final corollary
deduces the full Erdős–Turán unboundedness conclusion for a cofinite basis
whose six-fold sums have lower natural density zero.

The spectral estimate and its literature are described in the six-representation
section above. The argument uses a finite geometric tail to pass from weighted
sums to natural counts.
-/

namespace OMA.Erdos28PositiveDensity

open Finset AdditiveCombinatorics OMA.Erdos28Six

/-- A globally bounded coefficient can be large only on the exceptional level,
outside the finite initial interval and the tail of a truncation. -/
theorem coefficient_defect (T : Finset ℕ) (n K D g : ℕ) (high : Prop) [Decidable high]
    (cap : K≤n → sumRep (T:Set ℕ) n≤g) (low : ¬high → sumRep (T:Set ℕ) n≤5)
    (covered : K≤n → n≤D → 0<sumRep (T:Set ℕ) n) :
    let c := (sumRep (T:Set ℕ) n:ℝ)
    let d : ℝ := if ∃a∈T,a+a=n then 1 else 0
    let p : ℝ := if n<K then ((K:ℝ)+3)^2 else 0
    let h : ℝ := if high then ((g:ℝ)+3)^2 else 0
    c^2 ≤ 5*c+p+h ∧ (c-3)^2 ≤ c/2+4*d+p+h+(if D<n then 9 else 0) := by
  classical
  let c := (sumRep (T:Set ℕ) n:ℝ)
  have c0 : 0≤c := Nat.cast_nonneg _
  have di : 0≤ (if ∃a∈T,a+a=n then (1:ℝ) else 0) := by split <;> norm_num
  have post : 0≤ (if D<n then (9:ℝ) else 0) := by split <;> norm_num
  have hi : 0≤(if high then ((g:ℝ)+3)^2 else 0) := by split <;> positivity
  have bounds (b : ℕ) (hc : c≤b) : c^2≤((b:ℝ)+3)^2 ∧ (c-3)^2≤((b:ℝ)+3)^2 := by
    constructor
    · nlinarith [mul_nonneg (by linarith : 0≤(b:ℝ)+3-c) (by nlinarith : 0≤(b:ℝ)+3+c)]
    · nlinarith [mul_nonneg (by linarith : 0≤(b:ℝ)+3-(c-3)) (by nlinarith : 0≤(b:ℝ)+3+(c-3))]
  change c^2≤_ ∧ (c-3)^2≤_
  by_cases early : n<K
  · have cK : c≤K := by dsimp only [c]; exact_mod_cast (rep_limit (T:Set ℕ) n).trans (by omega : n+1≤K)
    obtain ⟨h1,h2⟩ := bounds K cK
    simp only [if_pos early]
    constructor <;> linarith
  · have hn : K≤n := by omega
    simp only [if_neg early,add_zero]
    by_cases big : high
    · have cg : c≤g := by dsimp only [c]; exact_mod_cast cap hn
      obtain ⟨h1,h2⟩ := bounds g cg
      simp only [if_pos big]
      constructor <;> linarith
    · have h5 := low big
      have c5 : c≤5 := by dsimp only [c]; exact_mod_cast h5
      simp only [if_neg big,add_zero]
      constructor
      · nlinarith [mul_nonneg c0 (sub_nonneg.mpr c5)]
      · by_cases late : D<n
        · simp only [if_pos late]
          nlinarith [mul_nonneg c0 (by linarith : 0≤6-c)]
        · simp only [if_neg late,add_zero]
          have h := deviation (T:Set ℕ) n (covered hn (by omega)) h5
          by_cases w : ∃a∈T,a+a=n
          · have ws : ∃a∈(T:Set ℕ),a+a=n := w
            rw [if_pos ws] at h
            simpa only [if_pos w,c] using h
          · have ws : ¬∃a∈(T:Set ℕ),a+a=n := w
            rw [if_neg ws] at h
            simpa only [if_neg w,c] using h

/-- The defect inequalities hold with an explicit weighted contribution for
indices of high multiplicity, even when the eventual cap is arbitrary. -/
theorem bounded_errors (T : Finset ℕ) (D K g : ℕ) (sub : T⊆Iic D)
    (high : ℕ → Prop) [DecidablePred high] (cap : ∀n,K≤n → sumRep (T:Set ℕ) n≤g)
    (low : ∀n,¬high n → sumRep (T:Set ℕ) n≤5)
    (covered : ∀n,K≤n → n≤D → 0<sumRep (T:Set ℕ) n)
    (t : ℝ) (ht : 0≤t) (ht1 : t<1) (tail : t^D≤1-t) :
    let L := range (2*D+1)
    let X := ∑ a∈T,t^a
    let E := ∑ n∈L,if high n then t^n else 0
    let Z := ((K:ℝ)+3)^2*K+((g:ℝ)+3)^2*E
    (∑ n∈L, (sumRep (T:Set ℕ) n:ℝ)^2*t^n)≤5*X^2+Z ∧
    (∑ n∈L, ((sumRep (T:Set ℕ) n:ℝ)-3)^2*t^n)≤X^2/2+4*X+Z+9 := by
  classical
  let L := range (2*D+1)
  let X := ∑ a∈T,t^a
  let c n := (sumRep (T:Set ℕ) n:ℝ)
  let pre n := if n<K then t^n else 0
  let post n := if D<n then t^n else 0
  let dia n := if ∃a∈T,a+a=n then t^n else 0
  let hi n := if high n then t^n else 0
  let M := ((K:ℝ)+3)^2
  let P := ((g:ℝ)+3)^2
  have isum : ∀ (prop : Prop) [Decidable prop] (x y : ℝ),
        (if prop then x else 0)*y=x*(if prop then y else 0) := by
    intro prop inst x y
    split <;> simp
  have wt (n : ℕ) : 0≤t^n := pow_nonneg ht n
  have weighted (n : ℕ) : (c n)^2*t^n ≤5*(c n*t^n)+M*pre n+P*hi n ∧
      (c n-3)^2*t^n ≤(1/2)*(c n*t^n)+4*dia n+M*pre n+P*hi n+9*post n := by
    obtain ⟨u,v⟩ := coefficient_defect T n K D g (high n) (cap n) (low n) (covered n)
    have u' := mul_le_mul_of_nonneg_right u (wt n)
    have v' := mul_le_mul_of_nonneg_right v (wt n)
    simp only [add_mul,isum, mul_assoc] at u' v'
    change _ ≤ _ ∧ _ ≤ _
    dsimp only [c,M,P,pre,post,dia,hi]
    constructor <;> linarith
  have ms : (∑ n∈L,c n*t^n)=X^2 := mass_sq T D sub t
  have bpre : M*(∑ n∈L,pre n) ≤ M*K :=
    mul_le_mul_of_nonneg_left (small_prefix_mass K _ t ht ht1.le) (sq_nonneg _)
  have bdiag : (∑ n∈L,dia n)≤X := diag_mass T _ t ht ht1.le
  have bpost : (∑ n∈L,post n)≤1 := late_mass D t ht ht1 tail
  constructor
  · change (∑ n∈L,(c n)^2*t^n)≤5*X^2+(M*K+P*(∑ n∈L,hi n))
    have hh := sum_le_sum (fun n (_:n∈L) => (weighted n).1)
    simp only [sum_add_distrib,←mul_sum,ms] at hh
    linarith
  · change (∑ n∈L,(c n-3)^2*t^n)≤X^2/2+4*X+(M*K+P*(∑ n∈L,hi n))+9
    have hh := sum_le_sum (fun n (_:n∈L) => (weighted n).2)
    simp only [sum_add_distrib,←mul_sum,ms] at hh
    linarith

end OMA.Erdos28PositiveDensity

namespace OMA.Erdos28PositiveDensity

open Finset AdditiveCombinatorics OMA.Erdos28Six

/-- Uniform in the eventual cap g. Once the finite geometric mass is large,
the weight of six-fold sums is at least its square divided by 8(g+3)². -/
theorem high_weight (A : Set ℕ) (D K g : ℕ)
    (covered : ∀n,K≤n → 0<sumRep A n) (cap : ∀n,K≤n → sumRep A n≤g)
    (r : ℝ) (hr : 0≤r) (hr1 : r<1) (tail : (r^2)^D≤1-r^2) :
    let T := (Iic D).filter (·∈A)
    let X := ∑ a∈T,(r^2)^a
    let E := ∑ n∈range (2*D+1), if 6≤sumRep A n then (r^2)^n else 0
    300000+8*(((K:ℝ)+3)^2*K+10) ≤ X →
    X^2 ≤ 8*((g:ℝ)+3)^2*E := by
  classical
  let T := (Iic D).filter (·∈A)
  let X := ∑ a∈T,(r^2)^a
  let P := ((g:ℝ)+3)^2
  let M := ((K:ℝ)+3)^2*(K:ℝ)
  let E := ∑ n∈range (2*D+1), if 6≤sumRep A n then (r^2)^n else 0
  let U := energy ((gen T r)^2)
  let V := energy ((gen T r)^2-baseline D r)
  change 300000+8*(M+10)≤X → X^2≤8*P*E
  intro large
  have sub : T⊆Iic D := filter_subset _ _
  have sa : (T:Set ℕ)⊆A := fun _ hn => (mem_filter.mp hn).2
  have capT (n : ℕ) (hn : K≤n) : sumRep (T:Set ℕ) n≤g := (rep_subset sa n).trans (cap n hn)
  have low (n : ℕ) (hn : ¬6≤sumRep A n) : sumRep (T:Set ℕ) n≤5 := (rep_subset sa n).trans (by omega)
  have pc (n : ℕ) (hn : K≤n) (hD : n≤D) : 0<sumRep (T:Set ℕ) n := by
    rw [rep_initial A D n hD]
    exact covered n hn
  have hq : r^2<1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1.le)]
  have eb := bounded_errors T D K g sub (fun n => 6≤sumRep A n) capT low pc
    (r^2) (sq_nonneg r) hq tail
  dsimp only at eb
  obtain ⟨u,v⟩ := energy_forms T D sub r
  rw [←u,←v] at eb
  change U≤5*X^2+(M+P*E) ∧ V≤X^2/2+4*X+(M+P*E)+9 at eb
  have wave := finite_spectral T r hr hr1.le D
  change X^2≤U/100+(1/40)*X^2+3*V/4+X^2/3+24000*X at wave
  have e0 : 0≤E := sum_nonneg fun n _ => by split <;> positivity
  have p0 : 0≤P := sq_nonneg _
  have m0 : 0≤M := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have x0 : 1≤X := by linarith
  have coarse : X^2≤120000*X+4*(M+P*E+10) := by
    nlinarith only [wave,eb.1,eb.2,x0,m0,mul_nonneg p0 e0]
  nlinarith only [coarse,large,x0,m0,mul_nonneg (sub_nonneg.mpr large) (show 0≤X by linarith),
    mul_nonneg (sub_nonneg.mpr x0) (add_nonneg m0 (by norm_num : (0:ℝ)≤10))]

end OMA.Erdos28PositiveDensity

namespace OMA.Erdos28PositiveDensity

open Finset AdditiveCombinatorics OMA.Erdos28Six
open scoped Classical Pointwise

theorem weight_coverage (T : Finset ℕ) (D K : ℕ) (sub : T⊆Iic D)
    (cov : ∀ n,K≤n → n≤D → 0<sumRep (T:Set ℕ) n) (t : ℝ)
    (ht : 0≤t) (ht1 : t<1) (tail : t^D≤1-t) :
    1 ≤ (1-t)*((∑ a∈T,t^a)^2+K+1) := by
  let c n := (sumRep (T:Set ℕ) n:ℝ)
  have nn (n : ℕ) : 0≤c n := Nat.cast_nonneg _
  have pt (n : ℕ) (hn : n∈range (D+1)) :
      t^n≤c n*t^n+(if n<K then t^n else 0) := by
    by_cases h : n<K
    · simp [h,mul_nonneg (nn n) (pow_nonneg ht n)]
    · have one : 1≤c n := by dsimp only [c]; exact_mod_cast cov n (by omega) (by have := mem_range.mp hn; omega)
      simp only [if_neg h,add_zero]
      simpa using mul_le_mul_of_nonneg_right one (pow_nonneg ht n)
  have a := sum_le_sum pt
  rw [sum_add_distrib] at a
  have b := small_prefix_mass K (D+1) t ht ht1.le
  have incl : range (D+1) ⊆ range (2*D+1) := range_mono (by omega)
  have cc := sum_le_sum_of_subset_of_nonneg incl
    (fun n _ _ => mul_nonneg (nn n) (pow_nonneg ht n))
  change (∑ n∈range (D+1),c n*t^n) ≤ ∑ n∈range (2*D+1),c n*t^n at cc
  have ms : (∑ n∈range (2*D+1),c n*t^n)=(∑ a∈T,t^a)^2 := mass_sq T D sub t
  rw [ms] at cc
  have ge : (∑ n∈range (D+1),t^n) ≤ (∑ a∈T,t^a)^2+K := by linarith
  have mulge := mul_le_mul_of_nonneg_right ge (sub_nonneg.mpr ht1.le)
  have ez := geom_sum_mul_neg t (D+1)
  have monotone : t^(D+1)≤t^D := pow_le_pow_of_le_one ht ht1.le (by omega)
  nlinarith only [ez,mulge,monotone,tail]

theorem prefix_and_tail (p : ℕ→Prop) [DecidablePred p] (N L : ℕ) (hNL : N≤L)
    (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    (1-t)*(∑ n∈range L, if p n then t^n else 0) ≤
      (1-t)*((range N).filter p).card+t^N := by
  let f n := if p n then t^n else 0
  have split := sum_Ico_eq_sub f hNL
  have a : (∑ n∈range N,f n)≤((range N).filter p).card := by
    calc
      _ ≤ ∑ n∈range N, if p n then (1:ℝ) else 0 := sum_le_sum (fun n _ => by
        dsimp only [f]; split <;> simp [pow_le_one₀ ht ht1.le])
      _ = _ := by simp
  have b : (∑ n∈Ico N L,f n) ≤ ∑ n∈Ico N L,t^n :=
    sum_le_sum fun n _ => by dsimp only [f]; split <;> simp [pow_nonneg ht n]
  have a' := mul_le_mul_of_nonneg_left a (sub_nonneg.mpr ht1.le)
  have b' := mul_le_mul_of_nonneg_left b (sub_nonneg.mpr ht1.le)
  have s' := congrArg (fun v:ℝ => (1-t)*v) split
  have g := geom_sum_Ico_mul_neg t hNL
  change (1-t)*(∑ n∈range L,f n)≤_
  nlinarith only [a',b',s',g,pow_nonneg ht L]

theorem geometric_decay (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (N : ℕ) :
    (1+(N:ℝ)*(1-t))*t^N≤1 := by
  have below : (N:ℝ)*t^N ≤ ∑ n∈range N,t^n := by
    calc
      _ = ∑ _n∈range N,t^N := by simp [nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun n hn => pow_le_pow_of_le_one ht ht1 (mem_range.mp hn).le
  have mulBelow := mul_le_mul_of_nonneg_right below (sub_nonneg.mpr ht1)
  have h := geom_sum_mul_neg t N
  nlinarith only [mulBelow,h]

/-- If a cofinite two-sum basis has an eventually bounded ordered representation
function, the integers with at least six representations have positive lower
natural density, with an explicit constant depending only on the eventual cap. -/
theorem six_positive_lower_density (A : Set ℕ) (cof : (A+A)ᶜ.Finite) (g : ℕ)
    (bounded : ∃K₀,∀n,K₀≤n → sumRep A n≤g) :
    ∃N₀,∀N≥N₀, N ≤ 1024*(g+3)^4*((range N).filter (fun n=>6≤sumRep A n)).card := by
  classical
  obtain ⟨K₀,hcap⟩ := bounded
  let F := cof.toFinset
  let K := K₀+F.sup id+1
  have cap (n : ℕ) (hn : K≤n) : sumRep A n≤g := hcap n (by dsimp [K] at hn;omega)
  have cov (n : ℕ) (hn : K≤n) : 0<sumRep A n := by
    have mem : n∈A+A := by
      by_contra missing
      have f : n∈F := cof.mem_toFinset.mpr missing
      have hm : n≤F.sup id := le_sup (f:=id) f
      dsimp [K] at hn
      omega
    obtain ⟨a,ha,b,hb,he⟩ := mem
    rw [sumRep_def]
    exact card_pos.mpr ⟨(a,b),mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr he,ha,hb⟩⟩
  let P₀ := (g+3)^2
  let B₀ := 32*P₀
  let Y₀ := 300000+8*((K+3)^2*K+10)
  let S₀ := K+1+Y₀^2
  refine ⟨8*B₀*S₀+1,?_⟩
  intro N hN
  have sN : 1≤S₀ := by dsimp [S₀];omega
  have bN : 0<B₀ := by dsimp [B₀,P₀]; positivity
  have BN := Nat.le_mul_of_pos_right B₀ sN
  have nB : B₀<N := by nlinarith only [hN,BN]
  let b := (B₀:ℝ)
  let P := (P₀:ℝ)
  let Y := (Y₀:ℝ)
  let Q := (S₀:ℝ)
  have bpos : 0<b := by dsimp only [b]; exact_mod_cast bN
  have NB : b<(N:ℝ) := by dsimp only [b]; exact_mod_cast nB
  have Npos : 0<(N:ℝ) := bpos.trans NB
  have Nbig : 8*b*Q≤N := by dsimp only [b,Q]; exact_mod_cast (show 8*B₀*S₀≤N by omega)
  have qform : Q=K+1+Y^2 := by simp [Q,Y,S₀]
  have pform : P=((g:ℝ)+3)^2 := by simp [P,P₀]
  have bform : b=32*P := by simp [b,B₀,P]
  have yform : Y=300000+8*(((K:ℝ)+3)^2*K+10) := by simp [Y,Y₀]
  let r := 1-b/N
  have hr : 0<r := by dsimp [r]; linarith [(div_lt_one Npos).mpr NB]
  have hr1 : r<1 := by dsimp [r]; linarith [div_pos bpos Npos]
  let t := r^2
  let z := 1-t
  have h0 : 0≤t := sq_nonneg r
  have ht : t<1 := by dsimp [t]; nlinarith [mul_pos hr (sub_pos.mpr hr1)]
  have hz : 0<z := sub_pos.mpr ht
  have idr : (N:ℝ)*(1-r)=b := by dsimp [r];field_simp;ring
  have nz1 : b≤N*z := by dsimp [z,t];nlinarith only [idr,mul_nonneg Npos.le (mul_nonneg hr.le (sub_nonneg.mpr hr1.le))]
  have nz2 : (N:ℝ)*z≤2*b := by dsimp [z,t];nlinarith only [idr,mul_nonneg Npos.le (sq_nonneg (1-r))]
  have qual : 4*z*Q≤1 := by
    apply le_of_mul_le_mul_right ?_ Npos
    have ho := mul_le_mul_of_nonneg_right nz2 (by dsimp [Q];positivity : 0≤4*Q)
    nlinarith only [ho,Nbig]
  obtain ⟨d,hd⟩ := exists_pow_lt_of_lt_one hz ht
  let D := max d (max K N)
  have dD : d≤D := le_max_left _ _
  have ND : N≤D := (le_max_right _ _).trans (le_max_right _ _)
  have tD : t^D≤1-t := (pow_le_pow_of_le_one h0 ht.le dD).trans hd.le
  let T := (Iic D).filter (·∈A)
  let X := ∑ a∈T,t^a
  let E := ∑ n∈range (2*D+1), if 6≤sumRep A n then t^n else 0
  let H := (((range N).filter (fun n=>6≤sumRep A n)).card:ℝ)
  have x0 : 0≤X := sum_nonneg fun a _=>pow_nonneg h0 a
  have sub : T⊆Iic D := filter_subset _ _
  have repT (n : ℕ) (hn : K≤n) (hD : n≤D) : 0<sumRep (T:Set ℕ) n := by
    rw [rep_initial A D n hD]
    exact cov n hn
  have ww := weight_coverage T D K sub repT t h0 ht tD
  change 1≤ z*(X^2+K+1) at ww
  have scale : 4*z*(K+1+Y^2)≤1 := by rwa [qform] at qual
  have zx : 3≤4*z*X^2 := by
    nlinarith only [scale,ww,mul_nonneg hz.le (sq_nonneg Y)]
  have lx : Y≤X := by
    by_contra! sm
    have yy : X^2<Y^2 := by nlinarith [mul_pos (sub_pos.mpr sm) (by linarith : 0<X+Y)]
    have ll := mul_lt_mul_of_pos_left yy hz
    nlinarith only [scale,zx,ll,mul_nonneg hz.le (show 0≤(K:ℝ)+1 by positivity)]
  have he := high_weight A D K g cov cap r hr.le hr1 tD
  change 300000+8*(((K:ℝ)+3)^2*K+10)≤X → X^2≤8*((g:ℝ)+3)^2*E at he
  rw [←yform,←pform] at he
  have he' := mul_le_mul_of_nonneg_left (he lx) hz.le
  have upper := prefix_and_tail (fun n=>6≤sumRep A n) N (2*D+1) (by omega) t h0 ht
  change z*E≤z*H+t^N at upper
  have pow0 := pow_nonneg h0 N
  have decay := geometric_decay t h0 ht.le N
  change (1+(N:ℝ)*z)*t^N≤1 at decay
  have small : b*t^N≤1 := by nlinarith only [decay,pow0,mul_le_mul_of_nonneg_right nz1 pow0]
  have h0H : 0≤H := Nat.cast_nonneg _
  have p0 : 0≤P := Nat.cast_nonneg _
  have wcount := mul_le_mul_of_nonneg_left upper (show 0≤32*P by positivity)
  rw [bform] at small
  have share : 2≤32*P*z*H := by nlinarith only [zx,he',wcount,small]
  have shareN := mul_le_mul_of_nonneg_right share Npos.le
  have comp := mul_le_mul_of_nonneg_right nz2 (show 0≤32*P*H by positivity)
  rw [bform] at comp
  have final : (N:ℝ)≤1024*((g:ℝ)+3)^4*H := by
    rw [show ((g:ℝ)+3)^4=P^2 by rw [pform];ring]
    nlinarith only [shareN,comp]
  dsimp only [H] at final
  exact_mod_cast final

/-- The Erdős–Turán conclusion holds whenever the six-fold sums have lower natural
density zero, stated through arbitrarily sparse finite prefixes. -/
theorem unbounded_of_sparse_six (A : Set ℕ) (cof : (A+A)ᶜ.Finite)
    (sparse : ∀ c j : ℕ, ∃N≥j, c*((range N).filter (fun n=>6≤sumRep A n)).card<N) :
    ∀ g j : ℕ, ∃ n≥j, g<sumRep A n := by
  intro g j
  by_contra! cap
  obtain ⟨N₀,density⟩ := six_positive_lower_density A cof g ⟨j,cap⟩
  obtain ⟨N,hN,thin⟩ := sparse (1024*(g+3)^4) N₀
  exact (Nat.not_lt_of_ge (density N hN)) thin

end OMA.Erdos28PositiveDensity
