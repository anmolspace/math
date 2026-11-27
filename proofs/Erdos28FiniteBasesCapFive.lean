import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite exact bases with at most five ordered representations per sum

Borwein, Choi, and Chu's Table 1 reports that such bases have largest element 52
and cardinality at most 14. Here a basis must represent every integer from zero
through its largest element. The representation cap applies to *all* sums.

The certificate visits the integers in increasing order. At each integer it
checks the inclusion and exclusion branches. A crowded sum carries six distinct
first coordinates of ordered representations. A missing sum prevents the search
from skipping the current integer. The computation uses forward and reflected
bit masks to check these witnesses. The proof of correctness does not require the
lookup used to find the witnesses to be correct.

The computation inspects choices through 70 and possible sums through 140. Each
admissible inclusion certifies both its index and the number of selected integers.
Following the branch of any actual basis gives both bounds. The catalog also checks the converse for each inclusion and proves there are exactly 6,355 different bases.
-/

namespace OMA.Erdos28GlobalFive

private def pick (v : Nat) : Nat := ((0x555670577c7108588b7d6c722b090059008c767e236d6973002c000a39000f5a87002f004b77467f3324006e066a007467000d2d4400000b003a3c0062103e5b52880000843064004f4c12781f47408015345d251900546f7b078a6b2a00007522680000380e862e4a4532000500660c4300003b613d510083634e111e3f145c18537a892900210037854931046542006050824d1d1317792820364803415f811c162735025e1b26011a0000 : Nat) >>> (8*((v ^^^ (v-1))%173)))%256

private def gather : Nat → Nat → Bool
  | 0, _ => true
  | k+1, v =>
    let p := pick v
    v.testBit p && gather k (v ^^^ (1 <<< p))

private theorem singleBit (i j : Nat) : (1 <<< i : Nat).testBit j = decide (i=j) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

private theorem gather_sound {k v : Nat} (h : gather k v = true) :
    ∃ l : List Nat, l.length=k ∧ l.Nodup ∧ ∀ i ∈ l, v.testBit i=true := by
  induction k generalizing v with
  | zero => exact ⟨[],rfl,List.nodup_nil,by simp⟩
  | succ k ih =>
    let p := pick v
    obtain ⟨hp,hr⟩ := Bool.and_eq_true_iff.mp h
    change v.testBit p = true at hp
    obtain ⟨l,hl,hd,hs⟩ := ih hr
    have ne (i : Nat) (hi : i ∈ l) : p ≠ i := by
      rintro rfl
      have hz := hs _ hi
      simp [Nat.testBit_xor, singleBit, hp, p] at hz
    refine ⟨p::l, by simp [hl], List.nodup_cons.mpr ⟨fun z => ne _ z rfl, hd⟩, ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · exact hp
    · have hz := hs _ hi
      rw [Nat.testBit_xor, singleBit] at hz
      simpa only [show decide (pick v=i)=false from decide_eq_false (ne i hi), Bool.xor_false] using hz

private structure State where
  pos : Nat
  rev : Nat
  one : Nat
  two : Nat
  deriving DecidableEq

private def add (s : State) (x : Nat) : State :=
  let t := s.pos <<< x
  ⟨s.pos ||| (1 <<< x), s.rev ||| (1 <<< (140-x)),
   s.one ||| t, s.two ||| (s.one &&& t)⟩

private def pairs (s : State) (n : Nat) := s.pos &&& (s.rev >>> (140-n))

private def crowded (s : State) (n : Nat) : Bool :=
  decide (n ≤ 140) && gather 6 (pairs s n)

private def includeStops (s : State) (x : Nat) : Bool :=
  let bad := ((s.pos <<< x) &&& s.two) &&& (2^141-1)
  bad != 0 && crowded (add s x) (pick bad)

/-- Six distinct first coordinates of ordered representations of one sum. -/
def Six (A : Nat → Prop) : Prop :=
  ∃ n ≤ 140, ∃ l : List Nat, l.length = 6 ∧ l.Nodup ∧
    ∀ a ∈ l, ∃ b, A a ∧ A b ∧ a+b=n

private structure Fits (A : Nat → Prop) (x : Nat) (s : State) : Prop where
  complete : ∀ a < x, A a → s.pos.testBit a = true ∧ s.rev.testBit (140-a) = true
  forward : ∀ a, s.pos.testBit a = true → A a
  backward : ∀ i, s.rev.testBit i = true → ∃ b ≤ 140, A b ∧ i = 140-b

private theorem skipFits {A x s} (h : Fits A x s) (hn : ¬A x) : Fits A (x+1) s := by
  refine ⟨?_,h.forward,h.backward⟩
  intro a ha hA
  exact h.complete a (by by_cases z : a=x; exact False.elim (hn (z ▸ hA)); omega) hA

private theorem addFits {A x s} (h : Fits A x s) (hx : x ≤ 140) (ha : A x) :
    Fits A (x+1) (add s x) := by
  refine ⟨?_,?_,?_⟩
  · intro a hv hA
    by_cases hz : a=x
    · subst a
      simp [add,Nat.testBit_or,singleBit]
    · obtain ⟨hp,hr⟩ := h.complete a (by omega) hA
      simp [add,Nat.testBit_or,hp,hr]
  · intro a hb
    simp only [add,Nat.testBit_or,Bool.or_eq_true_iff,singleBit,decide_eq_true_eq] at hb
    rcases hb with hi|rfl
    · exact h.forward _ hi
    · exact ha
  · intro i hb
    simp only [add,Nat.testBit_or,Bool.or_eq_true_iff,singleBit,decide_eq_true_eq] at hb
    rcases hb with hi|rfl
    · exact h.backward _ hi
    · exact ⟨x,hx,ha,rfl⟩

private theorem pairSound {A x s n a} (h : Fits A x s) (hn : n ≤ 140)
    (ha : (pairs s n).testBit a = true) : ∃ b, A a ∧ A b ∧ a+b=n := by
  simp only [pairs,Nat.testBit_and,Nat.testBit_shiftRight,Bool.and_eq_true_iff] at ha
  obtain ⟨b,hb,hA,he⟩ := h.backward _ ha.2
  exact ⟨b,h.forward _ ha.1,hA,by omega⟩

private theorem crowdedSound {A x s n} (h : Fits A x s) (hc : crowded s n = true) : Six A := by
  obtain ⟨hn, hg⟩ := Bool.and_eq_true_iff.mp hc
  have hn' : n ≤ 140 := of_decide_eq_true hn
  obtain ⟨l,hl,hd,hs⟩ := gather_sound hg
  exact ⟨n,hn',l,hl,hd,fun a ha => pairSound h hn' (hs a ha)⟩

private def CoveredAt (A : Nat → Prop) (n : Nat) := ∃ a b, A a ∧ A b ∧ a+b=n

private theorem cannotSkip {A x s} (h : Fits A x s) (hx : x ≤ 140) (cov : CoveredAt A x)
    (hn : ¬A x) (hz : pairs s x = 0) : False := by
  obtain ⟨a,b,ha,hb,hs⟩ := cov
  have h₁ : a < x := by by_cases e : a=x; exact False.elim (hn (e ▸ ha)); omega
  have h₂ : b < x := by by_cases e : b=x; exact False.elim (hn (e ▸ hb)); omega
  have hp := (h.complete a h₁ ha).1
  have hr := (h.complete b h₂ hb).2
  have he : (140-x)+a=140-b := by omega
  have : (pairs s x).testBit a = true := by simp [pairs,Nat.testBit_shiftRight,he,hp,hr]
  simp [hz] at this

private def check : Nat → Nat → Nat → State → Bool
  | 0, _, _, _ => false
  | k+1, x, used, s =>
    (includeStops s x || (decide (x ≤ 52 ∧ used < 14) && check k (x+1) (used+1) (add s x))) &&
    (pairs s x == 0 || check k (x+1) used s)

private def Result (A : Nat → Prop) (d : Nat) : Prop :=
  d ≤ 52 ∧ ∃ l : List Nat, l.length ≤ 14 ∧ ∀ a, A a → a ∈ l

private theorem bounds_sound {A : Nat → Prop} {d : Nat}
    (last : A d) (within : ∀ a, A a → a ≤ d)
    (cov : ∀ n ≤ d, CoveredAt A n) (cap : ¬Six A)
    (k x : Nat) (taken : List Nat) (s : State) (bound : k+x ≤ 71)
    (hx : x ≤ d) (seen : ∀ a < x, A a → a ∈ taken)
    (h : Fits A x s) (hc : check k x taken.length s = true) : Result A d := by
  induction k generalizing x taken s with
  | zero => contradiction
  | succ k ih =>
    have small : x ≤ 140 := by omega
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp hc
    by_cases ha : A x
    · rcases Bool.or_eq_true_iff.mp left with stop|more
      · exact False.elim (cap (crowdedSound (addFits h small ha) (Bool.and_eq_true_iff.mp stop).2))
      · obtain ⟨limits,child⟩ := Bool.and_eq_true_iff.mp more
        have hl : x ≤ 52 ∧ taken.length < 14 := of_decide_eq_true limits
        have seen' : ∀ a < x+1, A a → a ∈ x::taken := by
          intro a hlt hA
          by_cases eq : a=x
          · exact List.mem_cons.mpr (Or.inl eq)
          · exact List.mem_cons.mpr (Or.inr (seen a (by omega) hA))
        by_cases eq : x=d
        · refine ⟨by omega, x::taken, by simp only [List.length_cons]; omega, ?_⟩
          exact fun a hA => seen' a (by have := within a hA; omega) hA
        · exact ih (x+1) (x::taken) _ (by omega) (by omega) seen' (addFits h small ha) child
    · rcases Bool.or_eq_true_iff.mp right with stop|more
      · exact False.elim (cannotSkip h small (cov x hx) ha (beq_iff_eq.mp stop))
      · have ne : x ≠ d := by rintro rfl; exact ha last
        have seen' : ∀ a < x+1, A a → a ∈ taken := by
          intro a hlt hA
          have ne' : a ≠ x := by rintro rfl; exact ha hA
          exact seen a (by omega) hA
        exact ih (x+1) taken s (by omega) (by omega) seen' (skipFits h ha) more

private theorem step {k x c : Nat} {s : State}
    (hl : includeStops s x = true ∨ (x ≤ 52 ∧ c < 14) ∧ check k (x+1) (c+1) (add s x) = true)
    (hr : pairs s x = 0 ∨ check k (x+1) c s = true) : check (k+1) x c s = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,Bool.or_eq_true_iff.mpr (hr.imp (fun h => beq_iff_eq.mpr h) id)⟩
  apply Bool.or_eq_true_iff.mpr
  exact hl.imp id (fun h => Bool.and_eq_true_iff.mpr ⟨decide_eq_true h.1,h.2⟩)

private def catalog : Nat → Nat → State → Finset Nat → List (Finset Nat)
  | 0, _, _, _ => []
  | k+1, x, s, taken =>
    (if includeStops s x then [] else
      insert x taken :: catalog k (x+1) (add s x) (insert x taken)) ++
    (if pairs s x == 0 then [] else catalog k (x+1) s taken)

private def catalogSize : Nat → Nat → State → Nat
  | 0, _, _ => 0
  | k+1, x, s =>
    (if includeStops s x then 0 else 1 + catalogSize k (x+1) (add s x)) +
    (if pairs s x == 0 then 0 else catalogSize k (x+1) s)

private def atMostBits : Nat → Nat → Bool
  | 0, v => v == 0
  | k+1, v => v == 0 || atMostBits k (v ^^^ (1 <<< pick v))

private def validate : Nat → Nat → State → List Nat → Bool
  | 0, _, _, _ => true
  | k+1, x, s, p =>
    (includeStops s x ||
      ((x::p).all (fun a => atMostBits 5 (pairs (add s x) (x+a))) &&
       validate k (x+1) (add s x) (x::p))) &&
    (pairs s x == 0 || validate k (x+1) s p)

private def combine : Option Nat → Option Nat → Option Nat
  | some u, some v => some (u+v)
  | _, _ => none

/-- Independent validation of surviving inclusions. At most two unequal unordered
pairs can share a sum when the ordered representation bound is five. The search
proposes crowded sums with bit planes, then explicitly checks six witnesses.
For a surviving inclusion, only sums of the newly inserted element and an element
of the enlarged set can gain representations. The audit verifies the five-witness
upper bound on each such sum and counts the surviving inclusions. -/
private def audit : Nat → Nat → State → List Nat → Option Nat
  | 0, _, _, _ => none
  | k+1, x, s, p =>
    combine
      (if includeStops s x then some 0 else
       if (decide (x ≤ 52 ∧ p.length < 14) &&
           (x::p).all (fun a => atMostBits 5 (pairs (add s x) (x+a)))) then
         (audit k (x+1) (add s x) (x::p)).map Nat.succ else none)
      (if pairs s x == 0 then some 0 else audit k (x+1) s p)

private theorem combine_inv {a b : Option Nat} {n : Nat} (h : combine a b = some n) :
    ∃ u v, a = some u ∧ b = some v ∧ u+v=n := by
  cases a <;> cases b <;> simp_all [combine]

private theorem audit_projects {k x s p n} (h : audit k x s p = some n) :
    check k x p.length s = true ∧ catalogSize k x s = n ∧ validate k x s p = true := by
  induction k generalizing x s p n with
  | zero => simp [audit] at h
  | succ k ih =>
    obtain ⟨u,v,ht,hs,sum⟩ := combine_inv h
    have up : (includeStops s x || (decide (x ≤ 52 ∧ p.length < 14) &&
        check k (x+1) (p.length+1) (add s x))) = true ∧
        (if includeStops s x then 0 else 1 + catalogSize k (x+1) (add s x)) = u ∧
        (includeStops s x || ((x::p).all (fun a => atMostBits 5 (pairs (add s x) (x+a))) &&
        validate k (x+1) (add s x) (x::p))) = true := by
      by_cases bad : includeStops s x = true
      · rw [if_pos bad] at ht
        have hu : 0=u := Option.some.inj ht
        simp [bad, ← hu]
      · by_cases ok : (decide (x ≤ 52 ∧ p.length < 14) &&
              (x::p).all (fun a => atMostBits 5 (pairs (add s x) (x+a)))) = true
        · rw [if_neg bad,if_pos ok] at ht
          cases child : audit k (x+1) (add s x) (x::p) with
          | none => simp [child] at ht
          | some w =>
            have ⟨bounds,sz,valid⟩ := ih child
            obtain ⟨small,each⟩ := Bool.and_eq_true_iff.mp ok
            rw [child] at ht
            have hu : w+1=u := Option.some.inj ht
            refine ⟨Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr ⟨small,bounds⟩)),
              ?_, Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr ⟨each,valid⟩))⟩
            rw [if_neg bad,sz]
            omega
        · rw [if_neg bad,if_neg ok] at ht
          contradiction
    have down : (pairs s x == 0 || check k (x+1) p.length s) = true ∧
        (if pairs s x == 0 then 0 else catalogSize k (x+1) s) = v ∧
        (pairs s x == 0 || validate k (x+1) s p) = true := by
      by_cases missing : (pairs s x == 0) = true
      · rw [if_pos missing] at hs
        have hv : 0=v := Option.some.inj hs
        simp [missing,← hv]
      · rw [if_neg missing] at hs
        obtain ⟨bounds,sz,valid⟩ := ih hs
        exact ⟨Bool.or_eq_true_iff.mpr (Or.inr bounds), by rw [if_neg missing,sz],
          Bool.or_eq_true_iff.mpr (Or.inr valid)⟩
    refine ⟨Bool.and_eq_true_iff.mpr ⟨up.1,down.1⟩, ?_, Bool.and_eq_true_iff.mpr ⟨up.2.2,down.2.2⟩⟩
    change _ + _ = n
    rw [up.2.1,down.2.1,sum]
private theorem auditStep {k x u v : Nat} {s : State} {p : List Nat}
    (ht : (includeStops s x = true ∧ u=0) ∨
      (includeStops s x = false ∧ (decide (x ≤ 52 ∧ p.length < 14) &&
      (x::p).all (fun a => atMostBits 5 (pairs (add s x) (x+a)))) = true ∧
      ∃ w, audit k (x+1) (add s x) (x::p) = some w ∧ w+1=u))
    (hs : ((pairs s x == 0) = true ∧ v=0) ∨
      ((pairs s x == 0) = false ∧ audit k (x+1) s p = some v)) :
    audit (k+1) x s p = some (u+v) := by
  have take : (if includeStops s x then some 0 else
      if (decide (x ≤ 52 ∧ p.length < 14) &&
          (x::p).all (fun a => atMostBits 5 (pairs (add s x) (x+a)))) then
        (audit k (x+1) (add s x) (x::p)).map Nat.succ else none) = some u := by
    rcases ht with ⟨t,rfl⟩|⟨t,hg,w,hw,rfl⟩
    · rw [if_pos t]
    · rw [if_neg (by simp [t]),if_pos hg,hw]
      rfl
  have skip : (if pairs s x == 0 then some 0 else audit k (x+1) s p) = some v := by
    rcases hs with ⟨q,rfl⟩|⟨q,hv⟩
    · rw [if_pos q]
    · rw [if_neg (by simp [q]),hv]
  change combine _ _ = some (u+v)
  rw [take,skip]
  rfl

private theorem apart0 : audit 62 9 (⟨0x15f,0x1f5000000000000000000000000000000000,0x5ffe,0x7f8⟩ : State) [8,6,4,3,2,1,0] = some 106 := by decide +kernel

private theorem apart1 : audit 62 9 (⟨0x5f,0x1f4000000000000000000000000000000000,0x7fe,0xf8⟩ : State) [6,4,3,2,1,0] = some 478 := by decide +kernel

private theorem apart2 : audit 63 8 (⟨0x5f,0x1f4000000000000000000000000000000000,0x7fe,0xf8⟩ : State) [6,4,3,2,1,0] = some 585 := auditStep (k:=62) (x:=8) (u:=107) (v:=478) (s:=(⟨0x5f,0x1f4000000000000000000000000000000000,0x7fe,0xf8⟩ : State)) (p:=[6,4,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,106,apart0,rfl⟩) (Or.inr ⟨by decide +kernel,apart1⟩)

private theorem apart3 : audit 64 7 (⟨0x5f,0x1f4000000000000000000000000000000000,0x7fe,0xf8⟩ : State) [6,4,3,2,1,0] = some 585 := auditStep (k:=63) (x:=7) (u:=0) (v:=585) (s:=(⟨0x5f,0x1f4000000000000000000000000000000000,0x7fe,0xf8⟩ : State)) (p:=[6,4,3,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart2⟩)

private theorem apart4 : audit 62 9 (⟨0x19f,0x1f3000000000000000000000000000000000,0x9ffe,0xfb8⟩ : State) [8,7,4,3,2,1,0] = some 16 := by decide +kernel

private theorem apart5 : audit 62 9 (⟨0x9f,0x1f2000000000000000000000000000000000,0xffe,0xb8⟩ : State) [7,4,3,2,1,0] = some 387 := by decide +kernel

private theorem apart6 : audit 63 8 (⟨0x9f,0x1f2000000000000000000000000000000000,0xffe,0xb8⟩ : State) [7,4,3,2,1,0] = some 404 := auditStep (k:=62) (x:=8) (u:=17) (v:=387) (s:=(⟨0x9f,0x1f2000000000000000000000000000000000,0xffe,0xb8⟩ : State)) (p:=[7,4,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,16,apart4,rfl⟩) (Or.inr ⟨by decide +kernel,apart5⟩)

private theorem apart7 : audit 62 9 (⟨0x11f,0x1f1000000000000000000000000000000000,0x1ffe,0x38⟩ : State) [8,4,3,2,1,0] = some 344 := by decide +kernel

private theorem apart8 : audit 62 9 (⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State) [4,3,2,1,0] = some 580 := by decide +kernel

private theorem apart9 : audit 63 8 (⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State) [4,3,2,1,0] = some 925 := auditStep (k:=62) (x:=8) (u:=345) (v:=580) (s:=(⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State)) (p:=[4,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,344,apart7,rfl⟩) (Or.inr ⟨by decide +kernel,apart8⟩)

private theorem apart10 : audit 64 7 (⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State) [4,3,2,1,0] = some 1330 := auditStep (k:=63) (x:=7) (u:=405) (v:=925) (s:=(⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State)) (p:=[4,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,404,apart6,rfl⟩) (Or.inr ⟨by decide +kernel,apart9⟩)

private theorem apart11 : audit 65 6 (⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State) [4,3,2,1,0] = some 1916 := auditStep (k:=64) (x:=6) (u:=586) (v:=1330) (s:=(⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State)) (p:=[4,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,585,apart3,rfl⟩) (Or.inr ⟨by decide +kernel,apart10⟩)

private theorem apart12 : audit 66 5 (⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State) [4,3,2,1,0] = some 1916 := auditStep (k:=65) (x:=5) (u:=0) (v:=1916) (s:=(⟨0x1f,0x1f0000000000000000000000000000000000,0xfe,0x38⟩ : State)) (p:=[4,3,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart11⟩)

private theorem apart13 : audit 62 9 (⟨0x6f,0x1ec000000000000000000000000000000000,0xbfe,0x1e8⟩ : State) [6,5,3,2,1,0] = some 414 := by decide +kernel

private theorem apart14 : audit 63 8 (⟨0x6f,0x1ec000000000000000000000000000000000,0xbfe,0x1e8⟩ : State) [6,5,3,2,1,0] = some 414 := auditStep (k:=62) (x:=8) (u:=0) (v:=414) (s:=(⟨0x6f,0x1ec000000000000000000000000000000000,0xbfe,0x1e8⟩ : State)) (p:=[6,5,3,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart13⟩)

private theorem apart15 : audit 64 7 (⟨0x6f,0x1ec000000000000000000000000000000000,0xbfe,0x1e8⟩ : State) [6,5,3,2,1,0] = some 414 := auditStep (k:=63) (x:=7) (u:=0) (v:=414) (s:=(⟨0x6f,0x1ec000000000000000000000000000000000,0xbfe,0x1e8⟩ : State)) (p:=[6,5,3,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart14⟩)

private theorem apart16 : audit 62 9 (⟨0xaf,0x1ea000000000000000000000000000000000,0x17fe,0x1a8⟩ : State) [7,5,3,2,1,0] = some 78 := by decide +kernel

private theorem apart17 : audit 63 8 (⟨0xaf,0x1ea000000000000000000000000000000000,0x17fe,0x1a8⟩ : State) [7,5,3,2,1,0] = some 78 := auditStep (k:=62) (x:=8) (u:=0) (v:=78) (s:=(⟨0xaf,0x1ea000000000000000000000000000000000,0x17fe,0x1a8⟩ : State)) (p:=[7,5,3,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart16⟩)

private theorem apart18 : audit 62 9 (⟨0x12f,0x1e9000000000000000000000000000000000,0x2ffe,0x128⟩ : State) [8,5,3,2,1,0] = some 126 := by decide +kernel

private theorem apart19 : audit 62 9 (⟨0x2f,0x1e8000000000000000000000000000000000,0x1fe,0x28⟩ : State) [5,3,2,1,0] = some 105 := by decide +kernel

private theorem apart20 : audit 63 8 (⟨0x2f,0x1e8000000000000000000000000000000000,0x1fe,0x28⟩ : State) [5,3,2,1,0] = some 232 := auditStep (k:=62) (x:=8) (u:=127) (v:=105) (s:=(⟨0x2f,0x1e8000000000000000000000000000000000,0x1fe,0x28⟩ : State)) (p:=[5,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,126,apart18,rfl⟩) (Or.inr ⟨by decide +kernel,apart19⟩)

private theorem apart21 : audit 64 7 (⟨0x2f,0x1e8000000000000000000000000000000000,0x1fe,0x28⟩ : State) [5,3,2,1,0] = some 311 := auditStep (k:=63) (x:=7) (u:=79) (v:=232) (s:=(⟨0x2f,0x1e8000000000000000000000000000000000,0x1fe,0x28⟩ : State)) (p:=[5,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,78,apart17,rfl⟩) (Or.inr ⟨by decide +kernel,apart20⟩)

private theorem apart22 : audit 65 6 (⟨0x2f,0x1e8000000000000000000000000000000000,0x1fe,0x28⟩ : State) [5,3,2,1,0] = some 726 := auditStep (k:=64) (x:=6) (u:=415) (v:=311) (s:=(⟨0x2f,0x1e8000000000000000000000000000000000,0x1fe,0x28⟩ : State)) (p:=[5,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,414,apart15,rfl⟩) (Or.inr ⟨by decide +kernel,apart21⟩)

private theorem apart23 : audit 62 9 (⟨0xcf,0x1e6000000000000000000000000000000000,0x27fe,0x388⟩ : State) [7,6,3,2,1,0] = some 12 := by decide +kernel

private theorem apart24 : audit 63 8 (⟨0xcf,0x1e6000000000000000000000000000000000,0x27fe,0x388⟩ : State) [7,6,3,2,1,0] = some 12 := auditStep (k:=62) (x:=8) (u:=0) (v:=12) (s:=(⟨0xcf,0x1e6000000000000000000000000000000000,0x27fe,0x388⟩ : State)) (p:=[7,6,3,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart23⟩)

private theorem apart25 : audit 62 9 (⟨0x14f,0x1e5000000000000000000000000000000000,0x4ffe,0x308⟩ : State) [8,6,3,2,1,0] = some 75 := by decide +kernel

private theorem apart26 : audit 62 9 (⟨0x4f,0x1e4000000000000000000000000000000000,0x3fe,0x8⟩ : State) [6,3,2,1,0] = some 134 := by decide +kernel

private theorem apart27 : audit 63 8 (⟨0x4f,0x1e4000000000000000000000000000000000,0x3fe,0x8⟩ : State) [6,3,2,1,0] = some 210 := auditStep (k:=62) (x:=8) (u:=76) (v:=134) (s:=(⟨0x4f,0x1e4000000000000000000000000000000000,0x3fe,0x8⟩ : State)) (p:=[6,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,75,apart25,rfl⟩) (Or.inr ⟨by decide +kernel,apart26⟩)

private theorem apart28 : audit 64 7 (⟨0x4f,0x1e4000000000000000000000000000000000,0x3fe,0x8⟩ : State) [6,3,2,1,0] = some 223 := auditStep (k:=63) (x:=7) (u:=13) (v:=210) (s:=(⟨0x4f,0x1e4000000000000000000000000000000000,0x3fe,0x8⟩ : State)) (p:=[6,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,12,apart24,rfl⟩) (Or.inr ⟨by decide +kernel,apart27⟩)

private theorem apart29 : audit 62 9 (⟨0x18f,0x1e3000000000000000000000000000000000,0x8fbe,0x708⟩ : State) [8,7,3,2,1,0] = some 44 := by decide +kernel

private theorem apart30 : audit 62 9 (⟨0x8f,0x1e2000000000000000000000000000000000,0x7be,0x8⟩ : State) [7,3,2,1,0] = some 214 := by decide +kernel

private theorem apart31 : audit 63 8 (⟨0x8f,0x1e2000000000000000000000000000000000,0x7be,0x8⟩ : State) [7,3,2,1,0] = some 259 := auditStep (k:=62) (x:=8) (u:=45) (v:=214) (s:=(⟨0x8f,0x1e2000000000000000000000000000000000,0x7be,0x8⟩ : State)) (p:=[7,3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,44,apart29,rfl⟩) (Or.inr ⟨by decide +kernel,apart30⟩)

private theorem apart32 : audit 64 7 (⟨0xf,0x1e0000000000000000000000000000000000,0x3e,0x8⟩ : State) [3,2,1,0] = some 260 := auditStep (k:=63) (x:=7) (u:=260) (v:=0) (s:=(⟨0xf,0x1e0000000000000000000000000000000000,0x3e,0x8⟩ : State)) (p:=[3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,259,apart31,rfl⟩) (Or.inl (by decide +kernel))

private theorem apart33 : audit 65 6 (⟨0xf,0x1e0000000000000000000000000000000000,0x3e,0x8⟩ : State) [3,2,1,0] = some 484 := auditStep (k:=64) (x:=6) (u:=224) (v:=260) (s:=(⟨0xf,0x1e0000000000000000000000000000000000,0x3e,0x8⟩ : State)) (p:=[3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,223,apart28,rfl⟩) (Or.inr ⟨by decide +kernel,apart32⟩)

private theorem apart34 : audit 66 5 (⟨0xf,0x1e0000000000000000000000000000000000,0x3e,0x8⟩ : State) [3,2,1,0] = some 1211 := auditStep (k:=65) (x:=5) (u:=727) (v:=484) (s:=(⟨0xf,0x1e0000000000000000000000000000000000,0x3e,0x8⟩ : State)) (p:=[3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,726,apart22,rfl⟩) (Or.inr ⟨by decide +kernel,apart33⟩)

private theorem apart35 : audit 67 4 (⟨0xf,0x1e0000000000000000000000000000000000,0x3e,0x8⟩ : State) [3,2,1,0] = some 3128 := auditStep (k:=66) (x:=4) (u:=1917) (v:=1211) (s:=(⟨0xf,0x1e0000000000000000000000000000000000,0x3e,0x8⟩ : State)) (p:=[3,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,1916,apart12,rfl⟩) (Or.inr ⟨by decide +kernel,apart34⟩)

private theorem apart36 : audit 62 9 (⟨0xb7,0x1da000000000000000000000000000000000,0x1bfe,0x2e0⟩ : State) [7,5,4,2,1,0] = some 87 := by decide +kernel

private theorem apart37 : audit 63 8 (⟨0xb7,0x1da000000000000000000000000000000000,0x1bfe,0x2e0⟩ : State) [7,5,4,2,1,0] = some 87 := auditStep (k:=62) (x:=8) (u:=0) (v:=87) (s:=(⟨0xb7,0x1da000000000000000000000000000000000,0x1bfe,0x2e0⟩ : State)) (p:=[7,5,4,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart36⟩)

private theorem apart38 : audit 62 9 (⟨0x137,0x1d9000000000000000000000000000000000,0x37fe,0x260⟩ : State) [8,5,4,2,1,0] = some 34 := by decide +kernel

private theorem apart39 : audit 62 9 (⟨0x37,0x1d8000000000000000000000000000000000,0x2fe,0x60⟩ : State) [5,4,2,1,0] = some 217 := by decide +kernel

private theorem apart40 : audit 63 8 (⟨0x37,0x1d8000000000000000000000000000000000,0x2fe,0x60⟩ : State) [5,4,2,1,0] = some 252 := auditStep (k:=62) (x:=8) (u:=35) (v:=217) (s:=(⟨0x37,0x1d8000000000000000000000000000000000,0x2fe,0x60⟩ : State)) (p:=[5,4,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,34,apart38,rfl⟩) (Or.inr ⟨by decide +kernel,apart39⟩)

private theorem apart41 : audit 64 7 (⟨0x37,0x1d8000000000000000000000000000000000,0x2fe,0x60⟩ : State) [5,4,2,1,0] = some 340 := auditStep (k:=63) (x:=7) (u:=88) (v:=252) (s:=(⟨0x37,0x1d8000000000000000000000000000000000,0x2fe,0x60⟩ : State)) (p:=[5,4,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,87,apart37,rfl⟩) (Or.inr ⟨by decide +kernel,apart40⟩)

private theorem apart42 : audit 65 6 (⟨0x37,0x1d8000000000000000000000000000000000,0x2fe,0x60⟩ : State) [5,4,2,1,0] = some 340 := auditStep (k:=64) (x:=6) (u:=0) (v:=340) (s:=(⟨0x37,0x1d8000000000000000000000000000000000,0x2fe,0x60⟩ : State)) (p:=[5,4,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart41⟩)

private theorem apart43 : audit 62 9 (⟨0xd7,0x1d6000000000000000000000000000000000,0x2ffe,0x1c0⟩ : State) [7,6,4,2,1,0] = some 173 := by decide +kernel

private theorem apart44 : audit 63 8 (⟨0xd7,0x1d6000000000000000000000000000000000,0x2ffe,0x1c0⟩ : State) [7,6,4,2,1,0] = some 173 := auditStep (k:=62) (x:=8) (u:=0) (v:=173) (s:=(⟨0xd7,0x1d6000000000000000000000000000000000,0x2ffe,0x1c0⟩ : State)) (p:=[7,6,4,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart43⟩)

private theorem apart45 : audit 62 9 (⟨0x157,0x1d5000000000000000000000000000000000,0x57fe,0x540⟩ : State) [8,6,4,2,1,0] = some 32 := by decide +kernel

private theorem apart46 : audit 62 9 (⟨0x57,0x1d4000000000000000000000000000000000,0x5fe,0x40⟩ : State) [6,4,2,1,0] = some 16 := by decide +kernel

private theorem apart47 : audit 63 8 (⟨0x57,0x1d4000000000000000000000000000000000,0x5fe,0x40⟩ : State) [6,4,2,1,0] = some 49 := auditStep (k:=62) (x:=8) (u:=33) (v:=16) (s:=(⟨0x57,0x1d4000000000000000000000000000000000,0x5fe,0x40⟩ : State)) (p:=[6,4,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,32,apart45,rfl⟩) (Or.inr ⟨by decide +kernel,apart46⟩)

private theorem apart48 : audit 64 7 (⟨0x57,0x1d4000000000000000000000000000000000,0x5fe,0x40⟩ : State) [6,4,2,1,0] = some 223 := auditStep (k:=63) (x:=7) (u:=174) (v:=49) (s:=(⟨0x57,0x1d4000000000000000000000000000000000,0x5fe,0x40⟩ : State)) (p:=[6,4,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,173,apart44,rfl⟩) (Or.inr ⟨by decide +kernel,apart47⟩)

private theorem apart49 : audit 62 9 (⟨0x197,0x1d3000000000000000000000000000000000,0x9ffe,0x300⟩ : State) [8,7,4,2,1,0] = some 73 := by decide +kernel

private theorem apart50 : audit 62 9 (⟨0x97,0x1d2000000000000000000000000000000000,0xbfe,0x0⟩ : State) [7,4,2,1,0] = some 6 := by decide +kernel

private theorem apart51 : audit 63 8 (⟨0x97,0x1d2000000000000000000000000000000000,0xbfe,0x0⟩ : State) [7,4,2,1,0] = some 80 := auditStep (k:=62) (x:=8) (u:=74) (v:=6) (s:=(⟨0x97,0x1d2000000000000000000000000000000000,0xbfe,0x0⟩ : State)) (p:=[7,4,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,73,apart49,rfl⟩) (Or.inr ⟨by decide +kernel,apart50⟩)

private theorem apart52 : audit 64 7 (⟨0x17,0x1d0000000000000000000000000000000000,0x7e,0x0⟩ : State) [4,2,1,0] = some 81 := auditStep (k:=63) (x:=7) (u:=81) (v:=0) (s:=(⟨0x17,0x1d0000000000000000000000000000000000,0x7e,0x0⟩ : State)) (p:=[4,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,80,apart51,rfl⟩) (Or.inl (by decide +kernel))

private theorem apart53 : audit 65 6 (⟨0x17,0x1d0000000000000000000000000000000000,0x7e,0x0⟩ : State) [4,2,1,0] = some 305 := auditStep (k:=64) (x:=6) (u:=224) (v:=81) (s:=(⟨0x17,0x1d0000000000000000000000000000000000,0x7e,0x0⟩ : State)) (p:=[4,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,223,apart48,rfl⟩) (Or.inr ⟨by decide +kernel,apart52⟩)

private theorem apart54 : audit 66 5 (⟨0x17,0x1d0000000000000000000000000000000000,0x7e,0x0⟩ : State) [4,2,1,0] = some 646 := auditStep (k:=65) (x:=5) (u:=341) (v:=305) (s:=(⟨0x17,0x1d0000000000000000000000000000000000,0x7e,0x0⟩ : State)) (p:=[4,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,340,apart42,rfl⟩) (Or.inr ⟨by decide +kernel,apart53⟩)

private theorem apart55 : audit 62 9 (⟨0x167,0x1cd000000000000000000000000000000000,0x6fee,0x1c0⟩ : State) [8,6,5,2,1,0] = some 182 := by decide +kernel

private theorem apart56 : audit 62 9 (⟨0x67,0x1cc000000000000000000000000000000000,0x9ee,0xc0⟩ : State) [6,5,2,1,0] = some 8 := by decide +kernel

private theorem apart57 : audit 63 8 (⟨0x67,0x1cc000000000000000000000000000000000,0x9ee,0xc0⟩ : State) [6,5,2,1,0] = some 191 := auditStep (k:=62) (x:=8) (u:=183) (v:=8) (s:=(⟨0x67,0x1cc000000000000000000000000000000000,0x9ee,0xc0⟩ : State)) (p:=[6,5,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,182,apart55,rfl⟩) (Or.inr ⟨by decide +kernel,apart56⟩)

private theorem apart58 : audit 64 7 (⟨0x67,0x1cc000000000000000000000000000000000,0x9ee,0xc0⟩ : State) [6,5,2,1,0] = some 191 := auditStep (k:=63) (x:=7) (u:=0) (v:=191) (s:=(⟨0x67,0x1cc000000000000000000000000000000000,0x9ee,0xc0⟩ : State)) (p:=[6,5,2,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart57⟩)

private theorem apart59 : audit 62 9 (⟨0x1a7,0x1cb000000000000000000000000000000000,0xb7ee,0x380⟩ : State) [8,7,5,2,1,0] = some 94 := by decide +kernel

private theorem apart60 : audit 62 9 (⟨0xa7,0x1ca000000000000000000000000000000000,0x13ee,0x80⟩ : State) [7,5,2,1,0] = some 78 := by decide +kernel

private theorem apart61 : audit 63 8 (⟨0xa7,0x1ca000000000000000000000000000000000,0x13ee,0x80⟩ : State) [7,5,2,1,0] = some 173 := auditStep (k:=62) (x:=8) (u:=95) (v:=78) (s:=(⟨0xa7,0x1ca000000000000000000000000000000000,0x13ee,0x80⟩ : State)) (p:=[7,5,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,94,apart59,rfl⟩) (Or.inr ⟨by decide +kernel,apart60⟩)

private theorem apart62 : audit 62 9 (⟨0x127,0x1c9000000000000000000000000000000000,0x27ee,0x0⟩ : State) [8,5,2,1,0] = some 39 := by decide +kernel

private theorem apart63 : audit 63 8 (⟨0x27,0x1c8000000000000000000000000000000000,0xee,0x0⟩ : State) [5,2,1,0] = some 40 := auditStep (k:=62) (x:=8) (u:=40) (v:=0) (s:=(⟨0x27,0x1c8000000000000000000000000000000000,0xee,0x0⟩ : State)) (p:=[5,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,39,apart62,rfl⟩) (Or.inl (by decide +kernel))

private theorem apart64 : audit 64 7 (⟨0x27,0x1c8000000000000000000000000000000000,0xee,0x0⟩ : State) [5,2,1,0] = some 214 := auditStep (k:=63) (x:=7) (u:=174) (v:=40) (s:=(⟨0x27,0x1c8000000000000000000000000000000000,0xee,0x0⟩ : State)) (p:=[5,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,173,apart61,rfl⟩) (Or.inr ⟨by decide +kernel,apart63⟩)

private theorem apart65 : audit 65 6 (⟨0x27,0x1c8000000000000000000000000000000000,0xee,0x0⟩ : State) [5,2,1,0] = some 406 := auditStep (k:=64) (x:=6) (u:=192) (v:=214) (s:=(⟨0x27,0x1c8000000000000000000000000000000000,0xee,0x0⟩ : State)) (p:=[5,2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,191,apart58,rfl⟩) (Or.inr ⟨by decide +kernel,apart64⟩)

private theorem apart66 : audit 66 5 (⟨0x7,0x1c0000000000000000000000000000000000,0xe,0x0⟩ : State) [2,1,0] = some 407 := auditStep (k:=65) (x:=5) (u:=407) (v:=0) (s:=(⟨0x7,0x1c0000000000000000000000000000000000,0xe,0x0⟩ : State)) (p:=[2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,406,apart65,rfl⟩) (Or.inl (by decide +kernel))

private theorem apart67 : audit 67 4 (⟨0x7,0x1c0000000000000000000000000000000000,0xe,0x0⟩ : State) [2,1,0] = some 1054 := auditStep (k:=66) (x:=4) (u:=647) (v:=407) (s:=(⟨0x7,0x1c0000000000000000000000000000000000,0xe,0x0⟩ : State)) (p:=[2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,646,apart54,rfl⟩) (Or.inr ⟨by decide +kernel,apart66⟩)

private theorem apart68 : audit 68 3 (⟨0x7,0x1c0000000000000000000000000000000000,0xe,0x0⟩ : State) [2,1,0] = some 4183 := auditStep (k:=67) (x:=3) (u:=3129) (v:=1054) (s:=(⟨0x7,0x1c0000000000000000000000000000000000,0xe,0x0⟩ : State)) (p:=[2,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,3128,apart35,rfl⟩) (Or.inr ⟨by decide +kernel,apart67⟩)

private theorem apart69 : audit 62 9 (⟨0x7b,0x1bc000000000000000000000000000000000,0xffa,0x2f0⟩ : State) [6,5,4,3,1,0] = some 263 := by decide +kernel

private theorem apart70 : audit 63 8 (⟨0x7b,0x1bc000000000000000000000000000000000,0xffa,0x2f0⟩ : State) [6,5,4,3,1,0] = some 263 := auditStep (k:=62) (x:=8) (u:=0) (v:=263) (s:=(⟨0x7b,0x1bc000000000000000000000000000000000,0xffa,0x2f0⟩ : State)) (p:=[6,5,4,3,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart69⟩)

private theorem apart71 : audit 64 7 (⟨0x7b,0x1bc000000000000000000000000000000000,0xffa,0x2f0⟩ : State) [6,5,4,3,1,0] = some 263 := auditStep (k:=63) (x:=7) (u:=0) (v:=263) (s:=(⟨0x7b,0x1bc000000000000000000000000000000000,0xffa,0x2f0⟩ : State)) (p:=[6,5,4,3,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart70⟩)

private theorem apart72 : audit 62 9 (⟨0xbb,0x1ba000000000000000000000000000000000,0x1ffa,0x1b0⟩ : State) [7,5,4,3,1,0] = some 208 := by decide +kernel

private theorem apart73 : audit 63 8 (⟨0xbb,0x1ba000000000000000000000000000000000,0x1ffa,0x1b0⟩ : State) [7,5,4,3,1,0] = some 208 := auditStep (k:=62) (x:=8) (u:=0) (v:=208) (s:=(⟨0xbb,0x1ba000000000000000000000000000000000,0x1ffa,0x1b0⟩ : State)) (p:=[7,5,4,3,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart72⟩)

private theorem apart74 : audit 62 9 (⟨0x13b,0x1b9000000000000000000000000000000000,0x3bfa,0x330⟩ : State) [8,5,4,3,1,0] = some 383 := by decide +kernel

private theorem apart75 : audit 62 9 (⟨0x3b,0x1b8000000000000000000000000000000000,0x3fa,0x30⟩ : State) [5,4,3,1,0] = some 63 := by decide +kernel

private theorem apart76 : audit 63 8 (⟨0x3b,0x1b8000000000000000000000000000000000,0x3fa,0x30⟩ : State) [5,4,3,1,0] = some 447 := auditStep (k:=62) (x:=8) (u:=384) (v:=63) (s:=(⟨0x3b,0x1b8000000000000000000000000000000000,0x3fa,0x30⟩ : State)) (p:=[5,4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,383,apart74,rfl⟩) (Or.inr ⟨by decide +kernel,apart75⟩)

private theorem apart77 : audit 64 7 (⟨0x3b,0x1b8000000000000000000000000000000000,0x3fa,0x30⟩ : State) [5,4,3,1,0] = some 656 := auditStep (k:=63) (x:=7) (u:=209) (v:=447) (s:=(⟨0x3b,0x1b8000000000000000000000000000000000,0x3fa,0x30⟩ : State)) (p:=[5,4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,208,apart73,rfl⟩) (Or.inr ⟨by decide +kernel,apart76⟩)

private theorem apart78 : audit 65 6 (⟨0x3b,0x1b8000000000000000000000000000000000,0x3fa,0x30⟩ : State) [5,4,3,1,0] = some 920 := auditStep (k:=64) (x:=6) (u:=264) (v:=656) (s:=(⟨0x3b,0x1b8000000000000000000000000000000000,0x3fa,0x30⟩ : State)) (p:=[5,4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,263,apart71,rfl⟩) (Or.inr ⟨by decide +kernel,apart77⟩)

private theorem apart79 : audit 62 9 (⟨0x15b,0x1b5000000000000000000000000000000000,0x5ffa,0x290⟩ : State) [8,6,4,3,1,0] = some 34 := by decide +kernel

private theorem apart80 : audit 62 9 (⟨0x5b,0x1b4000000000000000000000000000000000,0x6fa,0x90⟩ : State) [6,4,3,1,0] = some 145 := by decide +kernel

private theorem apart81 : audit 63 8 (⟨0x5b,0x1b4000000000000000000000000000000000,0x6fa,0x90⟩ : State) [6,4,3,1,0] = some 180 := auditStep (k:=62) (x:=8) (u:=35) (v:=145) (s:=(⟨0x5b,0x1b4000000000000000000000000000000000,0x6fa,0x90⟩ : State)) (p:=[6,4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,34,apart79,rfl⟩) (Or.inr ⟨by decide +kernel,apart80⟩)

private theorem apart82 : audit 64 7 (⟨0x5b,0x1b4000000000000000000000000000000000,0x6fa,0x90⟩ : State) [6,4,3,1,0] = some 180 := auditStep (k:=63) (x:=7) (u:=0) (v:=180) (s:=(⟨0x5b,0x1b4000000000000000000000000000000000,0x6fa,0x90⟩ : State)) (p:=[6,4,3,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart81⟩)

private theorem apart83 : audit 62 9 (⟨0x19b,0x1b3000000000000000000000000000000000,0x9fba,0x990⟩ : State) [8,7,4,3,1,0] = some 255 := by decide +kernel

private theorem apart84 : audit 62 9 (⟨0x9b,0x1b2000000000000000000000000000000000,0xdba,0x90⟩ : State) [7,4,3,1,0] = some 67 := by decide +kernel

private theorem apart85 : audit 63 8 (⟨0x9b,0x1b2000000000000000000000000000000000,0xdba,0x90⟩ : State) [7,4,3,1,0] = some 323 := auditStep (k:=62) (x:=8) (u:=256) (v:=67) (s:=(⟨0x9b,0x1b2000000000000000000000000000000000,0xdba,0x90⟩ : State)) (p:=[7,4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,255,apart83,rfl⟩) (Or.inr ⟨by decide +kernel,apart84⟩)

private theorem apart86 : audit 62 9 (⟨0x11b,0x1b1000000000000000000000000000000000,0x1bba,0x10⟩ : State) [8,4,3,1,0] = some 54 := by decide +kernel

private theorem apart87 : audit 62 9 (⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State) [4,3,1,0] = some 54 := by decide +kernel

private theorem apart88 : audit 63 8 (⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State) [4,3,1,0] = some 109 := auditStep (k:=62) (x:=8) (u:=55) (v:=54) (s:=(⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State)) (p:=[4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,54,apart86,rfl⟩) (Or.inr ⟨by decide +kernel,apart87⟩)

private theorem apart89 : audit 64 7 (⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State) [4,3,1,0] = some 433 := auditStep (k:=63) (x:=7) (u:=324) (v:=109) (s:=(⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State)) (p:=[4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,323,apart85,rfl⟩) (Or.inr ⟨by decide +kernel,apart88⟩)

private theorem apart90 : audit 65 6 (⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State) [4,3,1,0] = some 614 := auditStep (k:=64) (x:=6) (u:=181) (v:=433) (s:=(⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State)) (p:=[4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,180,apart82,rfl⟩) (Or.inr ⟨by decide +kernel,apart89⟩)

private theorem apart91 : audit 66 5 (⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State) [4,3,1,0] = some 1535 := auditStep (k:=65) (x:=5) (u:=921) (v:=614) (s:=(⟨0x1b,0x1b0000000000000000000000000000000000,0xba,0x10⟩ : State)) (p:=[4,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,920,apart78,rfl⟩) (Or.inr ⟨by decide +kernel,apart90⟩)

private theorem apart92 : audit 62 9 (⟨0xeb,0x1ae000000000000000000000000000000000,0x3ffa,0x1c0⟩ : State) [7,6,5,3,1,0] = some 313 := by decide +kernel

private theorem apart93 : audit 63 8 (⟨0xeb,0x1ae000000000000000000000000000000000,0x3ffa,0x1c0⟩ : State) [7,6,5,3,1,0] = some 313 := auditStep (k:=62) (x:=8) (u:=0) (v:=313) (s:=(⟨0xeb,0x1ae000000000000000000000000000000000,0x3ffa,0x1c0⟩ : State)) (p:=[7,6,5,3,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart92⟩)

private theorem apart94 : audit 62 9 (⟨0x16b,0x1ad000000000000000000000000000000000,0x6bfa,0xb40⟩ : State) [8,6,5,3,1,0] = some 177 := by decide +kernel

private theorem apart95 : audit 62 9 (⟨0x6b,0x1ac000000000000000000000000000000000,0xbfa,0x40⟩ : State) [6,5,3,1,0] = some 136 := by decide +kernel

private theorem apart96 : audit 63 8 (⟨0x6b,0x1ac000000000000000000000000000000000,0xbfa,0x40⟩ : State) [6,5,3,1,0] = some 314 := auditStep (k:=62) (x:=8) (u:=178) (v:=136) (s:=(⟨0x6b,0x1ac000000000000000000000000000000000,0xbfa,0x40⟩ : State)) (p:=[6,5,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,177,apart94,rfl⟩) (Or.inr ⟨by decide +kernel,apart95⟩)

private theorem apart97 : audit 64 7 (⟨0x6b,0x1ac000000000000000000000000000000000,0xbfa,0x40⟩ : State) [6,5,3,1,0] = some 628 := auditStep (k:=63) (x:=7) (u:=314) (v:=314) (s:=(⟨0x6b,0x1ac000000000000000000000000000000000,0xbfa,0x40⟩ : State)) (p:=[6,5,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,313,apart93,rfl⟩) (Or.inr ⟨by decide +kernel,apart96⟩)

private theorem apart98 : audit 62 9 (⟨0xab,0x1aa000000000000000000000000000000000,0x15fa,0x100⟩ : State) [7,5,3,1,0] = some 1 := by decide +kernel

private theorem apart99 : audit 63 8 (⟨0xab,0x1aa000000000000000000000000000000000,0x15fa,0x100⟩ : State) [7,5,3,1,0] = some 1 := auditStep (k:=62) (x:=8) (u:=0) (v:=1) (s:=(⟨0xab,0x1aa000000000000000000000000000000000,0x15fa,0x100⟩ : State)) (p:=[7,5,3,1,0]) (Or.inl (by decide +kernel)) (Or.inr ⟨by decide +kernel,apart98⟩)

private theorem apart100 : audit 64 7 (⟨0x2b,0x1a8000000000000000000000000000000000,0x17a,0x0⟩ : State) [5,3,1,0] = some 2 := auditStep (k:=63) (x:=7) (u:=2) (v:=0) (s:=(⟨0x2b,0x1a8000000000000000000000000000000000,0x17a,0x0⟩ : State)) (p:=[5,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,1,apart99,rfl⟩) (Or.inl (by decide +kernel))

private theorem apart101 : audit 65 6 (⟨0x2b,0x1a8000000000000000000000000000000000,0x17a,0x0⟩ : State) [5,3,1,0] = some 631 := auditStep (k:=64) (x:=6) (u:=629) (v:=2) (s:=(⟨0x2b,0x1a8000000000000000000000000000000000,0x17a,0x0⟩ : State)) (p:=[5,3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,628,apart97,rfl⟩) (Or.inr ⟨by decide +kernel,apart100⟩)

private theorem apart102 : audit 66 5 (⟨0xb,0x1a0000000000000000000000000000000000,0x1a,0x0⟩ : State) [3,1,0] = some 632 := auditStep (k:=65) (x:=5) (u:=632) (v:=0) (s:=(⟨0xb,0x1a0000000000000000000000000000000000,0x1a,0x0⟩ : State)) (p:=[3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,631,apart101,rfl⟩) (Or.inl (by decide +kernel))

private theorem apart103 : audit 67 4 (⟨0xb,0x1a0000000000000000000000000000000000,0x1a,0x0⟩ : State) [3,1,0] = some 2168 := auditStep (k:=66) (x:=4) (u:=1536) (v:=632) (s:=(⟨0xb,0x1a0000000000000000000000000000000000,0x1a,0x0⟩ : State)) (p:=[3,1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,1535,apart91,rfl⟩) (Or.inr ⟨by decide +kernel,apart102⟩)

private theorem apart104 : audit 68 3 (⟨0x3,0x180000000000000000000000000000000000,0x2,0x0⟩ : State) [1,0] = some 2169 := auditStep (k:=67) (x:=3) (u:=2169) (v:=0) (s:=(⟨0x3,0x180000000000000000000000000000000000,0x2,0x0⟩ : State)) (p:=[1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,2168,apart103,rfl⟩) (Or.inl (by decide +kernel))

private theorem apart105 : audit 69 2 (⟨0x3,0x180000000000000000000000000000000000,0x2,0x0⟩ : State) [1,0] = some 6353 := auditStep (k:=68) (x:=2) (u:=4184) (v:=2169) (s:=(⟨0x3,0x180000000000000000000000000000000000,0x2,0x0⟩ : State)) (p:=[1,0]) (Or.inr ⟨by decide +kernel,by decide +kernel,4183,apart68,rfl⟩) (Or.inr ⟨by decide +kernel,apart104⟩)

private theorem apart106 : audit 70 1 (⟨0x1,0x100000000000000000000000000000000000,0x0,0x0⟩ : State) [0] = some 6354 := auditStep (k:=69) (x:=1) (u:=6354) (v:=0) (s:=(⟨0x1,0x100000000000000000000000000000000000,0x0,0x0⟩ : State)) (p:=[0]) (Or.inr ⟨by decide +kernel,by decide +kernel,6353,apart105,rfl⟩) (Or.inl (by decide +kernel))

private theorem apart107 : audit 71 0 (⟨0x0,0x0,0x0,0x0⟩ : State) [] = some 6355 := auditStep (k:=70) (x:=0) (u:=6355) (v:=0) (s:=(⟨0x0,0x0,0x0,0x0⟩ : State)) (p:=[]) (Or.inr ⟨by decide +kernel,by decide +kernel,6354,apart106,rfl⟩) (Or.inl (by decide +kernel))

private theorem allRoots : check 71 0 0 (⟨0,0,0,0⟩ : State) = true ∧
    catalogSize 71 0 (⟨0,0,0,0⟩ : State) = 6355 ∧
    validate 71 0 (⟨0,0,0,0⟩ : State) [] = true :=
  audit_projects (k:=71) (x:=0) (s:=(⟨0,0,0,0⟩ : State)) (p:=[]) (n:=6355) apart107

theorem bounds (A : Nat → Prop) (d : Nat) (last : A d) (within : ∀ a, A a → a ≤ d)
    (cover : ∀ n ≤ d, ∃ a b, A a ∧ A b ∧ a+b=n) (cap : ¬Six A) :
    d ≤ 52 ∧ ∃ l : List Nat, l.length ≤ 14 ∧ ∀ a, A a → a ∈ l := by
  apply bounds_sound last within cover cap 71 0 [] (⟨0,0,0,0⟩ : State) (by decide) (by omega) (by simp)
    (by exact ⟨by simp,by simp,by simp⟩) allRoots.1

end OMA.Erdos28GlobalFive

namespace OMA.Erdos28GlobalFive

private theorem notSix (S : Finset Nat)
    (cap : ∀ n, ((Finset.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card ≤ 5) :
    ¬Six (fun a => a ∈ S) := by
  rintro ⟨n, _, l, hl, hd, hw⟩
  let f : Nat → Nat × Nat := fun a => (a,n-a)
  have fi : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  have card := Finset.card_image_of_injective l.toFinset fi
  rw [List.toFinset_card_of_nodup hd, hl] at card
  have sub : l.toFinset.image f ⊆ (Finset.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, h₁, h₂, he⟩ := hw a (List.mem_toFinset.mp ha)
    have hb : n-a=b := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (by change a+(n-a)=n; omega),
      h₁, by change n-a ∈ S; simpa only [hb] using h₂⟩
  have hb := Finset.card_le_card sub
  have := cap n
  omega

/-- A finite basis that covers every sum through its largest element and has globally
at most five ordered representations of each sum has degree at most 52 and size at most 14. -/
theorem finite_bounds (d : Nat) (S : Finset Nat) (last : d ∈ S) (within : S ⊆ Finset.Iic d)
    (cov : ∀ n ≤ d, ∃ a ∈ S, ∃ b ∈ S, a+b=n)
    (cap : ∀ n, ((Finset.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card ≤ 5) :
    d ≤ 52 ∧ S.card ≤ 14 := by
  obtain ⟨deg,l,hl,hmem⟩ := bounds (fun a => a ∈ S) d last
    (fun _ ha => Finset.mem_Iic.mp (within ha)) (by
      intro n hn
      obtain ⟨a,ha,b,hb,he⟩ := cov n hn
      exact ⟨a,b,ha,hb,he⟩) (notSix S cap)
  have sub : S ⊆ l.toFinset := fun a ha => List.mem_toFinset.mpr (hmem a ha)
  have hcard := Finset.card_le_card sub
  have hlen := List.toFinset_card_le l
  exact ⟨deg, by omega⟩

end OMA.Erdos28GlobalFive

namespace OMA.Erdos28GlobalFive

private theorem length_catalog (k x : Nat) (s : State) (taken : Finset Nat) :
    (catalog k x s taken).length = catalogSize k x s := by
  induction k generalizing x s taken with
  | zero => rfl
  | succ k ih =>
    simp only [catalog, catalogSize, List.length_append]
    by_cases stop : includeStops s x = true <;> by_cases skip : (pairs s x == 0) = true <;>
      simp [stop,skip,ih, Nat.add_comm]

private theorem catalog_contains (S : Finset Nat) (d : Nat) (last : d ∈ S)
    (within : ∀ a ∈ S, a ≤ d) (cover : ∀ n ≤ d, CoveredAt (fun a => a ∈ S) n)
    (cap : ¬ Six (fun a => a ∈ S)) (k x : Nat) (s : State) (taken : Finset Nat)
    (lim : x+k ≤ 71) (fuel : d < x+k) (hx : x ≤ d)
    (seen : ∀ a < x, a ∈ S → a ∈ taken) (sub : taken ⊆ S)
    (fit : Fits (fun a => a ∈ S) x s) : S ∈ catalog k x s taken := by
  induction k generalizing x s taken with
  | zero => omega
  | succ k ih =>
    have small : x ≤ 140 := by omega
    rw [catalog, List.mem_append]
    by_cases ha : x ∈ S
    · left
      have ns : includeStops s x ≠ true := fun hs =>
        cap (crowdedSound (addFits fit small ha) (Bool.and_eq_true_iff.mp hs).2)
      simp [ns]
      have seen' : ∀ a < x+1, a ∈ S → a ∈ insert x taken := by
        intro a hab hA
        by_cases eq : a=x
        · exact Finset.mem_insert.mpr (Or.inl eq)
        · exact Finset.mem_insert.mpr (Or.inr (seen a (by omega) hA))
      have sub' : insert x taken ⊆ S := Finset.insert_subset ha sub
      by_cases eq : x=d
      · exact Or.inl (Finset.Subset.antisymm (fun a hA => seen' a (by have := within a hA; omega) hA) sub')
      · exact Or.inr (ih (x+1) _ _ (by omega) (by omega) (by omega) seen' sub' (addFits fit small ha))
    · right
      have ns : (pairs s x == 0) ≠ true := fun hs =>
        cannotSkip fit small (cover x hx) ha (beq_iff_eq.mp hs)
      simp [ns]
      have nd : x ≠ d := by rintro rfl; exact ha last
      have seen' : ∀ a < x+1, a ∈ S → a ∈ taken := by
        intro a hlt hA
        have ne : a ≠ x := by rintro rfl; exact ha hA
        exact seen a (by omega) hA
      exact ih (x+1) s taken (by omega) (by omega) (by omega) seen' sub (skipFits fit ha)

/-- Every exact basis of global ordered representation cap five occurs in this finite catalog. -/
def finiteCatalog : List (Finset Nat) := catalog 71 0 ⟨0,0,0,0⟩ ∅

theorem finiteCatalog_length : finiteCatalog.length = 6355 :=
  (length_catalog ..).trans allRoots.2.1

theorem mem_finiteCatalog (d : Nat) (S : Finset Nat) (last : d ∈ S) (within : S ⊆ Finset.Iic d)
    (cov : ∀ n ≤ d, ∃ a ∈ S, ∃ b ∈ S, a+b=n)
    (cap : ∀ n, ((Finset.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card ≤ 5) :
    S ∈ finiteCatalog := by
  have h := (finite_bounds d S last within cov cap).1
  apply catalog_contains S d last (fun _ ha => Finset.mem_Iic.mp (within ha)) _ (notSix S cap)
    71 0 _ ∅ (by decide) (by omega) (by omega) (by simp) (by simp) (by exact ⟨by simp,by simp,by simp⟩)
  intro n hn
  obtain ⟨a,ha,b,hb,he⟩ := cov n hn
  exact ⟨a,b,ha,hb,he⟩

end OMA.Erdos28GlobalFive

namespace OMA.Erdos28GlobalFive

private theorem atMostBits_sound {k v : Nat} (hk : atMostBits k v = true) :
    ∃ l : List Nat, l.length ≤ k ∧ ∀ i, v.testBit i = true → i ∈ l := by
  induction k generalizing v with
  | zero =>
    have hz : v=0 := beq_iff_eq.mp hk
    subst v
    exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    rcases Bool.or_eq_true_iff.mp hk with hz|hr
    · have hv : v=0 := beq_iff_eq.mp hz
      subst v
      exact ⟨[], by simp, by simp⟩
    · obtain ⟨l,hl,hs⟩ := ih hr
      refine ⟨(pick v)::l, by simp; omega, ?_⟩
      intro i hi
      by_cases he : i=pick v
      · exact List.mem_cons.mpr (Or.inl he)
      · apply List.mem_cons.mpr ∘ Or.inr
        apply hs
        rw [Nat.testBit_xor, singleBit, decide_eq_false (Ne.symm he), Bool.xor_false]
        exact hi

private def ordered (S : Finset Nat) (n : Nat) : Finset (Nat × Nat) :=
  (Finset.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)

private theorem reflectedPairs {S : Finset Nat} {x n : Nat} {s : State}
    (fit : Fits (fun a => a ∈ S) x s) (upto : ∀ a ∈ S, a < x)
    (small : x ≤ 71) (hn : n ≤ 140) {a b : Nat}
    (ha : a ∈ S) (hb : b ∈ S) (sum : a+b=n) :
    (pairs s n).testBit a = true := by
  obtain ⟨hp,_⟩ := fit.complete a (upto _ ha) ha
  obtain ⟨_,hr⟩ := fit.complete b (upto _ hb) hb
  simp only [pairs,Nat.testBit_and,Nat.testBit_shiftRight,Bool.and_eq_true_iff]
  exact ⟨hp, by simpa only [show 140-n+a=140-b by have := upto _ hb; omega] using hr⟩

private theorem boundedPairCount {S : Finset Nat} {x n : Nat} {s : State}
    (fit : Fits (fun a => a ∈ S) x s) (upto : ∀ a ∈ S, a < x)
    (small : x ≤ 71) (hn : n ≤ 140) (bits : atMostBits 5 (pairs s n) = true) :
    (ordered S n).card ≤ 5 := by
  obtain ⟨l,hl,hs⟩ := atMostBits_sound bits
  let f : Nat → Nat × Nat := fun a => (a,n-a)
  have incl : ordered S n ⊆ l.toFinset.image f := by
    intro p hp
    obtain ⟨hh,ha,hb⟩ := Finset.mem_filter.mp hp
    have he := Finset.mem_antidiagonal.mp hh
    apply Finset.mem_image.mpr
    refine ⟨p.1,List.mem_toFinset.mpr (hs p.1 (reflectedPairs fit upto small hn ha hb he)), ?_⟩
    apply Prod.ext
    · rfl
    · change n-p.1=p.2
      omega
  have h₁ := Finset.card_le_card incl
  have h₂ := Finset.card_image_le (s:=l.toFinset) (f:=f)
  have h₃ := List.toFinset_card_le l
  omega

private theorem broaden {P : Finset Nat} {x : Nat} {s : State} (h : Fits (fun a => a ∈ P) x s) :
    Fits (fun a => a ∈ insert x P) x s := by
  refine ⟨?_, fun a ha => Finset.mem_insert_of_mem (h.forward a ha), ?_⟩
  · intro a hx hi
    rcases Finset.mem_insert.mp hi with eq|ha
    · omega
    · exact h.complete _ hx ha
  · intro i hi
    obtain ⟨b,hb,hA,he⟩ := h.backward _ hi
    exact ⟨b,hb,Finset.mem_insert_of_mem hA,he⟩

private def Basis (S : Finset Nat) (d : Nat) : Prop :=
  d ∈ S ∧ (∀ a ∈ S, a ≤ d) ∧ (∀ n ≤ d, CoveredAt (fun a => a ∈ S) n) ∧
  ∀ n, (ordered S n).card ≤ 5

private theorem validate_sound (k x : Nat) (s : State) (p : List Nat)
    (lim : x+k ≤ 71) (fit : Fits (fun a => a ∈ p.toFinset) x s)
    (upto : ∀ a ∈ p.toFinset, a < x)
    (cover : ∀ n < x, CoveredAt (fun a => a ∈ p.toFinset) n)
    (cap : ∀ n, (ordered p.toFinset n).card ≤ 5)
    (hc : validate k x s p = true) :
    ∀ S ∈ catalog k x s p.toFinset, ∃ d, Basis S d := by
  induction k generalizing x s p with
  | zero => simp [catalog]
  | succ k ih =>
    have hx : x ≤ 70 := by omega
    obtain ⟨hplus,hskip⟩ := Bool.and_eq_true_iff.mp hc
    intro S hS
    rw [catalog, List.mem_append] at hS
    rcases hS with left|right
    · split at left
      next => simp at left
      next nh =>
        obtain ⟨valid, nextOk⟩ := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hplus).resolve_left nh)
        let Q := (x::p).toFinset
        have ins : Q = insert x p.toFinset := by simp [Q]
        have fit' : Fits (fun a => a ∈ Q) (x+1) (add s x) := by
          rw [ins]; exact addFits (broaden fit) (by omega) (Finset.mem_insert_self ..)
        have upt' : ∀ a ∈ Q, a < x+1 := by
          intro a ha
          rw [ins,Finset.mem_insert] at ha
          rcases ha with rfl|ha <;> first | omega | have := upto a ha; omega
        have lift {a} (ha : a ∈ p.toFinset) : a ∈ Q := ins ▸ Finset.mem_insert_of_mem ha
        have xmem : x ∈ Q := ins ▸ Finset.mem_insert_self ..
        have zero : 0 ∈ Q := by
          by_cases e : x = 0
          · simpa [e] using xmem
          · obtain ⟨a,b,ha,_,he⟩ := cover 0 (by omega)
            exact (show a=0 by omega) ▸ lift ha
        have cov' : ∀ n < x+1, CoveredAt (fun a => a ∈ Q) n := by
          intro n hn
          by_cases e : n=x
          · exact ⟨x,0,xmem,zero,by omega⟩
          · obtain ⟨a,b,ha,hb,he⟩ := cover n (by omega)
            exact ⟨a,b,lift ha,lift hb,he⟩
        have cap' : ∀ n, (ordered Q n).card ≤ 5 := by
          intro n
          by_cases h : ∃ a ∈ Q, x+a=n
          · obtain ⟨a,ha,he⟩ := h
            have hb := (List.all_eq_true.mp valid) a (List.mem_toFinset.mp ha)
            rw [he] at hb
            exact boundedPairCount fit' upt' (by omega) (by have := upt' a ha; omega) hb
          · have sub : ordered Q n ⊆ ordered p.toFinset n := by
              intro q hq
              obtain ⟨hh,ha,hb⟩ := Finset.mem_filter.mp hq
              have he := Finset.mem_antidiagonal.mp hh
              have ne₁ : q.1 ≠ x := fun e => h ⟨q.2,hb,by omega⟩
              have ne₂ : q.2 ≠ x := fun e => h ⟨q.1,ha,by omega⟩
              rw [ins,Finset.mem_insert] at ha hb
              exact Finset.mem_filter.mpr ⟨hh,ha.resolve_left ne₁,hb.resolve_left ne₂⟩
            exact (Finset.card_le_card sub).trans (cap n)
        rcases List.mem_cons.mp left with rfl|later
        · exact ⟨x, ins ▸ xmem, fun a ha => by rw [← ins] at ha; exact Nat.lt_succ_iff.mp (upt' _ ha),
            by rw [← ins]; exact fun n h => cov' n (by omega), by rw [← ins]; exact cap'⟩
        · apply ih (x+1) (add s x) (x::p) (by omega) fit' upt' cov' cap' nextOk
          change S ∈ catalog k (x+1) (add s x) Q
          rw [ins]
          exact later
    · split at right
      next => simp at right
      next nh =>
        have nz : pairs s x ≠ 0 := fun e => nh (beq_iff_eq.mpr e)
        obtain ⟨a,ha⟩ := Nat.exists_testBit_of_ne_zero nz
        obtain ⟨b, hA, hB, he⟩ := pairSound fit (by omega) ha
        have cov' : ∀ n < x+1, CoveredAt (fun a => a ∈ p.toFinset) n := by
          intro n hn
          by_cases eq : n=x
          · exact ⟨a,b,hA,hB,by omega⟩
          · exact cover n (by omega)
        have neg : ¬x ∈ p.toFinset := fun h => (Nat.lt_irrefl x) (upto x h)
        exact ih (x+1) s p (by omega) (skipFits fit neg)
          (fun a h => by have := upto a h; omega) cov' cap
          ((Bool.or_eq_true_iff.mp hskip).resolve_left nh) S right


private theorem catalog_shape (k x : Nat) (s : State) (p : Finset Nat)
    (bound : ∀ a ∈ p, a < x) :
    ∀ S ∈ catalog k x s p, (∀ a < x, a ∈ S ↔ a ∈ p) ∧ ∃ a ∈ S, x ≤ a := by
  induction k generalizing x s p with
  | zero => simp [catalog]
  | succ k ih =>
    intro S hs
    rw [catalog,List.mem_append] at hs
    have inc : ∀ a ∈ insert x p, a < x+1 := by
      intro a h
      rcases Finset.mem_insert.mp h with rfl|h
      · omega
      · have := bound a h; omega
    rcases hs with up|down
    · split at up
      next => simp at up
      next =>
        rcases List.mem_cons.mp up with rfl|up
        · refine ⟨fun a ha => ?_, x, Finset.mem_insert_self .., by omega⟩
          simp [show a ≠ x by omega]
        · obtain ⟨lo,y,hy,hi⟩ := ih _ _ _ inc S up
          refine ⟨fun a ha => ?_, y, hy, by omega⟩
          simpa only [Finset.mem_insert, show ¬ a=x by omega, false_or] using lo a (by omega)
    · split at down
      next => simp at down
      next =>
        obtain ⟨lo,y,hy,hi⟩ := ih _ _ _ (fun a h => by have := bound a h; omega) S down
        exact ⟨fun a ha => lo a (by omega), y, hy, by omega⟩

private theorem catalog_nodup (k x : Nat) (s : State) (p : Finset Nat)
    (bound : ∀ a ∈ p, a < x) : (catalog k x s p).Nodup := by
  induction k generalizing x s p with
  | zero => exact List.nodup_nil
  | succ k ih =>
    have inc : ∀ a ∈ insert x p, a < x+1 := by
      intro a h
      rcases Finset.mem_insert.mp h with rfl|h
      · omega
      · have := bound a h; omega
    have down : ∀ a ∈ p, a < x+1 := fun a h => by have := bound a h; omega
    let plus := catalog k (x+1) (add s x) (insert x p)
    let skip := catalog k (x+1) s p
    have hp : (insert x p :: plus).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,ih _ _ _ inc⟩
      intro bad
      obtain ⟨_, a, ha, hlarge⟩ := catalog_shape k _ _ _ inc _ bad
      have := inc a ha
      omega
    have hs : skip.Nodup := ih _ s p down
    have both : ((insert x p :: plus) ++ skip).Nodup := by
      apply List.Nodup.append hp hs
      intro S ha hb
      have xmem : x ∈ S := by
        rcases List.mem_cons.mp ha with rfl|ha
        · exact Finset.mem_insert_self ..
        · exact ((catalog_shape k _ _ _ inc _ ha).1 x (by omega)).mpr (Finset.mem_insert_self ..)
      have bad := ((catalog_shape k _ _ _ down _ hb).1 x (by omega)).mp xmem
      exact (Nat.lt_irrefl x) (bound _ bad)
    rw [catalog]
    by_cases t : includeStops s x = true <;> by_cases u : (pairs s x == 0) = true <;>
      simp only [t,u,if_true,if_false,List.nil_append,List.append_nil,List.nodup_nil] <;>
      first | trivial | exact hp | exact hs | exact both

theorem finiteCatalog_nodup : finiteCatalog.Nodup :=
  catalog_nodup 71 0 _ ∅ (by simp)

theorem finiteCatalog_spec (S : Finset Nat) : S ∈ finiteCatalog ↔ ∃ d,
    d ∈ S ∧ S ⊆ Finset.Iic d ∧ (∀ n ≤ d, ∃ a ∈ S, ∃ b ∈ S, a+b=n) ∧
    ∀ n, ((Finset.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card ≤ 5 := by
  constructor
  · intro h
    obtain ⟨d, last, within, cov, cap⟩ := validate_sound 71 0 (⟨0,0,0,0⟩ : State) []
      (by decide) (by exact ⟨by simp,by simp,by simp⟩) (by simp) (by simp) (by simp [ordered])
      allRoots.2.2 S h
    refine ⟨d,last,fun a ha => Finset.mem_Iic.mpr (within a ha), ?_, cap⟩
    intro n hn
    obtain ⟨a,b,ha,hb,he⟩ := cov n hn
    exact ⟨a,ha,b,hb,he⟩
  · rintro ⟨d,hd,hs,hc,hcap⟩
    exact mem_finiteCatalog d S hd hs hc hcap

/-- There are exactly 6,355 finite sets that cover all integers through their maximum
and have at most five ordered representations of every nonnegative integer. -/
theorem exact_family : ∃ F : Finset (Finset Nat), F.card = 6355 ∧
    ∀ S, S ∈ F ↔ ∃ d, d ∈ S ∧ S ⊆ Finset.Iic d ∧
      (∀ n ≤ d, ∃ a ∈ S, ∃ b ∈ S, a+b=n) ∧
      ∀ n, ((Finset.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card ≤ 5 := by
  refine ⟨finiteCatalog.toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup finiteCatalog_nodup,finiteCatalog_length]
  · intro S
    rw [List.mem_toFinset,finiteCatalog_spec]

end OMA.Erdos28GlobalFive

namespace OMA.Erdos28GlobalFive

/-- A single basis attains both upper bounds for global cap five. -/
def extremalBasis : Finset Nat := {0,1,2,3,5,6,11,14,18,24,31,38,45,52}

private def extremalCount (n : Nat) : Nat :=
  ((Finset.antidiagonal n).filter (fun p => p.1 ∈ extremalBasis ∧ p.2 ∈ extremalBasis)).card

theorem extremal_degree : 52 ∈ extremalBasis ∧ extremalBasis ⊆ Finset.Iic 52 := by decide

theorem extremal_size : extremalBasis.card = 14 := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 9000000 in
private theorem extremal_counts : ∀ n : Fin 105, extremalCount n ≤ 5 ∧
    (n.val ≤ 52 → 0 < extremalCount n) := by decide

theorem extremal_cover (n : Nat) (hn : n ≤ 52) :
    ∃ a ∈ extremalBasis, ∃ b ∈ extremalBasis, a+b=n := by
  have h := (extremal_counts ⟨n, by omega⟩).2 hn
  change 0 < ((Finset.antidiagonal n).filter
    (fun p => p.1 ∈ extremalBasis ∧ p.2 ∈ extremalBasis)).card at h
  obtain ⟨p,hp⟩ := Finset.card_pos.mp h
  obtain ⟨hs, ha, hb⟩ := Finset.mem_filter.mp hp
  exact ⟨p.1, ha, p.2, hb, Finset.mem_antidiagonal.mp hs⟩

theorem extremal_cap (n : Nat) :
    ((Finset.antidiagonal n).filter (fun p => p.1 ∈ extremalBasis ∧ p.2 ∈ extremalBasis)).card ≤ 5 := by
  by_cases hn : n ≤ 104
  · exact (extremal_counts ⟨n, by omega⟩).1
  · by_contra! h
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt h)
    obtain ⟨hs,ha,hb⟩ := Finset.mem_filter.mp hp
    have hsum := Finset.mem_antidiagonal.mp hs
    have h₁ := Finset.mem_Iic.mp (extremal_degree.2 ha)
    have h₂ := Finset.mem_Iic.mp (extremal_degree.2 hb)
    omega

end OMA.Erdos28GlobalFive
