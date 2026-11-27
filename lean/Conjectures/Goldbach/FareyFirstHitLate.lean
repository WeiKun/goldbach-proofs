import Mathlib
import Conjectures.Goldbach.FareyLateFirstHitFactorSwitch
import Conjectures.Goldbach.FareyLatePrimeSquareLoss

/-! A reduction of HD-8015 to a separated-prime count.

The two inverse marks have the same count in the full residue system.
`GoldbachLatePrimeCounts.separated_approximation` bounds the loss from
discarding squares and a fixed relative neighborhood of the diagonal.
`GoldbachLatePrimeCounts.from_separated_margin` combines this with the
cube-to-square-root density ratio. Its remaining hypothesis is a uniform
upper bound strictly below 7/4, in units of the terminal main term, for the
two oriented counts of separated factors. -/

namespace GoldbachLateWindow
open Finset Real
open scoped BigOperators
noncomputable section

def window (n : ℕ) := Icc ((n+2)/3) ((2*n)/3)
def cubeCut (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
def firstHit (n : ℕ) := (window n).filter fun u =>
  u.Coprime n ∧ cubeCut n < (u*(n-u)).minFac ∧ (u*(n-u)).minFac ≤ n.sqrt
def band (n : ℕ) := (range (n+1)).filter fun p => p.Prime ∧ n < p^3 ∧ p^2 ≤ n
def partners (n p : ℕ) := (Icc p n).filter fun q =>
  q.Prime ∧ p*q ∈ window n ∧ (p*q).Coprime n ∧ p ≤ (n-p*q).minFac
def distinctPairs (n : ℕ) := ∑ p ∈ band n, ((partners n p).filter (fun q => q ≠ p)).card
def squarePairs (n : ℕ) := ∑ p ∈ band n, ((partners n p).filter (fun q => q = p)).card
def closePairs (n w : ℕ) := ∑ p ∈ band n,
  ((partners n p).filter (fun q => p < q ∧ q ≤ p+w)).card
def farPairs (n w : ℕ) := ∑ p ∈ band n,
  ((partners n p).filter (fun q => p+w < q)).card

theorem cut_lt (n p : ℕ) : cubeCut n < p ↔ n < p^3 := by
  rw [cubeCut, Nat.floor_lt (by positivity), one_div, Real.rpow_inv_lt_iff_of_pos
    (by positivity) (by positivity) (by norm_num)]
  rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  exact_mod_cast (Iff.rfl : n < p^3 ↔ n < p^3)

private theorem full_mark (n u b : ℕ) (hn : 1<n) (hc : u.Coprime n) (hb : b<n) :
    ((range n).filter fun a => a*u%n=b).Nonempty := by
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hn
  refine ⟨(b*i)%n,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by omega)),?_⟩⟩
  calc
    _ = (b*i*u)%n := Nat.mod_mul_mod _ _ _
    _ = b*(u*i)%n := by rw [mul_assoc, Nat.mul_comm i u]
    _ = b := by rw [Nat.mul_mod, hi, Nat.mod_eq_of_lt hb, mul_one, Nat.mod_eq_of_lt hb]

/-- Both admissible orientations contribute the same unsigned semiprime sum. -/
theorem full_count (n : ℕ) (hn : 64 ≤ n) :
    (firstHit n).card = 2 * ∑ p ∈ band n, (partners n p).card := by
  let mark := fun u b : ℕ => ((range n).filter fun a => (a*u)%n=b).Nonempty
  let tagged := (window n).filter fun u => u.Coprime n ∧ mark u 1 ∧
    n < ((u*(n-u)).minFac)^3 ∧ ((u*(n-u)).minFac)^2 ≤ n
  let qset := fun p b : ℕ => (Icc p n).filter fun q => q.Prime ∧ p*q ∈ window n ∧
    (p*q).Coprime n ∧ p ≤ (n-p*q).minFac ∧ mark (p*q) b
  have ht : firstHit n = tagged := by
    ext u
    simp only [firstHit,tagged,mem_filter,cut_lt,Nat.le_sqrt']
    constructor
    · rintro ⟨hu,hc,ha,hb⟩
      exact ⟨hu,hc,full_mark n u 1 (by omega) hc (by omega),ha,hb⟩
    · rintro ⟨hu,hc,_,ha,hb⟩
      exact ⟨hu,hc,ha,hb⟩
  have hq (p b : ℕ) (hb : b<n) : qset p b = partners n p := by
    ext q
    simp only [qset,partners,mem_filter]
    constructor
    · rintro ⟨hr,hp,hw,hc,hl,_⟩
      exact ⟨hr,hp,hw,hc,hl⟩
    · rintro ⟨hr,hp,hw,hc,hl⟩
      exact ⟨hr,hp,hw,hc,hl,full_mark n _ b (by omega) hc hb⟩
  have h := Conjectures.Goldbach.FareyLateFirstHitFactorSwitch n (range n) hn
  change tagged.card = ∑ p ∈ band n, ((qset p 1).card+(qset p (n-1)).card) at h
  rw [ht,h,Finset.mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [hq p 1 (by omega),hq p (n-1) (by omega),two_mul]

theorem diagonal_split (n : ℕ) (hn : 64 ≤ n) :
    (firstHit n).card = 2 * (distinctPairs n + squarePairs n) := by
  rw [full_count n hn, distinctPairs, squarePairs, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro p hp
  simpa only [not_not, add_comm] using
    (card_filter_add_card_filter_not (s:=partners n p) (p:=fun q => q=p)).symm

theorem band_card (n : ℕ) : (band n).card ≤ n.sqrt := by
  have hsub : band n ⊆ Icc 1 n.sqrt := by
    intro p hp
    obtain ⟨_,hpp,_,hh⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨hpp.pos,Nat.le_sqrt'.mpr hh⟩
  simpa using card_le_card hsub

theorem square_bound (n : ℕ) : squarePairs n ≤ n.sqrt := by
  calc
    squarePairs n ≤ ∑ _p ∈ band n, 1 := by
      apply sum_le_sum
      intro p hp
      apply (card_le_card (show (partners n p).filter (fun q => q = p) ⊆ {p} from
        fun q hq => mem_singleton.mpr (mem_filter.mp hq).2)).trans
      simp
    _ = (band n).card := by simp
    _ ≤ _ := band_card n

theorem close_bound (n w : ℕ) : closePairs n w ≤ n.sqrt*w := by
  calc
    _ ≤ ∑ _p ∈ band n, w := by
      apply sum_le_sum
      intro p _
      have hsub : (partners n p).filter (fun q => p<q ∧ q≤p+w) ⊆ Ioc p (p+w) :=
        fun q h => mem_Ioc.mpr (mem_filter.mp h).2
      simpa using card_le_card hsub
    _ = (band n).card*w := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (band_card n)

theorem distinct_split (n w : ℕ) : distinctPairs n = closePairs n w + farPairs n w := by
  unfold distinctPairs closePairs farPairs
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  let D := (partners n p).filter (fun q => q≠p)
  have hmin {q : ℕ} (hq : q∈partners n p) : p≤q := (mem_Icc.mp (mem_filter.mp hq).1).1
  have hlow : D.filter (fun q => q≤p+w) = (partners n p).filter (fun q => p<q ∧ q≤p+w) := by
    ext q; simp only [D,mem_filter]
    constructor
    · rintro ⟨⟨h,hne⟩,h'⟩
      exact ⟨h,lt_of_le_of_ne (hmin h) hne.symm,h'⟩
    · rintro ⟨h,hl,hu⟩
      exact ⟨⟨h,hl.ne'⟩,hu⟩
  have hhigh : D.filter (fun q => ¬ q≤p+w) = (partners n p).filter (fun q => p+w<q) := by
    ext q; simp only [D,mem_filter,not_le]
    exact ⟨fun ⟨⟨h,_⟩,hb⟩ => ⟨h,hb⟩,fun ⟨h,hb⟩ => ⟨⟨h,by omega⟩,hb⟩⟩
  rw [← hlow,← hhigh,card_filter_add_card_filter_not]

end
end GoldbachLateWindow

namespace GoldbachLatePrimeCounts
open Filter Real Finset Asymptotics
open scoped Topology
noncomputable section

def π₀ (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

lemma prime_count_relative (η : ℝ) (hη : 0 < η) : ∀ᶠ x : ℝ in atTop,
    (1-η)*(x/log x) ≤ π₀ x ∧ π₀ x ≤ (1+η)*(x/log x) := by
  have hq : Tendsto (fun x => π₀ x/(x/log x)) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      exact div_ne_zero (by linarith) (log_pos hx).ne')).mp Nat.isEquivalent_primeCounting
  have hh := (Metric.tendsto_nhds.mp hq) η hη
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with x hx hx1
  rw [Real.dist_eq,abs_lt] at hx
  have hy : 0 < x/log x := div_pos (by linarith) (log_pos hx1)
  exact ⟨(le_div_iff₀ hy).mp (by linarith),(div_le_iff₀ hy).mp (by linarith)⟩

/-- The constant in this bound is uniform in the width of the window.
Only the point at which the bound starts may depend on that width. -/
theorem short_ratio (d : ℝ) (hd : 0<d) (hd1 : d≤1) : ∀ᶠ x : ℝ in atTop,
    π₀ ((1+d)*x) - π₀ x ≤ 2*d*(x/log x) := by
  have h := prime_count_relative (d/4) (by positivity)
  obtain ⟨X,hX⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop X,eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hxpos : 0≤x := by linarith
  have hxy : x≤(1+d)*x := by nlinarith [mul_nonneg hd.le hxpos]
  have hlog := log_pos hx1
  have hlog' := log_le_log (by linarith : 0<x) hxy
  have u := (hX _ (hx.trans hxy)).2
  have l := (hX _ hx).1
  have hb : ((1+d)*x)/log ((1+d)*x) ≤ (1+d)*(x/log x) := by
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) hlog hlog'
  have hprod := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1+d/4)
  have hdiff : (1+d/4)*(1+d) - (1-d/4) ≤ 2*d := by
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
  nlinarith only [u,l,hprod,mul_le_mul_of_nonneg_right hdiff (div_nonneg hxpos hlog.le)]

open GoldbachLateWindow

def ratioPartners (n p : ℕ) (d : ℝ) := (partners n p).filter
  (fun q => p<q ∧ (q:ℝ)≤(1+d)*p)
def ratioCount (n : ℕ) (d : ℝ) := ∑ p ∈ band n, (ratioPartners n p d).card

lemma ratio_partners_le (n p : ℕ) (d : ℝ) (hd : 0≤d) :
    ((ratioPartners n p d).card:ℝ) ≤ π₀ ((1+d)*p) - π₀ p := by
  let b := ⌊(1+d)*(p:ℝ)⌋₊
  have hpb : p≤b := Nat.le_floor (by nlinarith [mul_nonneg hd (Nat.cast_nonneg p)])
  have hsub : p.primesLE ⊆ b.primesLE := fun q h => Nat.mem_primesLE.mpr
    ⟨(Nat.mem_primesLE.mp h).1.trans hpb, (Nat.mem_primesLE.mp h).2⟩
  have hset : ratioPartners n p d ⊆ b.primesLE \ p.primesLE := by
    intro q hq
    obtain ⟨h,hl,hu⟩ := mem_filter.mp hq
    exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hu,(mem_filter.mp h).2.1⟩,
      fun hh => (not_lt_of_ge (Nat.mem_primesLE.mp hh).1) hl⟩
  have hc := card_le_card hset
  have hcard : (ratioPartners n p d).card + p.primesLE.card ≤ b.primesLE.card := by
    rw [Finset.card_sdiff_of_subset hsub] at hc
    have := card_le_card hsub
    omega
  rw [Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting] at hcard
  unfold π₀
  rw [Nat.floor_natCast]
  exact (le_sub_iff_add_le).mpr (by exact_mod_cast hcard)

/-- Uniform linear dependence on the relative separation of the two factors.
For each fixed positive width the threshold may depend on the width. -/
theorem relative_strip_bound (d : ℝ) (hd : 0<d) (hd1 : d≤1) :
    ∀ᶠ n : ℕ in atTop, (ratioCount n d:ℝ) ≤ 24*d*((n:ℝ)/(log n)^2) := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (short_ratio d hd hd1)
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (prime_count_relative 1 (by norm_num))
  have hc := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hc.eventually_ge_atTop X,hs.eventually_ge_atTop Y,eventually_ge_atTop 64]
    with n hx hy hn
  change X≤(n:ℝ)^(1/3:ℝ) at hx
  change Y≤Real.sqrt (n:ℝ) at hy
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlog : 0<log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1<n))
  let R := Real.sqrt (n:ℝ)
  have hπ : (band n).card ≤ n.sqrt.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply card_le_card
    intro p hp
    obtain ⟨_,hpp,_,hp2⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_sqrt'.mpr hp2,hpp⟩
  have hband : ((band n).card:ℝ) ≤ 4*R/log n := by
    apply (show ((band n).card:ℝ) ≤ π₀ R by
      dsimp [π₀,R]; rw [nat_floor_real_sqrt_eq_nat_sqrt]; exact_mod_cast hπ).trans
    have hh := (hY R hy).2
    have hl : log R = log (n:ℝ)/2 := by
      dsimp [R]; rw [sqrt_eq_rpow,log_rpow hn0]; ring
    rw [hl] at hh
    exact hh.trans (le_of_eq (by ring))
  have hpcount (p : ℕ) (hp : p ∈ band n) :
      ((ratioPartners n p d).card:ℝ) ≤ 6*d*R/log n := by
    obtain ⟨_,hpp,h3,h2⟩ := mem_filter.mp hp
    have hlow : (n:ℝ)^(1/3:ℝ)<p := (Nat.floor_lt (by positivity)).mp ((cut_lt n p).mpr h3)
    have hh := hX p (hx.trans hlow.le)
    have hhi : (p:ℝ)≤R := by
      have hpn : p≤n.sqrt := Nat.le_sqrt'.mpr h2
      rw [←nat_floor_real_sqrt_eq_nat_sqrt] at hpn
      exact (Nat.le_floor_iff (sqrt_nonneg _)).mp hpn
    have hplog : (1/3:ℝ)*log n ≤ log p := by
      rw [←Real.log_rpow hn0]
      exact log_le_log (Real.rpow_pos_of_pos hn0 _) hlow.le
    have hquot : (p:ℝ)/log p ≤ R/((1/3:ℝ)*log n) :=
      div_le_div₀ (sqrt_nonneg _) hhi (by positivity) hplog
    apply ((ratio_partners_le n p d hd.le).trans hh).trans
    calc
      _ ≤ 2*d*(R/((1/3:ℝ)*log n)) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = _ := by ring
  unfold ratioCount
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _p ∈ band n, 6*d*R/log n := sum_le_sum hpcount
    _ = ((band n).card:ℝ)*(6*d*R/log n) := by simp
    _ ≤ (4*R/log n)*(6*d*R/log n) := mul_le_mul_of_nonneg_right hband
      (div_nonneg (mul_nonneg (by positivity) (sqrt_nonneg _)) hlog.le)
    _ = _ := by
      have hr : R^2 = (n:ℝ) := Real.sq_sqrt hn0.le
      rw [← hr]
      ring

end
end GoldbachLatePrimeCounts

/- The factorial and small-prime product estimates below are adapted from
   goldbach-proofs PR #2973 by 34245621 (Apache-2.0), commit
   5470a2c93f224ef9186b2c13aef54a42e49e2348. The factorial identities
   originate in ErdosStraus/Estimates/Mertens.lean, © 2026 Sushaan Kandukoori,
   Apache-2.0, revision f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660. -/
namespace GoldbachLateEstimates
namespace FareyBrun
open Finset Real
open scoped BigOperators ArithmeticFunction Nat
/-- `log n! = ∑_{m ≤ n} log m`. -/
theorem log_factorial_eq_sum_log (n : ℕ) :
    log (n ! : ℝ) = ∑ m ∈ Icc 1 n, log (m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

/-- Legendre's identity `log n! = ∑_{d ≤ n} Λ(d) ⌊n/d⌋`. -/
theorem log_factorial_eq (n : ℕ) :
    log (n ! : ℝ) = ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have hdiv : ∀ m ∈ Icc 1 n, log (m : ℝ) = ∑ d ∈ m.divisors, Λ d := fun m _ =>
    ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl hdiv,
    Finset.sum_comm' (t' := Icc 1 n) (s' := fun d => (Icc 1 n).filter (fun m => d ∣ m))]
  · apply Finset.sum_congr rfl
    intro d _
    have hIcc : Icc 1 n = Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
    rw [sum_const, nsmul_eq_mul, hIcc, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
  · intro m d
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h1, hm⟩, hdm, -⟩
      exact ⟨⟨⟨h1, hm⟩, hdm⟩, Nat.pos_of_dvd_of_pos hdm h1, (Nat.le_of_dvd h1 hdm).trans hm⟩
    · rintro ⟨⟨⟨h1, hm⟩, hdm⟩, -, -⟩
      exact ⟨⟨h1, hm⟩, hdm, by omega⟩

/-- `⌊n/d⌋ ≤ n/d ≤ ⌊n/d⌋ + 1`. -/
theorem natDiv_le_div_le (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hdr]
  have h3 : (n : ℝ) = d * (n / d : ℕ) + (n % d : ℕ) := by exact_mod_cast (Nat.div_add_mod n d).symm
  have h4 : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
  nlinarith

end FareyBrun

namespace FareyBrun
open Finset Real
open scoped BigOperators ArithmeticFunction Nat
noncomputable section

/-- A uniform logarithmic budget, without any prime-number asymptotic. -/
theorem log_prime_budget (n : ℕ) (hn : 0 < n) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ n) :
    (∑ p ∈ s, Real.log p / p) ≤ 2 * Real.log n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hterm (p : ℕ) (hp : p ∈ s) :
      (n:ℝ) * (Real.log p / p) ≤ 2 * (Λ p * (n / p : ℕ)) := by
    obtain ⟨hprime,hpn⟩ := hs p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
    have hdiv : 1 ≤ n / p := (Nat.one_le_div_iff hprime.pos).mpr hpn
    have hx := (natDiv_le_div_le n p hprime.pos).2
    have hcast : (1:ℝ) ≤ (n / p : ℕ) := by exact_mod_cast hdiv
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_le)
    calc _ = Real.log p * ((n:ℝ)/p) := by ring
         _ ≤ Real.log p * (2*(n/p:ℕ)) :=
           mul_le_mul_of_nonneg_left (by linarith) hlog
         _ = _ := by ring
  have hsub : s ⊆ Icc 1 n := fun p hp => mem_Icc.mpr ⟨(hs p hp).1.one_le,(hs p hp).2⟩
  have hfac : Real.log (n ! : ℝ) ≤ (n:ℝ) * Real.log n := by
    rw [←Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow n)
  apply le_of_mul_le_mul_left ?_ hn'
  calc
    (n:ℝ) * (∑ p ∈ s, Real.log p / p) ≤ 2 * ∑ p ∈ s, Λ p * (n / p : ℕ) := by
      rw [mul_sum,mul_sum]
      exact sum_le_sum hterm
    _ ≤ 2 * ∑ p ∈ Icc 1 n, Λ p * (n / p : ℕ) := by
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))) (by norm_num)
    _ = 2 * Real.log (n ! : ℝ) := by rw [log_factorial_eq]
    _ ≤ (n:ℝ) * (2*Real.log n) := by linarith

/-- Local density for the two forbidden residues of an odd prime. -/
theorem euler_density_lower (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p) :
    Real.exp (-3 * ∑ p ∈ s, 2/(p:ℝ)) ≤ ∏ p ∈ s, (1-2/(p:ℝ)) := by
  rw [mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le)
  intro p hp
  have h3 : (3:ℝ) ≤ p := by exact_mod_cast hs p hp
  have hpos : (0:ℝ) < p := by linarith
  let w := 2/(p:ℝ)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hu : w ≤ 2/3 := by dsimp [w]; rw [div_le_div_iff₀ hpos (by norm_num : (0:ℝ)<3)]; linarith
  have hv : 0 < 1-w := by linarith
  have hi : (1-w)⁻¹ ≤ 3 := by rw [inv_eq_one_div,div_le_iff₀ hv]; linarith
  have hh := Real.one_sub_inv_le_log_of_pos hv
  have hcan := inv_mul_cancel₀ hv.ne'
  have hm := mul_le_mul_of_nonneg_right hi hw
  apply (Real.le_log_iff_exp_le hv).mp
  change -3*w ≤ _
  nlinarith
end
end FareyBrun

namespace FareyBrun
open Finset Real Filter
open scoped BigOperators Topology
noncomputable section
def primes (z : ℕ) := (Icc 2 z).filter Nat.Prime
theorem log_tail_budget {n : ℕ} (hn : 0<n) (s : Finset ℕ) (L : ℝ)
    (hs : ∀ p ∈ s, p.Prime ∧ p≤n ∧ L ≤ Real.log p) :
    L * (∑ p ∈ s, 2/(p:ℝ)) ≤ 4*Real.log n := by
  calc _ ≤ 2 * ∑ p ∈ s, Real.log p / p := by
          rw [mul_sum,mul_sum]
          apply sum_le_sum
          intro p hp
          have h := (hs p hp).2.2
          rw [show L*(2/(p:ℝ))=(2*L)/p by ring,
            show 2*(Real.log p/p)=(2*Real.log p)/p by ring]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
       _ ≤ _ := by linarith [log_prime_budget n hn s (fun p hp => ⟨(hs p hp).1,(hs p hp).2.1⟩)]
/-- A fixed, very weak polynomial floor suffices to absorb the integer rounding errors. -/
theorem mertens_weak_floor : ∃ c : ℝ, 0<c ∧ ∀ n y : ℕ, 2≤n → y≤n →
    c * (n:ℝ)^(-(1/16):ℝ) ≤ ∏ p ∈ primes y, (1-(p:ℝ)⁻¹) := by
  obtain ⟨A,hA⟩ := exists_nat_gt (Real.exp 256)
  refine ⟨(1/2:ℝ)^A,by positivity,?_⟩
  intro n y hn hy
  let S := (primes y).filter (fun p => p≤A)
  let T := primes y \ S
  have hsub : S ⊆ primes y := filter_subset _ _
  have hcard : S.card ≤ A := by
    have hs : S ⊆ Icc 1 A := by
      intro p hp
      obtain ⟨h,hpA⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(mem_filter.mp h).2.one_le,hpA⟩
    simpa using card_le_card hs
  have hsmall : (1/2:ℝ)^A ≤ ∏ p ∈ S, (1-(p:ℝ)⁻¹) := by
    calc _ ≤ (1/2:ℝ)^S.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
         _ = ∏ _p ∈ S, (1/2:ℝ) := by simp
         _ ≤ _ := by
           apply Finset.prod_le_prod₀ (fun _ _ => by norm_num)
           intro p hp
           have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp (hsub hp)).2.two_le
           have h := one_div_le_one_div_of_le (by norm_num : 0<(2:ℝ)) h2
           rw [one_div] at h
           linarith
  have hlarge (p : ℕ) (hp : p ∈ T) : p.Prime ∧ p≤n ∧ (256:ℝ) ≤ Real.log p := by
    obtain ⟨hy',hS⟩ := mem_sdiff.mp hp
    have hAp : A<p := by by_contra! h; exact hS (mem_filter.mpr ⟨hy',h⟩)
    have hexp : Real.exp 256 ≤ (p:ℝ) := hA.le.trans (by exact_mod_cast hAp.le)
    have hlog := Real.log_le_log (Real.exp_pos _) hexp
    exact ⟨(mem_filter.mp hy').2,(mem_Icc.mp (mem_filter.mp hy').1).2.trans hy,by simpa using hlog⟩
  have hmass := log_tail_budget (by omega : 0<n) T 256 hlarge
  have hnlog : 0 ≤ log (n:ℝ) := log_nonneg (by exact_mod_cast (by omega : 1≤n))
  have h3 (p : ℕ) (hp : p ∈ T) : 3≤p := by
    have hpr := (hlarge p hp).1
    have hlog := (hlarge p hp).2.2
    have h2 := hpr.two_le
    by_contra! h
    obtain rfl : p=2 := by omega
    push_cast at hlog
    linarith [Real.log_two_lt_d9]
  have hbig : (n:ℝ)^(-(1/16):ℝ) ≤ ∏ p ∈ T, (1-(p:ℝ)⁻¹) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0<n))]
    apply le_trans _ ((euler_density_lower T h3).trans ?_)
    · apply Real.exp_le_exp.mpr
      linarith
    · apply Finset.prod_le_prod₀
      · intro p hp
        have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hlarge p hp).1.two_le
        exact sub_nonneg.mpr ((div_le_one (by linarith : (0:ℝ)<p)).mpr h2)
      · intro p hp
        have h0 : 0 ≤ (p:ℝ)⁻¹ := by positivity
        rw [div_eq_mul_inv]
        linarith
  have hh := mul_le_mul hbig hsmall (by positivity : 0≤(1/2:ℝ)^A)
    (by exact (Real.rpow_nonneg (by positivity) _).trans hbig)
  rw [mul_comm ((n:ℝ)^(-(1/16):ℝ))] at hh
  change _ ≤ (∏ p ∈ primes y \ S, (1-(p:ℝ)⁻¹)) * ∏ p ∈ S, (1-(p:ℝ)⁻¹) at hh
  rwa [prod_sdiff hsub] at hh
end
end FareyBrun
end GoldbachLateEstimates

namespace GoldbachLateWindow
open Finset Real Filter
open scoped BigOperators Topology
open GoldbachLateEstimates.FareyBrun
noncomputable section

def localFactor (p : ℕ) : ℝ := 1-(p:ℝ)⁻¹
def V (n z : ℕ) : ℝ := ((window n).card:ℝ)*n.totient/n *
  ∏ p ∈ (primes z).filter (fun p => ¬p∣n), (1-2/(p:ℝ))

private theorem product_subset (n : ℕ) (s : Finset ℕ) (hs : s ⊆ primes n) :
    ∏ p ∈ primes n, localFactor p ≤ ∏ p ∈ s, localFactor p := by
  rw [← Finset.prod_sdiff hs]
  apply mul_le_of_le_one_left
  · apply prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast (mem_filter.mp (hs hp)).2.one_le))
  · apply Finset.prod_le_one₀
    · intro p hp
      have h := (mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.one_le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast h))
    · intro p _
      exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- A weak polynomial lower bound suffices to absorb the whole diagonal. -/
theorem terminal_growth : ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 64≤n → Even n →
    C * (n:ℝ)^(3/4:ℝ) ≤ V n n.sqrt := by
  obtain ⟨c,hc,hM⟩ := mertens_weak_floor
  refine ⟨c^4/4,by positivity,?_⟩
  intro n hn heven
  let B := (primes n.sqrt).filter (fun p => ¬p∣n)
  let M : ℝ := c*(n:ℝ)^(-(1/16):ℝ)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hM0 : 0≤M := by dsimp [M]; positivity
  have hbase (s : Finset ℕ) (h : s ⊆ primes n) : M ≤ ∏ p ∈ s, localFactor p :=
    (hM n n (by omega) le_rfl).trans (product_subset n s h)
  have hphi : M ≤ (n.totient:ℝ)/n := by
    have hf : (n.totient:ℝ)=(n:ℝ)*∏ p ∈ n.primeFactors, localFactor p := by
      have hh := congrArg (fun x : ℚ => (x:ℝ)) (Nat.totient_eq_mul_prod_factors n)
      push_cast at hh
      exact hh
    rw [hf,mul_div_cancel_left₀ _ hn0.ne']
    apply hbase
    intro p hp
    have h := Nat.prime_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h.two_le,Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)⟩,h⟩
  have hB : B ⊆ primes n := by
    intro p hp
    obtain ⟨h,_⟩ := mem_filter.mp hp
    obtain ⟨hI,hp'⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.two_le,(mem_Icc.mp hI).2.trans (Nat.sqrt_le_self _)⟩,hp'⟩
  have heuler : M^3 ≤ ∏ p ∈ B, (1-2/(p:ℝ)) := by
    apply (pow_le_pow_left₀ hM0 (hbase B hB) 3).trans
    rw [← prod_pow]
    apply Finset.prod_le_prod₀
    · intro p hp
      exact pow_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast
        (mem_filter.mp (hB hp)).2.one_le))) _
    · intro p hp
      have hpp := (mem_filter.mp (hB hp)).2
      have h3 : 3≤p := by
        have := hpp.two_le
        have hne : p≠2 := fun hh => (mem_filter.mp hp).2 (hh ▸ even_iff_two_dvd.mp heven)
        omega
      have hi : (p:ℝ)⁻¹ ≤ 1/3 := by
        rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h3)
      have hi0 : 0≤(p:ℝ)⁻¹ := by positivity
      dsimp [localFactor]
      rw [div_eq_mul_inv]
      nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hi),pow_nonneg hi0 3]
  have hcard : n ≤ 4*(window n).card := by simp only [window,Nat.card_Icc]; omega
  have hi : (n:ℝ)/4 ≤ (window n).card := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    rw [mul_comm]
    exact_mod_cast hcard
  have hh := mul_le_mul (mul_le_mul hi hphi hM0 (Nat.cast_nonneg _)) heuler
    (pow_nonneg hM0 _) (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) hn0.le))
  change _ ≤ ((window n).card:ℝ)*n.totient/n*∏ p ∈ B, (1-2/(p:ℝ))
  rw [mul_div_assoc]
  refine le_trans (le_of_eq ?_) hh
  have he : (n:ℝ)*(n:ℝ)^((-(1/16):ℝ)*((4:ℕ):ℝ))=(n:ℝ)^(3/4:ℝ) := by
    rw [mul_comm, ← Real.rpow_add_one hn0.ne']; norm_num
  calc
    _ = ((n:ℝ)/4)*c^4*((n:ℝ)^(-(1/16):ℝ))^4 := by
      rw [← Real.rpow_mul_natCast hn0.le,← he]; ring
    _ = _ := by dsimp [M]; ring

/-- Prime squares consume an arbitrarily small fraction of the terminal volume. -/
theorem square_absorbed (δ : ℝ) (hδ : 0<δ) : ∀ᶠ n : ℕ in atTop, Even n →
    2*(squarePairs n:ℝ) ≤ δ*V n n.sqrt := by
  obtain ⟨C,hC,hV⟩ := terminal_growth
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop (2/(δ*C)),eventually_ge_atTop 64] with n h hn
  intro he
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  change 2/(δ*C) ≤ (n:ℝ)^(1/4:ℝ) at h
  have hfac := (div_le_iff₀ (mul_pos hδ hC)).mp h
  have hs : (n.sqrt:ℝ) ≤ (n:ℝ)^(1/2:ℝ) := by
    rw [← sqrt_eq_rpow, ← nat_floor_real_sqrt_eq_nat_sqrt]
    exact Nat.floor_le (sqrt_nonneg _)
  calc
    _ ≤ 2 * (n:ℝ)^(1/2:ℝ) := mul_le_mul_of_nonneg_left
      ((show (squarePairs n:ℝ) ≤ n.sqrt by exact_mod_cast square_bound n).trans hs) (by norm_num)
    _ ≤ ((n:ℝ)^(1/4:ℝ)*(δ*C)) * (n:ℝ)^(1/2:ℝ) :=
      mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = δ * (C * (n:ℝ)^(3/4:ℝ)) := by
      have heq : (n:ℝ)^(1/4:ℝ)*(n:ℝ)^(1/2:ℝ)=(n:ℝ)^(3/4:ℝ) := by
        rw [← Real.rpow_add hn0]; norm_num
      rw [← heq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hV n hn he) hδ.le

/-- An estimate for the distinct-factor sum with any fixed positive margin
implies the requested half-budget after the square terms are restored. -/
theorem from_distinct_estimate (δ : ℝ) (hδ : 0<δ)
    (hs : ∀ᶠ n : ℕ in atTop, Even n →
      2*(distinctPairs n:ℝ) ≤ V n (cubeCut n) - (1/2+δ)*V n n.sqrt) :
    ∃ N : ℕ, 64 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n →
      (firstHit n).card ≤ V n (cubeCut n) - V n n.sqrt + V n n.sqrt/2 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hs.and (square_absorbed δ hδ))
  refine ⟨max 64 N,le_max_left ..,?_⟩
  intro n hn he
  obtain ⟨h1,h2⟩ := hN n ((le_max_right ..).trans hn)
  rw [diagonal_split n ((le_max_left ..).trans hn)]
  push_cast
  linarith only [h1 he,h2 he]

/-- A power-width band of unequal prime factors also has negligible mass. -/
theorem close_absorbed (δ : ℝ) (hδ : 0<δ) : ∀ᶠ n : ℕ in atTop, Even n →
    2*(closePairs n ⌊(n:ℝ)^(1/8:ℝ)⌋₊:ℝ) ≤ δ*V n n.sqrt := by
  obtain ⟨C,hC,hV⟩ := terminal_growth
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop (2/(δ*C)),eventually_ge_atTop 64] with n h hn
  intro he
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  change 2/(δ*C) ≤ (n:ℝ)^(1/8:ℝ) at h
  have hfac := (div_le_iff₀ (mul_pos hδ hC)).mp h
  let w := ⌊(n:ℝ)^(1/8:ℝ)⌋₊
  have hs : (n.sqrt:ℝ) ≤ (n:ℝ)^(1/2:ℝ) := by
    rw [← sqrt_eq_rpow,← nat_floor_real_sqrt_eq_nat_sqrt]; exact Nat.floor_le (sqrt_nonneg _)
  have hw : (w:ℝ) ≤ (n:ℝ)^(1/8:ℝ) := Nat.floor_le (by positivity)
  have hcard : (closePairs n w:ℝ) ≤ n.sqrt*(w:ℝ) := by exact_mod_cast close_bound n w
  have hprod : (n:ℝ)^(1/2:ℝ)*(n:ℝ)^(1/8:ℝ)=(n:ℝ)^(5/8:ℝ) := by rw [←rpow_add hn0]; norm_num
  have hprod' : (n:ℝ)^(1/8:ℝ)*(n:ℝ)^(5/8:ℝ)=(n:ℝ)^(3/4:ℝ) := by rw [←rpow_add hn0]; norm_num
  have hbound := hcard.trans (mul_le_mul hs hw (Nat.cast_nonneg _) (by positivity))
  rw [hprod] at hbound
  calc
    _ ≤ 2*(n:ℝ)^(5/8:ℝ) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ ≤ ((n:ℝ)^(1/8:ℝ)*(δ*C))*(n:ℝ)^(5/8:ℝ) := mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = δ * (C*(n:ℝ)^(3/4:ℝ)) := by rw [←hprod']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hV n hn he) hδ.le

end
end GoldbachLateWindow

/- Weighted prime sum from the Goldbach project, revision 5a7853e, adapted there from
PrimeNumberTheoremAnd, IEANTN/Mertens.lean, c39a751132c88b6e8080b74c74023fd95b3d8be0 (Apache-2.0).
The reciprocal sum and prime product arguments are excerpted from Sushaan Kandukoori,
erdos-straus-lean, revision f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660 (Apache-2.0). -/
namespace WeightedTorusJets.Mertens
open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem prime_log_div_bounded_error :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C := by
  refine ⟨log 4 + 6 + E₁, by positivity [E₁.nonneg], fun x hx => ?_⟩
  rw [Nat.primesLE_eq_filter_Ioc_zero]
  change |E₁p x| ≤ log 4 + 6 + E₁
  have hlog : 0 ≤ log 4 := by positivity
  exact abs_le.mpr
    ⟨by linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx],
     by linarith [E₁Λ.le hx, E₁p.le_E₁Λ x, E₁.nonneg]⟩

end WeightedTorusJets.Mertens
namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real

/-- The set of primes `p ≤ x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter Nat.Prime

@[simp]
theorem mem_primesUpTo {p x : ℕ} : p ∈ primesUpTo x ↔ p.Prime ∧ p ≤ x := by
  simp [primesUpTo, and_comm]

theorem primesUpTo_eq_empty_of_le_one {x : ℕ} (hx : x ≤ 1) : primesUpTo x = ∅ := by
  ext p
  simp only [mem_primesUpTo, Finset.notMem_empty, iff_false]
  intro hp'
  have hp2 := hp'.1.two_le
  omega

/-- The sum `∑_{p ≤ x} 1/p`. -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  (primesUpTo x).sum fun p => 1 / (p : ℝ)

/-- The Euler product `∏_{p ≤ x} (1 - 1/p)`. -/
noncomputable def primeProduct (x : ℕ) : ℝ :=
  (primesUpTo x).prod fun p => 1 - 1 / (p : ℝ)

theorem primeFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp1)).mpr hp1)

theorem primeProduct_pos (x : ℕ) : 0 < primeProduct x := by
  unfold primeProduct
  exact Finset.prod_pos fun p hp => primeFactor_pos (mem_primesUpTo.mp hp).1

theorem log_primeProduct (x : ℕ) :
    log (primeProduct x) =
      (primesUpTo x).sum (fun p => log (1 - 1 / (p : ℝ))) := by
  unfold primeProduct
  rw [Real.log_prod]
  intro p hp
  exact (primeFactor_pos (mem_primesUpTo.mp hp).1).ne'

theorem abs_log_one_sub_add_le {t : ℝ} (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    |log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  have hne : 1 - t ≠ 0 := ne_of_gt hpos
  have hub : log (1 - t) ≤ -t := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlb : -t - 2 * t ^ 2 ≤ log (1 - t) := by
    have hrec2 : 1 / (1 - t) ≤ 1 + 2 * t := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have hmul : t / (1 - t) ≤ t * (1 + 2 * t) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hrec2 (le_of_lt ht0)
    calc
      -t - 2 * t ^ 2 = -(t * (1 + 2 * t)) := by ring
      _ ≤ -(t / (1 - t)) := neg_le_neg hmul
      _ = 1 - (1 - t)⁻¹ := by field_simp [hne]; ring
      _ ≤ log (1 - t) := Real.one_sub_inv_le_log_of_pos hpos
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_log_primeFactor_add_le {p : ℕ} (hp : p.Prime) :
    |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 := by
  have ht0 : 0 < 1 / (p : ℝ) := by
    exact div_pos one_pos (by exact_mod_cast hp.pos)
  have htle : 1 / (p : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hp.two_le)
  simpa only [div_pow, one_pow, mul_one_div] using
    abs_log_one_sub_add_le ht0 htle

end ErdosStraus.PrimeEstimates.Mertens
namespace ErdosStraus.PrimeEstimates
open Finset
theorem sum_Ico_weight_differences (u : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Ico m n, (u k - u (k + 1))) = u m - u n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [Finset.sum_Ico_succ_top hmn, ih]; ring

theorem sum_Ioc_eq_prefix_sub (c : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Ioc m n, c j) =
      (∑ j ∈ Icc 0 n, c j) - (∑ j ∈ Icc 0 m, c j) := by
  have hsplit : (∑ j ∈ Icc 0 n, c j) =
      (∑ j ∈ Icc 0 m, c j) + (∑ j ∈ Ioc m n, c j) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := c) (Nat.zero_le n),
      ← Finset.add_sum_Ioc_eq_sum_Icc (f := c) (Nat.zero_le m),
      ← Finset.sum_Ioc_consecutive c (Nat.zero_le m) hmn]
    ring
  linarith
end ErdosStraus.PrimeEstimates
namespace ErdosStraus.PrimeEstimates.Mertens

open Filter MeasureTheory Real Set
open scoped Topology

theorem hasDerivAt_neg_inv_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => -(log t)⁻¹) (x⁻¹ / (log x) ^ 2) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : log x ≠ 0 := (log_pos hx).ne'
  refine ((Real.hasDerivAt_log hx0).inv hl0).neg.congr_deriv ?_
  simp [div_eq_mul_inv]

theorem inv_log_tendsto_zero :
    Tendsto (fun t : ℝ => -(log t)⁻¹) atTop (𝓝 0) := by
  simpa using Real.tendsto_log_atTop.inv_tendsto_atTop.neg

theorem integrableOn_inv_div_log_sq_Ioi {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Ioi x) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := fun t : ℝ => -(log t)⁻¹)
    (l := 0) (fun t ht => hasDerivAt_neg_inv_log (hx.trans_le ht))
    (fun t ht => div_nonneg (inv_nonneg.mpr (zero_lt_one.trans (hx.trans ht)).le)
      (sq_nonneg _)) inv_log_tendsto_zero

theorem integral_inv_div_log_sq_Ioi {x : ℝ} (hx : 1 < x) :
    (∫ t in Ioi x, t⁻¹ / (log t) ^ 2) = 1 / log x := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun t : ℝ => -(log t)⁻¹)
    (l := 0) (fun t ht => hasDerivAt_neg_inv_log (hx.trans_le ht))
    (fun t ht => div_nonneg (inv_nonneg.mpr (zero_lt_one.trans (hx.trans ht)).le)
      (sq_nonneg _)) inv_log_tendsto_zero
  simpa using h

theorem integral_interval_sub_Ioi {f : ℝ → ℝ} {a x : ℝ}
    (hf : IntegrableOn f (Ioi a)) (hx : a ≤ x) :
    (∫ t in a..x, f t) - (∫ t in Ioi a, f t) = -(∫ t in Ioi x, f t) := by
  have hdisj : Disjoint (Ioc a x) (Ioi x) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  have h := setIntegral_union hdisj measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hx))
  rw [Ioc_union_Ioi_eq_Ioi hx] at h
  rw [intervalIntegral.integral_of_le hx]
  linarith

end ErdosStraus.PrimeEstimates.Mertens
namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real
open scoped BigOperators
theorem mertensFirst :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log x| ≤ C := by
  obtain ⟨C,hC,hh⟩ := WeightedTorusJets.Mertens.prime_log_div_bounded_error
  refine ⟨C,hC, fun x hx => ?_⟩
  have heq : primesUpTo ⌊x⌋₊ = Nat.primesLE ⌊x⌋₊ := by
    ext q
    simp [Nat.mem_primesLE, and_comm]
  rw [heq]
  exact hh x (by linarith)
/-- `B₁(x) = ∑_{p ≤ x} log p / p`. -/
noncomputable def primeLogReciprocal (x : ℝ) : ℝ := ∑ p ∈ primesUpTo ⌊x⌋₊, log p / p

/-- The remainder `R(x) = B₁(x) - log x` in Mertens' first theorem. -/
noncomputable def mertensRemainder (x : ℝ) : ℝ := primeLogReciprocal x - log x

/-- `R(x) = B₁(x) - log x` is bounded on `[2, ∞)`. -/
theorem mertensRemainder_bound :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x → |mertensRemainder x| ≤ C :=
  mertensFirst

/-- `B₁(x)` as a prefix sum of prime-supported coefficients. -/
theorem primeLogReciprocal_eq_sum_Icc (x : ℝ) :
    primeLogReciprocal x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, if n.Prime then log (n : ℝ) / n else 0 := by
  rw [primeLogReciprocal, primesUpTo, sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [mem_range, mem_Icc]
  omega

theorem measurable_primeLogReciprocal : Measurable primeLogReciprocal :=
  (measurable_of_countable
    (fun N : ℕ => ∑ p ∈ primesUpTo N, log (p : ℝ) / p)).comp Nat.measurable_floor

theorem measurable_mertensRemainder : Measurable mertensRemainder :=
  measurable_primeLogReciprocal.sub measurable_log

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Mertens' second theorem

Abel summation against `B₁` gives
`∑_{p ≤ x} 1/p = B₁(x)/log x + ∫_2^x B₁(t)/(t (log t)²) dt`.
Writing `B₁(t) = log t + R(t)` with `R` bounded, the error integral converges
with tail `O(1/log x)`, so `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset MeasureTheory Real
open scoped BigOperators

/-- A function dominated by `C / (t (log t)²)` has tail integral at most `C / log x`. -/
theorem norm_integral_Ioi_le_div_log {f : ℝ → ℝ} {x C : ℝ} (hx : 1 < x)
    (hbound : ∀ t ∈ Set.Ioi x, ‖f t‖ ≤ C * (t⁻¹ / (log t) ^ 2)) :
    ‖∫ t in Set.Ioi x, f t‖ ≤ C / log x := by
  have hk : IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Set.Ioi x) volume :=
    integrableOn_inv_div_log_sq_Ioi hx
  have hCk : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi x) volume :=
    hk.const_mul C
  calc
    ‖∫ t in Set.Ioi x, f t‖ ≤ ∫ t in Set.Ioi x, C * (t⁻¹ / (log t) ^ 2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hCk
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = C * ∫ t in Set.Ioi x, t⁻¹ / (log t) ^ 2 := by rw [integral_const_mul]
    _ = C / log x := by rw [integral_inv_div_log_sq_Ioi hx]; ring

/-- `(1 / log t)' = -1 / (t (log t)²)`. -/
theorem hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => (log u)⁻¹) (-(t⁻¹ / (log t) ^ 2)) t := by
  convert (hasDerivAt_neg_inv_log ht).neg using 1 <;> first | rfl | (ext u; simp)
/-- Abel summation against `B₁`:
`∑_{p ≤ x} 1/p = B₁(x)/log x + ∫_2^x B₁(t)/(t (log t)²) dt`. -/
theorem primeReciprocalSum_abel {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ =
      primeLogReciprocal x / log x +
        ∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime then log (n : ℝ) / n else 0
  let f : ℝ → ℝ := fun u => (log u)⁻¹
  have hderiv : ∀ t : ℝ, 1 < t → deriv f t = -(t⁻¹ / (log t) ^ 2) :=
    fun t ht => (hasDerivAt_inv_log ht).deriv
  have hf : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ f t :=
    fun t ht => (hasDerivAt_inv_log (by linarith [ht.1])).differentiableAt
  have hfi : IntegrableOn (deriv f) (Set.Icc 2 x) := by
    have hc : ContinuousOn (fun t : ℝ => -(t⁻¹ / (log t) ^ 2)) (Set.Icc 2 x) := by
      have hlog : ContinuousOn log (Set.Icc 2 x) := fun t ht =>
        (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
      refine (((continuousOn_id' _).inv₀ fun t ht => ?_).div (hlog.pow 2) fun t ht => ?_).neg
      · exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
      · exact pow_ne_zero 2 (log_pos (by linarith [ht.1])).ne'
    exact hc.integrableOn_Icc.congr_fun
      (fun t ht => (hderiv t (by linarith [ht.1])).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c (by norm_num : (0 : ℝ) ≤ 2) hx hf hfi
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  simp only [Nat.floor_ofNat] at h
  rw [sum_Ioc_eq_prefix_sub (fun n => f n * c n) hfloor] at h
  have hinit : (∑ n ∈ Icc (0 : ℕ) 2, f n * c n) = f 2 * ∑ n ∈ Icc (0 : ℕ) 2, c n := by
    norm_num [c, Finset.sum_Icc_succ_top]
  have hB : ∀ t : ℝ, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) = primeLogReciprocal t :=
    fun t => (primeLogReciprocal_eq_sum_Icc t).symm
  have hsum : (∑ n ∈ Icc 0 ⌊x⌋₊, f n * c n) = primeReciprocalSum ⌊x⌋₊ := by
    unfold primeReciprocalSum primesUpTo
    have hset : range (⌊x⌋₊ + 1) = Icc 0 ⌊x⌋₊ := by
      ext n
      simp only [mem_range, mem_Icc]
      omega
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · have hl : log (n : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      simp only [c, f, hp, if_true]
      field_simp
    · simp [c, hp]
  rw [hinit, hsum] at h
  simp_rw [hB] at h
  rw [← intervalIntegral.integral_of_le hx] at h
  have hint : -(∫ t in (2 : ℝ)..x, deriv f t * primeLogReciprocal t) =
      ∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl0 : log t ≠ 0 := (log_pos ht1).ne'
    simp only [hderiv t ht1]
    field_simp
  have hfx : f x * primeLogReciprocal x = primeLogReciprocal x / log x := by
    simp only [f]; ring
  linarith

/-- The integrand `R(t) / (t (log t)²)` of the remainder in Mertens' second theorem. -/
noncomputable def mertensKernel (t : ℝ) : ℝ := mertensRemainder t * (t⁻¹ / (log t) ^ 2)

theorem measurable_mertensKernel : Measurable mertensKernel :=
  measurable_mertensRemainder.mul (measurable_inv.div (measurable_log.pow_const 2))

/-- `|R(t) / (t (log t)²)| ≤ C / (t (log t)²)` whenever `|R(t)| ≤ C`. -/
theorem norm_mertensKernel_le {C t : ℝ} (ht : 0 ≤ t) (hR : |mertensRemainder t| ≤ C) :
    ‖mertensKernel t‖ ≤ C * (t⁻¹ / (log t) ^ 2) := by
  have hpos : 0 ≤ t⁻¹ / (log t) ^ 2 := by positivity
  rw [Real.norm_eq_abs, mertensKernel, abs_mul, abs_of_nonneg hpos]
  exact mul_le_mul_of_nonneg_right hR hpos

/-- The error integral `∫_2^∞ R(t) / (t (log t)²) dt` converges. -/
theorem integrableOn_mertensKernel : IntegrableOn mertensKernel (Set.Ioi 2) := by
  obtain ⟨C, _, hR⟩ := mertensRemainder_bound
  have hg : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi 2) :=
    (integrableOn_inv_div_log_sq_Ioi (by norm_num)).const_mul C
  refine hg.mono' measurable_mertensKernel.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : (2 : ℝ) ≤ t := le_of_lt ht
  exact norm_mertensKernel_le (by linarith) (hR t ht2)

/-- The constant `B` in `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
noncomputable def mertensSecondConstant : ℝ :=
  1 - log (log 2) + ∫ t in Set.Ioi (2 : ℝ), mertensKernel t

/-- The remainder in Mertens' second theorem:
`∑_{p ≤ x} 1/p - log log x - B = R(x)/log x - ∫_x^∞ R(t)/(t (log t)²) dt`. -/
theorem mertensSecond_error_eq {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant) =
      mertensRemainder x / log x - ∫ t in Set.Ioi x, mertensKernel t := by
  have hlx : 0 < log x := log_pos (by linarith)
  have hlog : ContinuousOn log (Set.Icc 2 x) := fun t ht =>
    (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
  have hK : IntervalIntegrable mertensKernel volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      (integrableOn_mertensKernel.mono_set Set.Ioc_subset_Ioi_self)
  have hL : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ((continuousOn_id' _).inv₀ fun t ht => ?_).div hlog fun t ht => ?_
    · exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
    · exact (log_pos (by linarith [ht.1])).ne'
  have hsplit : (∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2)) =
      (∫ t in (2 : ℝ)..x, t⁻¹ / log t) + ∫ t in (2 : ℝ)..x, mertensKernel t := by
    rw [← intervalIntegral.integral_add hL hK]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    simp only [mertensKernel, mertensRemainder]
    field_simp
    ring
  have hloglog : (∫ t in (2 : ℝ)..x, t⁻¹ / log t) = log (log x) - log (log 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hL
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact (Real.hasDerivAt_log ht0).log hl0
  have htail := integral_interval_sub_Ioi integrableOn_mertensKernel hx
  have hBx : primeLogReciprocal x / log x = 1 + mertensRemainder x / log x := by
    unfold mertensRemainder
    field_simp
    ring
  rw [primeReciprocalSum_abel hx, hsplit, hloglog, hBx]
  unfold mertensSecondConstant
  linarith

/-- Mertens' second theorem: `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
theorem mertensSecond :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤ C / log x := by
  obtain ⟨C, hC, hR⟩ := mertensRemainder_bound
  refine ⟨2 * C, by positivity, fun x hx => ?_⟩
  have hlx : 0 < log x := log_pos (by linarith)
  rw [mertensSecond_error_eq hx]
  have h1 : |mertensRemainder x / log x| ≤ C / log x := by
    rw [abs_div, abs_of_pos hlx]
    exact div_le_div_of_nonneg_right (hR x hx) hlx.le
  have h2 : ‖∫ t in Set.Ioi x, mertensKernel t‖ ≤ C / log x :=
    norm_integral_Ioi_le_div_log (by linarith) fun t ht =>
      norm_mertensKernel_le (by linarith [ht.out]) (hR t (hx.trans ht.out.le))
  rw [Real.norm_eq_abs] at h2
  calc
    _ ≤ |mertensRemainder x / log x| + |∫ t in Set.Ioi x, mertensKernel t| := abs_sub _ _
    _ ≤ C / log x + C / log x := add_le_add h1 h2
    _ = 2 * C / log x := by ring

/-- Natural-number form of Mertens' second theorem. -/
theorem mertensSecond_nat :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - (log (log n) + mertensSecondConstant)| ≤
        C / log n := by
  obtain ⟨C, hC, h⟩ := mertensSecond
  exact ⟨C, hC, fun n hn => by simpa [Nat.floor_natCast] using h n (by exact_mod_cast hn)⟩
end ErdosStraus.PrimeEstimates.Mertens
namespace ErdosStraus.PrimeEstimates

open Finset
open scoped BigOperators

/-- `∑_{k ≤ K} 1/k² ≤ 2`, by telescoping against `2(1/k - 1/(k+1))`. -/
theorem sum_reciprocal_sq_le_two (K : ℕ) :
    (∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) ≤ 2 := by
  have hdom : (∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) ≤
      ∑ k ∈ Icc 1 K, 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hnextpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc
      (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hkpos) (mul_pos hkpos hnextpos)).mpr
        nlinarith
      _ = 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
        field_simp
        ring
  have hset : Icc 1 K = Ico 1 (K + 1) := by ext k; simp only [mem_Icc, mem_Ico]; omega
  have htel : (∑ k ∈ Icc 1 K, 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1))) =
      2 * (1 - 1 / ((K + 1 : ℕ) : ℝ)) := by
    rw [hset, ← Finset.mul_sum]
    have hh := sum_Ico_weight_differences (fun k : ℕ => (1 : ℝ) / k)
      (m := 1) (n := K + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, div_one] using
      congrArg (fun y : ℝ => 2 * y) hh
  rw [htel] at hdom
  have hnonneg : (0 : ℝ) ≤ 1 / ((K + 1 : ℕ) : ℝ) := by positivity
  linarith

end ErdosStraus.PrimeEstimates

/-! ## Euler products at integers -/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset Real
open scoped BigOperators

theorem primesUpTo_eq_filter_Icc (n : ℕ) :
    primesUpTo n = (Icc 0 n).filter Nat.Prime := by
  ext p
  simp only [mem_primesUpTo, mem_filter, mem_Icc, Nat.zero_le, true_and]
  tauto

theorem prime_square_sum_le_two (n : ℕ) :
    (∑ p ∈ primesUpTo n, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  apply le_trans _ (sum_reciprocal_sq_le_two n)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp', hpn⟩ := mem_primesUpTo.mp hp
    exact mem_Icc.mpr ⟨hp'.pos, hpn⟩
  · intro p _ _; positivity

/-- `∑_{p ≤ n} 1/p - log log n` is bounded for `n ≥ 2`. -/
theorem reciprocal_defect_bounded :
    ∃ E > 0, ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - log (log n)| ≤ E := by
  obtain ⟨C, hC, h⟩ := mertensSecond_nat
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨C / log 2 + |mertensSecondConstant| + 1, by positivity, ?_⟩
  intro n hn
  have hln : log (2 : ℝ) ≤ log n := log_le_log (by norm_num) (by exact_mod_cast hn)
  have hh := (h n hn).trans (div_le_div_of_nonneg_left hC.le hl2 hln)
  have heq : primeReciprocalSum n - log (log n) =
      (primeReciprocalSum n - (log (log n) + mertensSecondConstant)) +
        mertensSecondConstant := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

/-- The difference `∑_{p ≤ n} (-log(1 - 1/p) - 1/p)` between `-log ∏_{p ≤ n} (1 - 1/p)` and
`∑_{p ≤ n} 1/p`. -/
noncomputable def correction (n : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo n, (-log (1 - 1 / (p : ℝ)) - 1 / p)

theorem correction_bounds (n : ℕ) : 0 ≤ correction n ∧ correction n ≤ 4 := by
  have hlocal : ∀ p ∈ primesUpTo n,
      0 ≤ -log (1 - 1 / (p : ℝ)) - 1 / p ∧
        -log (1 - 1 / (p : ℝ)) - 1 / p ≤ 2 / (p : ℝ) ^ 2 := by
    intro p hp
    have hp' := (mem_primesUpTo.mp hp).1
    have hu := Real.log_le_sub_one_of_pos (primeFactor_pos hp')
    have ha := (abs_le.mp (abs_log_primeFactor_add_le hp')).1
    constructor <;> linarith
  constructor
  · exact Finset.sum_nonneg (fun p hp => (hlocal p hp).1)
  · calc
      correction n ≤ ∑ p ∈ primesUpTo n, 2 / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
      _ = 2 * ∑ p ∈ primesUpTo n, (1 : ℝ) / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
      _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (prime_square_sum_le_two n) (by norm_num)
      _ = 4 := by norm_num

theorem log_product_identity (n : ℕ) :
    log (primeProduct n) = -primeReciprocalSum n - correction n := by
  rw [log_primeProduct]
  unfold primeReciprocalSum correction
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- `∏_{p ≤ n} (1 - 1/p) ≍ 1/log n` for `n ≥ 2`. -/
theorem product_bounds_nat :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      c / log n ≤ primeProduct n ∧ primeProduct n ≤ C / log n := by
  obtain ⟨E, hE, h⟩ := reciprocal_defect_bounded
  refine ⟨exp (-(E + 4)), exp (E + 4), exp_pos _, exp_pos _, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln := log_pos hn1
  have hP := primeProduct_pos n
  have hcorr := correction_bounds n
  have hlog : |log (primeProduct n) + log (log n)| ≤ E + 4 := by
    rw [log_product_identity]
    have heq : -primeReciprocalSum n - correction n + log (log n) =
        -(primeReciprocalSum n - log (log n)) - correction n := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by rw [abs_neg, abs_of_nonneg hcorr.1]; linarith [h n hn])
  have hlow := Real.exp_le_exp.mpr (abs_le.mp hlog).1
  have hupp := Real.exp_le_exp.mpr (abs_le.mp hlog).2
  rw [exp_add, exp_log hP, exp_log hln] at hlow hupp
  exact ⟨(div_le_iff₀ hln).mpr hlow, (le_div_iff₀ hln).mpr hupp⟩
end ErdosStraus.PrimeEstimates.Mertens

/- The following terminal-volume comparison is from the published Goldbach proof FareySieveTerminalFloor.lean at 7dfa6251c81d297b9d632d84c9892da7a1c35739, Apache-2.0. -/
/-!
# PREPUB goldbach gap: `L-goldbach-farey-sieve-terminal-floor`

On the Farey middle third the normalized sieve mass `V n z` dominates `(2/3)·|I|·M(z)²`.
The proof splits the prime factors `p ≤ √n` into those dividing `n` (local factor
`1 - 1/p`) and those not dividing `n` (local factor `(1 - 1/p)²/(1 - 2/p)`), then bounds

* `∏_{p ∣ n, p ≤ √n} (1 - 1/p) ≤ 1/2` (the prime `2` divides the even number `n`),
* `∏_{p ≤ √n, p ∤ n} (1 - 1/p)²/(1 - 2/p) ≤ 2` (a Wallis-type telescoping product),
* `∏_{p ∣ n, p > √n} (1 - 1/p) ≥ 4/5` (at most one such prime, and it is at least `5`).
-/


open scoped BigOperators
open Finset

namespace PEqualNP.Outside

/-- The Wallis-type factor `m²/((m-1)(m+1)) = 1 + 1/(m²-1)`. -/
noncomputable def wallisFac (m : ℕ) : ℝ := (m:ℝ)^2 / (((m:ℝ)-1)*((m:ℝ)+1))

/-- Wallis-type telescoping product: `∏_{m=2}^{M} wallisFac m = 2M/(M+1)`. -/
theorem wallis_telescope : ∀ M : ℕ, 1 ≤ M →
    ∏ m ∈ Finset.Icc 2 M, wallisFac m = 2*(M:ℝ)/((M:ℝ)+1) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => norm_num [wallisFac]
  | succ M hM ih =>
      rw [Finset.prod_Icc_succ_top (f := wallisFac) (by omega : 2 ≤ M + 1)]
      rw [ih]
      have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      have h1 : (M:ℝ) + 1 ≠ 0 := by positivity
      have h2 : (M:ℝ) + 2 ≠ 0 := by positivity
      simp only [wallisFac]
      push_cast
      field_simp [hM0, h1, h2]
      ring

/- PREPUB frozen statement `L-goldbach-farey-sieve-terminal-floor`. -/
set_option maxHeartbeats 1000000 in
theorem L_goldbach_farey_sieve_terminal_floor :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3);
    let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime;
    let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹);
    let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ));
    ∀ n : ℕ, 12 ≤ n → Even n → (2/3:ℝ)*((I n).card:ℝ)*(M (Nat.sqrt n))^2 ≤ V n (Nat.sqrt n) := by
  dsimp only
  classical
  intro n hn hEven
  set z : ℕ := Nat.sqrt n with hz
  set Pz : Finset ℕ := (Finset.Icc 2 z).filter Nat.Prime with hPz
  set Sz : Finset ℕ := Pz.filter (fun p => p ∣ n) with hSz
  set Tz : Finset ℕ := Pz.filter (fun p => ¬ p ∣ n) with hTz
  set Iz : Finset ℕ := Finset.Icc ((n+2)/3) ((2*n)/3) with hIz
  set Es : Finset ℕ := n.primeFactors.filter (fun p => z < p) with hEs
  set A : ℝ := ∏ p ∈ Sz, (1 - (p:ℝ)⁻¹) with hA
  set B : ℝ := ∏ p ∈ Tz, (1 - (p:ℝ)⁻¹) with hB
  set Tp : ℝ := ∏ p ∈ Tz, (1 - 2/(p:ℝ)) with hTp
  set E : ℝ := ∏ p ∈ Es, (1 - (p:ℝ)⁻¹) with hE
  have hn0 : n ≠ 0 := by omega
  have hz3 : 3 ≤ z := by
    rw [hz, Nat.le_sqrt']
    omega
  have hz_sq : z ^ 2 ≤ n := by rw [hz]; exact Nat.sqrt_le' n
  have hz_succ_sq : n < (z + 1) ^ 2 := by rw [hz]; exact Nat.lt_succ_sqrt' n
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp hEven
  -- |I| > 0
  have hIfact : Iz.card = (2*n)/3 + 1 - ((n+2)/3) := by rw [hIz]; exact Nat.card_Icc _ _
  have hIpos : (0:ℝ) < (Iz.card:ℝ) := by
    have hle : ((n+2)/3) ≤ ((2*n)/3) := by
      apply Nat.div_le_div_right; omega
    have hpos : 0 < Iz.card := by rw [hIfact]; omega
    exact_mod_cast hpos
  -- membership characterisations
  have hmemP : ∀ p : ℕ, p ∈ Pz ↔ p.Prime ∧ p ≤ z := by
    intro p
    rw [hPz, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, hpz⟩, hpp⟩; exact ⟨hpp, hpz⟩
    · rintro ⟨hpp, hpz⟩; exact ⟨⟨hpp.two_le, hpz⟩, hpp⟩
  have hmemS : ∀ p : ℕ, p ∈ Sz ↔ p.Prime ∧ p ∣ n ∧ p ≤ z := by
    intro p
    rw [hSz, Finset.mem_filter, hmemP]
    constructor
    · rintro ⟨⟨hpp, hpz⟩, hdvd⟩; exact ⟨hpp, hdvd, hpz⟩
    · rintro ⟨hpp, hdvd, hpz⟩; exact ⟨⟨hpp, hpz⟩, hdvd⟩
  have hmemT : ∀ p : ℕ, p ∈ Tz ↔ p.Prime ∧ ¬ p ∣ n ∧ p ≤ z := by
    intro p
    rw [hTz, Finset.mem_filter, hmemP]
    constructor
    · rintro ⟨⟨hpp, hpz⟩, hnd⟩; exact ⟨hpp, hnd, hpz⟩
    · rintro ⟨hpp, hnd, hpz⟩; exact ⟨⟨hpp, hpz⟩, hnd⟩
  have hmemE : ∀ p : ℕ, p ∈ Es ↔ p.Prime ∧ p ∣ n ∧ z < p := by
    intro p
    rw [hEs, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hpp, hdvd, -⟩, hzp⟩; exact ⟨hpp, hdvd, hzp⟩
    · rintro ⟨hpp, hdvd, hzp⟩; exact ⟨⟨hpp, hdvd, hn0⟩, hzp⟩
  have hdisj : Disjoint Sz Tz := by
    rw [hSz, hTz]
    exact Finset.disjoint_filter_filter_not _ _ _
  have hPsplit : Pz = Sz ∪ Tz := by
    rw [hSz, hTz]
    exact (Finset.filter_union_filter_not_eq (p := fun p => p ∣ n) Pz).symm
  -- `p ∈ Tz` is odd and at least 3
  have hT_three : ∀ p ∈ Tz, 3 ≤ p := by
    intro p hp
    have hpp : p.Prime := ((hmemT p).mp hp).1
    have hnd : ¬ p ∣ n := ((hmemT p).mp hp).2.1
    have hp2 : 2 ≤ p := hpp.two_le
    have hne2 : p ≠ 2 := by intro h; exact hnd (h ▸ h2dvd)
    have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hne2
    omega
  -- `Tp ≥ 0`
  have hTp_nonneg : 0 ≤ Tp := by
    rw [hTp]
    apply Finset.prod_nonneg
    intro p hp
    have hp3 : 3 ≤ p := hT_three p hp
    have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    have hpos : (0:ℝ) < (p:ℝ) := by linarith
    rw [sub_nonneg, div_le_one hpos]
    linarith
  -- the Wallis-type bound: `∏ (1-1/p)²/(1-2/p) ≤ 2`
  have hQ : (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ)))) ≤ 2 := by
    have hfac : ∀ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ))) = wallisFac (p - 1) := by
      intro p hp
      have hp3 : 3 ≤ p := hT_three p hp
      have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hp0
      have hp2a : (p:ℝ) - 2 ≠ 0 := by intro h; linarith
      have hp2b : (-2 + (p:ℝ)) ≠ 0 := by intro h; linarith
      have hA1 : (p:ℝ) - 1 - 1 ≠ 0 := by intro h; linarith
      have hA2 : (p:ℝ) - 1 + 1 ≠ 0 := by intro h; linarith
      have hden : (1:ℝ) - 2/(p:ℝ) ≠ 0 := by
        have hlt : (2:ℝ)/(p:ℝ) < 1 := by
          rw [div_lt_one hp0]; linarith
        linarith
      have h1 : (((p - 1 : ℕ)) : ℝ) = (p:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p)]
        norm_num
      simp only [wallisFac]
      rw [h1]
      field_simp
      ring
    have hstep : (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ))))
        = ∏ p ∈ Tz, wallisFac (p - 1) := Finset.prod_congr rfl hfac
    rw [hstep]
    have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑Tz : Set ℕ) := by
      intro a ha b hb hab
      have ha3 : 3 ≤ a := hT_three a ha
      have hb3 : 3 ≤ b := hT_three b hb
      have hab' : a - 1 = b - 1 := hab
      omega
    have hsubimg : (Tz.image (fun p => p - 1)) ⊆ Finset.Icc 2 (z - 1) := by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      have hp3 : 3 ≤ p := hT_three p hp
      have hpz : p ≤ z := ((hmemT p).mp hp).2.2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hfac1 : ∀ m ∈ Finset.Icc 2 (z - 1), (1:ℝ) ≤ wallisFac m := by
      intro m hm
      obtain ⟨hm2, -⟩ := Finset.mem_Icc.mp hm
      have hm2r : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
      have hpos : (0:ℝ) < ((m:ℝ)-1)*((m:ℝ)+1) := by nlinarith
      simp only [wallisFac]
      rw [le_div_iff₀ hpos]
      nlinarith
    have hfac0 : ∀ m ∈ Finset.Icc 2 (z - 1), (0:ℝ) ≤ wallisFac m := by
      intro m hm
      obtain ⟨hm2, -⟩ := Finset.mem_Icc.mp hm
      have hm2r : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
      have hpos : (0:ℝ) < ((m:ℝ)-1)*((m:ℝ)+1) := by nlinarith
      simp only [wallisFac]
      exact div_nonneg (sq_nonneg _) hpos.le
    calc ∏ p ∈ Tz, wallisFac (p - 1)
        = ∏ m ∈ Tz.image (fun p => p - 1), wallisFac m :=
          (Finset.prod_image (f := wallisFac) (g := fun p : ℕ => p - 1) hinj).symm
      _ ≤ ∏ m ∈ Finset.Icc 2 (z - 1), wallisFac m := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀ hsubimg
          · intro m hm
            exact hfac0 m (hsubimg hm)
          · intro m hm _
            exact hfac1 m hm
      _ = 2*(((z - 1 : ℕ)):ℝ)/((((z - 1 : ℕ)):ℝ)+1) := wallis_telescope (z - 1) (by omega)
      _ ≤ 2 := by
          have hz1 : (1:ℝ) ≤ (((z - 1 : ℕ)):ℝ) := by exact_mod_cast (by omega : 1 ≤ z - 1)
          have hden : (0:ℝ) < (((z - 1 : ℕ)):ℝ) + 1 := by linarith
          rw [div_le_iff₀ hden]
          nlinarith
  have hB2 : B ^ 2 ≤ 2 * Tp := by
    have heq : B ^ 2 = (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ)))) * Tp := by
      rw [hB, hTp, sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp3 : 3 ≤ p := hT_three p hp
      have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      have hden : (1:ℝ) - 2/(p:ℝ) ≠ 0 := by
        have hlt : (2:ℝ)/(p:ℝ) < 1 := by
          rw [div_lt_one hp0]; linarith
        linarith
      have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hp0
      have hp2a : (p:ℝ) - 2 ≠ 0 := by intro h; linarith
      have hp2b : (-2 + (p:ℝ)) ≠ 0 := by intro h; linarith
      have hA1 : (p:ℝ) - 1 - 1 ≠ 0 := by intro h; linarith
      have hA2 : (p:ℝ) - 1 + 1 ≠ 0 := by intro h; linarith
      field_simp
    rw [heq]
    nlinarith [hQ, hTp_nonneg]
  -- `A ≤ 1/2`: the prime `2` divides the even number `n`
  have h2S : (2:ℕ) ∈ Sz := (hmemS 2).mpr ⟨by norm_num, h2dvd, by omega⟩
  have hA2 : A ≤ 1/2 := by
    rw [hA]
    have heq : (∏ p ∈ Sz, (1 - (p:ℝ)⁻¹))
        = (∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹)) * (1 - (2:ℝ)⁻¹) :=
      Finset.prod_eq_prod_sdiff_singleton_mul h2S _
    rw [heq]
    have hrest_nonneg : 0 ≤ ∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro p hp
      have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
      have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
      have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
      linarith
    have hrest_le : (∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹)) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
        have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
        have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
        linarith
      · intro p hp
        have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
        have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
        have hinv : 0 ≤ (p:ℝ)⁻¹ := inv_nonneg.mpr hp1.le
        linarith
    have hconst : (1 - (2:ℝ)⁻¹) = 1/2 := by norm_num
    rw [hconst]
    nlinarith [hrest_nonneg, hrest_le]
  -- `E ≥ 4/5`: at most one prime factor of `n` exceeds `√n`, and it is at least 5
  have hEs_card : Es.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hne
    have hpp : p.Prime := ((hmemE p).mp hp).1
    have hqp : q.Prime := ((hmemE q).mp hq).1
    have hpd : p ∣ n := ((hmemE p).mp hp).2.1
    have hqd : q ∣ n := ((hmemE q).mp hq).2.1
    have hzp : z < p := ((hmemE p).mp hp).2.2
    have hzq : z < q := ((hmemE q).mp hq).2.2
    have hcop : p.Coprime q := (Nat.coprime_primes hpp hqp).mpr hne
    have hpqdvd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
    have hpqle : p * q ≤ n := Nat.le_of_dvd (by omega) hpqdvd
    have hpq_ge : (z + 1) ^ 2 ≤ p * q := by
      rw [pow_two]
      apply Nat.mul_le_mul <;> omega
    omega
  have hE_ge : (4/5:ℝ) ≤ E := by
    rw [hE]
    have hfac : ∀ p ∈ Es, (4/5:ℝ) ≤ (1 - (p:ℝ)⁻¹) := by
      intro p hp
      have hpp : p.Prime := ((hmemE p).mp hp).1
      have hzp : z < p := ((hmemE p).mp hp).2.2
      have hne2 : p ≠ 2 := by omega
      have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hne2
      have hp5 : 5 ≤ p := by omega
      have hp5r : (5:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp5
      have hinv : (p:ℝ)⁻¹ ≤ 1/5 := by
        have h5 : ((5:ℝ))⁻¹ = 1/5 := by norm_num
        rw [← h5]
        exact (inv_le_inv₀ (by linarith : (0:ℝ) < (p:ℝ)) (by norm_num : (0:ℝ) < 5)).mpr hp5r
      linarith
    have hc : Es.card = 0 ∨ Es.card = 1 := by omega
    rcases hc with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty]
      norm_num
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
      rw [hp, Finset.prod_singleton]
      exact hfac p (by rw [hp]; exact Finset.mem_singleton_self p)
  -- the totient factorisation `φ(n)/n = A · E`
  have hphi : ((n.totient:ℝ)/(n:ℝ)) = A * E := by
    have htot : ((n.totient:ℝ)/(n:ℝ)) = ∏ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹) := by
      have hcast : (n.totient:ℝ) * (∏ p ∈ n.primeFactors, (p:ℝ))
          = (n:ℝ) * (∏ p ∈ n.primeFactors, ((p:ℝ) - 1)) := by
        have hnat := Nat.totient_mul_prod_primeFactors n
        have h1 := congrArg (fun m : ℕ => (m:ℝ)) hnat
        push_cast at h1
        have hprod : (∏ p ∈ n.primeFactors, (((p - 1 : ℕ)) : ℝ))
            = ∏ p ∈ n.primeFactors, ((p:ℝ) - 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)), Nat.cast_one]
        rw [hprod] at h1
        exact h1
      have hn0' : (n:ℝ) ≠ 0 := by positivity
      have hPne : (∏ p ∈ n.primeFactors, (p:ℝ)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro p hp
        have hpos : (0:ℝ) < (p:ℝ) := by
          have := (Nat.prime_of_mem_primeFactors hp).pos
          exact_mod_cast this
        linarith
      have hQP : ∏ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹)
          = (∏ p ∈ n.primeFactors, ((p:ℝ) - 1)) / (∏ p ∈ n.primeFactors, (p:ℝ)) := by
        have hfac : ∀ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹) = ((p:ℝ) - 1) / (p:ℝ) := by
          intro p hp
          have hpos : (0:ℝ) < (p:ℝ) := by
            have := (Nat.prime_of_mem_primeFactors hp).pos
            exact_mod_cast this
          have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hpos
          field_simp
        rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib]
      rw [hQP, div_eq_div_iff hn0' hPne]
      simpa [mul_comm] using hcast
    rw [htot, hA, hE, hEs]
    have hprod := Finset.prod_filter_mul_prod_filter_not (s := n.primeFactors)
      (p := fun p => p ≤ z) (f := fun p => (1 - (p:ℝ)⁻¹))
    have hnotle : n.primeFactors.filter (fun p => ¬ p ≤ z)
        = n.primeFactors.filter (fun p => z < p) := by
      apply Finset.filter_congr
      intro p _
      exact Nat.not_le
    rw [← hprod, hnotle]
    have hSz_eq : n.primeFactors.filter (fun p => p ≤ z) = Sz := by
      ext p
      rw [Finset.mem_filter, hmemS]
      constructor
      · rintro ⟨hp, hpz⟩
        obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
        exact ⟨hpp, hdvd, hpz⟩
      · rintro ⟨hpp, hdvd, hpz⟩
        exact ⟨Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hn0⟩, hpz⟩
    rw [hSz_eq]
  -- `A ≥ 0`
  have hA0 : 0 ≤ A := by
    rw [hA]
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := ((hmemS p).mp hp).1
    have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
    linarith
  -- assembly
  have hMz : (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹)) = A * B := by
    rw [hPsplit, Finset.prod_union hdisj, hA, hB]
  have hcore : (2/3:ℝ) * A^2 * B^2 ≤ A * E * Tp := by
    have h1 : (2/3:ℝ) * A^2 * B^2 ≤ (4/3) * A^2 * Tp := by
      have h := mul_le_mul_of_nonneg_left hB2 (by positivity : (0:ℝ) ≤ (2/3) * A^2)
      nlinarith [h]
    have h2 : (4/3:ℝ) * A^2 * Tp ≤ (2/3) * A * Tp := by
      have hAA : A^2 ≤ A * (1/2) := by nlinarith [hA0, hA2]
      have h := mul_le_mul_of_nonneg_right hAA hTp_nonneg
      nlinarith [h]
    have h3 : (2/3:ℝ) * A * Tp ≤ A * E * Tp := by
      have hAT : 0 ≤ A * Tp := mul_nonneg hA0 hTp_nonneg
      have h := mul_le_mul_of_nonneg_right hE_ge hAT
      nlinarith [h]
    linarith
  have hmain : (2/3:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2
      ≤ ((n.totient:ℝ)/(n:ℝ)) * (∏ p ∈ Tz, (1 - 2/(p:ℝ))) := by
    rw [hMz, hphi]
    calc (2/3:ℝ) * (A * B)^2 = (2/3:ℝ) * A^2 * B^2 := by ring
      _ ≤ A * E * Tp := hcore
      _ = (A * E) * Tp := by ring
  calc (2/3:ℝ) * (Iz.card:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2
      = (Iz.card:ℝ) * ((2/3:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2) := by ring
    _ ≤ (Iz.card:ℝ) * (((n.totient:ℝ)/(n:ℝ)) * (∏ p ∈ Tz, (1 - 2/(p:ℝ)))) :=
        mul_le_mul_of_nonneg_left hmain hIpos.le
    _ = (Iz.card:ℝ) * (n.totient:ℝ) / (n:ℝ) * (∏ p ∈ Tz, (1 - 2/(p:ℝ))) := by ring

end PEqualNP.Outside


/-! ## Platform module-name alias (the live guard requires the theorem named `<module>`) -/

/- PREPUB frozen statement `L-goldbach-farey-sieve-terminal-floor`, under its platform
module name. -/
set_option maxHeartbeats 1000000 in
theorem Conjectures.Goldbach.FareySieveTerminalFloor :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3);
    let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime;
    let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹);
    let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ));
    ∀ n : ℕ, 12 ≤ n → Even n → (2/3:ℝ)*((I n).card:ℝ)*(M (Nat.sqrt n))^2 ≤ V n (Nat.sqrt n) :=
  PEqualNP.Outside.L_goldbach_farey_sieve_terminal_floor

namespace GoldbachLatePrimeCounts
open GoldbachLateWindow GoldbachLateEstimates.FareyBrun
open ErdosStraus.PrimeEstimates.Mertens Finset Filter Real
noncomputable section

theorem logarithmic_floor : ∃ c : ℝ, 0<c ∧ ∀ n : ℕ, 64≤n → Even n →
    c*((n:ℝ)/(log n)^2) ≤ V n n.sqrt := by
  obtain ⟨a,_,ha,_,hM⟩ := product_bounds_nat
  refine ⟨a^2/6,by positivity,?_⟩
  intro n hn he
  have hy : 2 ≤ n.sqrt := Nat.le_sqrt'.mpr (by omega)
  have hyl : 0 < log (n.sqrt:ℝ) := log_pos (by exact_mod_cast (by omega : 1<n.sqrt))
  have hnl : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1<n))
  have hl : log (n.sqrt:ℝ) ≤ log n := log_le_log
    (by exact_mod_cast (by omega : 0<n.sqrt)) (by exact_mod_cast Nat.sqrt_le_self n)
  have hm : a/log n ≤ primeProduct n.sqrt :=
    (div_le_div_of_nonneg_left ha.le hyl hl).trans (hM n.sqrt hy).1
  have hp (z : ℕ) : primesUpTo z = primes z := by
    ext p
    simp only [mem_primesUpTo,primes,mem_filter,mem_Icc]
    exact ⟨fun H => ⟨⟨H.1.two_le,H.2⟩,H.1⟩,fun H => ⟨H.2,H.1.2⟩⟩
  have hf := Conjectures.Goldbach.FareySieveTerminalFloor n (by omega) he
  change (2/3:ℝ)*((window n).card:ℝ)*(∏ p ∈ primes n.sqrt, (1-(p:ℝ)⁻¹))^2 ≤ V n n.sqrt at hf
  unfold primeProduct at hm
  simp only [hp, one_div] at hm
  have hcard : n ≤ 4*(window n).card := by simp only [window,Nat.card_Icc]; omega
  have hi : (n:ℝ)/4 ≤ (window n).card := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    rw [mul_comm]; exact_mod_cast hcard
  calc
    _ = (2/3:ℝ)*((n:ℝ)/4)*(a/log n)^2 := by ring
    _ ≤ _ := (mul_le_mul (mul_le_mul_of_nonneg_left hi (by norm_num))
      (pow_le_pow_left₀ (by positivity) hm 2) (sq_nonneg _) (by positivity)).trans hf

def separatedCount (n : ℕ) (d : ℝ) := ∑ p ∈ band n,
  ((partners n p).filter (fun q : ℕ => (1+d)*p < (q:ℝ))).card

theorem separation_partition (n : ℕ) (d : ℝ) (hd : 0≤d) :
    distinctPairs n = ratioCount n d + separatedCount n d := by
  unfold distinctPairs ratioCount separatedCount ratioPartners
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  let D := (partners n p).filter (fun q => q≠p)
  have hmin {q : ℕ} (h : q∈partners n p) : p≤q := (mem_Icc.mp (mem_filter.mp h).1).1
  have hlo : D.filter (fun q : ℕ => (q:ℝ)≤(1+d)*p) =
      (partners n p).filter (fun q => p<q ∧ (q:ℝ)≤(1+d)*p) := by
    ext q; simp only [D,mem_filter]
    exact ⟨fun ⟨⟨h,hd'⟩,hr⟩ => ⟨h,lt_of_le_of_ne (hmin h) hd'.symm,hr⟩,
      fun ⟨h,hs,hr⟩ => ⟨⟨h,hs.ne'⟩,hr⟩⟩
  have hhi : D.filter (fun q : ℕ => ¬ (q:ℝ)≤(1+d)*p) =
      (partners n p).filter (fun q : ℕ => (1+d)*p < (q:ℝ)) := by
    ext q; simp only [D,mem_filter,not_le]
    refine ⟨fun ⟨⟨h,_⟩,hb⟩ => ⟨h,hb⟩,fun ⟨h,hb⟩ => ⟨⟨h,?_⟩,hb⟩⟩
    intro heq
    rw [heq] at hb
    nlinarith [mul_nonneg hd (Nat.cast_nonneg p : 0≤(p:ℝ))]
  rw [← hlo,← hhi,card_filter_add_card_filter_not]

/-- A fixed positive relative separation can be imposed on the two prime
factors, at any prescribed cost measured on the terminal main-term scale. -/
theorem separated_approximation (ε : ℝ) (hε : 0<ε) : ∃ d : ℝ, 0<d ∧ d≤1 ∧
    ∀ᶠ n : ℕ in atTop, Even n →
    0 ≤ ((firstHit n).card:ℝ)-2*(separatedCount n d:ℝ) ∧
      ((firstHit n).card:ℝ)-2*(separatedCount n d:ℝ) ≤ ε*V n n.sqrt := by
  obtain ⟨c,hc,hfloor⟩ := logarithmic_floor
  let d := min 1 (ε*c/96)
  have hd : 0<d := by dsimp [d]; positivity
  have hd1 : d≤1 := min_le_left .. 
  refine ⟨d,hd,hd1,?_⟩
  filter_upwards [relative_strip_bound d hd hd1,square_absorbed (ε/2) (by positivity),
    eventually_ge_atTop 64] with n hclose hsq hn
  intro he
  have hcost : 48*d ≤ (ε/2)*c := by linarith [show d≤ε*c/96 from min_le_right ..]
  have hscale := (mul_le_mul_of_nonneg_right hcost
    (show 0 ≤ (n:ℝ)/(log n)^2 by positivity)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hfloor n hn he) (show 0≤ε/2 by positivity))
  rw [diagonal_split n hn,separation_partition n d hd.le]
  push_cast
  constructor
  · linarith [Nat.cast_nonneg (ratioCount n d) (α:=ℝ),Nat.cast_nonneg (squarePairs n) (α:=ℝ)]
  · linarith only [hclose,hsq he,hscale]

end
end GoldbachLatePrimeCounts

/- Cube-to-square-root main-term comparison from catalogue proposal #2986. -/
namespace GoldbachLateDensity
open Finset Real Filter
open ErdosStraus.PrimeEstimates.Mertens
open scoped Topology BigOperators
noncomputable section

def low (n : ℕ) : ℝ := (n:ℝ)^(1/3:ℝ)
def high (n : ℕ) : ℝ := (n:ℝ)^(1/2:ℝ)
def strip (n : ℕ) := primesUpTo ⌊high n⌋₊ \ primesUpTo ⌊low n⌋₊
def good (n : ℕ) := (strip n).filter fun p => ¬p∣n
def mass (s : Finset ℕ) : ℝ := ∑ p ∈ s, 1/(p:ℝ)
def tail (n : ℕ) : ℝ := ∏ p ∈ good n, (1-2/(p:ℝ))

lemma endpoints (n : ℕ) (hn : 64≤n) : 4 ≤ low n ∧ low n ≤ high n := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  constructor
  · rw [low,one_div,Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
    rw [show (3:ℝ)=((3:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    norm_num
    exact_mod_cast hn
  · exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)

lemma strip_mem {n p : ℕ} (hp : p ∈ strip n) :
    p.Prime ∧ low n < p ∧ p ≤ ⌊high n⌋₊ := by
  obtain ⟨h,nl⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hpp,hh⟩ := mem_primesUpTo.mp h
  exact ⟨hpp,(Nat.floor_lt (by unfold low; positivity)).mp (by
    by_contra! hle; exact nl (mem_primesUpTo.mpr ⟨hpp,hle⟩)),hh⟩

lemma strip_mass (n : ℕ) (hn : 64≤n) :
    mass (strip n) = primeReciprocalSum ⌊high n⌋₊ - primeReciprocalSum ⌊low n⌋₊ := by
  have hsub : primesUpTo ⌊low n⌋₊ ⊆ primesUpTo ⌊high n⌋₊ := fun p hp =>
    mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp).1,(mem_primesUpTo.mp hp).2.trans
      (Nat.floor_mono (endpoints n hn).2)⟩
  apply eq_sub_of_add_eq
  exact Finset.sum_sdiff hsub

theorem strip_mass_error : ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 64≤n →
    |mass (strip n) - log (3/2:ℝ)| ≤ C / log n := by
  obtain ⟨C,hC,h⟩ := mertensSecond
  refine ⟨5*C,by positivity,?_⟩
  intro n hn
  obtain ⟨hl,hhl⟩ := endpoints n hn
  have h0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlog : 0<log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1<n))
  have hu := abs_le.mp (h (high n) (by linarith))
  have hd := abs_le.mp (h (low n) (by linarith))
  have ha : log (high n) = (1/2:ℝ)*log n := log_rpow h0 _
  have hb : log (low n) = (1/3:ℝ)*log n := log_rpow h0 _
  have hdiff : log (log (high n)) - log (log (low n)) = log (3/2:ℝ) := by
    rw [ha,hb,← log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [ha] at hu
  rw [hb] at hd
  rw [strip_mass n hn,← hdiff,ha,hb]
  have hu' : C/((1/2:ℝ)*log n) = 2*C/log n := by ring
  have hd' : C/((1/3:ℝ)*log n) = 3*C/log n := by ring
  rw [hu'] at hu
  rw [hd'] at hd
  rw [show 5*C/log (n:ℝ) = 2*C/log n + 3*C/log n by ring]
  rw [abs_le]
  constructor <;> linarith only [hu.1,hu.2,hd.1,hd.2]

theorem mass_limit : Tendsto (fun n => mass (strip n)) atTop (𝓝 (log (3/2:ℝ))) := by
  obtain ⟨C,_,h⟩ := strip_mass_error
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht : Tendsto (fun n : ℕ => C/log (n:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hl
  rw [Metric.tendsto_nhds] at ht ⊢
  intro ε hε
  filter_upwards [ht ε hε,eventually_ge_atTop 64] with n hne hn
  rw [Real.dist_eq] at hne ⊢
  exact (h n hn).trans_lt ((le_abs_self _).trans_lt (by simpa using hne))

/-- A product of divisors in the strip contains at most three distinct primes.
The estimate is uniform in the factorisation of the target integer. -/
lemma excluded_card (n : ℕ) (hn : 64≤n) :
    ((strip n).filter (fun p => p∣n)).card ≤ 3 := by
  let D := (strip n).filter (fun p => p∣n)
  have hpos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlog : 0<log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1<n))
  have hp (p : ℕ) (hp : p ∈ D) := strip_mem (mem_filter.mp hp).1
  have hsub : D ⊆ n.primeFactors := by
    intro p hp'
    exact Nat.mem_primeFactors.mpr ⟨(hp p hp').1,(mem_filter.mp hp').2,by omega⟩
  have hdvd : (∏ p ∈ D, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset D n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)
  have hle : (∏ p ∈ D, (p:ℝ)) ≤ n := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (by omega : 0<n) hdvd
  have hprod := log_le_log (Finset.prod_pos (fun p h => by exact_mod_cast (hp p h).1.pos)) hle
  rw [Real.log_prod (fun p h => by exact_mod_cast (hp p h).1.ne_zero)] at hprod
  have hsum : (D.card:ℝ) * ((1/3:ℝ)*log n) ≤ log n := by
    apply le_trans _ hprod
    rw [← nsmul_eq_mul,← sum_const]
    apply sum_le_sum
    intro p h
    rw [← Real.log_rpow hpos]
    exact log_le_log (Real.rpow_pos_of_pos hpos _) (hp p h).2.1.le
  change D.card ≤ 3
  have : (D.card:ℝ) * log n ≤ 3*log n := by linarith
  exact_mod_cast (le_of_mul_le_mul_right this hlog)

lemma lost_mass (n : ℕ) (hn : 64≤n) : 0 ≤ mass (strip n)-mass (good n) ∧
    mass (strip n)-mass (good n) ≤ 3/low n := by
  let D := (strip n).filter fun p => p∣n
  have hd : mass D + mass (good n) = mass (strip n) := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hl := (endpoints n hn).1
  have hd0 : 0 ≤ mass D := sum_nonneg fun p _ => by positivity
  have hdb : mass D ≤ 3/low n := by
    calc
      _ ≤ ∑ _p ∈ D, (1/low n) := sum_le_sum fun p hp =>
        one_div_le_one_div_of_le (by linarith) (strip_mem (mem_filter.mp hp).1).2.1.le
      _ = D.card * (1/low n) := by simp
      _ ≤ 3/low n := by
        rw [show (3:ℝ)/low n = 3*(1/low n) by ring]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast excluded_card n hn)
          (one_div_nonneg.mpr (by linarith))
  constructor <;> linarith

lemma low_tendsto : Tendsto low atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : 0<(1/3:ℝ))).comp (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem good_limit : Tendsto (fun n => mass (good n)) atTop (𝓝 (log (3/2:ℝ))) := by
  have ht : Tendsto (fun n : ℕ => 3/low n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop low_tendsto
  have hlost : Tendsto (fun n => mass (strip n)-mass (good n)) atTop (𝓝 0) :=
    squeeze_zero' ((eventually_ge_atTop 64).mono (fun n hn => (lost_mass n hn).1))
      ((eventually_ge_atTop 64).mono (fun n hn => (lost_mass n hn).2)) ht
  simpa only [sub_zero,sub_sub_cancel,Pi.sub_apply] using mass_limit.sub hlost

lemma log_tail_error (n : ℕ) (hn : 64≤n) :
    |log (tail n) + 2*mass (good n)| ≤ (8/low n)*mass (good n) := by
  have hL := (endpoints n hn).1
  have hp (p : ℕ) (h : p ∈ good n) : low n < p := (strip_mem (mem_filter.mp h).1).2.1
  have ht (p : ℕ) (h : p ∈ good n) : 2/(p:ℝ) ≤ 1/2 := by
    have h4 : (4:ℝ)≤p := hL.trans (hp p h).le
    apply (div_le_iff₀ (by linarith : (0:ℝ)<p)).mpr
    linarith
  have hprod (p : ℕ) (h : p ∈ good n) : 1-2/(p:ℝ)≠0 := by linarith [ht p h]
  rw [tail,Real.log_prod hprod,mass,mul_sum,← sum_add_distrib,mul_sum]
  refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum ?_)
  intro p h
  have hpp : (0:ℝ)<p := by linarith [hp p h]
  have hsmall := abs_log_one_sub_add_le (div_pos (by norm_num : (0:ℝ)<2) hpp) (ht p h)
  calc
    _ = |log (1-2/(p:ℝ)) + 2/(p:ℝ)| := by rw [mul_one_div]
    _ ≤ _ := hsmall
    _ = (8*(1/(p:ℝ)))*(1/(p:ℝ)) := by ring
    _ ≤ _ := by
      rw [show (8:ℝ)/low n = 8*(1/low n) by ring]
      gcongr
      exact (hp p h).le

lemma tail_pos (n : ℕ) (hn : 64 ≤ n) : 0 < tail n := by
  apply Finset.prod_pos
  intro p hp
  have hbig := (strip_mem (mem_filter.mp hp).1).2.1
  have hL := (endpoints n hn).1
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

theorem tail_limit : Tendsto tail atTop (𝓝 (4/9:ℝ)) := by
  have h0 : Tendsto (fun n : ℕ => 8/low n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop low_tendsto
  have hupper : Tendsto (fun n => (8/low n)*mass (good n)) atTop (𝓝 0) := by
    simpa only [zero_mul] using h0.mul good_limit
  have hd : Tendsto (fun n => log (tail n)+2*mass (good n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds] at hupper ⊢
    intro ε he
    filter_upwards [hupper ε he,eventually_ge_atTop 64] with n h hn
    simp only [Real.dist_eq,sub_zero] at h ⊢
    exact (log_tail_error n hn).trans_lt ((le_abs_self _).trans_lt h)
  have hm : Tendsto (fun n => 2*mass (good n)) atTop (𝓝 (2*log (3/2:ℝ))) :=
    tendsto_const_nhds.mul good_limit
  have hl : Tendsto (fun n => log (tail n)) atTop (𝓝 (-(2*log (3/2:ℝ)))) := by
    simpa only [Pi.sub_apply,add_sub_cancel_right,zero_sub] using hd.sub hm
  have heq : exp (-(2*log (3/2:ℝ))) = 4/9 := by
    rw [exp_neg,show 2*log (3/2:ℝ)=log (3/2:ℝ)+log (3/2:ℝ) by ring, exp_add,
      exp_log (by norm_num : 0 < (3/2:ℝ))]
    norm_num
  rw [← heq]
  apply (Real.continuous_exp.continuousAt.tendsto.comp hl).congr'
  filter_upwards [eventually_ge_atTop 64] with n hn
  exact exp_log (tail_pos n hn)

def factors (n z : ℕ) := (primesUpTo z).filter fun p => ¬p∣n
def vol (n z : ℕ) : ℝ := ((Icc ((n+2)/3) ((2*n)/3)).card:ℝ)*n.totient/n *
  ∏ p ∈ factors n z, (1-2/(p:ℝ))

lemma vol_pos (n z : ℕ) (hn : 64≤n) (he : Even n) : 0 < vol n z := by
  have hI : 0 < (Icc ((n+2)/3) ((2*n)/3)).card :=
    Finset.card_pos.mpr ⟨(n+2)/3, mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
  have hphi := Nat.totient_pos.mpr (by omega : 0<n)
  apply mul_pos (div_pos (mul_pos (by exact_mod_cast hI) (by exact_mod_cast hphi))
    (by exact_mod_cast (by omega : 0<n)))
  apply Finset.prod_pos
  intro p hp
  obtain ⟨hprod,hnd⟩ := mem_filter.mp hp
  have hp2 := (mem_primesUpTo.mp hprod).1.two_le
  have hne : p≠2 := fun hh => hnd (hh ▸ even_iff_two_dvd.mp he)
  have hr : (2:ℝ)<p := by exact_mod_cast (by omega : 2<p)
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hr)

lemma volume_ratio (n : ℕ) (hn : 64≤n) (he : Even n) :
    vol n ⌊low n⌋₊ / vol n n.sqrt = (tail n)⁻¹ := by
  have hs : ⌊high n⌋₊ = n.sqrt := by
    change ⌊(n:ℝ)^(1/2:ℝ)⌋₊ = _
    rw [←sqrt_eq_rpow,nat_floor_real_sqrt_eq_nat_sqrt]
  have hsub : factors n ⌊low n⌋₊ ⊆ factors n ⌊high n⌋₊ := by
    intro p hp
    obtain ⟨hh,hnd⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hh).1,
      (mem_primesUpTo.mp hh).2.trans (Nat.floor_mono (endpoints n hn).2)⟩,hnd⟩
  have hset : factors n ⌊high n⌋₊ \ factors n ⌊low n⌋₊ = good n := by
    ext p
    simp only [factors,good,strip,Finset.mem_sdiff,mem_filter]
    exact ⟨fun ⟨⟨hh,hnd⟩,hl⟩ => ⟨⟨hh,fun h => hl ⟨h,hnd⟩⟩,hnd⟩,
      fun ⟨⟨hh,hl⟩,hnd⟩ => ⟨⟨hh,hnd⟩,fun h => hl h.1⟩⟩
  have hfac : vol n ⌊high n⌋₊ = tail n*vol n ⌊low n⌋₊ := by
    have hprod := Finset.prod_sdiff (f:=fun p : ℕ => 1-2/(p:ℝ)) hsub
    rw [hset] at hprod
    unfold vol tail
    rw [←hprod]
    ring
  rw [← hs,hfac]
  field_simp [(vol_pos n ⌊low n⌋₊ hn he).ne',(tail_pos n hn).ne']

theorem sharp_ratio (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, 64≤N ∧ ∀ n : ℕ, N≤n →
    Even n → |vol n ⌊low n⌋₊/vol n n.sqrt-9/4| ≤ ε := by
  have hi : Tendsto (fun n => (tail n)⁻¹) atTop (𝓝 (9/4:ℝ)) := by
    convert tail_limit.inv₀ (by norm_num : (4/9:ℝ)≠0) using 1 <;> norm_num
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hi) ε hε)
  refine ⟨max 64 N,le_max_left ..,?_⟩
  intro n hn he
  rw [volume_ratio n ((le_max_left ..).trans hn) he]
  exact (hN n ((le_max_right ..).trans hn)).le

end
end GoldbachLateDensity

theorem Conjectures.Goldbach.FareyCubeSqrtDensityRatio :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 64 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n → |V n (Z₁ n) / V n n.sqrt - 9/4| ≤ ε := by
  have hP (z : ℕ) : (Finset.Icc 2 z).filter Nat.Prime =
      ErdosStraus.PrimeEstimates.Mertens.primesUpTo z := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Icc,ErdosStraus.PrimeEstimates.Mertens.mem_primesUpTo]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.two_le,h.2⟩,h.1⟩⟩
  dsimp only
  simp only [hP]
  exact GoldbachLateDensity.sharp_ratio

namespace GoldbachLatePrimeCounts
open GoldbachLateWindow Filter

/-- HD-8015 follows from a fixed saving below 7/4 for the two oriented
    separated-factor counts. The relative separation is fixed before n varies. -/
theorem from_separated_margin (η : ℝ) (hη : 0<η) :
    ∃ d : ℝ, 0<d ∧ d≤1 ∧
      ((∀ᶠ n : ℕ in atTop, Even n →
        2*(separatedCount n d:ℝ) ≤ (7/4-η)*V n n.sqrt) →
      ∃ N : ℕ, 64≤N ∧ ∀ n : ℕ, N≤n → Even n →
        (firstHit n).card ≤ V n (cubeCut n) - V n n.sqrt + V n n.sqrt/2) := by
  obtain ⟨d,hd,hd1,hstrip⟩ := separated_approximation (η/2) (by positivity)
  refine ⟨d,hd,hd1,?_⟩
  intro hsep
  obtain ⟨K,hK,hlim⟩ := Conjectures.Goldbach.FareyCubeSqrtDensityRatio (η/2) (by positivity)
  obtain ⟨C,hC,hgrowth⟩ := terminal_growth
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hsep.and hstrip)
  refine ⟨max K N,hK.trans (le_max_left ..),?_⟩
  intro n hn he
  have hKn := (le_max_left K N).trans hn
  have hn64 := hK.trans hKn
  have hv : 0 < V n n.sqrt := (show 0 < C*(n:ℝ)^(3/4:ℝ) by
    have : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    positivity).trans_le (hgrowth n hn64 he)
  have hr : |V n (cubeCut n)/V n n.sqrt - 9/4| ≤ η/2 := hlim n hKn he
  have hl : 9/4-η/2 ≤ V n (cubeCut n)/V n n.sqrt := by
    linarith only [(abs_le.mp hr).1]
  obtain ⟨hs,ht⟩ := hN n ((le_max_right K N).trans hn)
  linarith only [(le_div_iff₀ hv).mp hl,hs he,(ht he).2]

end GoldbachLatePrimeCounts
