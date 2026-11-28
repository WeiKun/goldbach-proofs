import Mathlib

/-- Count Gaussian-norm prime failures using a finite valuation sieve and a one-sided moment. -/
-- child 1 zh: 将自然数的两平方和表示判定为坏素因子集合为空。
-- child 1 en: Detect a sum of two squares by an empty finite valuation obstruction set.
-- child 2 zh: 若三整除两平方和，则九整除该数，除以九后仍是两平方和，反之亦然。
-- child 2 en: Descend a sum of two squares divisible by three by a factor of nine and lift it back.
-- child 3 zh: 以计数相对固定门槛的单侧平方亏损控制零表示目标数。
-- child 3 en: Control the zero fiber by the squared one-sided deficit from a threshold.
-- child 4 zh: 在允许的模九目标上，对归一化高斯范数素数配对数的平方亏损给出幂节省。
-- child 4 en: Bound the squared deficit of normalized Gaussian-norm prime representations on the admissible targets.

theorem Conjectures.Cuts.Cutcdb1553562dc6fb00abd8bd2
    (h₁ : by
  classical
  exact ∀ m : ℕ, (∃ a b : ℕ, m=a^2+b^2) ↔ (m.primeFactors.filter (fun r => r % 4=3 ∧ ¬ Even (padicValNat r m))).card=0)
    (h₂ : ∀ m : ℕ, 3∣m → ((∃ a b : ℕ, m=a^2+b^2) ↔ 9∣m ∧ ∃ a b : ℕ, m/9=a^2+b^2))
    (h₃ : by
  classical
  exact ∀ (S : Finset ℕ) (W : ℕ → ℕ) (z : ℝ), 0≤z →
    (((S.filter (fun n => W n=0)).card:ℝ)*z^2) ≤ ∑ n ∈ S, (max 0 (z-(W n:ℝ)))^2)
    (h₄ : by
  classical
  exact let cap := fun m : ℕ => (m.primeFactors.filter (fun r => r % 4=3 ∧ ¬ Even (padicValNat r m))).card=0
    let ok := fun p : ℕ => p.Prime ∧ (if 3∣p-1 then 9∣p-1 ∧ cap ((p-1)/9) else cap (p-1))
    let W := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => ok p ∧ ok (n-p))).card
    let S := fun X : ℕ => (Finset.Icc 2 X).filter (fun n => Even n ∧ n % 9≠5 ∧ n % 9≠8)
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∃ T : ℕ, ∀ X ≥ T,
      (∑ n ∈ S X, (max 0 (Real.sqrt (X:ℝ)-(W n:ℝ)))^2) ≤ (X:ℝ)^(1-δ)*(X:ℝ))
    : (let lp := fun p : ℕ => Nat.Prime p ∧ ∃ a b : ℕ, p=a^2+b^2+1; let bad := fun n : ℕ => Even n ∧ n % 9 ≠ 5 ∧ n % 9 ≠ 8 ∧ ¬ ∃ p q : ℕ, lp p ∧ lp q ∧ p+q=n; ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 2 X)).card : ℝ) ≤ (X : ℝ)^(1-δ)) := by
  classical
  intro lp bad
  let cap := fun m : ℕ => (m.primeFactors.filter (fun r => r % 4=3 ∧ ¬ Even (padicValNat r m))).card=0
  let ok := fun p : ℕ => p.Prime ∧ (if 3∣p-1 then 9∣p-1 ∧ cap ((p-1)/9) else cap (p-1))
  let W := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => ok p ∧ ok (n-p))).card
  let S := fun X : ℕ => (Finset.Icc 2 X).filter (fun n => Even n ∧ n % 9≠5 ∧ n % 9≠8)
  have equiv (p : ℕ) : lp p ↔ ok p := by
    change (p.Prime ∧ ∃ a b : ℕ, p=a^2+b^2+1) ↔ p.Prime ∧ _
    refine and_congr_right fun hp => ?_
    have hp1 := hp.one_lt
    have shift : (∃ a b : ℕ, p=a^2+b^2+1) ↔ ∃ a b : ℕ,p-1=a^2+b^2 := by
      constructor <;> rintro ⟨a,b,he⟩ <;> exact ⟨a,b,by omega⟩
    rw [shift]
    by_cases hd : 3∣p-1
    · simpa only [if_pos hd, h₂ (p-1) hd,h₁ ((p-1)/9),cap]
    · simpa only [if_neg hd,h₁ (p-1),cap]
  obtain ⟨δ,hδ,hδ',T,hT⟩ := h₄
  refine ⟨δ,hδ,hδ',max 2 T,?_⟩
  intro X hX
  have hX2 : 2≤X := (le_max_left _ _).trans hX
  have hXT : T≤X := (le_max_right _ _).trans hX
  have hx : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have sub : (@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 2 X)) ⊆ (S X).filter (fun n => W n=0) := by
    intro n hn
    have hn' : n ∈ Finset.Icc 2 X ∧ bad n := by
      simpa only [Finset.mem_filter] using hn
    obtain ⟨hr,he,h5,h8,hn⟩ := hn'
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr,he,h5,h8⟩,?_⟩
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp hh
    have hle := Finset.mem_range.mp hp
    exact hn ⟨p,n-p,(equiv p).mpr hh.1,(equiv _).mpr hh.2,by omega⟩
  have moment := h₃ (S X) W (Real.sqrt (X:ℝ)) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hx.le] at moment
  have bound : (((S X).filter (fun n => W n=0)).card:ℝ)*(X:ℝ) ≤ (X:ℝ)^(1-δ)*(X:ℝ) :=
    le_trans moment (hT X hXT)
  exact (Nat.cast_le.mpr (Finset.card_le_card sub)).trans ((le_of_mul_le_mul_right bound hx))
