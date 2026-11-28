import Mathlib

/-- Separate the exceptional Chen summand and transport the quadratic sample to square indices. -/
-- child 1 zh: 在目标 6s+4 上分离加数 3，并把其余陈素数对化为模六指标和。
-- child 1 en: Separate the summand three and reduce the remaining Chen pairs to residue-class indices.
-- child 2 zh: 判定平方目标上的例外加数 3，并证明模三障碍。
-- child 2 en: Identify the quadratic prime pattern and its modulo-three obstruction.
-- child 3 zh: 用整数平方根精确重排带任意筛选条件的平方样本。
-- child 3 en: Reindex filtered square samples by their integer square root.
-- child 4 zh: 控制平方样本中同时避开特殊素数形式和两个陈指标之和的例外数。
-- child 4 en: Bound the uncovered square indices after the exceptional branch and the Chen index sumset are removed.

theorem Conjectures.Cuts.Cut7efff205cefc119489df1080
    (h₁ : let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  ∀ s : ℕ, 1 ≤ s → ((∃ p q : ℕ, ch p ∧ ch q ∧ p+q=6*s+4) ↔
    ch (6*s+1) ∨ ∃ a b : ℕ, a+b+1=s ∧ ch (6*a+5) ∧ ch (6*b+5)))
    (h₂ : let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  ∀ t : ℕ, 1 ≤ t → (ch (6*t^2+1) ↔ (t^2=1 ∨ 3∣t^2) ∧ Nat.Prime (6*t^2+1) ∧ Nat.Prime (2*t^2+1)))
    (h₃ : by
  classical
  exact ∀ (X : ℕ) (P : ℕ → Bool), ((Finset.Icc 1 X).filter (fun t => P (t^2) = true)).card =
    ((Finset.Icc 1 (X^2)).filter (fun s => s.sqrt^2=s ∧ P s = true)).card)
    (h₄ : by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
    let B := fun s : ℕ => ¬ ((s=1 ∨ 3∣s) ∧ Nat.Prime (6*s+1) ∧ Nat.Prime (2*s+1)) ∧ ¬ ((Finset.range s).filter (fun a => ch (6*a+5) ∧ ch (6*(s-1-a)+5))).Nonempty
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∃ T : ℕ, ∀ X ≥ T,
      (((Finset.Icc 1 (X^2)).filter (fun s => s.sqrt^2=s ∧ B s)).card:ℝ) ≤ (X:ℝ)^(1-δ))
    : (by
  classical
  let chen := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  let good := fun n : ℕ => ∃ p q : ℕ, chen p ∧ chen q ∧ p+q=n
  exact ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ T : ℕ, ∀ X : ℕ, T ≤ X → (((Finset.Icc 1 X).filter (fun t => ¬good (6*t^2+4))).card:ℝ) ≤ (X:ℝ)^(1-δ)) := by
  classical
  let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  let B := fun s : ℕ => ¬ ((s=1 ∨ 3∣s) ∧ Nat.Prime (6*s+1) ∧ Nat.Prime (2*s+1)) ∧ ¬ ((Finset.range s).filter (fun a => ch (6*a+5) ∧ ch (6*(s-1-a)+5))).Nonempty
  have idx (s : ℕ) : (∃ a b : ℕ, a+b+1=s ∧ ch (6*a+5) ∧ ch (6*b+5)) ↔ ((Finset.range s).filter (fun a => ch (6*a+5) ∧ ch (6*(s-1-a)+5))).Nonempty := by
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),ha,(show b=s-1-a by omega) ▸ hb⟩⟩
    · rintro ⟨a,ha⟩
      obtain ⟨hr,hp,hq⟩ := Finset.mem_filter.mp ha
      have := Finset.mem_range.mp hr
      exact ⟨a,s-1-a,by omega,hp,hq⟩
  obtain ⟨δ,hδ,hδ',T,hT⟩ := h₄
  refine ⟨δ,hδ,hδ',T,?_⟩
  intro X hX
  have he : (Finset.Icc 1 X).filter (fun t => ¬ ∃ p q : ℕ, ch p ∧ ch q ∧ p+q=6*t^2+4) =
      (Finset.Icc 1 X).filter (fun t => B (t^2)) := by
    apply Finset.filter_congr
    intro t ht
    have ht' := (Finset.mem_Icc.mp ht).1
    change (¬ ∃ p q : ℕ, ch p ∧ ch q ∧ p+q=6*t^2+4) ↔ _
    rw [h₁ (t^2) (by simpa using Nat.pow_le_pow_left ht' 2), h₂ t ht',idx (t^2)]
    exact not_or
  change (((Finset.Icc 1 X).filter (fun t => ¬ ∃ p q : ℕ, ch p ∧ ch q ∧ p+q=6*t^2+4)).card:ℝ) ≤ _
  rw [he]
  have hcard : ((Finset.Icc 1 X).filter (fun t => B (t^2))).card =
      ((Finset.Icc 1 (X^2)).filter (fun s => s.sqrt^2=s ∧ B s)).card := by
    convert h₃ X (fun s => decide (B s)) using 2 <;> ext j <;> simp
  rw [hcard]
  exact hT X hX
