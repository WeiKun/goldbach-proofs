import Mathlib

/-- Pass from bounded prime reservoirs for all finite horizons to a common reservoir. -/
-- child 1 zh: 从任意布尔选取序列抽出一个在每个有限前缀上与任意晚选取相符的极限。
-- child 1 en: Extract one Boolean mask matching arbitrarily late finite prefixes of a sequence.
-- child 2 zh: 证明素数集的用量和短窗例外计数仅依赖截至窗口右端点的选取。
-- child 2 en: Prove that reservoir size and the exceptional-window count depend only on the mask up to the window endpoint.
-- child 3 zh: 对每个有限截止 K，用统一常数构造有限素数集，同时控制所有截至 K 的窗口及用量。
-- child 3 en: At each finite horizon construct a prime reservoir with uniform constants for all eligible scales up to that horizon.

theorem Conjectures.Cuts.Cute705b55732a2fe45e8129f94
    (h₁ : ∀ A : ℕ → ℕ → Bool, ∃ b : ℕ → Bool, ∀ R : ℕ, ∃ k ≥ R, ∀ p ≤ R, A k p=b p)
    (h₂ : by
  classical
  exact let count := fun (u : ℕ → Bool) (n : ℕ) => ((Finset.Icc 1 n).filter (fun p => u p=true ∧ Nat.Prime (n-p))).card
    let misses := fun (u : ℕ → Bool) (X H : ℕ) (z : ℝ) => ((Finset.Ioc X (X+H)).filter (fun n => Even n ∧ (count u n:ℝ)<z)).card
    ∀ (u v : ℕ → Bool) (X H : ℕ) (z : ℝ), (∀ p ≤ X+H, u p=v p) →
    (((Finset.Icc 1 X).filter (fun p => u p=true)).card = ((Finset.Icc 1 X).filter (fun p => v p=true)).card) ∧ misses u X H z = misses v X H z)
    (h₃ : by
  classical
  exact let count := fun (u : ℕ → Bool) (n : ℕ) => ((Finset.Icc 1 n).filter (fun p => u p=true ∧ Nat.Prime (n-p))).card
    let misses := fun (u : ℕ → Bool) (X H : ℕ) (z : ℝ) => ((Finset.Ioc X (X+H)).filter (fun n => Even n ∧ (count u n:ℝ)<z)).card
    ∃ C c : ℝ, 0<C ∧ 0<c ∧ ∃ T : ℕ, ∀ K : ℕ, ∃ u : ℕ → Bool,
      (∀ p : ℕ, u p=true → p≤2*K ∧ Nat.Prime p) ∧ ∀ X : ℕ, T≤X → X≤K →
      (((Finset.Icc 1 X).filter (fun p => u p=true)).card:ℝ) ≤ C*Real.log (X:ℝ)*Real.log (Real.log (X:ℝ)) ∧
      ∀ H : ℕ, X≤H^2 → H≤X → (misses u X H (c*Real.log (Real.log (X:ℝ))):ℝ) ≤ C*(H:ℝ)/(Real.log (X:ℝ))^2)
    : (by
  classical
  exact ∃ B : Set ℕ, (∀ p ∈ B, Nat.Prime p) ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ T : ℕ, ∀ X : ℕ, T ≤ X →
    (((Finset.Icc 1 X).filter (fun p => p ∈ B)).card : ℝ) ≤ C*Real.log (X : ℝ)*Real.log (Real.log (X : ℝ)) ∧
    ∀ H : ℕ, X ≤ H^2 → H ≤ X →
      let small := fun n : ℕ => (((Finset.Icc 1 n).filter (fun p => p ∈ B ∧ Nat.Prime (n-p))).card : ℝ) < c*Real.log (Real.log (X : ℝ))
      (((Finset.Ioc X (X+H)).filter (fun n => Even n ∧ small n)).card : ℝ) ≤ C*(H : ℝ)/(Real.log (X : ℝ))^2) := by
  classical
  obtain ⟨C,c,hC,hc,T,hT⟩ := h₃
  choose A hA using hT
  obtain ⟨b,hb⟩ := h₁ A
  refine ⟨{p | b p=true},?_,C,c,hC,hc,T,?_⟩
  · intro p hp
    obtain ⟨k,hk,agree⟩ := hb p
    exact ((hA k).1 p ((agree p le_rfl).trans hp)).2
  · intro X hX
    obtain ⟨k,hk,agree⟩ := hb (2*X)
    have localBounds := (hA k).2 X hX (by omega)
    constructor
    · have sizeEq := (h₂ (A k) b X 0 0 (fun p hp => agree p (by omega))).1
      simpa only [sizeEq,Set.mem_setOf_eq] using localBounds.1
    · intro H hH hHX
      have exceptionEq := (h₂ (A k) b X H (c*Real.log (Real.log (X:ℝ))) (fun p hp => agree p (by omega))).2
      simpa only [exceptionEq,Set.mem_setOf_eq] using localBounds.2 H hH hHX
