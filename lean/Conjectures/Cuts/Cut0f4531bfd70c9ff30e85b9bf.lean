import Mathlib

/-- Transfer estimates from aligned square-root-scale blocks to all admissible short windows. -/
-- child 1 zh: 用整除商将闭窗口内的筛选指数覆盖到对齐的半开区块，并求总计数上界。
-- child 1 en: Cover a filtered closed window by aligned half-open blocks with a uniform bound.
-- child 2 zh: 用整数平方根控制相交区块的个数、尺度与位置。
-- child 2 en: Bound the number, scale and location of blocks meeting a square-root window.
-- child 3 zh: 在平方根尺度上把区块的幂节省传递到整个较长窗口。
-- child 3 en: Absorb the endpoint-block loss while transferring a power saving.
-- child 4 zh: 在与平方根尺度对齐的单个区块上估计缺少双陈素数表示的目标。
-- child 4 en: Bound Chen exceptions on a single aligned block at square-root scale.

theorem Conjectures.Cuts.Cut0f4531bfd70c9ff30e85b9bf
    (h₁ : by
  classical
  exact ∀ (X H w : ℕ) (P : ℕ → Bool) (M : ℝ), 0<w →
    (∀ j ∈ Finset.Icc (X/w) ((X+H)/w), (((Finset.Ico (j*w) ((j+1)*w)).filter (fun n => P n=true)).card:ℝ) ≤ M) →
    (((Finset.Icc X (X+H)).filter (fun n => P n=true)).card:ℝ) ≤ ((Finset.Icc (X/w) ((X+H)/w)).card:ℝ)*M)
    (h₂ : ∀ X H : ℕ, let w := X.sqrt
  4≤w → X≤H^2 → H≤X → w≤H ∧ H≤w^3 ∧ (Finset.Icc (X/w) ((X+H)/w)).card*w≤3*H ∧
    ∀ j ∈ Finset.Icc (X/w) ((X+H)/w), w≤j ∧ j≤8*w)
    (h₃ : ∀ δ : ℝ, 0<δ → δ<1 → ∃ T : ℕ, ∀ w H N : ℕ, T≤w → 1≤w → w≤H → H≤w^3 → N*w≤3*H →
    (N:ℝ)*(w:ℝ)^(1-δ) ≤ (H:ℝ)^(1-δ/4))
    (h₄ : by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
    let bad := fun n : ℕ => n % 6=4 ∧ ((Finset.range (n+1)).filter (fun p => ch p ∧ ch (n-p))).card=0
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∃ T : ℕ, ∀ w ≥ T, ∀ j : ℕ, w≤j → j≤8*w →
      (((Finset.Ico (j*w) ((j+1)*w)).filter bad).card:ℝ) ≤ (w:ℝ)^(1-δ))
    : (by
  classical
  let chen := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  let good := fun n : ℕ => ∃ p q : ℕ, chen p ∧ chen q ∧ p+q=n
  exact ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ T : ℕ, ∀ X : ℕ, T ≤ X → ∀ H : ℕ, X ≤ H^2 → H ≤ X →
    (((Finset.Icc X (X+H)).filter (fun n => n % 6=4 ∧ ¬good n)).card:ℝ) ≤ (H:ℝ)^(1-δ)) := by
  classical
  let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  let bad := fun n : ℕ => n % 6=4 ∧ ((Finset.range (n+1)).filter (fun p => ch p ∧ ch (n-p))).card=0
  let P := fun n : ℕ => decide (bad n)
  obtain ⟨δ,hδ,hδ',T,hlocal⟩ := h₄
  obtain ⟨S,hscale⟩ := h₃ δ hδ hδ'
  let A := max 4 (max T S)
  refine ⟨δ/4,by linarith,by linarith,A^2,?_⟩
  intro X hX H hmin hmax
  let w := X.sqrt
  have hA : A≤w := Nat.le_sqrt'.2 hX
  have h4w : 4≤w := le_trans (le_max_left _ _) hA
  have hwT : T≤w := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hA)
  have hwS : S≤w := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hA)
  obtain ⟨hwH,hHcube,hcount,hloc⟩ := h₂ X H h4w hmin hmax
  have hblock (j : ℕ) (hj : j ∈ Finset.Icc (X/w) ((X+H)/w)) :
      (((Finset.Ico (j*w) ((j+1)*w)).filter (fun n => P n=true)).card:ℝ) ≤ (w:ℝ)^(1-δ) := by
    obtain ⟨hl,hu⟩ := hloc j hj
    simpa [P,bad,ch] using hlocal w hwT j hl hu
  have hwindow := h₁ X H w P ((w:ℝ)^(1-δ)) (by omega) hblock
  have he : (Finset.Icc X (X+H)).filter (fun n => n % 6=4 ∧ ¬ ∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n) =
      (Finset.Icc X (X+H)).filter (fun n => P n=true) := by
    apply Finset.filter_congr
    intro n _
    have repr : (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n) ↔ ((Finset.range (n+1)).filter (fun p => ch p ∧ ch (n-p))).Nonempty := by
      constructor
      · rintro ⟨p,q,hp,hq,e⟩
        exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp,(show q=n-p by omega) ▸ hq⟩⟩
      · rintro ⟨p,hp⟩
        obtain ⟨hr,ha,hb⟩ := Finset.mem_filter.mp hp
        have := Finset.mem_range.mp hr
        exact ⟨p,n-p,ha,hb,by omega⟩
    simp only [P,decide_eq_true_eq,bad,repr,Finset.card_eq_zero,Finset.not_nonempty_iff_eq_empty]
  change (((Finset.Icc X (X+H)).filter (fun n => n % 6=4 ∧ ¬ ∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n)).card:ℝ) ≤ _
  rw [he]
  exact le_trans hwindow (hscale w H _ hwS (by omega) hwH hHcube hcount)
