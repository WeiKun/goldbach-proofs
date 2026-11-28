import Mathlib

/-- Transfer both prescribed Chen progressions into one compressed target interval. -/
-- child 1 zh: 把两端预定剩余类的陈素数表示精确换元为带进位的有界指标计数。
-- child 1 en: Reindex both prescribed Chen summands with the carry from their residues.
-- child 2 zh: 在压缩后的指标上解模六方程，得到唯一允许的剩余类。
-- child 2 en: Solve the modulo-six target condition on the compressed progression.
-- child 3 zh: 用两次向上取整除法精确重排闭区间内带筛选的等差数列。
-- child 3 en: Reindex a bounded filtered progression with both endpoint ceilings.
-- child 4 zh: 在压缩区间和指定模六指标类上控制没有陈素数配对的例外指标。
-- child 4 en: Estimate empty Chen fibers on the compressed interval and its single admissible class.

theorem Conjectures.Cuts.Cut253091d66a724f9e51bfa1c8
    (h₁ : by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
    let K := fun (d a b k : ℕ) => ((Finset.range (k+1)).filter (fun i => i+(a+b)/d ≤ k ∧ ch (d*i+a) ∧ ch (d*(k-i-(a+b)/d)+b))).Nonempty
    ∀ d a b n : ℕ, 0<d → a<d → b<d → n % d=(a+b) % d →
    ((∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ p % d=a ∧ q % d=b) ↔ K d a b (n/d)))
    (h₂ : ∀ d c k : ℕ, d.Coprime 6 → ((d*k+c) % 6=4 ↔ k % 6=(if d % 6=1 then (10-c % 6) % 6 else (c % 6+2) % 6)))
    (h₃ : by
  classical
  exact ∀ (L U d c : ℕ) (P : ℕ → Bool), 0<d → c<d →
    ((Finset.Icc L U).filter (fun n => n % d=c ∧ P (n/d)=true)).card =
      ((Finset.Ico (CeilDiv.ceilDiv (L-c) d) (CeilDiv.ceilDiv (U+1-c) d)).filter (fun k => P k=true)).card)
    (h₄ : by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
    let K := fun (d a b k : ℕ) => ((Finset.range (k+1)).filter (fun i => i+(a+b)/d ≤ k ∧ ch (d*i+a) ∧ ch (d*(k-i-(a+b)/d)+b))).Nonempty
    let R := fun (d c : ℕ) => if d % 6 = 1 then (10-c % 6) % 6 else (c % 6+2) % 6
    ∀ j : ℕ, ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∃ T : ℕ, ∀ X ≥ T, ∀ d a b : ℕ, 1≤d → d.Coprime 6 →
    (d:ℝ) ≤ (Real.log (X:ℝ))^j → a<d → b<d → (a*(a+2)*b*(b+2)).Coprime d →
    let c := (a+b) % d
    (((Finset.Ico (CeilDiv.ceilDiv (X-c) d) (CeilDiv.ceilDiv (2*X+1-c) d)).filter (fun k => k % 6=R d c ∧ ¬ K d a b k)).card:ℝ) ≤ ((X:ℝ)/(d:ℝ))^(1-δ))
    : (by
  classical
  let chen := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  exact ∀ k : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ T : ℕ, ∀ X : ℕ, T ≤ X → ∀ d a b : ℕ, 1 ≤ d → d.Coprime 6 → (d:ℝ) ≤ (Real.log (X:ℝ))^k → a < d → b < d → Nat.Coprime (a*(a+2)*b*(b+2)) d →
    let bad := fun n : ℕ => n % 6=4 ∧ n % d=(a+b) % d ∧ ¬ ∃ p q : ℕ, chen p ∧ chen q ∧ p+q=n ∧ p % d=a ∧ q % d=b
    (((Finset.Icc X (2*X)).filter bad).card:ℝ) ≤ ((X:ℝ)/(d:ℝ))^(1-δ)) := by
  classical
  let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  let K := fun (d a b k : ℕ) => ((Finset.range (k+1)).filter (fun i => i+(a+b)/d ≤ k ∧ ch (d*i+a) ∧ ch (d*(k-i-(a+b)/d)+b))).Nonempty
  let R := fun (d c : ℕ) => if d % 6 = 1 then (10-c % 6) % 6 else (c % 6+2) % 6
  intro _ch j
  obtain ⟨δ,hp,hl,T,hT⟩ := h₄ j
  refine ⟨δ,hp,hl,T,?_⟩
  intro X hX d a b hd h6 hlog ha hb hlocal
  let c := (a+b) % d
  let F := fun k : ℕ => k % 6=R d c ∧ ¬ K d a b k
  have hc : c<d := Nat.mod_lt _ hd
  have he : (Finset.Icc X (2*X)).filter (fun n => n % 6=4 ∧ n % d=c ∧ ¬ ∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ p % d=a ∧ q % d=b) =
      (Finset.Icc X (2*X)).filter (fun n => n % d=c ∧ F (n/d)) := by
    apply Finset.filter_congr
    intro n _
    by_cases hr : n % d=c
    · have rep : d*(n/d)+c=n := by simpa [hr, Nat.add_comm] using Nat.div_add_mod n d
      have hm := h₂ d c (n/d) h6
      rw [rep] at hm
      have hcq := h₁ d a b n hd ha hb hr
      change (_ ∧ _ ∧ ¬ _) ↔ _ ∧ _ ∧ _
      exact ⟨fun hh => ⟨hr,hm.mp hh.1,fun z => hh.2.2 (hcq.mpr z)⟩,
        fun hh => ⟨hm.mpr hh.2.1,hr,fun z => hh.2.2 (hcq.mp z)⟩⟩
    · simp [hr]
  change (((Finset.Icc X (2*X)).filter (fun n => n % 6=4 ∧ n % d=c ∧ ¬ ∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ p % d=a ∧ q % d=b)).card:ℝ) ≤ _
  rw [he]
  have hcard : ((Finset.Icc X (2*X)).filter (fun n => n % d=c ∧ F (n/d))).card =
      ((Finset.Ico (CeilDiv.ceilDiv (X-c) d) (CeilDiv.ceilDiv (2*X+1-c) d)).filter F).card := by
    convert h₃ X (2*X) d c (fun k => decide (F k)) hd hc using 2 <;> ext x <;> simp
  rw [hcard]
  exact hT X hX d a b hd h6 hlog ha hb hlocal
