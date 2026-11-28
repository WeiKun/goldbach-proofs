import Mathlib

theorem Conjectures.Cuts.Taskecdd8286c6771351e50a0f23 : (by
  classical
  exact ∀ m : ℕ, (∃ a b : ℕ, m=a^2+b^2) ↔ (m.primeFactors.filter (fun r => r % 4=3 ∧ ¬ Even (padicValNat r m))).card=0) := by
  classical
  intro m
  rw [Nat.eq_sq_add_sq_iff,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  constructor
  · intro h q hq hbad
    exact hbad.2 (h q hq hbad.1)
  · intro h q hq hmod
    by_contra hn
    exact h hq ⟨hmod,hn⟩
