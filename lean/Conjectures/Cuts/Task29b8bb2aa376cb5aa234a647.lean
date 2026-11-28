import Mathlib

theorem Conjectures.Cuts.Task29b8bb2aa376cb5aa234a647 : (by
  classical
  exact ∀ (X : ℕ) (P : ℕ → Bool), ((Finset.Icc 1 X).filter (fun t => P (t^2) = true)).card =
    ((Finset.Icc 1 (X^2)).filter (fun s => s.sqrt^2=s ∧ P s = true)).card) := by
  classical
  intro X P
  refine Finset.card_bij' (fun (t : ℕ) _ => t^2) (fun (s : ℕ) _ => (Nat.sqrt s)) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨ht,hP⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht1,htX⟩ := Finset.mem_Icc.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by simpa using Nat.pow_le_pow_left ht1 2,Nat.pow_le_pow_left htX 2⟩,by rw [Nat.sqrt_eq'],hP⟩
  · intro s hs
    obtain ⟨hs,he,hP⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs1,hsX⟩ := Finset.mem_Icc.mp hs
    have hi := Nat.sqrt_le_sqrt hsX
    rw [Nat.sqrt_eq'] at hi
    have lo : 1≤(Nat.sqrt s) := by
      by_contra! hz
      have z : (Nat.sqrt s)=0 := by omega
      simp [z] at he
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨lo,hi⟩,he.symm ▸ hP⟩
  · exact fun t _ => Nat.sqrt_eq' t
  · exact fun _ hs => (Finset.mem_filter.mp hs).2.1
