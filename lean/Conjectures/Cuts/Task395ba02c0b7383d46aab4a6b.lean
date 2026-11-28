import Mathlib

theorem Conjectures.Cuts.Task395ba02c0b7383d46aab4a6b : (by
  classical
  exact ∀ (L U d c : ℕ) (P : ℕ → Bool), 0<d → c<d →
    ((Finset.Icc L U).filter (fun n => n % d=c ∧ P (n/d)=true)).card =
      ((Finset.Ico (CeilDiv.ceilDiv (L-c) d) (CeilDiv.ceilDiv (U+1-c) d)).filter (fun k => P k=true)).card) := by
  classical
  intro L U d c P hd hc
  have lower (x k : ℕ) : CeilDiv.ceilDiv (x-c) d ≤ k ↔ x≤d*k+c := by
    rw [ceilDiv_le_iff_le_mul hd]
    omega
  have upper (x k : ℕ) : k<CeilDiv.ceilDiv (x-c) d ↔ d*k+c<x := by
    rw [← not_le,lower]
    omega
  refine Finset.card_bij' (fun (n : ℕ) _ => n/d) (fun (k : ℕ) _ => d*k+c) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hr,he,hP⟩ := Finset.mem_filter.mp hn
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hr
    have e : d*(n/d)+c=n := by rw [←he]; exact Nat.div_add_mod n d
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨(lower _ _).2 (by omega),(upper _ _).2 (by omega)⟩,hP⟩
  · intro k hk
    obtain ⟨hr,hP⟩ := Finset.mem_filter.mp hk
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hr
    have hl' := (lower _ _).1 hl
    have hu' := (upper _ _).1 hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl',by omega⟩,?_,?_⟩
    · rw [Nat.mul_add_mod,Nat.mod_eq_of_lt hc]
    · simpa only [Nat.mul_add_div hd,Nat.div_eq_of_lt hc, Nat.add_zero] using hP
  · intro n hn
    have hc' := (Finset.mem_filter.mp hn).2.1
    rw [←hc']
    exact Nat.div_add_mod n d
  · intro k _
    simp only [Nat.mul_add_div hd,Nat.div_eq_of_lt hc,Nat.add_zero]
