import Mathlib

theorem Conjectures.Cuts.Taska571f1c3077acc5aaa440e63 : (by
  classical
  exact ∀ (X H w : ℕ) (P : ℕ → Bool) (M : ℝ), 0<w →
    (∀ j ∈ Finset.Icc (X/w) ((X+H)/w), (((Finset.Ico (j*w) ((j+1)*w)).filter (fun n => P n=true)).card:ℝ) ≤ M) →
    (((Finset.Icc X (X+H)).filter (fun n => P n=true)).card:ℝ) ≤ ((Finset.Icc (X/w) ((X+H)/w)).card:ℝ)*M) := by
  classical
  intro X H w P M hw hM
  let I := Finset.Icc (X/w) ((X+H)/w)
  let B := fun j : ℕ => (Finset.Ico (j*w) ((j+1)*w)).filter (fun n => P n=true)
  let W := (Finset.Icc X (X+H)).filter (fun n => P n=true)
  have sub : W ⊆ I.biUnion B := by
    intro n hn
    obtain ⟨hI,hP⟩ := Finset.mem_filter.mp hn
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hI
    refine Finset.mem_biUnion.mpr ⟨n/w,Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hl,Nat.div_le_div_right hu⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.div_mul_le_self n w,(Nat.div_lt_iff_lt_mul hw).1 (Nat.lt_succ_self (n/w))⟩,hP⟩
  have bound : W.card ≤ ∑ j ∈ I, (B j).card := (Finset.card_le_card sub).trans Finset.card_biUnion_le
  calc
    (W.card:ℝ) ≤ ∑ j ∈ I, ((B j).card:ℝ) := by exact_mod_cast bound
    _ ≤ ∑ _j ∈ I, M := Finset.sum_le_sum hM
    _ = _ := by simp [I]
