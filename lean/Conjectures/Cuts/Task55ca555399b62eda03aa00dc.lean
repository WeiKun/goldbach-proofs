import Mathlib

theorem Conjectures.Cuts.Task55ca555399b62eda03aa00dc : (∀ X H : ℕ, let w := X.sqrt
  4≤w → X≤H^2 → H≤X → w≤H ∧ H≤w^3 ∧ (Finset.Icc (X/w) ((X+H)/w)).card*w≤3*H ∧
    ∀ j ∈ Finset.Icc (X/w) ((X+H)/w), w≤j ∧ j≤8*w) := by
  intro X H w h4 hmin hmax
  have hw : 0<w := by omega
  have ws : w^2≤X := Nat.sqrt_le' X
  have xs : X<(w+1)^2 := Nat.lt_succ_sqrt' X
  have wh : w≤H := by simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt hmin
  have hh : (w+1)^2 ≤ (2*w)^2 := Nat.pow_le_pow_left (by omega) 2
  have coarse : X<4*w^2 := by nlinarith
  have cube : H≤w^3 := by
    have h := Nat.mul_le_mul_right (w^2) h4
    nlinarith
  let a := X/w
  let b := (X+H)/w
  have hab : a≤b := Nat.div_le_div_right (by omega : X≤X+H)
  have eb : b*w≤X+H := Nat.div_mul_le_self _ _
  have ea : X<(a+1)*w := (Nat.div_lt_iff_lt_mul hw).1 (Nat.lt_succ_self _)
  have lower : w≤a := (Nat.le_div_iff_mul_le hw).2 (by simpa [pow_two] using ws)
  have upper : b≤8*w := by
    have e : (X+H)/w<8*w+1 := (Nat.div_lt_iff_lt_mul hw).2 (by nlinarith)
    omega
  refine ⟨wh,cube,?_,?_⟩
  · change (Finset.Icc a b).card*w ≤ 3*H
    rw [Nat.card_Icc]
    have he : b+1-a+a=b+1 := by omega
    have hm := congrArg (fun x : ℕ => x*w) he
    simp only [Nat.add_mul,Nat.one_mul] at hm ea
    omega
  · intro j hj
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hj
    exact ⟨lower.trans hl,hu.trans upper⟩
