import Mathlib

theorem Conjectures.Cuts.Task4496d411004e70e6e084ab9b : (∀ δ : ℝ, 0<δ → δ<1 → ∃ T : ℕ, ∀ w H N : ℕ, T≤w → 1≤w → w≤H → H≤w^3 → N*w≤3*H →
    (N:ℝ)*(w:ℝ)^(1-δ) ≤ (H:ℝ)^(1-δ/4)) := by
  intro δ hδ _
  obtain ⟨T,hT⟩ := exists_nat_ge ((3:ℝ)^(4/δ))
  refine ⟨T,?_⟩
  intro w H N hTw hw1 hwH hHw hbudget
  have hw : 0<(w:ℝ) := by exact_mod_cast (show 0<w by omega)
  have hh : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have he : 0<δ/4 := by linarith
  have hthree : (3:ℝ) ≤ (w:ℝ)^(δ/4) := by
    calc
      (3:ℝ) = ((3:ℝ)^(4/δ))^(δ/4) := by
        rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤3),show (4/δ)*(δ/4)=1 by field_simp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (hT.trans (by exact_mod_cast hTw)) he.le
  have hpow : (H:ℝ)^(δ/4) ≤ (w:ℝ)^(3*(δ/4)) := by
    calc
      _ ≤ ((w:ℝ)^3)^(δ/4) := Real.rpow_le_rpow hh.le (by exact_mod_cast hHw) he.le
      _ = _ := by rw [Real.rpow_mul hw.le]; norm_num
  have hmul : 3*(H:ℝ)^(δ/4) ≤ (w:ℝ)^δ := by
    calc
      _ ≤ (w:ℝ)^(δ/4)*(w:ℝ)^(3*(δ/4)) := mul_le_mul hthree hpow (by positivity) (by positivity)
      _ = _ := by rw [←Real.rpow_add hw]; congr 1; ring
  have hb : (N:ℝ)*w ≤ 3*H := by exact_mod_cast hbudget
  rw [Real.rpow_sub hw,Real.rpow_sub hh,Real.rpow_one,Real.rpow_one]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hh _)).2
  calc
    (N:ℝ)*(w/(w:ℝ)^δ)*(H:ℝ)^(δ/4) = ((N*w)*(H:ℝ)^(δ/4))/(w:ℝ)^δ := by ring
    _ ≤ ((3*H)*(H:ℝ)^(δ/4))/(w:ℝ)^δ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity)) (by positivity)
    _ ≤ H := (div_le_iff₀ (Real.rpow_pos_of_pos hw _)).2 (by
      calc
        (3*(H:ℝ))*(H:ℝ)^(δ/4) = (H:ℝ)*(3*(H:ℝ)^(δ/4)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hmul hh.le)
