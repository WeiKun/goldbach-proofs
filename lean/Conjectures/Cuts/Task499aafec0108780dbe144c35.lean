import Mathlib

theorem Conjectures.Cuts.Task499aafec0108780dbe144c35 : (let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  ∀ t : ℕ, 1 ≤ t → (ch (6*t^2+1) ↔ (t^2=1 ∨ 3∣t^2) ∧ Nat.Prime (6*t^2+1) ∧ Nat.Prime (2*t^2+1))) := by
  intro ch t ht
  have hs : 1≤t^2 := by simpa using Nat.pow_le_pow_left ht 2
  have cap (u : ℕ) (hu : 1<u) : (3*u).primeFactorsList.length ≤ 2 ↔ Nat.Prime u := by
    rw [← ArithmeticFunction.cardFactors_apply,ArithmeticFunction.cardFactors_mul (by decide) (by omega)]
    rw [ArithmeticFunction.cardFactors_apply_prime (by decide : Nat.Prime 3),← ArithmeticFunction.cardFactors_eq_one_iff_prime]
    have pos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hu
    omega
  change (Nat.Prime (6*t^2+1) ∧ (6*t^2+1+2).primeFactorsList.length ≤ 2) ↔ _
  rw [show 6*t^2+1+2=3*(2*t^2+1) by omega,cap _ (by omega)]
  constructor
  · rintro ⟨hp,hq⟩
    refine ⟨?_,hp,hq⟩
    by_cases hz : 3∣t^2
    · exact Or.inr hz
    have hsmod : t^2 % 3=0 ∨ t^2 % 3=1 := by
      have he : t^2 % 3=(t % 3)^2 % 3 := Nat.pow_mod _ _ _
      rw [he]
      have hlt := Nat.mod_lt t (by decide : 0<3)
      interval_cases e : t % 3 <;> decide
    have hd : 3 ∣ 2*t^2+1 := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hq).mp hd
    exact Or.inl (by omega)
  · exact fun h => h.2
