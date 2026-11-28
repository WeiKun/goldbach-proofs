import Mathlib

theorem Conjectures.Cuts.Task763de5f85b2797f6b7a9f994 : (let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  ∀ s : ℕ, 1 ≤ s → ((∃ p q : ℕ, ch p ∧ ch q ∧ p+q=6*s+4) ↔
    ch (6*s+1) ∨ ∃ a b : ℕ, a+b+1=s ∧ ch (6*a+5) ∧ ch (6*b+5))) := by
  intro ch s hs
  have residue (p : ℕ) (h : p.Prime) (h2 : p≠2) (h3 : p≠3) : p % 6=1 ∨ p % 6=5 := by
    have nd2 : ¬2∣p := fun hd => h2 ((Nat.prime_dvd_prime_iff_eq (by decide) h).mp hd).symm
    have nd3 : ¬3∣p := fun hd => h3 ((Nat.prime_dvd_prime_iff_eq (by decide) h).mp hd).symm
    omega
  constructor
  · rintro ⟨p,q,hp,hq,h⟩
    by_cases h3 : p=3
    · exact Or.inl ((show q=6*s+1 by omega) ▸ hq)
    by_cases hq3 : q=3
    · exact Or.inl ((show p=6*s+1 by omega) ▸ hp)
    have pp := hp.1
    have qp := hq.1
    have hp2 : p≠2 := by
      intro he
      have hd : 2∣q := by omega
      have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 2) qp).mp hd
      omega
    have hq2 : q≠2 := by
      intro he
      have hd : 2∣p := by omega
      have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 2) pp).mp hd
      omega
    have rp := residue p pp hp2 h3
    have rq := residue q qp hq2 hq3
    exact Or.inr ⟨p/6,q/6,by omega,(show p=6*(p/6)+5 by omega) ▸ hp,(show q=6*(q/6)+5 by omega) ▸ hq⟩
  · rintro (hq|⟨a,b,hab,hp,hq⟩)
    · have hthree : ch 3 := by
        refine ⟨by decide,?_⟩
        change (Nat.primeFactorsList 5).length ≤ 2
        rw [Nat.primeFactorsList_prime (by decide : Nat.Prime 5)]
        decide
      exact ⟨3,6*s+1,hthree,hq,by omega⟩
    · exact ⟨6*a+5,6*b+5,hp,hq,by omega⟩
