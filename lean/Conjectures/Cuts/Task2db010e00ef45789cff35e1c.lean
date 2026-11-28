import Mathlib

theorem Conjectures.Cuts.Task2db010e00ef45789cff35e1c : (by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
    let K := fun (d a b k : ℕ) => ((Finset.range (k+1)).filter (fun i => i+(a+b)/d ≤ k ∧ ch (d*i+a) ∧ ch (d*(k-i-(a+b)/d)+b))).Nonempty
    ∀ d a b n : ℕ, 0<d → a<d → b<d → n % d=(a+b) % d →
    ((∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ p % d=a ∧ q % d=b) ↔ K d a b (n/d))) := by
  classical
  intro ch K d a b n hd ha hb hn
  have carry (i j : ℕ) : (d*i+a+(d*j+b))/d = i+j+(a+b)/d := by
    rw [show d*i+a+(d*j+b)=d*(i+j)+(a+b) by ring, Nat.mul_add_div hd]
  constructor
  · rintro ⟨p,q,hp,hq,hadd,hpa,hqb⟩
    have ep : d*(p/d)+a=p := by rw [←hpa]; exact Nat.div_add_mod p d
    have eq : d*(q/d)+b=q := by rw [←hqb]; exact Nat.div_add_mod q d
    have ht : n/d=p/d+q/d+(a+b)/d := by
      calc
        n/d = (d*(p/d)+a+(d*(q/d)+b))/d := by rw [ep,eq,hadd]
        _ = _ := carry _ _
    have hlt : p/d < n/d+1 := by
      rw [ht]
      exact Nat.lt_succ_of_le (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    have hle : p/d+(a+b)/d ≤ n/d := by
      rw [ht]
      exact Nat.add_le_add_right (Nat.le_add_right _ _) _
    refine ⟨p/d,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,hle,ep.symm ▸ hp,?_⟩⟩
    have e : n/d-p/d-(a+b)/d=q/d := by rw [ht]; omega
    simpa only [e,eq] using hq
  · rintro ⟨i,hi⟩
    obtain ⟨_,hle,hp,hq⟩ := Finset.mem_filter.mp hi
    let j := n/d-i-(a+b)/d
    have hij : i+j+(a+b)/d=n/d := by dsimp [j]; omega
    have en : d*(n/d)+(a+b) % d=n := by rw [←hn]; exact Nat.div_add_mod n d
    have hab := Nat.div_add_mod (a+b) d
    refine ⟨d*i+a,d*j+b,hp,hq,?_,?_,?_⟩
    · calc
        d*i+a+(d*j+b) = d*(i+j)+(a+b) := by ring
        _ = d*(i+j+(a+b)/d)+(a+b) % d := by rw [Nat.mul_add d (i+j) ((a+b)/d),Nat.add_assoc,hab]
        _ = n := by rw [hij,en]
    · rw [Nat.mul_add_mod,Nat.mod_eq_of_lt ha]
    · rw [Nat.mul_add_mod,Nat.mod_eq_of_lt hb]
