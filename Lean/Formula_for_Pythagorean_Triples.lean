
open nat

def is_odd (a : nat) := ¬ ∃ b, a = 2*b 

def both_odd (m n: nat) := is_odd m ∧ is_odd n 

theorem Pythagorean_Triple_Theorem (a b c: ℕ) (h: a*a + b*b = c*c) (h1: coprime a b ∧ coprime a c ∧ coprime b c):
  (∀ k: ℕ, (k*a)^2 + (k*b)^2 = (k*c)^2) ∧ (∃ m n : ℕ, ¬ both_odd m n ∧ coprime m n ∧ m > n ∧ a = m^2 - n^2 ∧  b = 2*m*n ∧ c = m^2 + n^2)
 := sorry





def Pythagorean_triple (a b c: nat) := c*c = a*a + b*b

#check Pythagorean_triple

--def exists_unique_triple {α : Type}(a b c: α) (p : α → α → α → Prop) := 
--∃ a1 b1 c1, p a1 b1 c1 ∧ ∀ a b c, p a b c → a1 = a ∧ b1 = b ∧ c1 = c 

--#check exists_unique_triple