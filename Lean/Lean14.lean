open nat int


#eval (-15 : ℤ) / 6   --  -3

#eval (-15 : ℤ) % 6   --  3

lemma Lem1a (a : ℤ) : a ∣ 0 := 
begin
simp [(∣)],
existsi (0:ℤ),
rw [mul_zero],
end 

#check Lem1a 

lemma Lem1b (a b : ℤ) : abs(b) < a ∧ b ≠ 0 → ¬ (b ∣ a) := sorry

#check Lem1b 


theorem Thm1 (a b c : ℤ) : a ∣ b ∧ b ∣ c → a ∣ c :=
begin 
admit,
end 

theorem Thm2 (a b c m n : ℤ) : c ∣ a ∧  c ∣ a → c ∣ (a*m + b*n) := 
begin
admit,
end 

def sumSeries {α : Type} (f : ℕ → α) [has_add α] : ℕ → α
| 0 := f 0
| (succ n) := (sumSeries n) + (f (n+1))

#eval sumSeries (λ x: ℕ, (-2 : ℤ)*x*x + 100*x) 100 


theorem Thm3 (f:ℕ → ℤ) (n:ℕ) (a : ℤ): (∀ k : ℕ, k ≤ n → a ∣ f k) → (∀ g : ℕ → ℤ, a ∣ sumSeries (λ x : ℕ, (f x) * (g x)) n) :=
begin
 admit,
end

#eval (-15 : ℤ) / 6   --  -3

#eval (-15 : ℤ) % 6   --  3

lemma test1 : (-15 : ℤ) = (-3) * 6 + 3 :=
begin
refl,
end 



#eval gcd (24:ℤ) 18   -- 6

def nb1 : ℤ := 10

def nb2 : ℤ := 20

def m1 := nb1.to_nat

#eval m1 


def m2 := (nat_abs nb2)


-- def zgcd (a b : ℤ) : ℤ := gcd (int.nat_abs a) (int.nat_abs b)


#check gcd (-10:ℤ) (24)

lemma Lem2 (a b q r : ℤ) : a = b * q + r → gcd a b = gcd b r :=
begin
admit
end

meta def EuclideaAlgorithm : ℤ → ℤ → ℕ
| 0 b := nat_abs(b) 
| a 0 := nat_abs(a)
| a b := EuclideaAlgorithm b (a % b)

#check EuclideaAlgorithm

#eval EuclideaAlgorithm 24 18 

#eval EuclideaAlgorithm 4147 10672


#eval gcd (4147:ℤ) 10672

def isPrime (n : ℕ) : Prop := (n ≥ 2) ∧ (∀ m : ℕ, m ≥ 1 ∧ m ∣ n → (m = 1 ∨ m =n))

#print isPrime


lemma Lem3 (n : ℕ) : n > 1 → ∃ m : ℕ, isPrime m ∧ m ∣ n :=
begin
admit,
end 


theorem Thm4 (n : ℕ) : n > 1 ∧ ¬ isPrime n → ∃ m : ℕ, isPrime m ∧ m^2 ≤ n ∧ m ∣ n :=
begin
admit,
end 


def infinite (s : set ℕ) : Prop := ∀ n : ℕ, ∃ m ∈ s, n < m


def TheSetOfPrimes := {n : ℕ | isPrime n}

theorem Thm5: infinite TheSetOfPrimes :=
begin
 admit,
end 

theorem DirichletThm (a b : ℤ): a > 0 ∧ gcd a b = 1 → infinite {n | isPrime n  ∧ (∃ m : ℤ, ↑n = a * m + b)} :=
begin
admit,
end 


def modulo (a b : ℤ) (m: ℕ) : Prop := ↑m ∣ a - b

notation a `≡` b `mod` m  := modulo a b m

lemma LemCongruence (a b: ℤ) (m : ℕ) : (a ≡ b mod m) → ∃ k:ℤ, a = b + m * k :=
begin
rw modulo,
simp [(∣)],
intro H,
cases H with t Ht,
existsi t,
rw (symm Ht),
rw add_comm,
rw add_assoc,
rw add_left_neg,
rw add_zero,
end

#check LemCongruence


def phi (n : ℕ) : ℕ → ℕ
| 0 := 0
| 1 := if n ≠ 0 then 1 else 0
| (m+2) := if gcd ↑(m+2) n = 1 then phi (m +1) + 1 else phi (m+1)

def φ (n : ℕ) : ℕ := phi n (n-1)
#eval φ 1000

def power {α : Type} (a : α) [has_mul α] [has_one α] : ℕ → α
| 0 := 1 
| (succ n) := a * (power n)

#eval power (-2:ℤ) (10:ℕ)

#eval power (2 : ℕ) (10:ℕ)

#eval (-2:ℤ).to_nat

theorem EulerTheorem (a : ℤ) (m : ℕ): (m > 0) ∧ gcd a m =1 →  power a (φ m) ≡ 1 mod m :=
begin
admit,
end

#check EulerTheorem

theorem LittleFermatTheorem (a : ℤ) (p : ℕ): isPrime p ∧ ¬ (↑p ∣ a) →  power a (p-1) ≡ 1 mod p :=
begin
admit,
end

#check LittleFermatTheorem

def productSeries {α : Type} (f : ℕ → α) [has_mul α] : ℕ → α
| 0 := f 0
| (succ n) := (productSeries n) * (f (n+1))


#eval productSeries (λ x: ℕ, x+1) 4


#eval productSeries (λ x: ℕ, -(↑x+(1:ℤ))) 5


theorem ChineseRemainder (b : ℕ → ℤ) (m : ℕ → ℕ) (n : ℕ) : ((∀ i j : ℕ, i ≤ n ∧ j ≤ n ∧ i ≠ j → gcd ↑(m i) (m j) = 1) → 
(∃ k : ℤ, ∀ j : ℕ, j ≤ n → (k ≡ b j mod m j))) ∧ (let M := productSeries m n in 
(∀ k i : ℤ, ∀ j : ℕ, j ≤ n → (k ≡ b j mod m j) ∧ (i ≡ b j mod m j) → (k ≡ i mod M))) :=
begin
admit,
end














#check DirichletThm




