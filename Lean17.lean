
-- prelude
-- import init.data.list init.data.subtype init.meta.interactive init.data.fin


-- import init.data.subtype init.meta.interactive 

import data.vector 
import init.data.fin



open nat











/-

LISTS <----------> SETS <----------> VECTORS

-/










/- LISTS

inductive list (α : Type u)
| nil {} : list
| cons : α → list → list

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l


#check [1, 2, 3, 4, 5] --> list ℕ

[]

a s -> a :: s


cons a l := a :: l

-/


open list 


namespace list_hn


def s1 := ([1,2,3,4,5] : list ℕ)

def s2 := ([1,2,3,4,5] : list ℤ)

#eval list.length s1



#eval filter (λ x: ℤ, x > 3) s2


/- CREATE A LIST FROM A FUNCTION -/

def func_to_list {α : Type} (f : ℕ → α) (n : ℕ) : ℕ → list α
| 0        := [f n]
| (succ m) := (f (n - (succ m))) :: (func_to_list m)


def func_to_list2 {α : Type} (f : ℕ → α) (n : ℕ) : ℕ → list α
| 0        := [f 0]
| (succ m) := (f(succ m)) :: (func_to_list2 m)



#eval (func_to_list2 (λ x : ℕ , x) 3 3).reverse



#eval func_to_list (λ x : ℕ , x^2) 40 38


#eval s2 



-- Upate a list at nth position



#eval list.update_nth s2 2 19


#eval list.nth s2 2


-- Get a value at a spicific position


def nth_pos {α : Type} [has_zero α]: list α → nat → α
| []       n     := 0
| (a :: l) 0     := a
| (a :: l) (n+1) := nth_pos l n

#eval s2
#eval nth_pos s2 2



/- DECIDABLE PROPOSITION
class inductive decidable (p : Prop)
| is_false : ¬ p → decidable
| is_true :  p → decidable
-/


def isPrime (n : ℕ) : Prop := (n ≥ 2) ∧ (∀ m : ℕ, m ≥ 1 ∧ m ∣ n → (m = 1 ∨ m =n))

#eval isPrime 3

#eval (if (1 : ℤ) < 2 then "One" else "Two")

#eval (if isPrime 3 then "is Prime" else "not Prime")


/- Create a decdable for testing prime numbers -/ 


-- Find integer square root of a natural number n from 1 to m

meta def msquare_root (n : ℕ) : ℕ → ℕ → ℕ
| a          0 := a
| a          b := if b ≤ a+1 then (if (a+1)^2 ≤ n then a+1 else a)
                  else (let t := (a+b)/2 in 
                    if t^2 = n then t else (if t^2 ≤ n then msquare_root t b 
                    else msquare_root a t))


-- Find integer square root of a natural number n

meta def square_root: ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := msquare_root (n+2) 1 (n+2)


#eval square_root 

#eval square_root 121

#eval square_root 15625


-- Get a nontrivial divisor of n starting at m : get_divisor n m 


meta def get_prime_divisor (n : ℕ) : ℕ → ℕ 
| 0 := 0 
| m := if n < m then 0 else if (n % m = 0) then m else get_prime_divisor (succ m)

#eval get_prime_divisor 10001 2 --73

#eval 10001 % 73

#eval get_prime_divisor 10000000000000001 2  -- 353

#eval get_prime_divisor 353 10


-- test a prime number

meta def is_prime (n : ℕ) := let t := get_prime_divisor n 2 
                             in if (t = n) ∧ (t > 1) then tt else ff

-- The table of primes not exceed n

meta def prime_table : ℕ → list ℕ 
| 0 := []
| 1 := []
| (n + 2) := if is_prime (n+2) then ((n+2) :: prime_table (n+1)) else  prime_table (n+1)

#eval prime_table 1000


#eval list.reverse (prime_table 1000)

#eval (prime_table 1000).reverse


#eval is_prime 1000001


-- next_prime n =  the smallest prime p such that n ≤ p 

meta def next_prime : ℕ → ℕ
| 0 := 2 
| (succ n) := if is_prime (succ n) then (succ n) else next_prime (n + 2)

#eval next_prime 1000 --1009


-- the ith prime from the index 0

meta def prime : ℕ → ℕ
| 0 := 2
| 1 := 3
| (n+2) := next_prime ((prime (n+1)) + 2)

#eval prime 1000 --7927 



-- Next we can produce the table of primes and using this to find the nth prime 


meta def get_in_list (n : ℕ) : list ℕ → bool
| [] := tt
| (a :: s) := if n % a = 0 then ff else get_in_list s 

#eval get_in_list 17 [2,3,5,7,11]

meta def divisor_outside_list (s : list ℕ) : ℕ → ℕ
| n := if get_in_list n s then n else divisor_outside_list (n+1)

#eval  divisor_outside_list [2,3,5,7,9,11,13] 10


def sp := [2,3,5,7,11,13,17,19]

#eval divisor_outside_list sp 19


meta def pTable : ℕ → list ℕ
| 0 := [2]
| 1 := [3,2]
| (n+2) := let s := pTable (n+1) in 
           let p := s.head in let q := divisor_outside_list s (p+2) in q :: s  

#eval (pTable 1000).reverse   


meta def get_prime (n : ℕ) := (pTable n).head 

#eval get_prime 1000 --7927 

#eval is_prime 7927


end list_hn


/- SETS

def set (α : Type u) := α → Prop


DESCRIPTIONS:

p : α → Prop

s : set α = {x : α ∣ p x}

-/


namespace set_hn


/- From Lists to Sets-/


def st : set ℕ := {1, 2, 2, 3, 4, 5, 6, 7}

#print st 



def to_set {α : Type} : list α → set α
| [] := {}
| (h :: s) := {h} ∪ to_set s 

def l1 := ([1,2,3,4,5] : list ℕ)

def l2 := ([1,2,3,4,5] : list ℤ)

def s1 := to_set l1 

#print s1 

def s2 := to_set l2 

#check s1 

#check s2 

#reduce st 

#reduce s2 



/-

  HOW TO DEFINE FINITE SETS 

-/

end set_hn




/- VECTORS : vector α n, the n dimensional vector space αⁿ

       v =(a1,a2,...,an); ai ∈ α


inductive vector (α : Type u) : nat → Type u
| nil {}                              : vector zero
| cons {n : ℕ} (a : α) (v : vector n) : vector (succ n)


WE HAVE DEFINE IN vector.lean as follows:

def vector (α : Type u) (n : ℕ) := 
{ l : list α // l.length = n }


-/

open vector
namespace vector_hn


variables (α : Type) [has_zero α]


/-
  ZERO VECTORS
-/

def zero_vector (n : ℕ) : vector α n := repeat (0 : α) n

def zv5 := zero_vector ℤ 5

/- 
 v.to_list
-/

#eval zv5.to_list


def s3 := ([1,2,3,4,5,6] : list ℤ)

def s4 := ([3,4,5,6,7,8] : list ℤ)


#eval s3 


/- FROM A LIST TO A VECTOR -/


def list_to_vector {α : Type} (s : list α) 
: vector α (s.length) := ⟨s, by refl⟩



#eval (list_to_vector s3).1

def v3 := list_to_vector s3

def v4 := list_to_vector s4


-- Add two vectors: v1 + v2

/-

v := map₂ (f : α → β → φ) (v1: vector α n) (v2: vector β n) : vector φ n

v i = f (v1 i) (v2 i)

-/


def add_vec {α : Type} [has_add α] {n : ℕ} ( v1 v2 : vector α n) 
:= vector.map₂ (λ a b : α, a + b) v1 v2


notation u `+` v := add_vec u v 


#eval v3.to_list

#eval v4.to_list


#eval (v3 + v4).to_list


-- notation α^n := vector α n

-- Multiply a scalar and a vector : a * v

/-
     w :=  map (f : α → β) (v : vector α n) : vector β n
     
     w i = f (v i)
-/

def mul_vec {α : Type} [has_mul α] {n : ℕ} (a : α) (v : vector α n) 
:= vector.map (λ x:α, a * x) v

notation a `*` v := mul_vec a v 


#eval v3.to_list 

#eval (4*v3).to_list



-- sum of coordinate
/-

v : vector α n, means that v =⟨s, H⟩, where

s : list α

H : length s = n (where n = the length of s)

-/


def sum_coordinates {α : Type} [has_add α][has_zero α] : Π {n : ℕ}, vector α n → α
| 0   ⟨[], h⟩        := 0
| (n+1) ⟨ a :: v, H⟩ := a + @sum_coordinates n (⟨v, congr_arg nat.pred H⟩)


#eval v3.to_list

#eval v4.to_list

#eval  sum_coordinates v3

def dots_product {α : Type} [has_mul α][has_add α] [has_zero α] : Π {n : ℕ}, vector α n → vector α n → α
| 0 ⟨_, _⟩ ⟨_, _⟩ := 0
| (n+1)⟨a::v,h1⟩ ⟨b::u,h2⟩ := a * b + @dots_product n ⟨v, congr_arg pred h1⟩ ⟨u, congr_arg pred h2⟩

notation u `∙` v := dots_product u v

#eval v3.1
#eval v4.1


#eval v3 ∙ v4


-- The easier procedure is the following:

def sum_list {α : Type} [has_add α][has_zero α] : list α → α
| [] := 0
| (a :: s) := a + sum_list s 

def dot_product {α : Type} [has_mul α][has_add α] [has_zero α] {n : ℕ}  (u v: vector α n)
    := let w := map₂ (λ x y : α, x * y) u v in sum_list w.to_list

#eval dot_product v3 v4 
  

end vector_hn









