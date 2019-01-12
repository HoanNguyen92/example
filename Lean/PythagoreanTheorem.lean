import data.vector data.vector2 analysis.metric_space analysis.real


variable α :Type 
--variable n: ℕ 

def s3 := ([0,3] : list ℤ)

def s4 := ([4,0] : list ℤ)

#eval s3.length
#check s3.length 

def list_to_vector {α : Type} (s : list α) 
: vector α (s.length) := ⟨s, by refl⟩

def a := list_to_vector s3

def b := list_to_vector s4

#eval a.to_list
#eval b.to_list

----------------------------------
def add_vec {α : Type} [has_add α] {n : ℕ} ( v1 v2 : vector α n) 
:= vector.map₂ (λ a b : α, a + b) v1 v2

notation u `+` v := add_vec u v 

def sum_list {α : Type} [has_add α][has_zero α] : list α → α
| [] := 0
| (a :: s) := a + sum_list s 

def inner_product_vec {α :Type} [has_add α] [has_mul α] [has_zero α] {n:ℕ} (v1 v2 : vector α n)
:= let w:= vector.map₂ (λ x y:α, x*y) v1 v2 in sum_list w.to_list

def square_of_norm_vec {α : Type} [has_mul α] [has_zero α] [has_add α] {n : ℕ} (v: vector α n)
:= let w:= vector.map (λ x:α, x*x) v in (sum_list w.to_list) 

theorem Pythegorean_Theorem {α:Type} [has_add α] [has_mul α] [has_zero α]
{n:ℕ} ( a b : vector α n) (h: inner_product_vec a b = 0) : 
square_of_norm_vec (a + b) = 
square_of_norm_vec a + square_of_norm_vec b := sorry
----------------------------
#eval (a + b).to_list
#eval inner_product_vec a b 
#eval square_of_norm_vec (a + b)

#check a
