/- Chap 2: Dependent Type Theory-/

--2.2 Type as objects
constant α : Type
constant β  : Type
#check list α  
#check list nat 


#check prod
#check prod α β 

constant n: nat
constant z: ℤ 
#check prod nat ℤ 



--2.4 Introducing Definitions

def foo : (ℕ  → ℕ) → ℕ := λ f, f 0

#check foo 
#print foo

def foo' := λ f: ℕ → ℕ , f 0

#check foo'  
#print foo' 
#reduce foo

def nhandoi (x : ℕ) : ℕ := x + x 
#print nhandoi 
#check nhandoi 3 
#reduce nhandoi 3
#eval nhandoi 4

def binhphuong (n:ℕ ): ℕ := n*n
constant f : ℕ → nat 
constant g : (nat × nat) → (nat × nat) 
--def lam2lan : (ℕ → ℕ) → ℕ → ℕ := λ f x,f (f x)
def lam2lan : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)
#eval lam2lan nhandoi 4
#eval lam2lan binhphuong 2
constant f1: (ℕ → nat) →  ℕ → ℕ  
def lam4lan : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ g f, g (g f)
#eval lam4lan lam2lan binhphuong 2
#check lam4lan
#print lam4lan

def compose (α β γ : Type) (g: β → γ) (f : α → β) (x:α): γ := g (f x)

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ :=sorry 

def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ

--2.5 Local definitions

