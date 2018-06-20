def identity := λ x : nat, x

#check identity

theorem and_is_commutative (p q : Prop) : p ∧ q → q ∧ p := 
λ h : p ∧ q, and.intro 
    (and.right h)
    (and.left h)

#print and_is_commutative
theorem T : 1 = 0 ∧ 2 < 3 → 2 < 3 ∧ 1=0 := λ h, and_is_commutative (1=0) (2<3) h 


namespace hanoi
inductive unit'
| zero : unit' 

open unit'


theorem everything_is_zero : 
     ∀ u : unit', u = zero := 
        λ u, @unit'.rec 
           (λ u, u = zero) rfl u



#print unit'.rec 

#print or.rec 

inductive and' (a b : Prop): Prop
| intro: a → b → and'

#print and'.rec 


      
theorem and'.left {a b : Prop}
    (h: and' a b) : a := 
    @and'.rec a b a 
        (λ (ha : a)(hb : b), ha ) h 

theorem and'.right {a b : Prop}
    (h: and' a b) : b := 
    @and'.rec a b b 
        (λ (ha : a) (hb : b), hb ) h 

#print not 

inductive weird : Type
| succ (n:weird) : weird 

#print weird.rec 

#print nat.rec 

set_option pp.beta true
def nat_identity : nat → nat := 
@nat.rec (λ n, nat) 0  
        (λ prev IH, nat.succ IH)

/-

(λn:ℕ, ℕ) prev     ==== by beta reduction ==== ℕ 


)

-/

#check @congr_arg

#print nat_identity


theorem nat_identity_is_id 
    (n: nat) : nat_identity n= n := 
@nat.rec 
    (λ n, nat_identity n = n)
    rfl
    (λ n IH,
        show nat_identity (nat.succ n)
            = nat.succ n, from 
        show nat.succ (nat_identity n)
            = nat.succ n, from
    congr_arg nat.succ IH) n
    

end hanoi

