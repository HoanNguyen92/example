
section hanoi

/-example {x y : ℕ} (h : y + x = 0): x + y =0 :=
begin
rw  [← h]

end
-/

example (x y:nat) (h: x+y + 0 =0): (y+0)+x+0 * x = 0 :=
begin
simp [nat.add_comm] at ⊢h,
exact h,
end

example (x y:nat) (h: x+y + 0 =0): (y+0+0)+x+0 * x = 0 :=
begin
rw [zero_mul, add_zero, add_zero, add_zero, nat.add_comm],
rw [add_zero] at h,
exact h,
end

def my_add (x y:ℕ) := x+y

example (x y:nat) (h: my_add  x y + 0 =0): (y+0+0)+x+0 * x = 0 :=
begin
simp [my_add] at ⊢,
exact h,
end

set_option trace.simplify.rewrite true
theorem T (x y z : nat) (h : x + (z + y) = 0):
 x + y + z + 0 + z*0 = 0 :=
 begin
    --rw [add_zero, mul_zero, add_zero,zero_add, zero_mul,add_zero,nat.add_comm],
    simp [] at h ⊢,
    simp [h],
    --exact h, 
 end

end hanoi