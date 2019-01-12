import algebra.big_operators algebra.group_power
  analysis.real analysis.topology.infinite_sum analysis.exponential
noncomputable theory
open classical finset function filter

universes u v

variable β : Type v
variable α : Type u
variable l₁ : filter α 
variable f : α → β 
variable a: α

namespace presentation

structure filter (α : Type u) :=
(sets            : set (set α))
(exists_mem_sets : ∃x, x ∈ sets)
(upwards_sets    : ∀{x y}, x ∈ sets → x ⊆ y → y ∈ sets)
(directed_sets   : directed_on (⊆) sets)

end presentation

--Line 16 ... Lemma ''has_sum_of_absolute_convergence''
lemma has_sum_of_absolute_convergence {f : ℕ → ℝ}
  (hf : ∃r, tendsto (λn, (range n).sum (λi, abs (f i))) at_top (nhds r)) : 
  has_sum f := sorry
-- detail

/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def tendsto (f : α → β) (l₁ : filter α) (l₂ : filter β) := l₁.map f ≤ l₂
#check l₁.map f
def preimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}
def map (m : α → β) (f : filter α) : filter β := sorry

def at_top [preorder α] : filter α := ⨅ a, principal {b | a ≤ b}

def is_sum (f : β → α) (a : α) : Prop := tendsto (λs:finset β, s.sum f) at_top (nhds a)
/-- `has_sum f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def has_sum (f : β → α) : Prop := ∃a, is_sum f a

--Line 58 lemma is_sum_iff_tendsto_nat_of_nonneg
lemma is_sum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} {r : ℝ} (hf : ∀n, 0 ≤ f n) :
  is_sum f r ↔ tendsto (λn, (range n).sum f) at_top (nhds r) := sorry


--line 71 lemma mul_add_one_le_pow 
lemma mul_add_one_le_pow {r : ℝ} (hr : 0 ≤ r) : ∀{n:ℕ}, (n:ℝ) * r + 1 ≤ (r + 1) ^ n
| 0       := by simp; exact le_refl 1
| (n + 1) := sorry

--line 81 lemma tendsto_pow_at_top_at_top_of_gt_1   ????????????????????????????????????
lemma tendsto_pow_at_top_at_top_of_gt_1 {r : ℝ} (h : r > 1) : tendsto (λn:ℕ, r ^ n) at_top at_top := sorry

-- line 95
lemma tendsto_inverse_at_top_nhds_0 : tendsto (λr:ℝ, r⁻¹) at_top (nhds 0) :=sorry

--line 107                      ??????????????????????????????
lemma map_succ_at_top_eq : map nat.succ at_top = at_top := sorry
--detail
-- def map (m : α → β) (f : filter α) : filter β := sorry

--line 122
lemma tendsto_comp_succ_at_top_iff {α : Type*} {f : ℕ → α} {x : filter α} :
  tendsto (λn, f (nat.succ n)) at_top x ↔ tendsto f at_top x := sorry

--line 127
lemma tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  tendsto (λn:ℕ, r^n) at_top (nhds 0) := sorry

--line 137
lemma sum_geometric' {r : ℝ} (h : r ≠ 0) :
  ∀{n}, (finset.range n).sum (λi, (r + 1) ^ i) = ((r + 1) ^ n - 1) / r
| 0     := by simp [zero_div]
| (n+1) := sorry

--line 143
lemma sum_geometric {r : ℝ} {n : ℕ} (h : r ≠ 1) :
  (range n).sum (λi, r ^ i) = (r ^ n - 1) / (r - 1) :=sorry

--line 152
lemma is_sum_geometric {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  is_sum (λn:ℕ, r^n) (1 / (1 - r)) := sorry

open complex 

#check real.pi  
#eval real.pi

----------------------------------------------------------
def tong : ℝ := real.pi*real.pi/6
#check tong
lemma dinhly : is_sum (λn:ℕ, 1/(n:ℝ)*(n:ℝ)) tong := sorry
----------------------------------------------------------

