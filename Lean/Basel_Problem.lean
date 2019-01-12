import analysis.real analysis.topology.infinite_sum 
    analysis.exponential   
noncomputable theory

def Exact_Sum_of_Basel_Problem : ℝ := (real.pi^2)/6

theorem Basel_Problem : is_sum (λn:ℕ, 1/(n:ℝ)*(n:ℝ)) Exact_Sum_of_Basel_Problem := sorry

theorem Borsuk–Ulam_theorem (n:ℕ) (r: ℝ) (f:(ball (0:fin n → ℝ) r) → ℝ) (h1: continuous f) :
∃ x ∈ (ball (0: fin n → ℝ) r), f x = 0 := sorry 