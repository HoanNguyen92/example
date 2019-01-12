import analysis.metric_space analysis.real data.set data.set.basic
import init.data.fin.basic

variable r: real
variable f : ball (0:real) r → ℝ
#check f 
­­

theorem Borsuk–Ulam_theorem (n:ℕ) (r:ℝ) (f: (ball (0: fin n → ℝ) r) → ℝ) (h: continuous f): (∃ x ∈ ball (0: fin n → ℝ) r, f x = f -x) :=sorry




