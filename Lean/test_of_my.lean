import analysis.measure_theory.measure_space
import analysis.metric_space
import analysis.real analysis.exponential
import analysis.measure_theory.measurable_space
import data.set


def Circle{x: ℝ  × ℝ  }{r: ℝ} {r ≥ 0} := closed_ball (x) (r)
#check Circle

theorem Area_of_Circle [measurable_space (ℝ × ℝ)] [r :ℝ ] : real.pi * r^2
#check Area_of_Circle