import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

/-- The Geometric Distribution as defined in Grinstead & Snell's "Introduction to Probability"
    T represents the number of trials up to and including the first success.
    P(T = k) = q^(k-1) * p where q = 1-p and k ≥ 1 -/
structure GeometricDist where
  p : ℝ
  p_pos : 0 < p
  p_le_one : p ≤ 1

namespace GeometricDist

variable (g : GeometricDist)

/-- q = 1 - p, the probability of failure -/
noncomputable def q : ℝ := 1 - g.p

/-- Probability Mass Function
    P(T = k) = (1-p)^(k-1) * p for k ≥ 1 -/
noncomputable def pmf (k : ℕ) : ℝ :=
  if k = 0 then 0
  else g.q ^ (k - 1) * g.p

/-- The expected value (mean) E(T) = 1/p -/
noncomputable def expected_value : ℝ := 1 / g.p

/-- The variance V(T) = (1-p)/p² = q/p² -/
noncomputable def variance : ℝ := g.q / (g.p ^ 2)

/-- Cumulative Distribution Function
    P(T ≤ k) = 1 - (1-p)^k for k ≥ 1 -/
noncomputable def cdf (k : ℕ) : ℝ :=
  if k = 0 then 0
  else 1 - g.q ^ k

/-- The probability that T > k (survival function)
    P(T > k) = (1-p)^k -/
noncomputable def survival (k : ℕ) : ℝ := g.q ^ k

/-- Example: Geometric distribution with p = 1/2 
    (e.g., waiting for first heads in coin tosses) -/
noncomputable def example_dist : GeometricDist := {
  p := 1/2
  p_pos := by sorry
  p_le_one := by sorry
}

/-- Theorem: PMF at k=0 is always 0 -/
theorem pmf_zero : g.pmf 0 = 0 := by
  unfold pmf
  simp

/-- Theorem: For k ≥ 1, pmf k = (1-p)^(k-1) * p -/
theorem pmf_succ (k : ℕ) (hk : k ≥ 1) : 
    g.pmf k = g.q ^ (k - 1) * g.p := by
  unfold pmf q
  have : k ≠ 0 := by omega
  simp [this]

/-- Memoryless property: P(T > s + t | T > s) = P(T > t)
    In other words: P(T > s + t) = P(T > s) * P(T > t) -/
theorem memoryless_property (s t : ℕ) : 
    g.survival (s + t) = g.survival s * g.survival t := by
  unfold survival q
  rw [pow_add]

end GeometricDist

-- Example usage
#check GeometricDist.example_dist
#check GeometricDist.example_dist.expected_value
#check GeometricDist.example_dist.pmf 3