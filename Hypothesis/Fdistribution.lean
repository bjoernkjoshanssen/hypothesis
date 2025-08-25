import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real


import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# F distribution

-/

open Real
noncomputable def FDistributionNumerator (d₁ d₂ : ℝ) : ℝ → ℝ := fun x =>
  (√(((d₁ ^ d₁ * d₂ ^ d₂) * x ^ d₁) / ((d₁ * x + d₂) ^ (d₁ + d₂))))

noncomputable def Real.Beta (d₁ d₂ : ℝ) := Gamma (d₁) * Gamma (d₂) / Gamma (d₁ + d₂)

noncomputable def FDistribution (d₁ d₂ : ℝ) : ℝ → ℝ :=
  (fun x =>
  FDistributionNumerator d₁ d₂ x) /
  (fun x => (x * Beta (d₁ / 2) (d₂ / 2)))

example (d₁ d₂ : ℝ) (hd₁ : d₁ ≠ 0) : FDistributionNumerator d₁ d₂ 0 = 0 := by
  simp [FDistributionNumerator]
  refine sqrt_eq_zero'.mpr ?_
  apply le_of_eq
  simp
  left
  right
  exact zero_rpow hd₁

example (d₁ d₂ : ℝ) : FDistribution d₁ d₂ 0 = 0 := by
  simp [FDistribution]



lemma deriv_FdistributionNumerator (a d₁ d₂ x : ℝ)
  (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hx : 0 < x)
  : deriv (FDistributionNumerator d₁ d₂) x =

  (d₁ ^ d₁ * d₂ ^ d₂ * (d₁ * x ^ (d₁ - 1)) * (d₁ * x + d₂) ^ (d₁ + d₂) -
        d₁ ^ d₁ * d₂ ^ d₂ * x ^ d₁ * ((d₁ + d₂) * (d₁ * x + d₂) ^ (d₁ + d₂ - 1) * d₁)) /
      ((d₁ * x + d₂) ^ (d₁ + d₂)) ^ 2 /
    (2 * √(d₁ ^ d₁ * d₂ ^ d₂ * x ^ d₁ / (d₁ * x + d₂) ^ (d₁ + d₂)))


   := by
    have h₀ :  d₁ * x + d₂ ≠ 0 := by
      intro hc
      have : d₁ * x = - d₂ := Eq.symm (neg_eq_of_add_eq_zero_left hc)
      revert hd₂
      simp
      suffices 0 ≤ - d₂ by linarith
      rw [← this]
      positivity

    have h :  (d₁ * x + d₂) ^ (d₁ + d₂) ≠ 0 := by
      refine (rpow_ne_zero ?_ ?_).mpr ?_
      positivity
      linarith
      apply h₀
    unfold FDistributionNumerator
    rw [deriv_sqrt]
    conv =>
      left
      left
      change deriv (
        ((fun x ↦ d₁ ^ d₁ * d₂ ^ d₂ * x ^ d₁) / (fun x => (d₁ * x + d₂) ^ (d₁ + d₂))) ) x
    rw [deriv_div]
    rw [deriv_const_mul]
    rw [Real.deriv_rpow_const]
    conv =>
      left
      left
      left
      right
      right
      change  deriv ((fun x ↦ x ^ (d₁ + d₂)) ∘ fun x => (d₁ * x + d₂)) x
    rw [deriv_comp]
    rw [Real.deriv_rpow_const]

    conv =>
      left
      left
      left
      right
      right
      right
      change deriv ((fun x ↦ d₁ * x) + (fun x => d₂)) x
    rw [deriv_add]
    rw [deriv_const_mul]
    rw [deriv_const]
    rw [deriv_id'']
    rw [add_zero]
    conv =>
      left
      left
      left
      right
      right
      right
      right
      change 1
    rw [mul_one]
    sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · intro hc
      have := mul_eq_zero.mp hc
      cases this with
      | inl h =>
        have := mul_eq_zero.mp h
        cases this with
        | inl h => sorry
        | inr h =>
          revert h;simp;refine (rpow_ne_zero ?_ ?_).mpr ?_ <;> linarith
      | inr h => sorry


lemma deriv_Fdistribution (a d₁ d₂ x : ℝ)
  (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hx : 0 < x)
  : deriv (FDistribution d₁ d₂) x =
    (
      (d₁ ^ d₁ * d₂ ^ d₂ * d₁ * (
          ((x ^ (d₁ - 1)) *              (d₁ * x + d₂) ^ (d₁ + d₂)) -
          ( x ^ d₁        * ((d₁ + d₂) * (d₁ * x + d₂) ^ (d₁ + d₂ - 1)))
      )) /
      (
        (d₁ * x + d₂) ^ (d₁ + d₂)) ^ 2 /
        (2 * √(d₁ ^ d₁ * d₂ ^ d₂ * x ^ d₁ / (d₁ * x + d₂) ^ (d₁ + d₂))) * (x * Beta (d₁ / 2) (d₂ / 2))
        - (√(((d₁ ^ d₁ * d₂ ^ d₂) * x ^ d₁) / ((d₁ * x + d₂) ^ (d₁ + d₂)))) * (Beta (d₁ / 2) (d₂ / 2)
      )
    )
    /
    ((x * Beta (d₁ / 2) (d₂ / 2))^2)
     := by
     unfold FDistribution
     rw [deriv_div]
     rw [deriv_FdistributionNumerator]
     rw [deriv_mul_const]
     rw [deriv_id'']
     unfold FDistributionNumerator
     simp
     ring_nf
     simp
     exact 5.3 -- hmm...
     tauto
     tauto
     tauto
     unfold FDistributionNumerator
     apply DifferentiableAt.sqrt
     apply DifferentiableAt.div
     apply DifferentiableAt.mul
     apply DifferentiableAt.mul
     exact differentiableAt_const _
     exact differentiableAt_const _
     refine differentiableAt_rpow_const_of_ne d₁ ?_
     linarith
     refine DifferentiableAt.rpow ?_ ?_ ?_
     simp
     apply DifferentiableAt.const_mul
     simp
     simp
     -- as before
     sorry
     sorry
     sorry
     simp
     intro hc
     have := mul_eq_zero.mp hc
     cases this with
     | inl h => linarith
     | inr h =>
        unfold Real.Beta at h
        have := div_eq_zero_iff.mp h
        cases this with
        | inl h =>
          have := mul_eq_zero.mp h
          cases this with
          | inl h =>
            revert h;simp
            intro hc
            have ⟨m,hm⟩ := (Gamma_eq_zero_iff (d₁ / 2)).mp hc
            have : d₁ / 2 ≤ 0 := by
              rw [hm]
              simp
            linarith
          | inr h =>
            revert h;simp
            intro hc
            have ⟨m,hm⟩ := (Gamma_eq_zero_iff (d₂ / 2)).mp hc
            have : d₂ / 2 ≤ 0 := by
              rw [hm]
              simp
            linarith
        | inr h =>
            revert h;simp
            intro hc
            have ⟨m,hm⟩ := (Gamma_eq_zero_iff _).mp hc
            have : d₁ / 2 + d₂ / 2 ≤ 0 := by
              rw [hm]
              simp
            linarith

/-

((a^a*b^b*(a*x^(a-1))*(a*x+b)^(a+b)-
a^a*b^b*x^a*((a+b)*(a*x+b)^(a+b-1)*a))/
((a*x+b)^(a+b))^2/
(2*√(a^a*b^b*x^a/(a*x+b)^(a+b)))*(x*β(a/2)(b/2))
-(√(((a^a*b^b)*x^a)/((a*x+b)^(a+b))))*(β(a/2)(b/2)))/
((x*β(a/2)(b/2))^2)

-/


lemma simplify (a d₁ d₂ x : ℝ) (target : ℝ)
  (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hx : 0 < x)
  :
    (
      (d₁ ^ d₁ * d₂ ^ d₂ * d₁ * (
          ((x ^ (d₁ - 1)) *              (d₁ * x + d₂) ^ (d₁ + d₂)) -
          ( x ^ d₁        * ((d₁ + d₂) * (d₁ * x + d₂) ^ (d₁ + d₂ - 1)))
      )) /
      (
        (d₁ * x + d₂) ^ (d₁ + d₂)) ^ 2 /
        (2 * √(d₁ ^ d₁ * d₂ ^ d₂ * x ^ d₁ / (d₁ * x + d₂) ^ (d₁ + d₂))) * (x * Beta (d₁ / 2) (d₂ / 2))
        - (√(((d₁ ^ d₁ * d₂ ^ d₂) * x ^ d₁) / ((d₁ * x + d₂) ^ (d₁ + d₂)))) * (Beta (d₁ / 2) (d₂ / 2)
      )
    ) / ((x * Beta (d₁ / 2) (d₂ / 2))^2)

    =

-- Wolfram Alpha derivative d₃d₂
 -(d₂^(d₂/2) * d₁^(d₁/2) * x^(d₁/2 - 2) * (d₂ * (d₁ * (x - 1) + 2) + 2 * d₁ * x) * (d₂ + d₁ * x)^((1/2) * ((-d₂ - d₁) - 2)))/(2 * Beta (d₁/2) (d₂/2))



    := by
    sorry



    -- (Beta (d₁ / 2) (d₂ / 2) * (
    --   ((d₁ ^ d₁ * d₂ ^ d₂ * d₁ * x ^ (d₁ - 1) * (d₁ * x + d₂) ^ (d₁ + d₂ - 1) * (d₂ - x * d₂)) / (
    --     (d₁ * x + d₂) ^ (d₁ + d₂)) ^ 2 /
    --     (2 * √(d₁ ^ d₁ * d₂ ^ d₂ * x ^ d₁ / (d₁ * x + d₂) ^ (d₁ + d₂))))
    --     * x
    --     -
    --     (√(((d₁ ^ d₁ * d₂ ^ d₂) * x ^ d₁) / ((d₁ * x + d₂) ^ (d₁ + d₂))))

    -- ))
    -- /
    -- ((x * Beta (d₁ / 2) (d₂ / 2))^2)
