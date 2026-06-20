import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Hypothesis testing

 -/

open MeasureTheory ProbabilityTheory

noncomputable def one_sided_pval (a : ℝ)
  (p : Measure ℝ) :=
  let μ := moment id 1 p
  p {x | |x - μ| ≥ |a - μ| ∧
  Real.sign (x - μ) = Real.sign (a - μ)}

noncomputable def one_sided_pvalPMF (a : ℝ)
  (p : PMF ℝ) :=
  -- let μ := ∫ (x : ℝ), x ∂ p.toMeasure
  let μ := moment id 1 p.toMeasure
  p.toMeasure {x | |x - μ| ≥ |a - μ| ∧ Real.sign (x - μ) = Real.sign (a - μ)}



noncomputable def one_sided_pval' (a : ℝ)
  (p : Measure ℝ) :=
  let μ := moment id 1 p
  ite (a > μ)
    (p (Set.Ici a))
  (ite (a < μ)
    (p (Set.Iic a)) 1)

noncomputable def two_sided_pval' (a : ℝ)
  (p : Measure ℝ) :=
  let μ := moment id 1 p
  ite (a > μ)
    (p (Set.Ici a) + p (Set.Iic (μ - (a - μ))))
  (ite (a < μ)
    (p (Set.Iic a) + p (Set.Ici (μ + (μ - a)))) 1)

noncomputable def two_sided_pval (a : ℝ)
  (p : Measure ℝ) :=
  let μ := moment id 1 p
  p {x |  |x - μ| ≥ |a - μ|}

def twoSidedRejectionRegion (p : Measure ℝ)
  (threshold : ENNReal) := {observed | two_sided_pval observed p < threshold}

def power (threshold : ENNReal) (p₀ : Measure ℝ) := -- p₀ is the null hypothesis measure
  fun (p : Measure ℝ) => p (twoSidedRejectionRegion p₀ threshold)

/-- Type 1 error when testing
H₀ : θ = hypθ
Incorrectly reject H₀.
-/
def type1err (f : ℝ → Measure ℝ)
  (hypθ realθ observed : ℝ) (threshold : ENNReal) :=
    observed ∈ twoSidedRejectionRegion (f hypθ) threshold
    ∧ hypθ = realθ

/-- Type 2 error: incorrectly fail to reject H₀. -/
def type2err (f : ℝ → Measure ℝ)
  (hypθ realθ observed : ℝ) (threshold : ENNReal) :=
    observed ∉ twoSidedRejectionRegion (f hypθ) threshold
    ∧ hypθ ≠ realθ

def correct_fail_to_reject (f : ℝ → Measure ℝ)
  (hypθ realθ observed : ℝ) (threshold : ENNReal) :=
    observed ∉ twoSidedRejectionRegion (f hypθ) threshold
    ∧ hypθ = realθ

def correct_reject (f : ℝ → Measure ℝ)
  (hypθ realθ observed : ℝ) (threshold : ENNReal) :=
    observed ∈ twoSidedRejectionRegion (f hypθ) threshold
    ∧ hypθ ≠ realθ

-- example : binomial distribution with p = 1/2. expectation of PMF?

lemma two_sided_p_val_eq_two_sided_p_val' (a : ℝ)
  (p : Measure ℝ) : two_sided_pval a p = two_sided_pval' a p := by
  simp [two_sided_pval,two_sided_pval']
  split_ifs with g₀ g₁
  · have h₀ : Disjoint (Set.Ici a) (Set.Iic (moment id 1 ↑p - (a - moment id 1 ↑p))) := by
      intro A hA₀ hA₁ x hx
      have h₀ := hA₀ hx
      have h₁ := hA₁ hx
      simp at h₀ h₁
      have := le_trans h₀ h₁
      simp at this
      ring_nf at this
      have : a ≤ moment id 1 p := by linarith
      linarith
    have :  p (Set.Ici a ∪  Set.Iic (moment id 1 ↑p - (a - moment id 1 ↑p)))
         =  p (Set.Ici a) + p (Set.Iic (moment id 1 ↑p - (a - moment id 1 ↑p))) := by
      rw [measure_union]
      exact h₀
      exact measurableSet_Iic

    rw [← this]
    congr
    ext x
    constructor
    intro h
    · clear this h₀ g₀
      generalize moment id 1 p = α at *
      show x ∈ (Set.Ici a ∪ Set.Iic (α - (a - α)))
      simp
      by_cases H : a ≤ x
      · left
        exact H
      · right
        simp at H
        -- x -- avg(x,a) -- a
        --               α is closer to a; then α ≥ avg
        let avg := (x + a) / 2
        suffices avg ≤ α by
          unfold avg at this
          linarith
        have h₀ : |x - a| = |x - avg| + |avg - a| := by
          sorry
        have h₁ : x ≤ avg := by sorry
        have h₂ : avg ≤ a := by sorry
        by_cases G : a ≤ α
        · linarith
        ·
          simp at G
          -- x -- avg(x,a) -- a
          --               α- a
          by_contra J
          revert h
          simp at J ⊢
          have : |x - α| = |x - avg| + |avg - α| := by
            sorry
          rw [this]
          have : |x - avg| = |x - a| - |avg - a| := by linarith
          rw [this]
          sorry
    · have :  |a - moment id 1 p|
          = a - moment id 1 p := by
            apply (@abs_eq_self ℝ _ _ _ (a - moment id 1 p)).mpr
            linarith
      rw [this]

      rintro (h₀ | h₁)
      · have : moment id 1 p ≤ a := by linarith
        have :  |x - moment id 1 p|
          = x - moment id 1 p := by
            apply (@abs_eq_self ℝ _ _ _ (x - moment id 1 p)).mpr
            simp at h₀
            linarith
        rw [this]
        simp at h₀
        linarith
      · by_cases H : 0 ≤ x - moment id 1 p
        · have : |x - moment id 1 p| = x - moment id 1 p := by
                apply (@abs_eq_self ℝ _ _ _ (x - moment id 1 p)).mpr
                linarith
          rw [this]
          simp at h₁
          linarith
        · have : |x - moment id 1 p| = - (x - moment id 1 p) := by
                apply (@abs_eq_neg_self ℝ _ _ _ (x - moment id 1 p)).mpr
                linarith
          rw [this]
          simp at h₁
          linarith
  · sorry
  · sorry

lemma one_sided_p_val_eq_one_sided_p_val' (a : ℝ)
  (p : Measure ℝ) : one_sided_pval a p = one_sided_pval' a p
    := sorry


lemma one_sided_p_val_le_two_sided_p_val (a : ℝ)
  (p : Measure ℝ) : one_sided_pval a p ≤ two_sided_pval a p
    := sorry
