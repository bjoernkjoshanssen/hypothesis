import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!

# Exercises from Grinstead and Snell
-/

namespace exercise_1_2_4

def H := true
def T := false

lemma part_1 :
    {![H,H,H], ![H,H,T], ![H,T,H], ![H,T,T]} = {x | x 0 = H} := by
    apply subset_antisymm
    · intro v hv
      simp at hv
      cases hv with
      | inl h => subst h;simp
      | inr h => cases h with
      | inl h => subst h;simp
      | inr h => cases h with
      | inl h => subst h;simp
      | inr h => subst h;simp
    · intro v hv
      simp at hv ⊢
      by_cases H₁ : v 1 = H
      · by_cases H₂ : v 2 = H
        · left;ext i;fin_cases i <;> tauto
        · have H₂ : v 2 = T := eq_false_of_ne_true H₂
          right;left;ext i;fin_cases i <;> tauto
      · have H₁ : v 1 = T := eq_false_of_ne_true H₁
        by_cases H₂ : v 2 = H
        · right;right;left;ext i;fin_cases i <;> tauto
        · have H₂ : v 2 = T := eq_false_of_ne_true H₂
          right;right;right;ext i;fin_cases i <;> tauto

lemma part_2 :
    {![H,H,H], ![T,T,T]} = {x | ∀ i, x i = x 0} := by
    apply subset_antisymm
    · intro v hv
      simp at hv
      cases hv with
      | inl h => subst h;intro i;fin_cases i <;> tauto
      | inr h => subst h;intro i;fin_cases i <;> tauto
    · intro v hv
      simp at hv ⊢
      by_cases H₁ : v 0 = H
      · left; ext i; fin_cases i <;> simp_all
      · have : v 0 = T := eq_false_of_ne_true H₁
        rw [this] at hv
        right;ext i; fin_cases i <;> (simp; tauto)


lemma part_3 :
    {![H,H,T], ![H,T,H], ![T,H,H]} = {x | ∃! i, x i = T} := by
  apply subset_antisymm
  intro v hv
  simp at hv
  cases hv with
  | inl h =>
    subst h;simp
    use 2
    constructor
    simp
    intro i hi
    fin_cases i
    simp [H,T] at hi
    simp [H,T] at hi
    simp
  | inr h => cases h with
  | inl h =>
    subst h
    simp
    use 1
    simp
    intro i hi
    fin_cases i
    simp [H,T] at hi
    simp
    simp [H,T] at hi
  | inr h =>
    subst h
    simp
    use 0
    simp
    intro i hi
    fin_cases i
    simp
    simp [H,T] at hi
    simp [H,T] at hi
  intro v hv
  obtain ⟨i,hi⟩ := hv
  fin_cases i
  simp at hi ⊢
  right;right;ext j
  fin_cases j
  · simp;tauto
  · simp
    have := hi.2 1
    simp at this
    exact Bool.not_eq_not.mp this
  · simp
    have := hi.2 2
    simp at this
    exact Bool.not_eq_not.mp this

  simp at hi ⊢
  right;left;ext j
  fin_cases j
  · simp
    have := hi.2 0
    simp at this
    exact Bool.not_eq_not.mp this
  · simp;tauto
  · simp
    have := hi.2 2
    simp at this
    exact Bool.not_eq_not.mp this

  simp at hi ⊢
  left;ext j
  fin_cases j
  · simp
    have := hi.2 0
    simp at this
    exact Bool.not_eq_not.mp this
  · simp
    have := hi.2 1
    simp at this
    exact Bool.not_eq_not.mp this
  · simp;tauto

lemma part_4 : -- summer research
    {![H,H,T], ![H,T,H], ![H,T,T], ![T,H,H], ![T,H,T], ![T,T,H], ![T,T,T]}
    = {x | ∃ i, x i = T} := by
  sorry
end exercise_1_2_4
