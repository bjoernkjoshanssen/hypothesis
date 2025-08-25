import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Support vector machines

as in `s4cs`
-/

def separable {k : ℕ} (A B : Set (Fin k → ℝ)) := ∃ b : ℝ, ∃ w : Fin k → ℝ,
  (∀ x ∈ A, w ⬝ᵥ x - b ≤ -1) ∧
  (∀ x ∈ B, w ⬝ᵥ x - b ≥ 1)

/-- From Section 8.7 in `s4cs`.
 The first example we think of is
`b=1`, `(w₁,w₂)=(0,2)` which has `√(w₁^2+w₂^2)=2`.

Book claims that minimizing `√(w₁^2+w₂^2)`
will maximize the distance between the lines
![w₁,w₂] ⬝ᵥ x - b = -1
![w₁,w₂] ⬝ᵥ x - b = 1


Book claims `w₁=w₂=b=1` minimizes `√(w₁^2+w₂^2)`
subject to
`(1 ≤ b + w₁ ∧ 1 ≤ b) ∧ 1 ≤ w₁ + w₂ - b`
Let's first check that `w₁=w₂=b=1` satisfies our constrains:
-/
example : separable ({![-1,0], ![0,0]} : Set (Fin 2 → ℝ)) ({![1,1]} : Set (Fin 2 → ℝ)) := by
  simp [separable]
  use 1
  simp
  use ![1,1]
  simp

lemma tooHardForChatGPT (x y : ℝ) (h₀ : 2 ≤ x + y) : 2 ≤ x^2 + y^2 := by
  have : 2 ≤ x + |y| := by
    apply le_trans h₀
    rw [add_le_add_iff_left]
    exact le_abs_self y
  suffices 2 ≤ x^2 + |y|^2 by simp at this;tauto
  by_cases h : x ≤ 2
  · have : |y|^2 ≥ (2-x)^2 := by
      repeat rw [pow_two]
      refine mul_le_mul_of_nonneg ?_ ?_ ?_ (by simp) <;> linarith
    calc 2 ≤ x^2 + (2-x)^2 := by
          suffices 0 ≤ (x - 1)^2 by
            rw [sub_sq] at this; linarith
          positivity
        _ ≤ _ := by simp at this ⊢;exact this
  · suffices 2 ≤ x^2 by apply le_trans this;simp;positivity
    have : 2 < x := by linarith
    suffices 4 < x^2 by linarith
    rw [pow_two]
    calc _ = (2:ℝ) * 2 := by linarith
         _ < _ := by
          refine mul_lt_mul_of_pos_of_nonneg' this ?_ ?_ ?_
          <;> linarith

lemma tooHardForChatGPT₁ {x y : ℝ} (h₀ : 2 < x + y) : 2 < x^2 + y^2 := by
  have : 2 < x + |y| := by
    calc _ < _ := h₀
    _ ≤ _ := by
          rw [add_le_add_iff_left]
          exact le_abs_self y
  suffices 2 < x^2 + |y|^2 by simp at this;tauto
  by_cases h : x ≤ 2
  · have : |y|^2 > (2-x)^2 := by
      repeat rw [pow_two]
      refine mul_lt_mul_of_nonneg ?_ ?_ ?_ (by linarith) <;> linarith
    calc 2 ≤ x^2 + (2-x)^2 := by
          suffices 0 ≤ (x - 1)^2 by
            rw [sub_sq] at this; linarith
          positivity
        _ < _ := by linarith
  · suffices 2 < x^2 by
      calc _ < _ := this
           _ ≤ _ := by simp;positivity
    have : 2 < x := by linarith
    suffices 4 < x^2 by linarith
    rw [pow_two]
    calc _ = (2:ℝ) * 2 := by linarith
         _ < _ := by
          refine mul_lt_mul_of_pos_of_nonneg' this ?_ ?_ ?_
          <;> linarith


/-- Then the minimizing claim: -/
example (b w₁ w₂ : ℝ) (h : (1 ≤ b + w₁ ∧ 1 ≤ b) ∧ 1 ≤ w₁ + w₂ - b) :
  2 ≤ w₁ ^ 2 + w₂ ^ 2 := by
  have : 2 ≤ w₁ + w₂ := by linarith
  apply tooHardForChatGPT ; tauto


lemma uniqueClaim₂ (x y : ℝ) (h₀ : 2 ≤ x + y) (h₁ : x^2 + y^2 ≤ 2) :
    (x,y) = (1,1) := by
  have u (x y : ℝ) (h₀ : 2 = x + y) (h₁ : 2 = x^2 + y^2) :
      (x,y) = (1,1) := by
    simp
    have h : y = 2 - x := by linarith
    rw [h] at h₁
    have hx : x = 1 := by
      suffices x - 1 = 0 by linarith
      suffices (x-1)^2 = 0 by simp at this;tauto
      rw [sub_sq]
      simp
      rw [sub_sq] at h₁
      linarith
    constructor
    · suffices x - 1 = 0 by linarith
      suffices (x-1)^2 = 0 by simp at this;tauto
      rw [sub_sq]
      simp
      rw [sub_sq] at h₁
      linarith
    · linarith
  have : 2 ≤ x^2+y^2 := tooHardForChatGPT x y h₀
  apply u
  linarith
  by_contra hc
  have : 2 < x + y := lt_of_le_of_ne h₀ hc
  have := tooHardForChatGPT₁ (lt_of_le_of_ne h₀ hc)
  linarith

/-- Now let's consider the non-example.
`linarith` enables us to avoid thinking here.
-/
example : ¬ ∃ b w₁ w₂ : ℝ,
    (∀ x ∈ ({![0,0], ![1,1]} : Set (Fin 2 → ℝ)), ![w₁,w₂] ⬝ᵥ x - b ≤ -1) ∧
    (∀ x ∈ ({![0,1], ![1,0]} : Set (Fin 2 → ℝ)),          ![w₁,w₂] ⬝ᵥ x - b ≥ 1) := by
  push_neg
  intro b w₁ w₂ h
  simp at h ⊢
  contrapose! h
  intro h₀
  linarith

def A₀ := ({![0,0], ![1,1]} : Set (Fin 2 → ℝ))
def A₁ := ({![0,1], ![1,0]} : Set (Fin 2 → ℝ))

example : ¬ separable A₀ A₁ := by
  simp [separable, A₀, A₁]
  intro b w₁ w₂ h h'
  linarith

-- But we can transform the data to be separable:
def φ : (Fin 2 → ℝ) → (Fin 3 → ℝ) := fun x => ![x 0,x 1, (x 0 + x 1 - 1)^2]

example : separable (φ '' A₀) (φ '' A₁) := by
  simp [separable, A₀, A₁, φ]
  use -1
  use ![0,0,-2]
  constructor
  · intro x hx
    cases hx with
    | inl h => rw [← h];simp;linarith
    | inr h => rw [← h];simp;linarith
  · intro x hx
    cases hx with
    | inl h => rw [← h];simp
    | inr h => rw [← h];simp

/-- The "kernel trick" means we forget about the data just map
"without the computational burden of explicitly performing the transformation"
-/
def φ₀ : (Fin 2 → ℝ) → (Fin 1 → ℝ) := fun x => ![(x 0 + x 1 - 1)^2]

example : separable (φ₀ '' A₀) (φ₀ '' A₁) := by
  simp [separable, A₀, A₁, φ₀]
  use -1
  simp
  use -2
  simp
  conv =>
    right
    change 2
  linarith


/--  If x₁ and x₂ are on the same side of the line then so is
s x₁ + (1-s)x₁. This fact in part explains the previous example:
there the segments connecting points on the same side intersect.
 -/
 example (b w₁ w₂ : ℝ) (u v : Fin 2 → ℝ) (h : (∀ x ∈ ({u,v} : Set (Fin 2 → ℝ)),
  ![w₁,w₂] ⬝ᵥ x - b ≥ 1)) (s : ℝ) (hs : s ∈ Set.Icc 0 1):
    ![w₁,w₂] ⬝ᵥ (s • u + (1-s) • v) - b ≥ 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
   ge_iff_le, forall_eq_or_imp,
    forall_eq] at h
  unfold dotProduct at h
  simp at h hs
  unfold dotProduct
  simp
  cases h with
  | intro left right =>
    suffices  1 ≤ s * (w₁ * u 0 + w₂ * u 1 - b) + (1 - s) * (w₁ * v 0 + w₂ * v 1 - b) by
      linarith
    generalize  w₁ * u 0 + w₂ * u 1 - b = A at *
    generalize w₁ * v 0 + w₂ * v 1 - b = B at *
    calc 1 = s * 1 + (1 - s) * 1 := by linarith
         _ ≤ _ := by
          refine add_le_add ?_ ?_
          refine mul_le_mul_of_nonneg ?_ left ?_ ?_ <;> linarith
          refine mul_le_mul_of_nonneg ?_ right ?_ ?_ <;> linarith
