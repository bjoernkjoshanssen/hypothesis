import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear regression
-/

noncomputable def K₁ {n : ℕ} (x : Fin n → ℝ) := @Submodule.span ℝ (EuclideanSpace ℝ (Fin n)) _ _ _
    {x, fun _ => 1}

noncomputable def K₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) := @Submodule.span ℝ (EuclideanSpace ℝ (Fin n)) _ _ _
    {x₀, x₁, fun _ => 1}

theorem hxK₁ {n : ℕ} (x : Fin n → ℝ) : x ∈ K₁ x := Submodule.mem_span_of_mem (Set.mem_insert x {fun _ ↦ 1})

theorem hxK₂₀ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : x₀ ∈ K₂ x₀ x₁ := Submodule.mem_span_of_mem (Set.mem_insert x₀ _)
theorem hxK₂₁ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : x₁ ∈ K₂ x₀ x₁ := Submodule.mem_span_of_mem (by simp)

theorem h1K₁ {n : ℕ} (x : Fin n → ℝ) : (fun _ ↦ 1) ∈ K₁ x := Submodule.mem_span_of_mem (Set.mem_insert_of_mem x rfl)

theorem h1K₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : (fun _ ↦ 1) ∈ K₂ x₀ x₁ := Submodule.mem_span_of_mem (by simp)

theorem topsub₁ {n : ℕ} (x : Fin n → ℝ) :
    ⊤ ≤ Submodule.span ℝ (Set.range ![(⟨x, hxK₁ x⟩ : K₁ x), (⟨fun _ => 1, h1K₁ x⟩ : K₁ x)]) := by
  simp [K₁]
  apply Submodule.eq_top_iff'.mpr
  simp
  intro a ha
  apply Submodule.mem_span_pair.mpr
  obtain ⟨c,d,hcd⟩ := Submodule.mem_span_pair.mp ha
  use d, c
  simp
  rw [← hcd]
  rw [add_comm]

theorem topsub₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) :
    ⊤ ≤ Submodule.span ℝ (Set.range ![
      (⟨x₀, hxK₂₀ x₀ x₁⟩ : K₂ x₀ x₁),
      (⟨x₁, hxK₂₁ x₀ x₁⟩ : K₂ x₀ x₁),
      (⟨fun _ => 1, h1K₂ x₀ x₁⟩ : K₂ x₀ x₁)]) := by
  simp [K₂]
  apply Submodule.eq_top_iff'.mpr
  simp
  intro a ha
  apply Submodule.mem_span_triple.mpr
  obtain ⟨c,d,e,h⟩ := Submodule.mem_span_triple.mp ha
  use e, d, c
  simp
  rw [← h]
  grind


def Kvec₁ {n : ℕ} (x : Fin n → ℝ) := ![(⟨x, hxK₁ x⟩ : K₁ x), (⟨fun _ => 1, h1K₁ x⟩ : K₁ x)]

def Kvec₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) := ![
  (⟨x₀, hxK₂₀ x₀ x₁⟩ : K₂ x₀ x₁),
  (⟨x₁, hxK₂₁ x₀ x₁⟩ : K₂ x₀ x₁),
  (⟨fun _ => 1, h1K₂ x₀ x₁⟩ : K₂ x₀ x₁)]

/-- Given points `(x i, y i)`, obtain the coordinates `[c, d]` such that
`y = c x + d` is the best fit regression line. -/
noncomputable def regression_coordinates₁ {n : ℕ} (x y : Fin n → ℝ)
    (lin_indep : LinearIndependent ℝ (Kvec₁ x)) :
    Fin 2 → ℝ := fun i => ((Module.Basis.mk lin_indep (topsub₁ _)).repr
      ⟨Submodule.starProjection (K₁ x) y,
       Submodule.starProjection_apply_mem (K₁ x) y⟩) i

noncomputable def regression_coordinates₂ {n : ℕ} (x₀ x₁ y : Fin n → ℝ)
    (lin_indep : LinearIndependent ℝ (Kvec₂ x₀ x₁)) :
    Fin 3 → ℝ := fun i => ((Module.Basis.mk lin_indep (topsub₂ _ _)).repr
      ⟨Submodule.starProjection (K₂ x₀ x₁) y,
       Submodule.starProjection_apply_mem (K₂ x₀ x₁) y⟩) i


lemma indep₀₁₂ : LinearIndependent ℝ (Kvec₁ ![0, 1, 2]) := by
    simp [Kvec₁]
    refine LinearIndependent.pair_iff.mpr ?_
    intro s t h
    simp at h
    have : ![s * 0, s * 1, s * 2] + ![t * 1, t * 1, t * 1] = 0 := by
      rw [← h]
      congr <;> (ext i; fin_cases i <;> simp)
    simp at this
    have := this.1
    subst this
    simp at this
    tauto

lemma hvo₀₁₁ (w : EuclideanSpace ℝ (Fin 3))
    (hw : w ∈ K₁ ![0, 1, 2]) : inner ℝ (![0, 1, 1] - ![1 / 6, 4 / 6, 7 / 6]) w = 0 := by
  obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hw
  rw [← h]
  simp [inner]
  rw [Fin.sum_univ_three]
  repeat rw [Pi.sub_apply]
  simp
  grind

/--
The best fitting line for (0,0), (1,1), (1,2) is y=x/2+1/6:
  · · · · · · · · · · · · *
1 · · · · · · X · · · * · X
  · · · · · · · · * · · · ·
  · · · · · · * · · · · · ·
  · · · · * · · · · · · · ·
  · · * · · · · · · · · · ·
  * · · · · · · · · · · · ·
0 X · · · · · · · · · · · ·
  0 . . . . . 1 . . . . . 2
-/
example : regression_coordinates₁ ![0,1,2] ![0,1,1] indep₀₁₂ = ![1/2,1/6] := by
  unfold regression_coordinates₁
  simp
  have hvm : ![1 / 6, 4 / 6, 7 / 6] ∈ K₁ ![0, 1, 2] := by
    refine Submodule.mem_span_pair.mpr ?_
    use 1/2, 1/6
    ext i
    fin_cases i <;> (simp; try grind)
  rw [LinearIndependent.repr_eq indep₀₁₂ (l := {
    toFun := ![2⁻¹, 6⁻¹]
    support := Finset.univ
    mem_support_toFun := by intro i;fin_cases i <;> simp
  })]
  · simp
  · apply Subtype.coe_eq_of_eq_mk
    rw [Submodule.eq_starProjection_of_mem_of_inner_eq_zero hvm hvo₀₁₁]
    simp [Kvec₁]
    ext j
    fin_cases j <;> (simp [Finsupp.linearCombination, Finsupp.sum]; try grind)
