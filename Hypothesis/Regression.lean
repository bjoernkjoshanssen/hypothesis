import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear regression
-/
example : 0 ≤ 1505 := Nat.zero_le _
example : 1505 ≤ 1505 := Nat.le_refl _

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
example : regression_coordinates₁ ![0,1,2] ![0,1,1] indep₀₁₂
  = ![1/2,1/6] := by
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


def A (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![
  x 0,1;
  x 1,1;
  x 2,1
]
local notation "foo" x => x + 1
local notation x "ᵀ" => Matrix.transpose x

noncomputable def getCoeffs (x y : Fin 3 → ℝ) :=
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A x)ᵀ) (A x))⁻¹ ((A x)ᵀ))
  !![y 0; y 1; y 2]

theorem aug8_25 (x y : Fin 3 → ℝ) :
  (fun i ↦ (A x).mulᵣ (((A xᵀ.mulᵣ (A x))⁻¹.mulᵣ (A xᵀ)).mulᵣ !![y 0; y 1; y 2]) i 0) ∈ K₁ x := by
  simp [K₁]
  unfold A
  apply Submodule.mem_span_pair.mpr
  let α := ((!![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1])⁻¹ * !![x 0, 1; x 1, 1; x 2, 1]ᵀ *
          !![y 0; y 1; y 2])
  use α 0 0, α 1 0
  unfold α
  generalize !![y 0; y 1; y 2] = b
  have h₀ : !![x 0, 1; x 1, 1; x 2, 1]ᵀ
    = !![x 0, x 1, x 2; 1, 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have : !![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1]
    = !![x 0^2+x 1^2+x 2^2, x 0 + x 1 + x 2; x 0 + x 1 + x 2, 3] := by
    repeat rw [h₀]
    ext i j
    fin_cases i <;>
    · fin_cases j <;>
      · simp
        ring_nf
  repeat rw [this]
  have : !![x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2, x 0 + x 1 + x 2; x 0 + x 1 + x 2, 3]⁻¹
    = (2 * (x 0^2 + x 1^2 + x 2^2 - x 0 * x 1 - x 0 * x 2 - x 1 * x 2))⁻¹
    • !![3, - (x 0 + x 1 + x 2); - (x 0 + x 1 + x 2),x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2] := by
    rw [Matrix.inv_def]
    rw [Matrix.det_fin_two]
    rw [Matrix.adjugate_fin_two]
    simp
    constructor
    constructor
    · ring_nf
      field_simp
      ring_nf
    · left
      rw [← mul_inv]
      congr
      ring_nf
    · constructor <;>
      · left
        rw [← mul_inv]
        congr
        ring_nf

  repeat rw [this]
  repeat rw [h₀]
  have : (!![x 0, 1; x 1, 1; x 2, 1] *
        ((2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 0 * x 1 - x 0 * x 2 - x 1 * x 2))⁻¹ •
              !![3, -(x 0 + x 1 + x 2); -(x 0 + x 1 + x 2), x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2] *
            !![x 0, x 1, x 2; 1, 1, 1] *
          b)) =
         (2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 0 * x 1 - x 0 * x 2 - x 1 * x 2))⁻¹ •
    (!![x 0, 1; x 1, 1; x 2, 1] * (
              !![3, -(x 0 + x 1 + x 2); -(x 0 + x 1 + x 2), x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2] *
            !![x 0, x 1, x 2; 1, 1, 1] *
          b)) := by
        generalize !![3, -(x 0 + x 1 + x 2); -(x 0 + x 1 + x 2), x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2] = v
        simp
  repeat rw [this]
  generalize (2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 0 * x 1 - x 0 * x 2 - x 1 * x 2))⁻¹ = c
  generalize !![3, -(x 0 + x 1 + x 2); -(x 0 + x 1 + x 2), x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2] = d
  have : c • d * !![x 0, x 1, x 2; 1, 1, 1] * b
    = c • (d * !![x 0, x 1, x 2; 1, 1, 1] * b) := by simp
  rw [this]

  generalize d * !![x 0, x 1, x 2; 1, 1, 1] * b = e
  have : x = ![x 0, x 1, x 2] := by ext i;fin_cases i <;> simp
  nth_rewrite 1 [this]
  generalize x 0 = x₀
  generalize x 1 = x₁
  generalize x 2 = x₂
  by_cases H : c = 0
  · rw [H]
    simp
    ext i
    simp
  ext i
  fin_cases i
  simp
  have :  c * e 0 0 * x₀ + c * e 1 0
    =  c * (e 0 0 * x₀ + e 1 0) := by ring_nf
  rw [this]
  refine (IsUnit.mul_right_inj ?_).mpr ?_
  exact Ne.isUnit H
  simp [Matrix.vecMul]
  rw [mul_comm]
  congr
  simp
  have :  c * e 0 0 * x₁ + c * e 1 0
    =  c * (e 0 0 * x₁ + e 1 0) := by ring_nf
  rw [this]
  refine (IsUnit.mul_right_inj ?_).mpr ?_
  exact Ne.isUnit H
  simp [Matrix.vecMul]
  rw [mul_comm]
  congr
  simp
  have :  c * e 0 0 * x₂ + c * e 1 0
    =  c * (e 0 0 * x₂ + e 1 0) := by ring_nf
  rw [this]
  refine (IsUnit.mul_right_inj ?_).mpr ?_
  exact Ne.isUnit H
  simp [Matrix.vecMul]
  rw [mul_comm]
  congr

theorem star_projection_is_matrix_product (x y : Fin 3 → ℝ)
    (hB : IsUnit (!![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1]).det) :
    -- this just says ¬ (x 0 = x 1 ∧ x 0 = x 2)
  (fun i => Matrix.mulᵣ (A x) (
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A x)ᵀ) (A x))⁻¹ ((A x)ᵀ))
  !![y 0; y 1; y 2]) i 0) = Submodule.starProjection (K₁ x) y := by
  symm
  rw [Submodule.eq_starProjection_of_mem_of_inner_eq_zero]
  · apply aug8_25

  intro z hz
  simp [K₁] at hz
  obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hz
  rw [← h]
  unfold A
  have :  ((a • x + b • fun (x : Fin 3) ↦ (1:ℝ))) =
    fun i => Matrix.mulᵣ !![x 0, 1; x 1, 1; x 2, 1] ![![a], ![b]] i 0 := by
    ext i;fin_cases i <;> (simp [Matrix.vecMul];linarith)
  rw [this]
  revert hB
  generalize !![x 0, 1; x 1, 1; x 2, 1] = B
  intro hB
  rw [inner_sub_left]
  have (y z : EuclideanSpace ℝ (Fin 3)) : inner ℝ y z =
    Matrix.mulᵣ !![z 0, z 1, z 2] !![y 0; y 1; y 2] 0 0 := by
        simp [inner]
        rw [← add_assoc]
        exact Fin.sum_univ_three fun i ↦ z i * y i
  repeat rw [this]
  generalize ![![a],![b]] = m
  generalize y 0 = y₀
  generalize y 1 = y₁
  generalize y 2 = y₂
  let α := !![B.mulᵣ m 0 0, B.mulᵣ m 1 0, B.mulᵣ m 2 0]
  let β := (B.mulᵣ m)ᵀ
  have : α = β := by
    unfold α β
    ext i j; fin_cases i ; fin_cases j <;> simp
  unfold α β at this
  rw [this]
  generalize !![y₀; y₁; y₂] = P
  let γ := !![B.mulᵣ (((Bᵀ.mulᵣ B)⁻¹.mulᵣ (Bᵀ)).mulᵣ P) 0 0;
        B.mulᵣ (((Bᵀ.mulᵣ B)⁻¹.mulᵣ (Bᵀ)).mulᵣ P) 1 0;
        B.mulᵣ (((Bᵀ.mulᵣ B)⁻¹.mulᵣ (Bᵀ)).mulᵣ P) 2 0]
  let δ := B.mulᵣ (((Bᵀ.mulᵣ B)⁻¹.mulᵣ (Bᵀ)).mulᵣ P)
  have : γ = δ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ, δ]; try simp
  unfold γ δ at this
  rw [this]
  simp
  suffices (mᵀ * Bᵀ * P) 0 0 = (mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) 0 0 by
    exact sub_eq_zero_of_eq this
  suffices  (mᵀ * Bᵀ * P) = (mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) by
    rw [this]
  have h₁ : (Bᵀ * B) * ((Bᵀ * B)⁻¹) = 1 := by
    refine Matrix.mul_nonsing_inv (Bᵀ * B) hB
  have h₀ :  mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))
    =  mᵀ * (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) := by
        simp [Matrix.mul_assoc]
  rw [h₀]
  have : mᵀ * Bᵀ * P = mᵀ * (Bᵀ * P) := by
    simp [Matrix.mul_assoc]
  rw [this]
  suffices  (Bᵀ * P) = (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) by
    rw [this]
  have : Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P)) =
    (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ))) * P := by
    simp [Matrix.mul_assoc]
  rw [this]
  suffices Bᵀ = Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ)) by
    nth_rw 1 [this]
  repeat rw [← Matrix.mul_assoc]
  rw [h₁]
  simp


theorem getCoeffs_eq_regression_coordinates₁ (x y i)
  (hl : LinearIndependent ℝ (Kvec₁ x))
  (hB : IsUnit (!![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1]).det)
  :  getCoeffs x y i 0
  = regression_coordinates₁ x y hl i := by
  unfold getCoeffs regression_coordinates₁
  have := @star_projection_is_matrix_product x y hB
  simp_rw [← this]
  unfold K₁ A Kvec₁
  simp only [Module.Basis.mk_repr]
  rw [LinearIndependent.repr_eq
    ( l:= {
        toFun := fun i => ((!![x 0, 1; x 1, 1; x 2, 1]ᵀ.mulᵣ !![x 0, 1; x 1, 1; x 2, 1])⁻¹.mulᵣ (!![x 0, 1; x 1, 1; x 2, 1]ᵀ)).mulᵣ
            !![y 0; y 1; y 2] i 0
        support := {a | ((!![x 0, 1; x 1, 1; x 2, 1]ᵀ.mulᵣ !![x 0, 1; x 1, 1; x 2, 1])⁻¹.mulᵣ (!![x 0, 1; x 1, 1; x 2, 1]ᵀ)).mulᵣ
         !![y 0; y 1; y 2] a 0 ≠
            0}
        mem_support_toFun := by simp
    })
  ]
  · simp
  refine Subtype.coe_eq_of_eq_mk ?_

  generalize !![y 0; y 1; y 2] = z
  let X := !![x 0, 1; x 1, 1; x 2, 1]
  show _ =
  fun i ↦
  X.mulᵣ
    (((Xᵀ.mulᵣ X)⁻¹.mulᵣ (Xᵀ)).mulᵣ z) i 0
  conv =>
    left
    right
    right
    left
    change fun i ↦ ((Xᵀ.mulᵣ X)⁻¹.mulᵣ (Xᵀ)).mulᵣ z i 0
  have : X = !![x 0, 1; x 1, 1; x 2, 1] := rfl
  simp_rw [← this]
  let Y := ((Xᵀ.mulᵣ X)⁻¹.mulᵣ (Xᵀ)).mulᵣ z
  have : Y = ( ((Xᵀ.mulᵣ X)⁻¹.mulᵣ (Xᵀ)).mulᵣ z) := rfl
  simp_rw [← this]
  rw [Finsupp.linearCombination_apply]
  simp
  rw [Finsupp.sum]
  unfold X
  ext i;fin_cases i <;> (
    simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
    rw [Finset.sum_filter]
    simp
    split_ifs with g₀ g₁ g₂
    simp
    rw [g₀,g₁]
    simp
    rw [g₀]
    simp
    rw [g₂]
    simp
    rw [mul_comm]
    simp
    rw [mul_comm]
    )

example : getCoeffs ![0,1,2] ![0,1,1] = !![1/2;1/6] := by
  unfold getCoeffs A
  have (a : ℝ) : ![(0:ℝ),1,a] 2 = a := rfl
  repeat rw [this]
  have (a : ℝ) : ![(0:ℝ),1,a] 1 = 1 := rfl
  repeat rw [this]
  have (a : ℝ) : ![(0:ℝ),1,a] 0 = 0 := rfl
  repeat rw [this]
  have : !![(0:ℝ), 1; 1, 1; 2, 1]ᵀ
       = !![0, 1, 2; 1, 1, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this]
  rw [Matrix.inv_def]
  simp
  grind
example (a b c : ℝ) : getCoeffs ![a,b,c] ![0,0,0] = ![![0],![0]] := by
  unfold getCoeffs
  generalize ((A ![a, b, c]ᵀ.mulᵣ (A ![a, b, c]))⁻¹.mulᵣ (A ![a, b, c]ᵀ)) = x
  have : x = !![x 0 0, x 0 1, x 0 2;
                x 1 0, x 1 1, x 1 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this]
  ext i j; fin_cases i <;> fin_cases j <;> simp
