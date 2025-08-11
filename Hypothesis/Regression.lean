import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul

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



def A₃ (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![
  x 0, 1;
  x 1, 1;
  x 2, 1
]

local notation x "ᵀ" => Matrix.transpose x


/-- General version of `A₃`. -/
def A {m : ℕ} (x : Fin m → ℝ) : Matrix (Fin m) (Fin 2) ℝ :=
    ![x, fun _ => 1]ᵀ -- or maybe (Matrix.of ![x, fun _ => 1])ᵀ


noncomputable def getCoeffs₃ (x y : Fin 3 → ℝ) :=
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A₃ x)ᵀ) (A₃ x))⁻¹ ((A₃ x)ᵀ))
  !![y 0; y 1; y 2]

noncomputable def getCoeffs {m : ℕ} (x y : Fin m → ℝ) :=
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A x)ᵀ) (A x))⁻¹ ((A x)ᵀ))
  (fun i (_ : Fin 1) => y i)


lemma matrix_smul {m : ℕ} (b : Matrix (Fin m) (Fin 1) ℝ)
    (v : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (o : Matrix (Fin m) (Fin 2) ℝ) (i : Matrix (Fin 2) (Fin m) ℝ) :
    o * (c • v * i * b) = c • (o * (v * i * b)) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul]


lemma getx {m : ℕ} (x : Fin m → ℝ) (c : ℝ) (e : Matrix (Fin 2) (Fin 1) ℝ) :
    ((c • e) 0 0 • x + (c • e) 1 0 • fun (_ : Fin m) ↦ (1:ℝ)) =
    fun i ↦ (c • ((A x) * e)) i 0 := by
  have ho (o : ℝ) :  c * e 0 0 * o + c * e 1 0
    =  c * (e 0 0 * o + e 1 0) := by rw [mul_assoc,left_distrib]
  by_cases H : c = 0
  · rw [H]
    simp
    ext i
    simp
  · unfold A
    ext i
    simp
    rw [ho]
    apply (IsUnit.mul_right_inj (Ne.isUnit H)).mpr
    rw [mul_comm]
    /- this looks hard now but we can spell it out for Lean
     in great detail: -/
    have : e 1 0 = (fun x : Fin m => 1) i * e 1 0 := by
        simp
    rw [this]
    have : x i = (fun i => x i) i := by simp
    rw [this]
    have : x = fun i => x i := rfl
    nth_rw 2 [this]
    unfold Matrix.transpose
    have : (fun i => x i) = ![fun i ↦ x i, fun x ↦ 1] 0 := rfl
    nth_rw 1 [this]
    have : (fun x => 1) = ![fun i ↦ x i, fun x ↦ 1] 1 := rfl
    nth_rw 2 [this]
    generalize ![fun i ↦ x i, fun x ↦ 1] = q
    have : q 0 i * e 0 0 + q 1 i * e 1 0
        = ∑ j : Fin 2, q j i * e j 0 := by simp
    rw [this]
    congr

lemma getx₃ (x : Fin 3 → ℝ) (c : ℝ) (e : Matrix (Fin 2) (Fin 1) ℝ) :
    ((c • e) 0 0 • x + (c • e) 1 0 • fun (_ : Fin 3) ↦ (1:ℝ)) =
    fun i ↦ (c • (!![x 0, 1; x 1, 1; x 2, 1] * e)) i 0 := by

--   have := @getx 3 x c e
--   rw [this]
--   unfold A
--   congr

--   apply funext
--   rw [← funext_iff]
--   suffices (fun i ↦ (c • (![x, fun x ↦ 1]ᵀ * e)) i) = fun i ↦ (c • (!![x 0, 1; x 1, 1; x 2, 1] * e)) i by
--     simp_rw [this]
--   ext i j
--   fin_cases j
--   congr
--   simp only [Fin.zero_eta, Fin.isValue, Matrix.smul_apply,
--     smul_eq_mul]
--   congr
--   apply funext_iff.mp
--   apply funext_iff.mp
--   congr
--   simp [Matrix.transpose]

--   ext j k
--   simp
-- this may eventually succeed but may not be worth it

  have ho (o : ℝ) :  c * e 0 0 * o + c * e 1 0
    =  c * (e 0 0 * o + e 1 0) := by rw [mul_assoc,left_distrib]
  by_cases H : c = 0
  · rw [H]
    simp
    ext i
    simp
  · ext i
    fin_cases i <;> (
        simp
        rw [ho]
        apply (IsUnit.mul_right_inj (Ne.isUnit H)).mpr
        simp [Matrix.vecMul]
        rw [mul_comm]
        congr
    )

lemma getDet {n : ℕ} (x : Fin n → ℝ) :
    !![∑ i : Fin n, x i ^ 2, ∑ i : Fin n, x i; ∑ i : Fin n, x i, n]⁻¹ =
        ((∑ i : Fin n, x i ^ 2) * n - (∑ i : Fin n, x i) ^ 2)⁻¹ •
      !![(n:ℝ), -(∑ i : Fin n, x i); -(∑ i : Fin n, x i), ∑ i : Fin n, x i ^ 2] := by
    rw [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two]
    simp
    constructor
    · constructor
      · ring_nf
        left
        trivial
      · left
        ring_nf
    · constructor <;>
      · left
        ring_nf

lemma getDet₃ (x₀ x₁ x₂ : ℝ) :
  !![x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2, x₀ + x₁ + x₂; x₀ + x₁ + x₂, 3]⁻¹ =
    (2 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 - x₀ * x₁ - x₀ * x₂ - x₁ * x₂))⁻¹ •
      !![3, -(x₀ + x₁ + x₂); -(x₀ + x₁ + x₂), x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2] := by
    rw [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two]
    simp
    repeat rw [← mul_inv]
    constructor
    · constructor
      · ring_nf
      · left
        congr
        ring_nf
    · constructor <;>
      · left
        congr
        ring_nf

theorem matrix_proj_in_subspace {m : ℕ} (x : Fin m → ℝ) (Y : Matrix (Fin m) (Fin 1) ℝ) :
  (fun i ↦ (A x).mulᵣ (((A xᵀ.mulᵣ (A x))⁻¹.mulᵣ (A xᵀ)).mulᵣ Y) i 0) ∈ K₁ x := by
  simp [K₁]
  unfold A
  apply Submodule.mem_span_pair.mpr
  let α := ((A x)ᵀ * (A x))⁻¹ * (A x)ᵀ * Y
  use α 0 0, α 1 0
  unfold α
  have h₀ : (A x)ᵀ
    = ![x, fun _ => 1] := by
    unfold A
    simp
  have : (A x)ᵀ * (A x)
    = !![∑ i : Fin m, x i ^ 2, ∑ i : Fin m, x i;
         ∑ i : Fin m, x i,                   m] := by
    repeat rw [h₀]
    unfold A
    sorry
  repeat rw [this]
  have := @getDet m x
  rw [this]
  rw [h₀]
  simp only [Matrix.transpose_transpose]
  have := @getx m x ((∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2)⁻¹
    (!![
        (m : ℝ),
        -∑ i, x i;
        -∑ i : Fin m, x i,
        ∑ i : Fin m, x i ^ 2] * Matrix.of ![x, fun x : Fin m ↦ (1 : ℝ)] * Y)
  conv =>
    left
    left
    left
    change (((∑ i, x i ^ 2) * (m:ℝ) - (∑ i, x i) ^ 2)⁻¹ • !![↑m, -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2] * Matrix.of ![x, fun x ↦ 1] * Y) 0 0
  conv =>
    left
    right

    left
    change (((∑ i, x i ^ 2) * (m : ℝ) - (∑ i, x i) ^ 2)⁻¹ • !![(m : ℝ), -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2] * Matrix.of ![x, fun x ↦ 1] * Y) 1 0
--   rw [matrix_smul]
--   rw [this]
  sorry


theorem matrix_proj_in_subspace₃ (x : Fin 3 → ℝ) (Y : Matrix (Fin 3) (Fin 1) ℝ) :
  (fun i ↦ (A₃ x).mulᵣ (((A₃ xᵀ.mulᵣ (A₃ x))⁻¹.mulᵣ (A₃ xᵀ)).mulᵣ Y) i 0) ∈ K₁ x := by
  simp [K₁]
  unfold A₃
  apply Submodule.mem_span_pair.mpr
  let α := ((!![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1])⁻¹ * !![x 0, 1; x 1, 1; x 2, 1]ᵀ *
          Y)
  use α 0 0, α 1 0
  unfold α
  have h₀ : !![x 0, 1; x 1, 1; x 2, 1]ᵀ
    = !![x 0, x 1, x 2; 1, 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have : !![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1]
    = !![x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2, x 0 + x 1 + x 2;
         x 0     + x 1     + x 2,                   3] := by
    repeat rw [h₀]
    ext i j; fin_cases i <;> fin_cases j <;> (simp; ring_nf)
  repeat rw [this]
  repeat rw [getDet₃, h₀, matrix_smul]
  repeat rw [Matrix.smul_mul]
  apply getx₃

lemma matrix_algebra {n t o w : ℕ}
    (B : Matrix (Fin n) (Fin t) ℝ)
    (hB : IsUnit (Bᵀ * B).det)
    (m : Fin t → Fin o → ℝ)
    (P : Matrix (Fin n) (Fin w) ℝ) :
    mᵀ * Bᵀ * P = mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P)) := by
  suffices  (mᵀ * Bᵀ * P) = (mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) by
    rw [this]
  have h₁ : (Bᵀ * B) * ((Bᵀ * B)⁻¹) = 1 := Matrix.mul_nonsing_inv (Bᵀ * B) hB
  have h₀ :  mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))
          =  mᵀ * (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) := by
        simp [Matrix.mul_assoc]
  rw [h₀]
  have : mᵀ * Bᵀ * P = mᵀ * (Bᵀ * P) := by
    simp [Matrix.mul_assoc]
  rw [this]
  suffices  (Bᵀ * P) = (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) by
    rw [this]
  have : Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ    * P)) =
        (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ))) * P := by
    simp [Matrix.mul_assoc]
  rw [this]
  suffices Bᵀ = Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ)) by
    nth_rw 1 [this]
  repeat rw [← Matrix.mul_assoc]
  rw [h₁]
  simp

theorem star_projection_is_matrix_product {x : Fin 3 → ℝ}
    (y : Fin 3 → ℝ)
    (hB : IsUnit (!![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1]).det) :
    -- this just says ¬ (x 0 = x 1 ∧ x 0 = x 2)
  (fun i => Matrix.mulᵣ (A₃ x) (
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A₃ x)ᵀ) (A₃ x))⁻¹ ((A₃ x)ᵀ))
  !![y 0; y 1; y 2]) i 0) = Submodule.starProjection (K₁ x) y := by
  have : !![y 0; y 1; y 2] = fun i x ↦ y i := by
    ext i j; fin_cases i <;> simp;
  rw [this]
  symm
  rw [Submodule.eq_starProjection_of_mem_of_inner_eq_zero]
  · apply matrix_proj_in_subspace₃
  intro z hz
  simp [K₁] at hz
  obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hz
  rw [← h]
  unfold A₃
  have : (a • x + b • fun (x : Fin 3) ↦ (1:ℝ)) =
    fun i => Matrix.mulᵣ !![x 0, 1; x 1, 1; x 2, 1] ![![a], ![b]] i 0 := by
    ext i;fin_cases i <;> (simp [Matrix.vecMul];linarith)
  rw [this]
  generalize !![x 0, 1; x 1, 1; x 2, 1] = B at *
  -- general from here on
  rw [inner_sub_left]
  have {m : ℕ} (y z : EuclideanSpace ℝ (Fin m.succ)) : inner ℝ y z =
      Matrix.mulᵣ (fun _ i => z i) (fun i _ => y i) (0 : Fin 1) (0 : Fin 1) := by
    simp [inner, Matrix.mulᵣ, dotProduct]
  repeat rw [this]
  have h {m : ℕ} (xx : Matrix (Fin m.succ) (Fin 1) ℝ) :
    (fun _ i => xx i 0) = xxᵀ ∧
    (fun i _ => xx i 0) = xx := by
    constructor
    ext i j; fin_cases i; simp
    ext i j; fin_cases j; simp
  rw [(h _).1, (h _).2]
  generalize ![![a],![b]] = m
  simp
  rw [sub_eq_zero_of_eq]
  apply funext_iff.mp; apply funext_iff.mp
  apply matrix_algebra _ hB


theorem getCoeffs₃_eq_regression_coordinates₁ (x y i)
    (hl : LinearIndependent ℝ (Kvec₁ x))
    (hB : IsUnit (!![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1]).det) :
    getCoeffs₃ x y i 0 = regression_coordinates₁ x y hl i := by
  unfold getCoeffs₃ regression_coordinates₁
  simp_rw [← star_projection_is_matrix_product y hB]
  simp only [K₁, A₃, Kvec₁, Module.Basis.mk_repr]
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
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_filter]
  ext i;fin_cases i <;> (
    simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
    split_ifs with g₀ g₁ g₂ <;> (
        try rw [g₀]
        try rw [g₁]
        try rw [g₂]
        try simp
        try rw [mul_comm]))

example : getCoeffs₃ ![0,1,2] ![0,1,1] = !![1/2;1/6] := by
  unfold getCoeffs₃ A₃
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
example (a b c : ℝ) : getCoeffs₃ ![a,b,c] ![0,0,0] = ![![0],![0]] := by
  unfold getCoeffs₃
  generalize ((A₃ ![a, b, c]ᵀ.mulᵣ (A₃ ![a, b, c]))⁻¹.mulᵣ (A₃ ![a, b, c]ᵀ)) = x
  have : x = !![x 0 0, x 0 1, x 0 2;
                x 1 0, x 1 1, x 1 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this]
  ext i j; fin_cases i <;> fin_cases j <;> simp
