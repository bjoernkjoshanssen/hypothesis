import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1

/-!
# Linear regression

over ℝ or ℂ
-/

noncomputable def K₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) :=
    @Submodule.span R (EuclideanSpace R (Fin n)) _ _ _ {WithLp.toLp 2 x, WithLp.toLp 2 fun _ => 1}

theorem hxK₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) : WithLp.toLp 2 x ∈ K₁ x := Submodule.mem_span_of_mem (Set.mem_insert (WithLp.toLp 2 x) {WithLp.toLp 2 fun _ ↦ 1})
theorem h1K₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) : WithLp.toLp 2 (fun _ ↦ 1) ∈ K₁ x := Submodule.mem_span_of_mem (Set.mem_insert_of_mem (WithLp.toLp 2 x) rfl)

theorem topsub₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) :
    ⊤ ≤ Submodule.span R (Set.range ![(⟨WithLp.toLp 2 x, hxK₁ x⟩ : K₁ x), (⟨WithLp.toLp 2 fun _ => 1, h1K₁ x⟩ : K₁ x)]) := by
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



def Kvec₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) :=
    ![(⟨WithLp.toLp 2 x, hxK₁ x⟩ : K₁ x), (⟨WithLp.toLp 2 fun _ => 1, h1K₁ x⟩ : K₁ x)]


/-- Given points `(x i, y i)`, obtain the coordinates `[c, d]` such that
`y = c x + d` is the best fit regression line. -/
noncomputable def regression_coordinates₁ {n : ℕ} {R : Type*} [RCLike R] (x y : Fin n → R)
    (lin_indep : LinearIndependent R (Kvec₁ x)) :
    Fin 2 → R := fun i => ((Module.Basis.mk lin_indep (topsub₁ _)).repr
      ⟨Submodule.starProjection (K₁ x) (WithLp.toLp 2 y),
       Submodule.starProjection_apply_mem (K₁ x) (WithLp.toLp 2 y)⟩) i


local notation x "ᵀ" => Matrix.transpose x

def A {m : ℕ} {R : Type*} [RCLike R] (x : Fin m → R) : Matrix (Fin m) (Fin 2) R :=
    ![x, fun _ => 1]ᵀ -- or maybe (Matrix.of ![x, fun _ => 1])ᵀ

noncomputable def getCoeffs {m : ℕ} {R : Type*} [RCLike R] (x y : Fin m → R) :=
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A x)ᵀ) (A x))⁻¹ ((A x)ᵀ))
  (fun i (_ : Fin 1) => y i)

/-- getCoeffs is supposed to mimize this -/
def theDistance {m : ℕ} {R : Type*} [RCLike R] (x y : Fin m → R)
  (M : Matrix (Fin 2) (Fin 1) R) : R :=
  Finset.sum (Finset.univ : Finset (Fin m))
    (fun i => by exact (y i - (M 0 0 + (M 1 0) * (x i)))^2)

/-- `getCoeffs` minimizes `theDistance`. -/
theorem getCoeffs_minimizes_theDistance
   {m : ℕ} {R : Type*} [RCLike R] [LE R] (x y : Fin m → R) (M : Matrix (Fin 2) (Fin 1) R)
: ∀ a b : R,
  theDistance x y (getCoeffs x y) ≤ theDistance x y M := by
  intro a b
  unfold theDistance getCoeffs
  -- use Second Derivative Test with f = theDistance x y ?
  sorry

lemma matrix_smul {m : ℕ} {R : Type*} [RCLike R] (b : Matrix (Fin m) (Fin 1) R)
    (v : Matrix (Fin 2) (Fin 2) R) (c : R)
    (o : Matrix (Fin m) (Fin 2) R) (i : Matrix (Fin 2) (Fin m) R) :
    o * (c • v * i * b) = c • (o * (v * i * b)) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul]


lemma getx {m : ℕ} {R : Type*} [RCLike R] (x : Fin m → R) (c : R) (e : Matrix (Fin 2) (Fin 1) R) :
    ((c • e) 0 0 • x + (c • e) 1 0 • fun (_ : Fin m) ↦ (1:R)) =
    fun i ↦ (c • (Matrix.mulᵣ (A x) e)) i 0 := by
  have ho (o : R) :  c * e 0 0 * o + c * e 1 0
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


lemma getDet {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) :
    !![∑ i : Fin n, x i ^ 2, ∑ i : Fin n, x i; ∑ i : Fin n, x i, n]⁻¹ =
        ((∑ i : Fin n, x i ^ 2) * n - (∑ i : Fin n, x i) ^ 2)⁻¹ •
      !![(n : R), -(∑ i : Fin n, x i); -(∑ i : Fin n, x i), ∑ i : Fin n, x i ^ 2] := by
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

lemma matmulcase {m : ℕ} {R : Type*} [RCLike R] (x : Fin m → R) :
    Matrix.mulᵣ ![x, fun _ ↦ 1] (![x, fun _ ↦ 1]ᵀ) = !![∑ i, x i ^ 2, ∑ i, x i; ∑ i, x i, ↑m] := by
    unfold Matrix.mulᵣ
    rw [Matrix.transpose_transpose]
    ext i j
    fin_cases i
    fin_cases j
    simp -- yes!
    suffices  x ⬝ᵥ x = ∑ i, x i * x i by
        rw [this]
        congr
        ext i
        symm
        exact pow_two (x i)
    rfl
    simp
    suffices  x ⬝ᵥ (fun _ => 1) = ∑ i, x i * 1 by
        rw [this]
        congr
        ext i
        symm
        simp
    rfl
    fin_cases j
    simp
    suffices  (fun x ↦ 1) ⬝ᵥ x = ∑ i, 1 * x i by
        rw [this]
        congr
        ext i
        symm
        simp
    rfl
    simp
    suffices  (fun x ↦ (1 : R)) ⬝ᵥ (fun x => 1) = ∑ i : Fin m, 1 * 1 by
        rw [this]
        simp
    rfl

theorem matrix_proj_in_subspace {m : ℕ} {R : Type*} [RCLike R] (x : Fin m → R)
    (Y : Matrix (Fin m) (Fin 1) R) :
  (WithLp.toLp 2 fun i ↦ (A x).mulᵣ (((A xᵀ.mulᵣ (A x))⁻¹.mulᵣ (A xᵀ)).mulᵣ Y) i 0) ∈ K₁ x := by
  apply Submodule.mem_span_pair.mpr
  let α := ((A x)ᵀ * (A x))⁻¹ * (A x)ᵀ * Y
  use α 0 0, α 1 0
  unfold α
  have h₁' : ((A x)ᵀ) * (A x) = !![∑ i : Fin m, x i ^ 2, ∑ i : Fin m, x i;
                               ∑ i : Fin m, x i,                    m] := by
    unfold A
    rw [Matrix.transpose_transpose]
    rw [← matmulcase]
    symm
    exact Matrix.mulᵣ_eq ![x, fun x ↦ 1] (![x, fun x ↦ 1]ᵀ)
  rw [h₁']
  rw [getDet]
  conv =>
    left; left; left
    change  ((((∑ i, x i ^ 2) * (m : R) - (∑ i, x i) ^ 2)⁻¹) • !![↑m, -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2] * Matrix.of ![x, fun x ↦ 1] * Y) 0 0
  conv =>
    left; right; left
    change  ((((∑ i, x i ^ 2) * (m : R) - (∑ i, x i) ^ 2)⁻¹) • !![↑m, -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2] * Matrix.of ![x, fun x ↦ 1] * Y) 1 0
  simp only [Matrix.smul_mul]
  sorry
  -- rw [getx]
  -- simp only [A, Matrix.mulᵣ_eq]
  -- conv =>
  --   right
  --   change fun i ↦ (![x, fun x ↦ 1]ᵀ * ((Matrix.of ![x, fun x : Fin m ↦ (1 : R)] * ![x, fun x : Fin m ↦ (1 : R)]ᵀ)⁻¹ * Matrix.of ![x, fun x ↦ 1] * Y)) i 0
  -- ext i
  -- apply funext_iff.mp
  -- apply funext_iff.mp
  -- rw [A, Matrix.transpose_transpose] at h₁'
  -- conv at h₁' =>
  --   change Matrix.of ![x, fun x ↦ 1] * ![x, fun x ↦ 1]ᵀ = !![∑ i, x i ^ 2, ∑ i, x i; ∑ i, x i, ↑m]
  -- rw [h₁']
  -- rw [getDet]
  -- generalize ((∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2)⁻¹ = c
  -- generalize !![↑m, -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2] = d
  -- generalize ![x, fun x ↦ 1] = e
  -- show c • (eᵀ * (d * Matrix.of e * Y)) = eᵀ * (c • d * Matrix.of e * Y)
  -- simp

lemma matrix_algebra {n t o w : ℕ} {R : Type*} [RCLike R]
    (B : Matrix (Fin n) (Fin t) R)
    (hB : IsUnit (Bᵀ * B).det)
    (m : Fin t → Fin o → R)
    (P : Matrix (Fin n) (Fin w) R) :
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

/-- This does not hold over ℂ. -/
theorem star_projection_is_matrix_product {m : ℕ} {R : Type*} [RCLike R] [TrivialStar R] {x : Fin m → R}
    (y : Fin m → R)
    (hB : IsUnit ((A x)ᵀ * (A x)).det) :
  (fun i => Matrix.mulᵣ (A x) (
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A x)ᵀ) (A x))⁻¹ ((A x)ᵀ))
  (fun (j : Fin m) (_ : Fin 1) => y j)
  ) i 0) = Submodule.starProjection (K₁ x) (WithLp.toLp 2 y) := by
  symm
  rw [Submodule.eq_starProjection_of_mem_of_inner_eq_zero]
  sorry
  · apply @matrix_proj_in_subspace

    sorry
  intro z hz
  simp [K₁] at hz
  obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hz
  rw [← h]
  unfold A
  have : (a • x + b • fun (x : Fin m) ↦ (1 : R)) =
    fun i => Matrix.mulᵣ (A x) ![![a], ![b]] i 0 := by
    unfold A
    generalize (fun x : Fin m ↦ (1 : R)) = V
    have := ![x,V]ᵀ
    have (i : Fin m) : Matrix.mulᵣ (![x,V]ᵀ) (!![a;b]) i 0 = (a • x + b • V) i := by
        unfold Matrix.transpose Matrix.mulᵣ
        simp
        rw [mul_comm]
        nth_rw 2 [mul_comm]
    ext i
    rw [← this i]
    simp
    rfl
  sorry
  -- rw [this]
  -- rw [inner_sub_left]
  -- have {m : ℕ} (y z : EuclideanSpace R (Fin m)) : inner R y z =
  --       Matrix.mulᵣ (fun _ i => z i) (fun i _ => (starRingEnd R) (y i)) (0 : Fin 1) (0 : Fin 1) := by
  --       simp [inner, Matrix.mulᵣ, dotProduct]
  -- repeat rw [this]
  -- have h {m : ℕ} (xx : Matrix (Fin m) (Fin 1) R) :
  --       (fun _ i => xx i 0) = xxᵀ ∧
  --       (fun i _ => xx i 0) = xx := by
  --       constructor
  --       ext i j; fin_cases i; simp
  --       ext i j; fin_cases j; simp
  -- rw [(h _).1]
  -- generalize ![![a],![b]] = M
  -- simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulᵣ_eq, Matrix.transpose_mul, --conj_trivial,
  --   Fin.isValue, Matrix.transpose_transpose]
  -- rw [sub_eq_zero_of_eq]
  -- apply funext_iff.mp; apply funext_iff.mp
  -- have := @matrix_algebra m 2 1 1 R _ (A x) hB M
  -- rw [this]
  -- rw [Matrix.mul_assoc]
  -- nth_rw 2 [Matrix.mul_assoc]
  -- congr
  -- symm
  -- unfold A
  -- simp only [Fin.isValue, Matrix.transpose_transpose]
  -- simp only [conj_trivial]
  -- congr

theorem getCoeffs_eq_regression_coordinates₁ {m : ℕ} (x y : Fin m → ℝ) (i : Fin 2)
    (hl : LinearIndependent ℝ (Kvec₁ x))
    (hB : IsUnit ((A x)ᵀ * (A x)).det) :
    getCoeffs x y i 0 = regression_coordinates₁ x y hl i := by
  unfold getCoeffs regression_coordinates₁
  sorry
  -- simp_rw [← star_projection_is_matrix_product y hB]
  -- simp only [K₁, Kvec₁, Module.Basis.mk_repr]
  -- have := @LinearIndependent.repr_eq (hv := hl)
  -- let l : Fin 2 →₀ ℝ := {
  --   toFun := fun i =>
  --       (((A x)ᵀ.mulᵣ (A x))⁻¹.mulᵣ ((A x)ᵀ)).mulᵣ (Matrix.of fun a (z : Fin 1) => y a) i 0
  --   support := { i | (((A x)ᵀ.mulᵣ (A x))⁻¹.mulᵣ ((A x)ᵀ)).mulᵣ (Matrix.of fun a (z : Fin 1) => y a) i 0 ≠ 0}
  --   mem_support_toFun := by simp
  -- }
  -- rw [LinearIndependent.repr_eq (l := l)]
  -- · simp [A, l];rfl
  -- refine Subtype.coe_eq_of_eq_mk ?_
  -- rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_filter]
  -- unfold l
  -- simp only [Fin.isValue, ne_eq, Finsupp.coe_mk,
  --   ite_not, Fin.sum_univ_two, Matrix.cons_val_zero, SetLike.mk_smul_mk, Matrix.cons_val_one,
  --   Matrix.cons_val_fin_one, Submodule.coe_add]
  -- conv =>
  --   right
  --   change fun i ↦ (A x).mulᵣ (((A xᵀ.mulᵣ (A x))⁻¹.mulᵣ (A xᵀ)).mulᵣ (Matrix.of fun a z ↦ y a)) i 0

  -- generalize (((A xᵀ.mulᵣ (A x))⁻¹.mulᵣ (A xᵀ)).mulᵣ  (Matrix.of fun a z ↦ y a)) = Q

  -- unfold A
  -- have : Q = Matrix.of ![Q 0, Q 1] := by ext i j;fin_cases j;fin_cases i <;> simp
  -- rw [this]
  -- generalize Q 0 = Q₀
  -- generalize Q 1 = Q₁
  -- rw [Matrix.mulᵣ]
  -- simp
  -- split_ifs with g₀ g₁ g₂
  -- · simp at g₀
  --   simp at g₁
  --   simp
  --   rw [g₀, g₁]
  --   simp
  --   ext i
  --   simp
  -- · rw [g₀]
  --   simp
  --   ext i
  --   simp
  -- · simp
  --   rw [g₂]
  --   simp
  --   ext i
  --   simp
  --   rw [mul_comm]
  -- · simp
  --   ext i
  --   simp
  --   rw [mul_comm]




/-
From `Statistics for Calculus Students` (`s4cs`)
-/

/-- The coordinates "y hat" or `y^`. -/
noncomputable def hat {m : ℕ} (x y : Fin m → ℝ) (h : LinearIndependent ℝ (Kvec₁ x)) : Fin m → ℝ := by
  intro i
  let c := regression_coordinates₁ x y h
  exact c 0 * x i + c 1

/-- The value "y bar". -/
noncomputable def bar {m : ℕ} (y : Fin m → ℝ) : ℝ :=
    (1 / m) * ∑ i : Fin m, y i


def nonconstant {m : ℕ} (x : Fin m → ℝ) := ∃ i, ∃ j, x i ≠ x j

lemma indep_of_nonconstant {m : ℕ} {x : Fin m → ℝ} (h : nonconstant x) :
    LinearIndependent ℝ (Kvec₁ x) := by
  apply LinearIndependent.pair_iff.mpr
  contrapose! h
  obtain ⟨s,t,hst⟩ := h
  unfold nonconstant
  push_neg
  by_cases hm : m = 0
  · subst hm
    intro i j
    have := i.2
    simp at this
  obtain ⟨n,hn⟩ : ∃ n : ℕ, m = n.succ := Nat.exists_eq_succ_of_ne_zero hm
  subst hn
  simp at hst
  have hstx (j) : s * x j + t * 1 = 0 := sorry --congrFun hst.1 j
  by_cases hs : s = 0
  · have ht : t ≠ 0 := by tauto
    subst hs
    simp at hstx
    tauto
  · have : ∀ i, x i = - t / s := by
        intro i
        have := hstx i
        simp at this
        grind
    intro i j
    rw [this i, this j]


lemma isunit_of_nonconstant {m : ℕ} (x : Fin m → ℝ)
    (hx : (∑ i, (x i ^ 2)) * ↑m - (∑ i, x i) ^ 2 ≠ 0) :
    IsUnit (A xᵀ * A x).det := by
  unfold A
  rw [Matrix.transpose_transpose]
  rw [← Matrix.mulᵣ_eq]
  rw [matmulcase]
  simp
  contrapose! hx
  linarith



lemma sum_of_constant' {m : ℕ} (x : Fin m → ℝ) (h : nonconstant x) :
    (∑ (f ∈ {j : Fin 2 → Fin m | j 0 ≠ j 1 }),
    (x (f 0) - x (f 1)) ^ 2) ≠ 0 := by -- OH BUT ALL THE DIAGONAL STUFF IS UNNECESSARY?
  contrapose! h
  unfold nonconstant
  push_neg
  intro i j
  by_cases H : i = j
  · rw [H]
  · let f : Fin 2 → Fin m := ![i, j]
    suffices (x i - x j)^2 = 0 by
        simp at this
        linarith
    apply le_antisymm
    · calc _ ≤ ∑ f : Fin 2 → Fin m with f 0 ≠ f 1, (x (f 0) - x (f 1)) ^ 2 := by
            have hu : Finset.filter (fun f : Fin 2 → Fin m => f 0 ≠ f 1) (Finset.univ)
              = Finset.filter (fun f : Fin 2 → Fin m => f 0 ≠ f 1 ∧ f = ![i,j]) (Finset.univ)
              ∪ Finset.filter (fun f : Fin 2 → Fin m => f 0 ≠ f 1 ∧ f ≠ ![i,j]) (Finset.univ)
                := by ext;simp;tauto
            rw [hu]
            rw [Finset.sum_union]
            · simp
              have : ∑ x_1 with x_1 0 ≠ x_1 1 ∧ x_1 = ![i, j], (x (x_1 0) - x (x_1 1)) ^ 2
                = (x i - x j)^2 := by
                    calc _ = ∑ x_1 with x_1 = ![i, j], (x (x_1 0) - x (x_1 1)) ^ 2 := by
                            congr
                            ext l
                            simp
                            intro hl
                            rw [hl]
                            simp
                            tauto
                         _ = _ := by
                                calc _ = ∑ x_1 with x_1 = ![i, j], (x (![i, j] 0) - x (![i, j] 1)) ^ 2 := by
                                        apply le_antisymm <;>
                                        · refine Finset.sum_le_sum ?_
                                          intro l hl
                                          simp at hl
                                          rw [hl]
                                     _ = (x (![i, j] 0) - x (![i, j] 1)) ^ 2 := by
                                            simp
                                            have : Finset.filter (fun x_1 => x_1 = ![i,j]) Finset.univ = {![i,j]} := by
                                                ext
                                                simp
                                            rw [this]
                                            simp
                                     _ = _ := by simp
              rw [this]
              suffices 0 ≤ ∑ x_1 with ¬x_1 0 = x_1 1 ∧ ¬x_1 = ![i, j], (x (x_1 0) - x (x_1 1)) ^ 2 by
                linarith
              refine Finset.sum_nonneg ?_
              intro k _
              positivity
            · refine Finset.disjoint_filter.mpr ?_
              tauto
           _ ≤ _ := by rw [h]
    · positivity

open Classical
/-- A "missing lemma" in Mathlib? -/
lemma Finset.sum_iUnion {k : ℕ} {T : Type*} [Fintype T]
    (A : Fin k → Finset T) (X : T → ℝ)
    (h : Finset.univ.toSet.PairwiseDisjoint A) :
    ∑ i : T with i ∈ (⋃ j, A j), X i = ∑ j, ∑ i with i ∈ A j, X i := by
    have := @Finset.sum_biUnion T (Fin k) ℝ _ (fun i => X i)
        _ Finset.univ A h
    simp at this
    have h₀ : ∑ j, ∑ i with i ∈ A j, X i
        = ∑ j, ∑ i ∈ A j, X i := by simp only [Finset.filter_univ_mem]
    rw [h₀]
    rw [← this]
    congr
    ext i
    simp

lemma decompose_pair_sum {n : ℕ} (f : Fin n → ℝ) :  ∑ x : Fin 2 → Fin n, f (x 0)
                                             = ∑ i, ∑ g : Fin 2 → Fin n with g 0 = i, f (g 0) := by
    let A : Fin n → Finset (Fin 2 → Fin n) := by
        intro j
        exact Finset.filter (fun f => f 0 = j) Finset.univ
    have := @Finset.sum_iUnion n (Fin 2 → Fin n) _ A (fun σ => f (σ 0))
        (by
            simp [A]
            apply Set.pairwiseDisjoint_filter)
    unfold A at this
    have h₀ : ⋃ j, (Finset.filter (fun i : Fin 2 → Fin n => i 0 = j) Finset.univ).toSet = Set.univ := by
        ext
        simp
    rw [h₀] at this
    simp at this
    exact this


lemma diagonalSq {m : ℕ} (x : Fin m → ℝ)
  (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1, x (x_2 0) ^ 2 = ∑ i, x i ^ 2 := by

    have := @Finset.sum_bijective ({σ : Fin 2 → Fin m // σ 1 = x_1}) (Fin m) ℝ _ Finset.univ Finset.univ
        (fun σ => x (σ.1 0)^2) (fun i => x i^2) (fun σ => σ.1 0) (by
            constructor
            intro σ τ h
            simp at h
            ext i
            fin_cases i
            simp
            rw [h]
            simp
            rw [σ.2, τ.2]
            intro z
            use ⟨![z,x_1], by simp⟩
            simp) (by simp) (by simp)
    simp at this
    rw [← this]
    show
     (@Finset.sum (Fin 2 → Fin m)                    ℝ _ {x_2 | x_2 1 = x_1} fun x_2 ↦ x (x_2 0) ^ 2) =
      @Finset.sum { σ : Fin 2 → Fin m // σ 1 = x_1 } ℝ _ Finset.univ        (fun x_2 => x (x_2.1 0) ^ 2)
    rw [Finset.sum_subtype]
    intro σ
    simp

lemma sum_ij_xi2 {m : ℕ} (x : Fin m → ℝ) :
        ∑ σ : Fin 2 → Fin m, (x (σ 0) ^ 2) =
    m * ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 0) * x (σ 1)
     := by
  have : ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 1)
       = ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 0) := by
    repeat rw [Finset.sum_filter]
    congr
    ext i
    split_ifs with g₀
    · rw [g₀]
    · rfl
  rw [this]
  have :  ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 0)
    =  ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) ^2 := by
        congr
        ring_nf
  rw [this]
  have hf := @Finset.sum_iUnion m (Fin 2 → Fin m) _
    (fun j : Fin m => Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 1 = j ∧ x_1 0 = j) Finset.univ)
    (fun x_1 => x (x_1 0)^2) (by
        refine Finset.pairwiseDisjoint_iff.mpr ?_
        intro i _ j _ h₀

        have : ∃ x_1 : Fin 2 → Fin m, x_1 ∈ ({x_1 | x_1 1 = i ∧ x_1 0 = i} ∩ {x_1 | x_1 1 = j ∧ x_1 0 = j}) := by
            refine Set.inter_nonempty_iff_exists_left.mp ?_
            refine Set.toFinset_nonempty.mp ?_
            simp
            exact h₀
        obtain ⟨k,hk⟩ := this
        simp at hk
        apply Eq.trans hk.1.1.symm
        tauto)
  simp at hf
  rw [hf]
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_2 0) ^ 2
    = ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 := by
    apply le_antisymm <;> (
    apply Finset.sum_le_sum
    intro i hi
    simp at hi
    rw [← hi.2])
  simp_rw [this]
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2
    =  ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 * 1 := by simp
  simp_rw [this]
  have (x_1 : Fin m) :
    ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 * 1
    = x (x_1) ^ 2 * ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, 1
    := by rw [Finset.mul_sum]
  simp_rw [this]
  simp
  have (i : Fin m) : @Finset.card (Fin 2 → Fin m) {σ | σ 1 = i ∧ σ 0 = i}
   = 1 := by
   have : Finset.filter (fun σ : Fin 2 → Fin m => σ 1 = i ∧ σ 0 = i) Finset.univ = {![i,i]} := by
    ext σ
    simp
    constructor
    intro hσ
    ext j
    fin_cases j <;> tauto
    intro hσ
    rw [hσ]
    simp
   rw [this]
   simp
  simp_rw [this]
  simp
  have : ∑ x_1 : Fin 2 → Fin m, x (x_1 0) ^2
   = ∑ x_1 : Fin 2 → Fin m with ∃ j, x_1 1 = j, x (x_1 0) ^2 := by
    repeat rw [Finset.sum_filter]
    congr
    ext i
    split_ifs with g₀
    · rfl
    · exfalso;apply g₀;use i 1
  rw [this]

  have : ∑ x_1 : Fin 2 → Fin m with ∃ j, x_1 1 = j, x (x_1 0) ^2
    = ∑ x_1 with x_1 ∈ (⋃ j, {x_1 : Fin 2 → Fin m | x_1 1 = j}), x (x_1 0) ^2 := by
    repeat rw [Finset.sum_filter]
    simp
  rw [this]

  have hf := @Finset.sum_iUnion m (Fin 2 → Fin m) _
    (fun j : Fin m => Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 1 = j) Finset.univ)
    (fun x_1 => x (x_1 0)^2) (by
        refine Finset.pairwiseDisjoint_iff.mpr ?_
        intro i _ j _ h₀

        have : ∃ x_1 : Fin 2 → Fin m, x_1 ∈ ({x_1 | x_1 1 = i} ∩ {x_1 | x_1 1 = j}) := by
            refine Set.inter_nonempty_iff_exists_left.mp ?_
            refine Set.toFinset_nonempty.mp ?_
            simp
            exact h₀
        obtain ⟨k,hk⟩ := this
        simp at hk
        apply Eq.trans hk.1.symm
        tauto)
  have := @Finset.sum_biUnion (Fin 2 → Fin m) (Fin m) ℝ _ (fun x_1 => x (x_1 0) ^ 2)
    _ Finset.univ (fun j => {x_1 | x_1 1 = j}) (by apply Set.pairwiseDisjoint_filter)
  simp at this
  suffices  m * ∑ x_1, x x_1 ^ 2 = ∑ x_1 ∈ Finset.univ.biUnion fun j ↦ {x_1 : Fin 2 → Fin m | x_1 1 = j}, x (x_1 0) ^ 2 by
    rw [this]
    congr
    simp
    ext i
    simp
  rw [this]
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1, x (x_2 0) ^ 2
                     = ∑ i : Fin m, x (i) ^ 2 := by
    apply diagonalSq
  simp_rw [this]
  generalize  ∑ x_1, x x_1 ^ 2 = X
  simp


lemma offDiagonalSq {m : ℕ} (x : Fin m → ℝ) :
    (∑ (f : Fin 2 → Fin m) with f 0 ≠ f 1, x (f 1) ^ 2) =
    (m - 1) * ∑ i : Fin m, x i ^ 2 := by
  have h₀ := @sum_ij_xi2 m x
  have h₁ : ∑ σ : Fin 2 → Fin m, x (σ 1) ^ 2 =
         ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 1) ^ 2
       + ∑ σ : Fin 2 → Fin m with σ 0 ≠ σ 1, x (σ 1) ^ 2 := by
       rw [← Finset.sum_union]
       simp
       congr
       ext σ
       simp
       tauto
       apply Finset.disjoint_filter_filter_neg
  have h₂ : ∑ σ : Fin 2 → Fin m with σ 0 ≠ σ 1, x (σ 1) ^ 2
         =  ∑ σ : Fin 2 → Fin m, x (σ 1) ^ 2
         - ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 1) ^ 2 := by linarith
  rw [h₂]

  have h₅ : ∑ x_1 : Fin 2 → Fin m, x (x_1 0) ^ 2
       = ∑ x_1 : Fin 2 → Fin m, x (x_1 1) ^ 2 := by
    have := @Finset.sum_bijective (Fin 2 → Fin m) (Fin 2 → Fin m)
        ℝ _ (Finset.univ)
        (Finset.univ)
        (fun σ => x (σ 0)^2)
        (fun σ => x (σ 1)^2)
        (fun σ => ![σ 1, σ 0])
        (by
            constructor
            intro x y h
            simp at h
            ext i
            fin_cases i <;> tauto
            intro x
            use ![x 1, x 0]
            simp
            ext i
            fin_cases i <;> tauto) (by
                intro σ
                simp) (by
                intro σ
                simp)
    convert this


  have h₄ : ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 1) ^ 2 = ∑ i, x i^2 := by
    have := @Finset.sum_bijective ({σ : Fin 2 → Fin m // σ 0 = σ 1}) (Fin m) ℝ _ Finset.univ Finset.univ
        (fun σ => x (σ.1 1)^2) (fun i => x i^2) (fun σ => σ.1 0) (by
            constructor
            intro σ τ h
            simp at h
            ext i
            fin_cases i
            simp
            rw [h]
            simp
            rw [← σ.2, ← τ.2]
            rw [h]
            intro z
            use ⟨![z,z], by simp⟩
            simp) (by simp) (by simp;intro a ha;rw [ha])
    simp at this
    rw [← this]
    rw [Finset.sum_subtype]
    intro σ
    simp

  have h₃ : ∑ σ : Fin 2 → Fin m, x (σ 1) ^ 2  = m * ∑ i, x i^2 := by
    rw [← h₄]
    rw [← h₅]
    rw [h₀]
    suffices ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 0) * x (σ 1) =  ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 1) ^ 2 by
        rw [this]
    apply le_antisymm <;> (
    apply Finset.sum_le_sum
    intro i hi
    simp at hi
    rw [hi]
    ring_nf
    simp)

  linarith


lemma determinant_value_nonzero_of_nonconstant {m : ℕ} (x : Fin m → ℝ) (h : nonconstant x) :
  (∑ i, (x i ^ 2)) * ↑m - (∑ i, x i) ^ 2 ≠ 0 := by
  contrapose! h
  rw [Fintype.sum_pow] at h
  simp at h
  have : (Finset.univ : Finset (Fin 2 → Fin m)) =
      Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 0 = x_1 1) Finset.univ
    ∪ Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 0 ≠ x_1 1) Finset.univ := by
    ext;simp;tauto
  have : ∑ x_1 : Fin 2 → Fin m, (x (x_1 0) * x (x_1 1))
    = ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 1)
    + ∑ x_1 : Fin 2 → Fin m with x_1 0 ≠ x_1 1, x (x_1 0) * x (x_1 1)
    := by
        nth_rw 1 [this]
        rw [Finset.sum_union]
        apply Finset.disjoint_filter_filter_neg
  rw [this] at h

  -- helper start
  have : ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 1)
       = ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 0) := by
    repeat rw [Finset.sum_filter]
    congr
    ext i
    split_ifs with g₀
    · rw [g₀]
    · rfl
  rw [this] at h
  have :  ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 0)
    =  ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) ^2 := by
        congr
        ring_nf
  rw [this] at h

  have : ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) ^2
   = ∑ x_1 : Fin 2 → Fin m with ∃ j, x_1 0 = j ∧ x_1 1 = j, x (x_1 0) ^2 := by
    repeat rw [Finset.sum_filter]
    congr
    ext i
    split_ifs with g₀ g₁ g₂
    · rw [g₀]
    · push_neg at g₁
      specialize g₁ (i 0) (rfl)
      tauto
    · exfalso;apply g₀;obtain ⟨j,hj⟩ := g₂;apply Eq.trans hj.1 hj.2.symm
    · rfl
  have : ∑ x_1 : Fin 2 → Fin m with ∃ j, x_1 0 = j ∧ x_1 1 = j, x (x_1 0) ^2
    = ∑ x_1 with x_1 ∈ (⋃ j, {x_1 : Fin 2 → Fin m | x_1 0 = j ∧ x_1 1 = j}), x (x_1 0) ^2 := by
    repeat rw [Finset.sum_filter]
    simp
  have hf := @Finset.sum_iUnion m (Fin 2 → Fin m) _
    (fun j : Fin m => Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 1 = j ∧ x_1 0 = j) Finset.univ)
    (fun x_1 => x (x_1 0)^2) (by
        refine Finset.pairwiseDisjoint_iff.mpr ?_
        intro i _ j _ h₀

        have : ∃ x_1 : Fin 2 → Fin m, x_1 ∈ ({x_1 | x_1 1 = i ∧ x_1 0 = i} ∩ {x_1 | x_1 1 = j ∧ x_1 0 = j}) := by
            refine Set.inter_nonempty_iff_exists_left.mp ?_
            refine Set.toFinset_nonempty.mp ?_
            simp
            exact h₀
        obtain ⟨k,hk⟩ := this
        simp at hk
        apply Eq.trans hk.1.1.symm
        tauto)
  simp at hf
  rw [hf] at h
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_2 0) ^ 2
    = ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 := by
    apply le_antisymm <;> (
    apply Finset.sum_le_sum
    intro i hi
    simp at hi
    rw [← hi.2])

  simp_rw [this] at h
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2
    =  ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 * 1 := by simp
  simp_rw [this] at h
  have (x_1 : Fin m) :
    ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 * 1

    = x (x_1) ^ 2 * ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, 1
    := by rw [Finset.mul_sum]
  simp_rw [this] at h
  simp at h
  have (i : Fin m) : @Finset.card (Fin 2 → Fin m) {σ | σ 1 = i ∧ σ 0 = i}
   = 1 := by
   have : Finset.filter (fun σ : Fin 2 → Fin m => σ 1 = i ∧ σ 0 = i) Finset.univ = {![i,i]} := by
    ext σ
    simp
    constructor
    intro hσ
    ext j
    fin_cases j <;> tauto
    intro hσ
    rw [hσ]
    simp
   rw [this]
   simp
  simp_rw [this] at h
  simp at h
  have h : (∑ i, x i ^ 2) * ((m:ℝ) - 1) - (∑ x_1 : Fin 2 → Fin m with ¬x_1 0 = x_1 1, x (x_1 0) * x (x_1 1)) = 0 := by
    rw [← h]
    linarith
  rw [mul_comm] at h
  suffices ∑ σ : Fin 2 → Fin m with σ 0 ≠ σ 1, (x (σ 0) - x (σ 1))^2 = 0 by
    have := @sum_of_constant' m x
    tauto
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  simp

  rw [← offDiagonalSq] at h
  rw [sub_eq_zero] at h

  have : ∑ x_1 : Fin 2 → Fin m with ¬x_1 0 = x_1 1, x (x_1 0) ^ 2
       = ∑ x_1 : Fin 2 → Fin m with ¬x_1 0 = x_1 1, x (x_1 1) ^ 2 := by
    have := @Finset.sum_bijective (Fin 2 → Fin m) (Fin 2 → Fin m)
        ℝ _ (Finset.filter (fun σ => σ 0 ≠ σ 1) Finset.univ)
        (Finset.filter (fun σ => σ 0 ≠ σ 1) Finset.univ)
        (fun σ => x (σ 0)^2)
        (fun σ => x (σ 1)^2)
        (fun σ => ![σ 1, σ 0])
        (by
            constructor
            intro x y h
            simp at h
            ext i
            fin_cases i <;> tauto
            intro x
            use ![x 1, x 0]
            simp
            ext i
            fin_cases i <;> tauto) (by
                intro σ
                simp
                tauto) (by
                intro σ
                simp)
    convert this
  rw [this]
  ring_nf
  conv =>
    left
    left
    rw [mul_comm]
  have (x_1 : Fin 2 → Fin m) : x (x_1 0) * x (x_1 1) * 2
    = 2 * (x (x_1 0) * x (x_1 1)) := by ring_nf
  simp_rw [this]
  have := @Finset.mul_sum (Fin 2 → Fin m) ℝ _ (Finset.filter (fun σ => σ 0 ≠ σ 1) Finset.univ)
    (fun σ => x (σ 0) * x (σ 1)) 2
  rw [← this]
  suffices ∑ x_1 : Fin 2 → Fin m with ¬x_1 0 = x_1 1, x (x_1 1) ^ 2
         - ∑ i : Fin 2 → Fin m with i 0 ≠ i 1, x (i 0) * x (i 1) = 0
   by linarith
  rw [h]
  ring_nf



theorem average_predicted_value {m : ℕ} (x y : Fin m → ℝ) (h : nonconstant x) :
  ∑ i, y i = ∑ i, hat x y (indep_of_nonconstant h) i := by
    have hx := determinant_value_nonzero_of_nonconstant x h
    have h₀ : IsUnit (A xᵀ * A x).det := isunit_of_nonconstant _ hx
    unfold hat
    simp
    repeat rw [← getCoeffs_eq_regression_coordinates₁ _ _ _ _ h₀]
    unfold getCoeffs A

    have := @matmulcase m ℝ _ x
    rw [Matrix.transpose_transpose]
    rw [this]
    rw [getDet]

    have h₁ : (!![(m:ℝ), -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2]).mulᵣ ![x, fun x ↦ 1] =
        Matrix.of ![fun i => m * x i - ∑ j, x j, fun i => - (∑ j, x j) * x i + ∑ j, x j ^ 2 ] := by
        ext i j
        fin_cases i
        · unfold Matrix.mulᵣ
          simp
          rfl
        · unfold Matrix.mulᵣ
          simp
    -- simp
    have h₂ : (((∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2)⁻¹ • !![↑m, -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2]).mulᵣ ![x, fun x ↦ 1]
     = ((∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2)⁻¹ • (!![↑m, -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2]).mulᵣ ![x, fun x ↦ 1] := by
     generalize ((∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2)⁻¹ = c
     generalize !![↑m, -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2] = d
     generalize ![x, fun x ↦ 1] = e
     simp
    rw [h₂]
    rw [h₁]

    set c := ((∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2)⁻¹
    set d := !![↑m, -∑ i, x i; -∑ i, x i, ∑ i, x i ^ 2]
    set f := Matrix.of ![fun i ↦ ↑m * x i - ∑ j, x j, fun i ↦ (-∑ j, x j) * x i + ∑ j, x j ^ 2]
    let D (j : Fin m) :=  ((c • f).mulᵣ (fun i x ↦ y i) 0 (0:Fin 1) * x j
                       + (c • f).mulᵣ (fun i x ↦ y i) 1 (0:Fin 1))
    let E := ((c • f).mulᵣ (fun i (x:Fin 1) ↦ y i))
    let E₂ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 fun i => E i 0
    let F (j : Fin m) := inner ℝ E₂ (WithLp.toLp 2 ![x j, 1])
    suffices ∑ j, y j = ∑ j, F j by
        rw [this]
        congr
        ext j
        unfold F E₂ E
        simp [inner]
        linarith
    unfold F E₂ E
    have : (fun i ↦ (c • f).mulᵣ (fun i x ↦ y i) i (0:Fin 1))
        = c • (fun i ↦ f.mulᵣ (fun i x ↦ y i) i (0:Fin 1)) := by
        ext i
        simp
    rw [this]
    let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2
        (c • fun i ↦ f.mulᵣ (fun i x ↦ y i) i (0:Fin 1))
    let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2
        (fun i ↦ f.mulᵣ (fun i x ↦ y i) i (0:Fin 1))

    show  ∑ j, y j = ∑ j, inner ℝ v (WithLp.toLp 2 ![x j, 1])
    show  ∑ j, y j = ∑ j, inner ℝ (c • w) (WithLp.toLp 2 ![x j, 1])
    have (j : Fin m) : inner ℝ (c • w) (WithLp.toLp 2 ![x j, 1]) =
        c • inner ℝ (w) (WithLp.toLp 2 ![x j, 1]) := by
        exact inner_smul_left_eq_smul w (WithLp.toLp 2 ![x j, 1]) c
    simp_rw [this]
    suffices ∑ j, y j = c * ∑ x_1, inner ℝ w (WithLp.toLp 2 ![x x_1, 1])
        by rw [this];exact Finset.mul_sum Finset.univ (fun i ↦ inner ℝ w (WithLp.toLp 2 ![x i, 1])) c
    unfold c
    suffices (((∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2)) * ∑ j, y j = ∑ x_1, inner ℝ w (WithLp.toLp 2 ![x x_1, 1]) by
        rw [← this]
        set c := (∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2
        set d := ∑ j, y j

        refine Eq.symm (inv_mul_cancel_left₀ ?_ d)
        unfold c
        exact hx
    unfold w f
    set sx₁ := ∑ j, x j
    set sx₂ := ∑ j, x j^2
    set sy := ∑ j, y j
    simp [inner, Matrix.vecMul]
    have : (fun i ↦ ↑m * x i - sx₁)
        = (fun i ↦ ↑m * x i) - (fun _ => sx₁) := by rfl
    rw [this]
    simp_rw [dotProduct_comm]
    simp_rw [dotProduct_sub]
    have : (fun i ↦ -(sx₁ * x i) + sx₂) =
         fun i ↦ sx₂ -(sx₁ * x i) := by ext;linarith
    simp_rw [this]
    have : (fun i ↦ sx₂ -(sx₁ * x i))
        = (fun i ↦ sx₂) - (fun i => sx₁ * x i) := by rfl
    simp_rw [this]
    simp_rw [dotProduct_sub]
    rw [Finset.sum_add_distrib]
    repeat rw [Finset.sum_sub_distrib]
    have : (fun i : Fin m ↦ y i) ⬝ᵥ (fun i : Fin m ↦ sx₂)
    = sx₂ * ∑ i : Fin m, y i := by
        simp [dotProduct]
        simp_rw [mul_comm _ sx₂]
        exact Eq.symm (Finset.mul_sum Finset.univ y sx₂)
    rw [this]
    have : (fun i : Fin m ↦ y i) ⬝ᵥ (fun i : Fin m ↦ sx₁)
    = sx₁ * ∑ i : Fin m, y i := by
        simp [dotProduct]
        simp_rw [mul_comm _ sx₁]
        exact Eq.symm (Finset.mul_sum Finset.univ y sx₁)
    rw [this]
    conv =>
        right
        right
        left
        right
        change fun x => sx₂ * sy
    conv =>
        right
        left
        right
        change  fun x_1 ↦ x x_1 * (((fun i ↦ y i) ⬝ᵥ fun i ↦ ↑m * x i) - sx₁ * sy)
    have : ∑ x : Fin m, sx₂ * sy
        = sx₂ * ∑ x : Fin m, sy := by
            exact Eq.symm (Finset.mul_sum Finset.univ (fun i ↦ sy) sx₂)
    rw [this]
    have : ∑ x : Fin m, sy = ∑ x : Fin m, sy * 1 := by simp
    rw [this]
    have : ∑ x : Fin m, sy * 1 = sy * ∑ x : Fin m, 1 := by
        exact
        Eq.symm (Finset.mul_sum Finset.univ (fun i ↦ 1) sy)
    rw [this]
    have g₀ : ∑ x : Fin m, (1:ℝ) = m := by
        rw [Finset.sum_const]
        simp
    rw [g₀]
    have : ∑ x_1, x x_1 * (((fun i ↦ y i) ⬝ᵥ fun i ↦ ↑m * x i) - sx₁ * sy)
     = (((fun i ↦ y i) ⬝ᵥ fun i ↦ ↑m * x i) - sx₁ * sy) * ∑ x_1 : Fin m, x x_1 := by
        generalize (((fun i ↦ y i) ⬝ᵥ fun i ↦ ↑m * x i) - sx₁ * sy) = a
        simp_rw [mul_comm]
        exact Eq.symm (Finset.mul_sum Finset.univ x a)
    rw [this]
    conv =>
        right
        left
        right
        change sx₁
    have : ∑ x_1 : Fin m, (fun i ↦ y i) ⬝ᵥ (fun i ↦ sx₁ * x i)
        = ∑ x_1 : Fin m, (fun i ↦ y i) ⬝ᵥ (fun i ↦ sx₁ * x i) * 1 := by simp
    rw [this]
    have : ∑ x_1 : Fin m, (fun i ↦ y i) ⬝ᵥ (fun i ↦ sx₁ * x i) * 1
     = (fun i ↦ y i) ⬝ᵥ (fun i ↦ sx₁ * x i) * ∑ x_1 : Fin m, 1 := by
        exact Eq.symm (Finset.mul_sum Finset.univ (fun i ↦ 1) ((fun i ↦ y i) ⬝ᵥ fun i ↦ sx₁ * x i))
    rw [this]
    rw [g₀]
    have : (fun i : Fin m ↦ sx₁ * x i)
        = sx₁ • (fun i : Fin m ↦ x i) := by rfl
    rw [this]
    have : ((fun i ↦ y i) ⬝ᵥ sx₁ • fun i ↦ x i)
        = sx₁ * ((fun i ↦ y i) ⬝ᵥ fun i ↦ x i) := by
        simp
    rw [this]
    have : (fun i : Fin m ↦ (m:ℝ) * x i)
        = (m:ℝ) • (fun i : Fin m ↦ x i) := by rfl
    rw [this]
    have : ((fun i ↦ y i) ⬝ᵥ (m:ℝ) • fun i ↦ x i)
        = (m:ℝ) * ((fun i ↦ y i) ⬝ᵥ fun i ↦ x i) := by
        simp
    rw [this]

    set sxy := (fun i ↦ y i) ⬝ᵥ fun i ↦ x i
    linarith

/-- Sum of squares decomposition, Theorem 7.2 from `s4cs`. -/
example {m : ℕ} (x y : Fin m → ℝ)
    (h' : nonconstant x)
    (h : LinearIndependent ℝ (Kvec₁ x))
    (h₀ :  IsUnit (A xᵀ * A x).det) -- follows from h, anyway
    (hx :  (∑ i, x i ^ 2) * ↑m - (∑ i, x i) ^ 2 ≠ 0) -- also follows anyway
    :
    ∑ i, (y i - bar y) ^ 2 = ∑ i, ((hat x y h) i - bar y) ^ 2 + ∑ i, (y i - (hat x y h) i) ^ 2 := by
  repeat simp_rw [sub_sq]
  repeat rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  repeat simp_rw [mul_assoc]
  repeat rw [← Finset.mul_sum Finset.univ _ 2]
  suffices - ∑ i, y i * bar y = ∑ i, hat x y h i ^ 2 - ∑ i, hat x y h i * bar y +
    (- ∑ i, y i * hat x y h i) by linarith
  -- now take ybar outside
  simp_rw [mul_comm _ (bar y)]
  repeat rw [← Finset.mul_sum Finset.univ _ (bar y)]
  have : ∑ i, y i = ∑ i, hat x y h i := by
    apply average_predicted_value ; tauto
  rw [this]
  suffices ∑ i, y i * hat x y h i = ∑ i, hat x y h i ^ 2 by
    linarith
  unfold hat
  simp
  repeat rw [← getCoeffs_eq_regression_coordinates₁ _ _ _ _ h₀]
  set b₁ := getCoeffs x y 0 0
  set b₀ := getCoeffs x y 1 0
  show ∑ i, y i * (b₁ * x i + b₀) = ∑ i, (b₁ * x i + b₀) ^ 2
  simp_rw [add_sq]
  repeat rw [Finset.sum_add_distrib]
  -- but this is tedious!
  -- then move b₀, b₁ around
  set sx := ∑ i, x i
  set sy := ∑ i, y i
  set sx₂ := ∑ i, x i ^ 2
  set sxy := ∑ i, x i * y i
  have : b₀ = sy * (sx₂ - sxy) / (m * sx₂ - sx ^ 2) := sorry
  rw [this]
  have : b₁ = (m * sxy - sx * sy) / (m * sx₂ - sx ^ 2) := by sorry
  rw [this]

  field_simp
  sorry












/-
# Material specific to the case of 3 points
-/

def A₃ (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![
  x 0, 1;
  x 1, 1;
  x 2, 1
]

noncomputable def getCoeffs₃ (x y : Fin 3 → ℝ) :=
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A₃ x)ᵀ) (A₃ x))⁻¹ ((A₃ x)ᵀ))
  !![y 0; y 1; y 2]

lemma getx₃ (x : Fin 3 → ℝ) (c : ℝ) (e : Matrix (Fin 2) (Fin 1) ℝ) :
    ((c • e) 0 0 • x + (c • e) 1 0 • fun (_ : Fin 3) ↦ (1:ℝ)) =
    fun i ↦ (c • (!![x 0, 1; x 1, 1; x 2, 1] * e)) i 0 := by
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

theorem matrix_proj_in_subspace₃ (x : Fin 3 → ℝ) (Y : Matrix (Fin 3) (Fin 1) ℝ) :
  WithLp.toLp 2 (fun i ↦ (A₃ x).mulᵣ (((A₃ xᵀ.mulᵣ (A₃ x))⁻¹.mulᵣ (A₃ xᵀ)).mulᵣ Y) i 0) ∈ K₁ x := by
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
  sorry -- apply getx₃

theorem star_projection_is_matrix_product₃ {x : Fin 3 → ℝ}
    (y : Fin 3 → ℝ)
    (hB : IsUnit (!![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1]).det) :
    -- this just says ¬ (x 0 = x 1 ∧ x 0 = x 2)
  (fun i => Matrix.mulᵣ (A₃ x) (
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A₃ x)ᵀ) (A₃ x))⁻¹ ((A₃ x)ᵀ))
  !![y 0; y 1; y 2]) i 0) = Submodule.starProjection (K₁ x) (WithLp.toLp 2 y) := by
  sorry
  -- have : !![y 0; y 1; y 2] = fun i x ↦ y i := by
  --   ext i j; fin_cases i <;> simp;
  -- rw [this]
  -- symm
  -- rw [Submodule.eq_starProjection_of_mem_of_inner_eq_zero]
  -- · sorry -- apply matrix_proj_in_subspace₃
  -- intro z hz
  -- sorry


  -- simp [K₁] at hz
  -- obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hz
  -- rw [← h]
  -- unfold A₃
  -- have : (a • x + b • fun (x : Fin 3) ↦ (1:ℝ)) =
  --   fun i => Matrix.mulᵣ !![x 0, 1; x 1, 1; x 2, 1] ![![a], ![b]] i 0 := by
  --   ext i;fin_cases i <;> (simp [Matrix.vecMul];linarith)
  -- rw [this]
  -- generalize !![x 0, 1; x 1, 1; x 2, 1] = B at *
  -- rw [inner_sub_left]
  -- have {m : ℕ} (y z : EuclideanSpace ℝ (Fin m)) : inner ℝ y z =
  --     Matrix.mulᵣ (fun _ i => z i) (fun i _ => y i) (0 : Fin 1) (0 : Fin 1) := by
  --   simp [inner, Matrix.mulᵣ, dotProduct]
  -- repeat rw [this]
  -- have h {m : ℕ} (xx : Matrix (Fin m) (Fin 1) ℝ) :
  --   (fun _ i => xx i 0) = xxᵀ ∧
  --   (fun i _ => xx i 0) = xx := by
  --   constructor
  --   ext i j; fin_cases i; simp
  --   ext i j; fin_cases j; simp
  -- rw [(h _).1, (h _).2]
  -- generalize ![![a],![b]] = m
  -- simp
  -- rw [sub_eq_zero_of_eq]
  -- apply funext_iff.mp; apply funext_iff.mp
  -- apply matrix_algebra _ hB

theorem getCoeffs₃_eq_regression_coordinates₁ (x y i)
    (hl : LinearIndependent ℝ (Kvec₁ x))
    (hB : IsUnit (!![x 0, 1; x 1, 1; x 2, 1]ᵀ * !![x 0, 1; x 1, 1; x 2, 1]).det) :
    getCoeffs₃ x y i 0 = regression_coordinates₁ x y hl i := by
  unfold getCoeffs₃ regression_coordinates₁
  sorry
  -- simp_rw [← star_projection_is_matrix_product₃ y hB]
  -- simp only [K₁, A₃, Kvec₁, Module.Basis.mk_repr]
  -- rw [LinearIndependent.repr_eq
  --   ( l:= {
  --       toFun := fun i => ((!![x 0, 1; x 1, 1; x 2, 1]ᵀ.mulᵣ !![x 0, 1; x 1, 1; x 2, 1])⁻¹.mulᵣ (!![x 0, 1; x 1, 1; x 2, 1]ᵀ)).mulᵣ
  --           !![y 0; y 1; y 2] i 0
  --       support := {a | ((!![x 0, 1; x 1, 1; x 2, 1]ᵀ.mulᵣ !![x 0, 1; x 1, 1; x 2, 1])⁻¹.mulᵣ (!![x 0, 1; x 1, 1; x 2, 1]ᵀ)).mulᵣ
  --        !![y 0; y 1; y 2] a 0 ≠
  --           0}
  --       mem_support_toFun := by simp
  --   })
  -- ]
  -- · simp
  -- refine Subtype.coe_eq_of_eq_mk ?_
  -- rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_filter]
  -- ext i;fin_cases i <;> (
  --   simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
  --   split_ifs with g₀ g₁ g₂ <;> (
  --       try rw [g₀]
  --       try rw [g₁]
  --       try rw [g₂]
  --       try simp
  --       try rw [mul_comm]))

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


/-

#Specific material
-/

/-- Multivariate regression. -/
noncomputable def K₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) := @Submodule.span ℝ (EuclideanSpace ℝ (Fin n)) _ _ _
    {WithLp.toLp 2 x₀, WithLp.toLp 2 x₁, WithLp.toLp 2 fun _ => 1}
theorem hxK₂₀ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : WithLp.toLp 2 x₀ ∈ K₂ x₀ x₁ := Submodule.mem_span_of_mem (Set.mem_insert (WithLp.toLp 2 x₀) _)
theorem hxK₂₁ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : WithLp.toLp 2 x₁ ∈ K₂ x₀ x₁ := Submodule.mem_span_of_mem (by simp)
theorem h1K₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : WithLp.toLp 2 (fun _ ↦ 1) ∈ K₂ x₀ x₁ := Submodule.mem_span_of_mem (by simp)
theorem topsub₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) :
    ⊤ ≤ Submodule.span ℝ (Set.range ![
      (⟨WithLp.toLp 2 x₀, hxK₂₀ x₀ x₁⟩ : K₂ x₀ x₁),
      (⟨WithLp.toLp 2 x₁, hxK₂₁ x₀ x₁⟩ : K₂ x₀ x₁),
      (⟨WithLp.toLp 2 fun _ => 1, h1K₂ x₀ x₁⟩ : K₂ x₀ x₁)]) := by
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
def Kvec₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) := ![
  (⟨WithLp.toLp 2 x₀, hxK₂₀ x₀ x₁⟩ : K₂ x₀ x₁),
  (⟨WithLp.toLp 2 x₁, hxK₂₁ x₀ x₁⟩ : K₂ x₀ x₁),
  (⟨WithLp.toLp 2 fun _ => 1, h1K₂ x₀ x₁⟩ : K₂ x₀ x₁)]

noncomputable def regression_coordinates₂ {n : ℕ} (x₀ x₁ y : Fin n → ℝ)
    (lin_indep : LinearIndependent ℝ (Kvec₂ x₀ x₁)) :
    Fin 3 → ℝ := fun i => ((Module.Basis.mk lin_indep (topsub₂ _ _)).repr
      ⟨Submodule.starProjection (K₂ x₀ x₁) (WithLp.toLp 2 y),
       Submodule.starProjection_apply_mem (K₂ x₀ x₁) (WithLp.toLp 2 y)⟩) i


lemma indep₀₁₂ : LinearIndependent ℝ (Kvec₁ ![(0 : ℝ), 1, 2]) := by
    simp [Kvec₁]
    apply LinearIndependent.pair_iff.mpr
    intro s t h
    simp at h
    have : ![s * 0, s * 1, s * 2] + ![t * 1, t * 1, t * 1] = 0 := by
      sorry
      -- rw [← h]
      -- congr <;> (ext i; fin_cases i <;> simp)
    simp at this
    have := this.1
    subst this
    simp at this
    tauto

lemma hvo₀₁₁ (w : EuclideanSpace ℝ (Fin 3))
    (hw : w ∈ K₁ ![0, 1, 2]) : inner ℝ (WithLp.toLp 2 ![0, 1, 1] - WithLp.toLp 2 ![1 / 6, 4 / 6, 7 / 6]) w = 0 := by
  obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hw
  rw [← h]
  simp [inner]
  rw [Fin.sum_univ_three]
  -- repeat rw [Pi.sub_apply]
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
example : regression_coordinates₁ ![(0 : ℝ),1,2] ![0,1,1] indep₀₁₂
  = ![1/2,1/6] := by
  unfold regression_coordinates₁
  simp
  have hvm : WithLp.toLp 2 ![1 / 6, 4 / 6, 7 / 6] ∈ K₁ ![(0 : ℝ), 1, 2] := by
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










example : Unit := by
    have := @MeasureTheory.condExpL1CLM (Fin 2)
        ℝ _ _ _ {
            MeasurableSet' := by intro S; exact S = ∅ ∨ S = Set.univ
            measurableSet_compl := by
                intro s hs
                rcases hs with (h | h)
                · subst h
                  right
                  simp
                · subst h
                  left
                  simp
            measurableSet_empty := by simp
            measurableSet_iUnion := by
              intro f hf
              by_cases H : ∃ i, f i = Set.univ
              · right
                obtain ⟨j,hj⟩ := H
                apply subset_antisymm
                simp
                intro x _
                simp
                use j
                rw [hj]
                simp
              · push_neg at H
                have : ∀ i, f i = ∅ := by
                    intro i
                    specialize H i
                    specialize hf i
                    tauto
                left
                simp_rw [this]
                simp
        } {
            MeasurableSet' := ⊤
            measurableSet_compl  := by trivial
            measurableSet_empty := by simp
            measurableSet_iUnion := by
                intro f h
                trivial
        } (by exact fun s a ↦ trivial)
        {
            measureOf := by intro S; exact (ite (0 ∈ S) 1 0)
            empty := by simp
            mono := by
                intro s₁ s₂ h
                split_ifs <;> simp;tauto
            iUnion_nat := by
              intro s hs
              split_ifs with g₀
              simp at g₀
              obtain ⟨i,hi⟩ := g₀
              have : (if 0 ∈ s i then (1 : ENNReal) else 0) = 1 := by
                rw [if_pos hi]
              -- norm_num
              nth_rw 1 [← this]
              exact ENNReal.le_tsum i
              positivity
            m_iUnion := by
              intro f hf hp
              sorry
            trim_le := by
              sorry
        } (by sorry) ({
            val := by
                refine MeasureTheory.AEEqFun.mk ?_ ?_
                intro x
                exact (x.1 : ℝ)
                exact MeasureTheory.AEStronglyMeasurable.of_discrete
            property := by sorry
        })
    sorry
