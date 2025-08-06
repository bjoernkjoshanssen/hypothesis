import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear regression
-/

noncomputable def K {n : ℕ} (x : Fin n → ℝ) := @Submodule.span ℝ (EuclideanSpace ℝ (Fin n)) _ _ _
    {x, fun _ => 1}

theorem hxK {n : ℕ} (x : Fin n → ℝ) : x ∈ K x := Submodule.mem_span_of_mem (Set.mem_insert x {fun _ ↦ 1})

theorem h1K {n : ℕ} (x : Fin n → ℝ) : (fun _ ↦ 1) ∈ K x := Submodule.mem_span_of_mem (Set.mem_insert_of_mem x rfl)

theorem topsub {n : ℕ} (x : Fin n → ℝ) :
    ⊤ ≤ Submodule.span ℝ (Set.range ![(⟨x, hxK x⟩ : K x), (⟨fun _ => 1, h1K x⟩ : K x)]) := by
  simp [K]
  apply Submodule.eq_top_iff'.mpr
  simp
  intro a ha
  apply Submodule.mem_span_pair.mpr
  obtain ⟨c,d,hcd⟩ := Submodule.mem_span_pair.mp ha
  use d, c
  simp
  rw [← hcd]
  rw [add_comm]

def Kvec {n : ℕ} (x : Fin n → ℝ) := ![(⟨x, hxK x⟩ : K x), (⟨fun _ => 1, h1K x⟩ : K x)]

/-- Given points `(x i, y i)`, obtain the coordinates `[c, d]` such that
`y = c x + d` is the best fit regression line. -/
noncomputable def regression_coordinates {n : ℕ} (x y : Fin n → ℝ)
    (lin_indep : LinearIndependent ℝ (Kvec x)) :
    Fin 2 → ℝ := fun i => ((Module.Basis.mk lin_indep (topsub _)).repr <| (K x).orthogonalProjection y) i

noncomputable def regression_coordinates' {n : ℕ} (x y : Fin n → ℝ)
    (lin_indep : LinearIndependent ℝ (Kvec x)) :
    Fin 2 → ℝ := by
  let zz := @Submodule.starProjection ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ (K x)
    (Submodule.HasOrthogonalProjection.ofCompleteSpace _) y
  let z := (⟨zz,
    by exact Submodule.starProjection_apply_mem (K x) y⟩ : {z : EuclideanSpace ℝ (Fin n) // z ∈ K x})
  let rc := ((Module.Basis.mk lin_indep (topsub _)).repr <| z)
  exact fun i => rc i


lemma my : LinearIndependent ℝ (Kvec ![0, 1, 2]) := by
    simp [Kvec]
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

theorem hvo (w : EuclideanSpace ℝ (Fin 3))
    (hw : w ∈ K ![0, 1, 2]) : inner ℝ (![0, 1, 1] - ![1 / 6, 4 / 6, 7 / 6]) w = 0 := by
  obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hw
  rw [← h]
  simp [inner]
  rw [Fin.sum_univ_three]
  repeat rw [Pi.sub_apply]
  simp
  grind

example : regression_coordinates' ![0,1,2] ![0,1,1] my = ![1/2,1/6] := by
  simp [regression_coordinates']
  have hvm : ![1 / 6, 4 / 6, 7 / 6] ∈ K ![0, 1, 2] := by
    refine Submodule.mem_span_pair.mpr ?_
    use 1/2, 1/6
    ext i
    fin_cases i <;> (simp; try grind)
  rw [LinearIndependent.repr_eq my (l := {
    toFun := ![2⁻¹, 6⁻¹]
    support := Finset.univ
    mem_support_toFun := by intro i;fin_cases i <;> simp
  })]
  · simp
  · apply Subtype.coe_eq_of_eq_mk
    rw [Submodule.eq_starProjection_of_mem_of_inner_eq_zero hvm hvo]
    simp [Kvec]
    ext j
    fin_cases j <;> (simp [Finsupp.linearCombination, Finsupp.sum]; try grind)
