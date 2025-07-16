import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Data.ENNReal.Basic

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

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
  apply subset_antisymm
  · intro v
    intro h
    simp
    cases h with
    | inl h' =>
      use 2
      subst h'
      rfl
    | inr h' =>
      sorry -- etc.
  · intro v
    intro h
    simp
    by_cases H₀ : v 0 = T
    · by_cases H₁ : v 1 = T
      · by_cases H₂ : v 2 = T
        · right
          right
          right
          right
          right
          right
          ext i
          fin_cases i <;>
          · simp
            assumption
        · sorry
      · sorry
    · sorry -- etc.
end exercise_1_2_4

-- inductive omega
-- | a : omega
-- | b : omega
-- | c : omega

-- def m (s : omega) : ℚ := match s with
-- | omega.a => 1/2
-- | _ => 0


-- example : ({omega.a, omega.c} : Set omega)
--   ∈ (Set.univ : Set omega).powerset := by
--   simp
-- -- #check Set omega

-- def a : Fin 3 := 0
-- def b : Fin 3 := 1
-- def c : Fin 3 := 2
-- def mm (s : Fin 3) : ℚ := match s with
-- | 0 => 1/2
-- | 1 => 1/3
-- | 2 => 1/6

open MeasureTheory ENNReal

lemma arithmetic_for_exercise_1_2_7 :
    (1:ℝ≥0∞) / 2 + 1 = 11 / 12 + 1 / 4 + 1 / 3 := by
  rw [show (11 : ℝ≥0∞) = 4+4 + 3 by norm_num, show (12 : ℝ≥0∞) = 3 * 4 by norm_num]
  repeat rw [ENNReal.add_div]
  have : 4 / (3 * 4) = 1 / (3 : ℝ≥0∞) := by
    nth_rewrite 1 [← one_mul 4]
    apply ENNReal.mul_div_mul_right 1 3 <;> simp
  rw [this]
  have : 3 / (3 * 4) = 1 / (4 : ℝ≥0∞) := by
    nth_rewrite 1 [← mul_one 3]
    apply ENNReal.mul_div_mul_left 1 4 <;> simp
  rw [this]
  simp
  rw [← inv_three_add_inv_three]
  ring_nf
  rw [add_comm]
  congr
  rw [show (4 :ENNReal) = 2 * 2 by norm_num]
  rw [ENNReal.mul_inv, mul_assoc, ENNReal.inv_mul_cancel]
  all_goals simp

/-- Exercise 1.2.7:
  Let A and B be events such that P(A ∩ B) = 1/4, P(A˜) = 1/3, and P(B) =
  1/2. What is P(A ∪ B)? -/
lemma exercise_1_2_7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [i : IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A)
    (h₀ : μ (A ∩ B) = 1/4) (h₁ : μ Aᶜ = 1/3) (h₂ : μ B = 1/2) :
    μ (A ∪ B) = 11/12 := by
  apply (add_left_inj (show μ (A ∩ B) ≠ ⊤ by simp)).mp
  rw [measure_union_add_inter' hA, h₂, h₀]
  nth_rewrite 1 [add_comm]
  apply (add_left_inj (show μ Aᶜ ≠ ⊤ by simp)).mp
  nth_rewrite 1 [add_assoc]
  rw [← measure_union' (Set.disjoint_compl_right_iff_subset.mpr (by simp)) hA]
  rw [Set.union_compl_self A, measure_univ, h₁]
  exact arithmetic_for_exercise_1_2_7

lemma exercise_1_2_6 (μ : Measure (Fin 6)) [i : IsProbabilityMeasure μ]
  (h : μ {2} = 2 * μ {1} -- Have to be careful since (6 : Fin 6) = 0.
     ∧ μ {3} = 3 * μ {1}
     ∧ μ {4} = 4 * μ {1}
     ∧ μ {5} = 5 * μ {1}
     ∧ μ {6} = 6 * μ {1}) : μ {2,4,6} = 12 / 21 := by
  have h₀ : μ {2,4,6} = 12 * μ {1} := by
    have : {2,4,6} = (({2} ∪ {4,6}) : Set (Fin 6)) := by exact rfl
    have : μ {2,4,6} = μ {2} + μ {4,6} := this ▸ measure_union (by simp) trivial
    rw [this, h.1]
    have : {4,6} = (({4} ∪ {6}) : Set (Fin 6)) := by exact rfl
    have : μ {4,6} = μ {4} + μ {6} := by
      rw [this]
      refine measure_union ?_ trivial
      simp
    rw [this]
    rw [h.2.2.1]
    rw [h.2.2.2.2]
    ring_nf
  have h₂ : μ Set.univ = (1 : ENNReal) := by simp
  have h₃ : (Set.univ : Set (Fin 6)) = {1,2,3,4,5,6} := by
    ext j
    simp
    fin_cases j <;> tauto
  have h₆ : (1:ENNReal) + 2 + 3 + 4 + 5 + 6 = 21 := by
    have h₅ : (1:Real) + 2 + 3 + 4 + 5 + 6 = 21 := by
      linarith
    refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
    simp
    simp
    exact h₅
  have h₄ : μ {1} + μ {2} + μ {3} + μ {4} + μ {5} + μ {6} = μ {1,2,3,4,5,6} := by
    have h₇ : ({1,2,3,4,5,6} : Set (Fin 6)) = {1} ∪ {2} ∪ {3} ∪ {4} ∪ {5} ∪ {6}:= by
      ext j
      fin_cases j <;> simp
    rw [h₇]
    repeat rw [measure_union]
    all_goals simp
  have h₁ : μ {1} + μ {2} + μ {3} + μ {4} + μ {5} + μ {6} = 1 := by
    rw [h₄,← h₃,h₂]
  have h₂ : μ {1} = 1/21 := by
    suffices 21 * μ {1} = 1 by
      refine (ENNReal.eq_div_iff ?_ ?_).mpr this
      simp;simp
    rw [← h₂,h₃,← h₄]
    rw [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2]
    ring_nf
  rw [h₀, h₂]
  rw [mul_div]
  simp

def pmf {A : Type*} [Fintype A] := @Subtype (A → ℝ) fun f ↦ Finset.sum Finset.univ f = 1

noncomputable def X : @pmf (Fin 4) _ := by
  unfold pmf
  exact ⟨
    ![5⁻¹, 2*5⁻¹, 5⁻¹, 5⁻¹], by
  simp [Finset.sum]
  ring_nf⟩

noncomputable def P : PMF (Fin 4) := by
  unfold PMF
  apply PMF.ofFintype
  show  Finset.sum Finset.univ ![5⁻¹, 2*5⁻¹, 5⁻¹, 5⁻¹] = 1
  simp [Finset.sum]
  ring_nf
  refine ENNReal.inv_mul_cancel ?_ ?_
  simp
  simp

example : P 0 = 5⁻¹ := by rfl
example : P.toMeasure {0,1} = 3*5⁻¹ := by
    show P.toMeasure ({0} ∪ {1}) = 3 * 5⁻¹
    rw [measure_union (h := by simp) (hd := by simp)]
    repeat rw [PMF.toMeasure_apply_singleton P (h := by trivial)]
    simp [P]
    ring_nf

noncomputable def mX : PMF (Fin 7) := by
  apply PMF.ofFintype
  show  Finset.sum Finset.univ ![5⁻¹, 2*5⁻¹, 5⁻¹, 0, 0, 0, 5⁻¹] = 1
  simp [Finset.sum]
  ring_nf
  refine ENNReal.inv_mul_cancel ?_ ?_
  simp
  simp

noncomputable def mY : PMF (Fin 7) :=
  PMF.map (fun i => i + 3) mX

/-- This is a small but representative part of 1.2.14(a). -/
lemma exercise_1_2_14a : mY 2 = 1/5 := by
  simp [mY]
  have (a : Fin 7) : 2 = a + 3 ↔ a = -1 := by
    fin_cases a
    simp
    simp; exact not_eq_of_beq_eq_false rfl
    simp; exact not_eq_of_beq_eq_false rfl
    simp; exact not_eq_of_beq_eq_false rfl
    simp; exact not_eq_of_beq_eq_false rfl
    simp; exact not_eq_of_beq_eq_false rfl
    simp; exact rfl
  simp_rw [this]
  have : (∑' (a : Fin 7), if a = -1 then mX a else 0)
    = mX (-1) := by simp_all only [Fin.isValue, tsum_ite_eq]
  rw [this]
  rfl

noncomputable def mZ : PMF (Fin 7) :=
  PMF.map (fun i => i^2) mX

lemma a_case_of_exercise_1_2_14_c : mZ 2 = 0 := by
  simp [mZ]
  have (a : Fin 7) : 2 = a * a ↔ a = 3 ∨ a = 4:= by
    fin_cases a <;> simp
  simp_rw [this, mX]
  intro i hi
  cases hi with
  | inl h => subst h;simp
  | inr h => subst h;simp


noncomputable def ex_2_1' : Measure (Set.Icc 2 10 : Set ℝ) :=
   (8⁻¹ : ENNReal) • volume (α := (Set.Icc 2 10 : Set ℝ)) (self := Measure.Subtype.measureSpace)


noncomputable def uniformOn_2_10 : Measure ℝ :=
  (1 / 8 : ℝ≥0∞) • volume.restrict (Set.Icc 2 10)
#check MeasureTheory.Measure.rnDeriv

open MeasureTheory.Measure Classical
/-- The RN derivative of the measure: -/

lemma h₀ : (fun x ↦ if 2 ≤ x ∧ x ≤ 10 then (8⁻¹:ENNReal) else 0) =
        (8⁻¹:ENNReal) • fun x ↦ if (2:ℝ) ≤ x ∧ x ≤ 10 then (1:ENNReal) else 0 := by
        ext
        simp

lemma h₀' (A : Set ℝ) : (fun x ↦ if x ∈ A then (8⁻¹:ENNReal) else 0) =
        (8⁻¹:ENNReal) • fun x ↦ if x ∈ A then (1:ENNReal) else 0 := by
        ext
        simp


lemma rnDeriv_uniformOn_2_10 :
    uniformOn_2_10.rnDeriv volume =ᵐ[volume]
        (fun x ↦ if x ∈ Set.Icc 2 10 then 8⁻¹ else 0) := by
    simp [uniformOn_2_10, h₀]
    have h₁ : (volume.restrict (Set.Icc (2:ℝ) 10)).rnDeriv volume
        =ᶠ[ae volume] fun x ↦ if x ∈ Set.Icc 2 10 then 1 else 0 := by
      convert rnDeriv_restrict_self volume (show MeasurableSet (Set.Icc (2:ℝ) 10) by simp) using 1
      ext a
      simp
      split_ifs <;> simp_all
    exact .trans (rnDeriv_smul_left_of_ne_top _ _ (by simp))
       <| .trans (.smul (Filter.EventuallyEq.refl _ fun x ↦ (8⁻¹ : ℝ≥0∞)) h₁) <| by rfl

lemma u₀ (A : Set ℝ) (hA : MeasurableSet A) :
    uniformOn_2_10 A = ∫⁻ (x : ℝ) in A, (fun x ↦ if x ∈ Set.Icc 2 10 then 8⁻¹ else 0) x := by
    have h₀ := @MeasureTheory.Measure.setLIntegral_rnDeriv' Real Real.measurableSpace
        (volume.restrict (Set.Icc (2:ℝ) 10)) volume _ absolutelyContinuous_restrict
        A hA
    have h₁ := @MeasureTheory.Measure.setLIntegral_rnDeriv' Real Real.measurableSpace
        uniformOn_2_10 volume (by
            unfold uniformOn_2_10;simp
            exact haveLebesgueDecompositionSMul' (volume.restrict (Set.Icc 2 10)) volume 8⁻¹
            ) (by
            unfold uniformOn_2_10;simp
            refine AbsolutelyContinuous.smul_left absolutelyContinuous_restrict 8⁻¹)
        A hA
    have h₂ : ∫⁻ (x : ℝ) in A, uniformOn_2_10.rnDeriv volume x ∂volume
         = ∫⁻ (x : ℝ) in A, (fun x ↦ if x ∈ Set.Icc 2 10 then 8⁻¹ else 0) x ∂volume := by
        have := rnDeriv_uniformOn_2_10
        refine setLIntegral_congr_fun_ae hA ?_
        simp [Filter.Eventually]
        exact Filter.mem_of_superset this fun ⦃a⦄ a_1 a ↦ a_1
    exact h₁ ▸ h₂

lemma u₁ (A : Set ℝ) (hA : MeasurableSet A) :
      ∫⁻ (x : ℝ) in A, (fun x ↦ if x ∈ Set.Icc 2 10 then 8⁻¹ else 0) x
    = ∫⁻ (x : ℝ) in Set.Icc 2 10, (fun x ↦ if x ∈ A then 8⁻¹ else 0) x := by
    simp
    rw [← MeasureTheory.lintegral_indicator]
    rw [← MeasureTheory.lintegral_indicator]
    simp [Set.indicator]
    congr
    ext r
    aesop
    simp
    exact hA

lemma u₂ (A : Set ℝ) (hA : MeasurableSet A) :
    uniformOn_2_10 A = ∫⁻ (x : ℝ) in Set.Icc 2 10, (fun x ↦ if x ∈ A then 8⁻¹ else 0) x := by
  rw [← u₁ _ hA]
  rw [u₀ _ hA]

lemma u₃ (A : Set ℝ) (hA : MeasurableSet A) :
    uniformOn_2_10 A = ∫⁻ (x : ℝ) in Set.Icc 2 10, (8⁻¹:ENNReal) • if x ∈ A then (1:ENNReal) else 0 := by
  rw [u₂ _ hA]
  have := h₀' A
  simp at this
  rw [this]
  congr

lemma u₄ (A : Set ℝ) (hA : MeasurableSet A) :
    uniformOn_2_10 A = ∫⁻ (x : ℝ) in Set.Icc 2 10, (8⁻¹:ENNReal) • Set.indicator A 1 x := by
  rw [u₃ _ hA]
  congr

def IsPDF (μ : Measure ℝ) (f : ℝ → ENNReal) :=
    ∀ A, MeasurableSet A → μ A = ∫⁻ (x : ℝ), f x * Set.indicator A 1 x

def IsPDF' (μ : Measure ℝ) (f : ℝ → ENNReal) :=
    ∀ A, MeasurableSet A → μ A = ∫⁻ (x : ℝ) in A, f x

def isprob : IsProbabilityMeasure uniformOn_2_10 := {
    measure_univ := by
        simp [uniformOn_2_10]
        norm_num
        refine ENNReal.inv_mul_cancel ?_ ?_
        simp
        simp
}

lemma pdf (A : Set ℝ) (hA : MeasurableSet A) :
    uniformOn_2_10 A = ∫⁻ (x : ℝ), (8⁻¹ : ℝ≥0∞) • Set.indicator (A ∩ Set.Icc 2 10) 1 x := by
  rw [u₄ _ hA, ← MeasureTheory.lintegral_indicator measurableSet_Icc]
  rw [Set.inter_indicator_one, Set.indicator_smul]
  simp [Set.indicator]

noncomputable instance : Measure (ℝ × ℝ) := volume

noncomputable instance : Measure (Fin 2 → ℝ) := volume

noncomputable instance : Measure (EuclideanSpace ℝ (Fin 2)) := volume

example (c : ℝ) : ∫ (x : ℝ × ℝ),
    Set.indicator {(a,b) | {a,b} ⊆ Set.Icc 0 1} (fun (x,y) => y^2 - x^2) x = 1 := by
    sorry


example : (3,3) ∈ (Set.Icc 2 10 : Set (ℝ × ℝ)) := by
    simp [Set.Icc]
    constructor
    · sorry
    · sorry

example (a b : ℝ) (h₀ : a ≤ b) (h : Set.Icc a b ⊆ Set.Icc 2 10) :
    uniformOn_2_10 (Set.Icc a b) = some (8⁻¹ * ⟨b - a, by linarith⟩)  := by
  simp [uniformOn_2_10]
  congr
  have : Set.Icc a b ∩ Set.Icc 2 10 =
    Set.Icc a b := by
    ext x
    simp
    intro h₁ h₂
    have : x ∈ Set.Icc a b := by aesop
    have := h this
    simp at this
    exact this
  rw [this]
  refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
  simp
  simp
  simp
  exact h₀

lemma ispdf : IsPDF' uniformOn_2_10
    (fun x : ℝ => (8⁻¹:ENNReal) • Set.indicator (Set.Icc (2:ℝ) 10) 1 x) := by
  unfold IsPDF'
  intro A hA
  rw [u₀]
  congr
  ext r
  simp
  split_ifs <;> simp_all
  exact hA


namespace exercise_1_2_1

-- Code for using LEAN Finsets by Anne Dominique Malig

-- Define the sample space as a custom type
inductive Letter
| a
| b
| c
deriving DecidableEq, Repr

open Letter

def omega : Finset Letter := {a, b, c}

-- Assign probability to each letter
def m : Letter → ℚ
| a => 1/2
| b => 1/3
| c => 1/6

-- Function that calculates the probability of a Finset of Letters
def prob (s : Finset Letter) : ℚ :=
  Finset.sum s m

-- Maps and displays every subset of omega to a pair of the subset and its probability
#eval (@omega.powerset.map (Finset Letter)
    (Finset Letter × ℚ) (
        ⟨
            fun s => (s, prob s),
            fun _ _ h =>
            (Prod.mk.injEq _ _ _ _ ▸ h).1
        ⟩
    ))

-- Code for using LEAN Lists

-- Define the sample space as a custom type
inductive Letter'
| a'
| b'
| c'
deriving DecidableEq, Repr

open Letter'

-- Define the probability mass function
def m' : Letter' → ℚ
| a' => 1/2
| b' => 1/3
| c' => 1/6

-- List all subsets of {a, b, c}
def powerSet : List (List Letter') :=
  [[],
   [a'], [b'], [c'],
   [a', b'], [a', c'], [b', c'],
   [a', b', c']
  ]

-- Compute the probability of a subset
def prob' (s' : List Letter') : ℚ :=
  s'.foldl (fun acc x => acc + m' x) 0

-- Pair each subset with its probability
def powerSetProbs : List (List Letter' × ℚ) :=
  powerSet.map (fun s' => (s', prob' s'))

-- Print the results
def printPowerSetProbs : IO Unit :=
  for (s', p) in powerSetProbs do
    IO.print (repr s' )
    IO.print ", probability = "
    IO.println p

#eval printPowerSetProbs

end exercise_1_2_1
