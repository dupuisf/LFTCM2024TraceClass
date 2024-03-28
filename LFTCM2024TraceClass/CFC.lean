import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Topology.ContinuousFunction.UniqueCFC

namespace CFC

variable {A : Type*}

section IsSelfAdjoint

variable [NormedRing A] [PartialOrder A] [StarOrderedRing A]
  [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

noncomputable def posPart (a : A) : A := cfc a (fun (x : ℝ) => x⁺)

lemma posPart_def (a : A) : posPart a = cfc a (fun (x : ℝ) => x⁺) := rfl

noncomputable def negPart (a : A) : A := cfc a (fun (x : ℝ) => x⁻)

lemma negPart_def (a : A) : negPart a = cfc a (fun (x : ℝ) => x⁻) := rfl

end IsSelfAdjoint

section NNReal

open NNReal

variable [NormedRing A] [PartialOrder A] [StarOrderedRing A] [CompleteSpace A]
  [NormedAlgebra ℂ A] --[ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [CstarRing A] [StarModule ℂ A]

noncomputable def sqrt (a : A) := cfc a NNReal.sqrt

lemma sqrt_def (a : A) : sqrt a = cfc a NNReal.sqrt := rfl

attribute [fun_prop] NNReal.continuous_sqrt

lemma mul_self_sqrt (a : A) (hnonneg : 0 ≤ a := by cfc_tac) : sqrt a * sqrt a = a := by
  simp only [sqrt_def]
  rw [← cfc_mul _ NNReal.sqrt NNReal.sqrt,
      cfc_congr (g := id) (hfg := fun _ => by simp), cfc_id ℝ≥0 a]

lemma sq_sqrt (a : A) (hnonneg : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
  simp only [pow_two, mul_self_sqrt a hnonneg]

lemma sqrt_sq (a : A) (hnonneg : 0 ≤ a := by cfc_tac) : sqrt (a ^ 2) = a := by
  rw [sqrt_def, ← cfc_pow_id (R := ℝ≥0) a, ← cfc_comp (R := ℝ≥0)]
  sorry

end NNReal

end CFC

section selfadjoint

variable [NormedRing A] [PartialOrder A] [StarOrderedRing A]
  [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

@[aesop safe apply]
lemma CFC.isSelfAdjoint (f : ℝ → ℝ) (a : A) : IsSelfAdjoint (cfc (R := ℝ) (p := (IsSelfAdjoint : A → Prop)) a f) := by
  by_cases h : IsSelfAdjoint a ∧ ContinuousOn f (spectrum ℝ a)
  · exact cfc_predicate a f h.1 h.2
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · simp [cfc_apply_of_not_continuousOn a hf]

end selfadjoint

section nonneg

open scoped NNReal

variable [NormedRing A] [PartialOrder A] [StarOrderedRing A]
  [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ≥0 ((0 ≤ ·) : A → Prop)]

@[aesop safe apply]
lemma CFC.nonneg (f : ℝ≥0 → ℝ≥0) (a : A) : 0 ≤ cfc a f := by
  by_cases h : 0 ≤ a ∧ ContinuousOn f (spectrum ℝ≥0 a)
  · exact cfc_predicate a f h.1 h.2
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · simp [cfc_apply_of_not_continuousOn a hf]

end nonneg
