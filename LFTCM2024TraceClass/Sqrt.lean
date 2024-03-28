import LFTCM2024TraceClass.ContinuousLinearMap
import Mathlib.Topology.ContinuousFunction.UniqueCFC

open scoped NNReal

attribute [fun_prop] NNReal.continuous_sqrt

noncomputable section

namespace CFC

variable {A : Type*} [PartialOrder A] [Ring A] [StarOrderedRing A] [TopologicalSpace A]

section NNReal

variable [Algebra ℝ≥0 A] [ContinuousFunctionalCalculus ℝ≥0 ((0 : A) ≤ ·)] [UniqueContinuousFunctionalCalculus ℝ≥0 A]

def sqrt (a : A) : A := cfc a NNReal.sqrt

lemma sq_sqrt {a : A} (ha : 0 ≤ a) : sqrt a ^ 2 = a := by
  nth_rw 2 [← cfc_id ℝ≥0 a]
  rw [sqrt, ← cfc_pow ..]
  exact cfc_congr a (fun _ _ ↦ by simp)

lemma sqrt_sq {a : A} (ha : 0 ≤ a) : sqrt (a ^ 2) = a := by
  rw [sqrt, ← cfc_comp_pow ..]
  simp [cfc_id' ℝ≥0 a]

end NNReal

section Real

variable [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ ((0 : A) ≤ ·)] [UniqueContinuousFunctionalCalculus ℝ A]

-- maybe just show that `cfc` is order preserving?
lemma nonneg_on_spectrum_iff (f : ℝ → ℝ) (a : A) : ∀ x ∈ spectrum ℝ a, 0 ≤ f x ↔ 0 ≤ cfc a f := by
  sorry

-- maybe just show that `cfc` is order preserving?
lemma nonneg_of_coe_nnreal (f : ℝ → ℝ≥0) (a : A) (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) : 0 ≤ cfc a (f · : ℝ → ℝ) := by
  sorry

end Real

section Complex

variable [Algebra ℂ A] [ContinuousFunctionalCalculus ℂ ((0 : A) ≤ ·)] [UniqueContinuousFunctionalCalculus ℂ A]

lemma isSelfAdjoint_of_coe_real (f : ℂ → ℝ) (a : A) : IsSelfAdjoint (cfc a (f · : ℂ → ℂ)) := by
  rw [isSelfAdjoint_iff, ← cfc_star]
  exact cfc_congr a fun x _ ↦ Complex.conj_ofReal _



def abs (a : A) : A := cfc a (‖·‖₊ : ℂ → ℂ)



end Complex

end CFC

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {f : H →L[ℂ] H} (hf : 0 ≤ f) : CFC.sqrt f ^ 2 = f :=
  CFC.sq_sqrt hf
