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

def abs (a : A) : A := cfc (star a * a) NNReal.sqrt

lemma cfc_congr_nonneg {f : ℝ≥0 → ℝ≥0} (g : ℝ≥0 → ℝ≥0) {a : A} (hfg : f = g) : cfc a f = cfc a g :=
  cfc_congr a (fun x _ => by simp only [hfg])

attribute [simp] cfc_id

@[simp]
lemma abs_of_nonneg (a : A) (ha : 0 ≤ a) : abs a = a := by
  unfold abs
  have h₁ : star a = a := by sorry
  have h₂ : a * a = cfc a (fun (x : ℝ≥0) => x^2) := by sorry
  simp only [h₁, h₂]
  rw [← cfc_comp a NNReal.sqrt (fun x => x^2)]
  have h₃ : (NNReal.sqrt ∘ fun x => x^2) = id := by ext; simp
  rw [cfc_congr_nonneg id h₃, cfc_id ℝ≥0 a]

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

variable [Algebra ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)] [UniqueContinuousFunctionalCalculus ℂ A]

lemma isSelfAdjoint_of_coe_real (f : ℂ → ℝ) (a : A) : IsSelfAdjoint (cfc a (f · : ℂ → ℂ)) := by
  rw [isSelfAdjoint_iff, ← cfc_star]
  exact cfc_congr a fun x _ ↦ Complex.conj_ofReal _





end Complex

end CFC

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {f : H →L[ℂ] H} (hf : 0 ≤ f) : CFC.sqrt f ^ 2 = f :=
  CFC.sq_sqrt hf
