import LFTCM2024TraceClass.ContinuousLinearMap
import Mathlib.Topology.ContinuousFunction.UniqueCFC

open scoped NNReal

attribute [fun_prop] NNReal.continuous_sqrt

noncomputable section


variable {A : Type*} [PartialOrder A] [Ring A] [StarOrderedRing A] [TopologicalSpace A]


section OrderPreserving

-- this class exists solely to get a `StarOrderedRing` instance for continuous functions `C(α, R)`.
class ContinuousStarSqrt (R : Type*) [PartialOrder R] [NonUnitalSemiring R] [StarOrderedRing R]
    [TopologicalSpace R] where
  sqrt : R → R
  continuous_sqrt : ContinuousOn sqrt {x | 0 ≤ x}
  starSqrt_mul_self : ∀ x : R, 0 ≤ x → star (sqrt x) * sqrt x = x

instance ContinuousMap.instStarOrderedRing {X R : Type*} [TopologicalSpace X] [PartialOrder R]
    [NonUnitalRing R] [StarOrderedRing R] [TopologicalSpace R] [ContinuousStar R]
    [TopologicalRing R]  [ContinuousStarSqrt R] : StarOrderedRing C(X, R) :=
  StarOrderedRing.ofNonnegIff' add_le_add_left fun f ↦ by
    constructor
    · intro hf
      let f' : C(X, {x : R | 0 ≤ x}) := .mk _ (map_continuous f |>.codRestrict fun x ↦ by exact hf x)
      let sqrt' : C({x : R | 0 ≤ x}, R) := .mk _ ContinuousStarSqrt.continuous_sqrt.restrict
      use sqrt'.comp f'
      ext x
      exact ContinuousStarSqrt.starSqrt_mul_self (f x) (hf x) |>.symm
    · rintro ⟨f, rfl⟩
      rw [ContinuousMap.le_def]
      exact fun x ↦ star_mul_self_nonneg (f x)

instance : ContinuousStarSqrt ℝ where
  sqrt := Real.sqrt
  continuous_sqrt := Real.continuous_sqrt.continuousOn
  starSqrt_mul_self _ := Real.mul_self_sqrt

-- I don't know why we have this instance
instance : ContinuousStarSqrt ℝ≥0 where
  sqrt := NNReal.sqrt
  continuous_sqrt := NNReal.continuous_sqrt.continuousOn
  starSqrt_mul_self _ _ := NNReal.mul_self_sqrt _

open scoped ComplexOrder in
instance : ContinuousStarSqrt ℂ where
  sqrt := (↑) ∘ Real.sqrt ∘ Complex.re
  continuous_sqrt := by fun_prop
  starSqrt_mul_self x hx := by
    simp only [Function.comp_apply, IsROrC.star_def]
    have : x.re = x := Complex.eq_re_of_ofReal_le hx |>.symm
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt, this]
    rwa [← Complex.zero_le_real, this]

instance ContinuousMap.instStarOrderedRingNNReal {X : Type*} [TopologicalSpace X] :
    StarOrderedRing C(X, ℝ≥0) :=
  StarOrderedRing.ofLEIff fun f g ↦ by
    constructor
    · intro hfg
      use .comp ⟨NNReal.sqrt, by fun_prop⟩ (g - f)
      ext1 x
      simpa using add_tsub_cancel_of_le (hfg x) |>.symm
    · rintro ⟨s, rfl⟩
      exact fun _ ↦ by simp

section Generic

variable {R : Type*} {p : A → Prop} [PartialOrder R] [CommRing R] [StarOrderedRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [ContinuousStarSqrt R] [Algebra R A] [StarModule R A]
variable [ContinuousFunctionalCalculus R p]

lemma cfcHom_mono (a : A) (ha : p a) (f g : C(spectrum R a, R)) (hfg : f ≤ g) :
    cfcHom ha f ≤ cfcHom ha g :=
  OrderHomClass.mono (cfcHom ha) hfg

lemma cfc_mono {f g : R → R} {a : A} (h : ∀ x ∈ spectrum R a, f x ≤ g x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc a f ≤ cfc a g := by
  rw [cfc_apply a f, cfc_apply a g]
  exact cfcHom_mono a ha _ _ fun x ↦ h x.1 x.2

lemma CFC.nonneg_on_spectrum (f : R → R) (a : A) (h : ∀ x ∈ spectrum R a, 0 ≤ f x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    0 ≤ cfc a f := by
  simpa using cfc_mono h

lemma CFC.nonpos_on_spectrum (f : R → R) (a : A) (h : ∀ x ∈ spectrum R a, f x ≤ 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc a f ≤ 0 := by
  simpa using cfc_mono h

end Generic

section NNReal

variable [Algebra ℝ≥0 A] [ContinuousFunctionalCalculus ℝ≥0 ((0 : A) ≤ ·)]

lemma cfcHom_mono_nnreal (a : A) (ha : 0 ≤ a) (f g : C(spectrum ℝ≥0 a, ℝ≥0)) (hfg : f ≤ g) :
    cfcHom ha f ≤ cfcHom ha g := by
  have := @OrderHomClass.mono (C(spectrum ℝ≥0 a, ℝ≥0) →⋆ₐ[ℝ≥0] A) C(spectrum ℝ≥0 a, ℝ≥0) A _ _ _
    StarRingHomClass.instOrderHomClass
  exact this (cfcHom ha (R := ℝ≥0)) hfg

lemma cfc_mono_nnreal {f g : ℝ≥0 → ℝ≥0} {a : A} (h : ∀ x ∈ spectrum ℝ≥0 a, f x ≤ g x)
    (hf : ContinuousOn f (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum ℝ≥0 a) := by cfc_cont_tac) (ha : 0 ≤ a := by cfc_tac) :
    cfc a f ≤ cfc a g := by
  rw [cfc_apply a f, cfc_apply a g]
  exact cfcHom_mono_nnreal a ha _ _ fun x ↦ h x.1 x.2

end NNReal

end OrderPreserving

namespace CFC
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

def abs (a : A) : A := sqrt (star a * a)

lemma cfc_congr_nonneg {f : ℝ≥0 → ℝ≥0} (g : ℝ≥0 → ℝ≥0) {a : A} (hfg : f = g) : cfc a f = cfc a g :=
  cfc_congr a (fun x _ => by simp only [hfg])

attribute [simp] cfc_id

lemma abs_of_nonneg (a : A) (ha : 0 ≤ a) : abs a = a := by
  rw [abs, (IsSelfAdjoint.of_nonneg ha).star_eq, ← sq, sqrt_sq ha]

end NNReal

section Real

variable [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [UniqueContinuousFunctionalCalculus ℝ A]

attribute [fun_prop] NNReal.continuous_coe

lemma nonneg_toReal (f : ℝ → ℝ≥0) (a : A) (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) : 0 ≤ cfc a (f · : ℝ → ℝ) :=
  nonneg_on_spectrum (h := fun _ _ ↦ by positivity)


end Real

section Complex

variable [Algebra ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]
variable [UniqueContinuousFunctionalCalculus ℂ A]

lemma isSelfAdjoint_of_coe_real (f : ℂ → ℝ) (a : A) : IsSelfAdjoint (cfc a (f · : ℂ → ℂ)) := by
  rw [isSelfAdjoint_iff, ← cfc_star]
  exact cfc_congr a fun x _ ↦ Complex.conj_ofReal _

open ComplexOrder in
lemma nonneg_coe_nnreal (f : ℂ → ℝ≥0) (a : A) (hf : ContinuousOn f (spectrum ℂ a) := by cfc_cont_tac)
    (ha : IsStarNormal a := by cfc_tac) : 0 ≤ cfc a (f · : ℂ → ℂ) :=
  nonneg_on_spectrum (h := fun _ _ ↦ by positivity)

end Complex

end CFC

end
