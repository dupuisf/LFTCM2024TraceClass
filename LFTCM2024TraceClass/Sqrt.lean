import LFTCM2024TraceClass.ContinuousLinearMap
import Mathlib.Topology.ContinuousFunction.UniqueCFC

open scoped NNReal

attribute [fun_prop] NNReal.continuous_sqrt

noncomputable section


variable {A : Type*} [PartialOrder A] [Ring A] [StarOrderedRing A] [TopologicalSpace A]


section OrderPreserving

-- this class exists solely to get a `StarOrderedRing` instance for continuous functions `C(α, R)`.
-- actually, the better solution is to pass the `Star` operation as a parameter to
-- `StarOrderedRing` so that it becomes a `Prop` mixin.
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

@[simp]
lemma sqrt_nonneg (a : A) : 0 ≤ sqrt a := by
  by_cases h : 0 ≤ a
  · exact cfc_predicate ..
  · rw [sqrt, cfc_apply_of_not_predicate a h]

@[simp]
lemma isSelfAdjoint_sqrt (a : A) : IsSelfAdjoint (sqrt a) :=
  IsSelfAdjoint.of_nonneg <| by simp

-- is there some reaspon this isn't marked `simp` already?
attribute [simp] IsSelfAdjoint.star_eq

lemma star_sqrt (a : A) : star (sqrt a) = sqrt a := by simp

lemma sq_sqrt_of_nonneg {a : A} (ha : 0 ≤ a) : sqrt a ^ 2 = a := by
  nth_rw 2 [← cfc_id ℝ≥0 a]
  rw [sqrt, ← cfc_pow ..]
  exact cfc_congr a (fun _ _ ↦ by simp)

@[simp]
lemma sq_sqrt (a : {x : A // 0 ≤ x}) : sqrt (a : A) ^ 2 = a :=
  sq_sqrt_of_nonneg a.2

lemma sqrt_sq_of_nonneg {a : A} (ha : 0 ≤ a) : sqrt (a ^ 2) = a := by
  rw [sqrt, ← cfc_comp_pow ..]
  simp [cfc_id' ℝ≥0 a]

@[simp]
lemma sqrt_sq (a : {x : A // 0 ≤ x}) : sqrt (a ^ 2 : A) = a :=
  sqrt_sq_of_nonneg a.2

def abs (a : A) : A := sqrt (star a * a)

@[simp] -- maybe we don't want this as a `simp` lemma so we don't go hunting for `IsStarNormal` instances?
lemma _root_.IsStarNormal.abs_star (a : A) [IsStarNormal a] : abs (star a) = abs a := by
  rw [abs, abs, star_star, ← star_comm_self']

lemma cfc_congr_nonneg {f : ℝ≥0 → ℝ≥0} (g : ℝ≥0 → ℝ≥0) {a : A} (hfg : f = g) : cfc a f = cfc a g :=
  cfc_congr a (fun x _ => by simp only [hfg])

@[simp]
lemma nonneg_star_val_eq (a : {x : A // 0 ≤ x}) : star (a : A) = a :=
  (IsSelfAdjoint.of_nonneg a.2).star_eq

attribute [simp] star_mul_self_nonneg mul_star_self_nonneg

@[simp]
lemma abs_nonneg (a : A) : 0 ≤ abs a := cfc_predicate ..

lemma abs_of_nonneg {a : A} (ha : 0 ≤ a) : abs a = a := by
  lift a to {x : A // 0 ≤ x} using ha
  simp [abs, ←sq]

@[simp]
lemma abs_val_eq (a : {x : A // 0 ≤ x}) : abs (a : A) = a :=
  abs_of_nonneg a.2

@[simp]
lemma abs_abs (a : A) : abs (abs a) = abs a := by
  lift abs a to {x : A // 0 ≤ x} using (by simp) with b
  simp

lemma abs_sq (a : A) : (abs a) ^ 2 = star a * a := by
  rw [abs, sq_sqrt_of_nonneg (by simp)]

@[simp]
lemma isSelfAdjoint_abs (a : A) : IsSelfAdjoint (abs a) :=
  IsSelfAdjoint.of_nonneg <| abs_nonneg a

@[simp]
lemma star_abs (a : A) : star (abs a) = abs a :=
  isSelfAdjoint_abs a |>.star_eq

lemma pow_nonneg {a : A} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ a ^ n := by
  induction n with
  | zero => simpa using star_mul_self_nonneg (1 : A)
  | succ n ih => sorry --exact mul_nonneg ha ih

@[simp]
lemma one_nonneg : 0 ≤ (1 : A) := by
  simpa using star_mul_self_nonneg (1 : A)

lemma sq_nonneg {a : A} (ha : IsSelfAdjoint a) : 0 ≤ a ^ 2 := by
  simpa [ha.star_eq, sq] using star_mul_self_nonneg a

lemma pow_two_mul_nonneg {a : A} (ha : IsSelfAdjoint a) (n : ℕ) : 0 ≤ a ^ (2 * n) :=
  pow_mul a 2 n ▸ pow_nonneg (sq_nonneg ha) n

attribute [aesop safe apply] conjugate_nonneg conjugate_nonneg'
attribute [aesop unsafe 70% apply] pow_nonneg add_nonneg
attribute [aesop unsafe 30% apply] sq_nonneg pow_two_mul_nonneg

example {a b : A} (ha : IsSelfAdjoint a) (hb : 0 ≤ b) (n : ℕ) : 0 ≤ a ^ 2 + b ^ n + a ^ (2 * n) + b ^ 2 := by cfc_tac

example (a b c : A) (hb : 0 ≤ 1 + b) : 0 ≤ star a * (1 + (1 + b)) ^ 2 * a + c * star c + sqrt (abs a) := by cfc_tac

end NNReal

section Real

variable [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [UniqueContinuousFunctionalCalculus ℝ A]

attribute [fun_prop] NNReal.continuous_coe

lemma nonneg_toReal (f : ℝ → ℝ≥0) (a : A) (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) : 0 ≤ cfc a (f · : ℝ → ℝ) :=
  nonneg_on_spectrum (h := fun _ _ ↦ by positivity)


end Real

section IsROrC

variable {𝕜 : Type*} [IsROrC 𝕜] {p : A → Prop} [Algebra 𝕜 A] [ContinuousFunctionalCalculus 𝕜 p]
variable [UniqueContinuousFunctionalCalculus 𝕜 A] [TopologicalRing A] [ContinuousStar A] [StarModule 𝕜 A]

open Polynomial in
lemma _root_.Polynomial.toContinuousMapOn_X_eq_restrict_id {R : Type*} [Semiring R] [TopologicalSpace R]
    [TopologicalSemiring R] (s : Set R) :
    (X : R[X]).toContinuousMapOn s = .restrict s (.id R) := by
  ext; simp

variable (𝕜)

theorem cfcHom_range {a : A} (ha : p a) :
    (cfcHom ha (R := 𝕜)).range = elementalStarAlgebra 𝕜 a := by
  have := UniqueContinuousFunctionalCalculus.compactSpace_spectrum a (R := 𝕜)
  rw [StarAlgHom.range_eq_map_top, ← polynomialFunctions.starClosure_topologicalClosure, ←
    StarSubalgebra.topologicalClosure_map _ _ (cfcHom_closedEmbedding ha (R := 𝕜)),
    polynomialFunctions.starClosure_eq_adjoin_X, StarAlgHom.map_adjoin]
  congr
  rw [Set.image_singleton, Polynomial.toContinuousMapOnAlgHom_apply,
    Polynomial.toContinuousMapOn_X_eq_restrict_id, cfcHom_id ha]

theorem cfc_range {a : A} (ha : p a) : Set.range (cfc a (R := 𝕜)) = (cfcHom ha (R := 𝕜)).range := by
  ext
  constructor
  · rintro ⟨f, rfl⟩
    by_cases hf : ContinuousOn f (spectrum 𝕜 a)
    · rw [cfc_apply a f, SetLike.mem_coe]
      exact ⟨_, rfl⟩
    · rw [cfc_apply_of_not_continuousOn a hf]
      exact zero_mem _
  · rintro ⟨f, rfl⟩
    classical
    let f' (x : 𝕜) : 𝕜 := if hx : x ∈ spectrum 𝕜 a then f ⟨x, hx⟩ else 0
    have hff' : f = Set.restrict (spectrum 𝕜 a) f'  := by ext; simp [f']
    have : ContinuousOn f' (spectrum 𝕜 a) := by
      rw [continuousOn_iff_continuous_restrict]
      exact hff' ▸ map_continuous f
    use f'
    rw [cfc_apply a f']
    congr!
    exact hff'.symm

#eval 1349^2 % 1763
#eval 385^2 % 1763
#eval 133^2 % 1763
#eval 59 ^ 2 % 1763
#eval 1718^2 % 1763

def digits : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => n % 2 :: digits (n / 2)

#exit

theorem induction_on (P : A → Prop) {a : A} (ha : p a) (f : C(spectrum 𝕜 a, 𝕜))
    (self : P a) (star_self : P (star a)) (algebraMap : ∀ r : 𝕜, P (cfcHom ha (algebraMap 𝕜 C(spectrum 𝕜 a, 𝕜) r)))
    (add : ∀ g₁ g₂ : C(spectrum 𝕜 a, 𝕜), P (cfcHom ha g₁) → P (cfcHom ha g₂) → P (cfcHom ha (g₁ + g₂)))
    (mul : ∀ g₁ g₂ : C(spectrum 𝕜 a, 𝕜), P (cfcHom ha g₁) → P (cfcHom ha g₂) → P (cfcHom ha (g₁ * g₂) : A))
    (closure : ∀ s : Set C(spectrum 𝕜 a, 𝕜), (∀ g ∈ s, P (cfcHom ha g)) → ∀ g' ∈ closure s, P (cfcHom ha g')) :
    P (cfcHom ha f) := by

  sorry


#check cfc_apply
-- the range of the continuous functional calculus is the elemental star algebra
lemma cfc_range_star (a : A) (ha : p a) : Set.range (cfc a (R := 𝕜)) = elementalStarAlgebra 𝕜 a := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    by_cases hf : ContinuousOn f (spectrum 𝕜 a)
    · rw [cfc_apply a f]


    · sorry --simpa [cfc_apply_of_not_continuousOn a hf] using zero_mem _
  · sorry

end IsROrC

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
