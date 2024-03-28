import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Module

namespace Conway

/- Standard Hilbert basis -/

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

def stdHilbertIndex := Classical.choose (exists_hilbertBasis ℂ E)

lemma stdHilbertIndex_spec : ∃ (b : HilbertBasis (stdHilbertIndex E) ℂ E), b = ((↑) : (stdHilbertIndex E) → E) :=
  Classical.choose_spec <| exists_hilbertBasis ℂ E

def stdHilbertBasis : HilbertBasis (stdHilbertIndex E) ℂ E :=
  Classical.choose <| stdHilbertIndex_spec E

end

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/- Continuous functional calculus definitions -/

/-- Absolute value of an operator, so |f| -/
def abs (f : E →L[ℂ] E) : E →L[ℂ] E := sorry

/-- Square of an operator, so f^2 -/
def sq (f : E →L[ℂ] E) : E →L[ℂ] E := sorry

/-- Square root of absolute value of an operator, so |f|^{1/2} -/
def sqrt_abs (f : E →L[ℂ] E) : E →L[ℂ] E := sorry

/-- Square root of absolute value is self-adjoint. -/
lemma adjoint_sqrt_abs (f : E →L[ℂ] E) :
  ContinuousLinearMap.adjoint (sqrt_abs f) = sqrt_abs f := by sorry

/-- Absolute value is self-adjoint. -/
lemma adjoint_abs (f : E →L[ℂ] E) :
  ContinuousLinearMap.adjoint (abs f) = abs f := by sorry

/-- Absolute value of adjoint is absolute value. -/
lemma abs_adjoint (f : E →L[ℂ] E) :
  abs (ContinuousLinearMap.adjoint f) = abs f := by sorry

/-- Square of absolute value is adjoint x f. -/
lemma sq_abs_eq_adjoint_self (f : E →L[ℂ] E) :
  sq (abs f) = (ContinuousLinearMap.adjoint f) * f := by sorry

/-- Abs of abs is abs -/
lemma abs_abs (f : E →L[ℂ] E) : abs (abs f) = abs f := sorry

/-- Square root of square is |f| -/
lemma sqrt_sq_eq_abs (f : E →L[ℂ] E) : sqrt_abs (sq (abs f)) = abs f := by sorry

/-- Abs * abs = adjoint x f -/
lemma abs_mul_abs (f : E →L[ℂ] E) (x : E) :
  (abs f) ((abs f) x) = (ContinuousLinearMap.adjoint f) (f x) := by sorry

/-- Norm of abs of vector is self norm  -/
lemma abs_vec_norm (f : E →L[ℂ] E) (x : E) : ‖(abs f) x‖^2 = ‖f x‖^2 := by
  rw [norm_sq_eq_inner (𝕜 := ℂ), norm_sq_eq_inner (𝕜 := ℂ)]
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [adjoint_abs, abs_mul_abs]
  rw [← ContinuousLinearMap.adjoint_inner_right]

lemma abs_vec_norm' (f : E →L[ℂ] E) (x : E) : ‖(abs f) x‖₊ = ‖f x‖₊ := by sorry

/- Definitions of diagonal and cross sums -/

def sum_diag_norm {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁), (‖f (B₁ i₁)‖₊^2 : ENNReal)

def sum_cross {ι₁ ι₂ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (B₂ : HilbertBasis ι₂ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁) (i₂ : ι₂), (‖⟪f (B₁ i₁), B₂ i₂⟫‖₊^2 : ENNReal)

lemma sum_diag_norm_abs {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) :
  sum_diag_norm B₁ (abs f) = sum_diag_norm B₁ f := by
  rw [sum_diag_norm, sum_diag_norm]
  conv =>
    enter [1, 1, i₁, 1, 1]
    rw [abs_vec_norm']

/-- Parseval identity ; should probably exist (or else be added to) the HilbertBasis file -/
lemma parseval {ι : Type*} (B : HilbertBasis ι ℂ E) (x : E) : ∑' (i : ι), ‖⟪x, B i⟫‖^2 = ‖x‖^2 := by
  rw [norm_sq_eq_inner (𝕜 := ℂ)]
  rw [← HilbertBasis.tsum_inner_mul_inner B]
  rw [IsROrC.re_tsum]
  conv =>
    enter [2, 1, a]
    rw [← inner_conj_symm]
    rw [← IsROrC.innerProductSpace.proof_1]
    rw [← inner_conj_symm, IsROrC.norm_conj]
  apply HilbertBasis.summable_inner_mul_inner B

lemma enn_parseval {ι : Type*} (B : HilbertBasis ι ℂ E) (x : E) :
  ∑' (i : ι), (‖⟪x, B i⟫‖₊^2 : ENNReal) = (‖x‖₊^2 : ENNReal) := by
  -- TODO: Deduce this ENNReal version of the previous one
  sorry

/- Conway's Proposition 18.1 -/

/-- For a bounded operator `f` on a Hilbert space `E`, given Hilbert bases `B₁` and `B₂` of `E`,
one has `∑ ‖f e₁‖² = ∑ ∑ |⟪f e₁, e₂⟫|²`. -/
lemma sum_diag_eq_sum_cross
  {ι₁ ι₂ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (B₂ : HilbertBasis ι₂ ℂ E) (f : E →L[ℂ] E) :
  sum_diag_norm B₁ f = sum_cross B₁ B₂ f := by
  rw [sum_diag_norm, sum_cross]
  conv =>
    enter [1, 1, i₁]
    rw [← enn_parseval B₂]

/-- The NNNorm of the conjugate is the NNNorm. -/
lemma nnnorm_conj (z : ℂ) : ‖(starRingEnd ℂ) z‖₊ = ‖z‖₊ := by
  apply NNReal.coe_injective
  exact (Complex.abs_conj z)

/-- The diagonal sum of norms of a self-adjoint operator is independent of the Hilbert basis -/
lemma sum_diag_norm_independent
  {ι₁ ι₂ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (B₂ : HilbertBasis ι₂ ℂ E) (f : E →L[ℂ] E)
  (h : ContinuousLinearMap.adjoint f = f) :
  sum_diag_norm B₁ f = sum_diag_norm B₂ f := by
  rw [sum_diag_eq_sum_cross B₁ B₂]
  rw [sum_diag_eq_sum_cross B₂ B₁]
  rw [sum_cross, sum_cross]
  rw [ENNReal.tsum_comm]
  conv =>
    enter [1, 1, b, 1, a, 1, 1]
    rw [← ContinuousLinearMap.adjoint_inner_right, h]
    rw [← InnerProductSpace.conj_symm]
    rw [nnnorm_conj]

/- Trace class -/

open ENNReal

class IsTraceClass (f : E →L[ℂ] E) where
  finite_diag_norm : ∀ {ι : Type*} (B : HilbertBasis ι ℂ E), sum_diag_norm B (sqrt_abs f) ≠ ∞

lemma IsTraceClass.mk_of_exists {ι : Type*} (B : HilbertBasis ι ℂ E)
  (h : sum_diag_norm B (sqrt_abs f) ≠ ∞) : IsTraceClass f where
    finite_diag_norm := by
      intro ι' B'
      rw [sum_diag_norm_independent B' B (sqrt_abs f) (adjoint_sqrt_abs f)]
      exact h

def trace_norm (f : E →L[ℂ] E) := sum_diag_norm (stdHilbertBasis E) (sqrt_abs f)

lemma sum_diag_eq_trace_norm {ι : Type*} (B : HilbertBasis ι ℂ E) :
  sum_diag_norm B (sqrt_abs f) = trace_norm f := by
  exact sum_diag_norm_independent B (stdHilbertBasis E) (sqrt_abs f) (adjoint_sqrt_abs f)

/- Hilbert-Schmidt -/

class IsHilbertSchmidt (f : E →L[ℂ] E) where
  sq_is_trace_class : IsTraceClass (sq (abs f))

def ENNReal.sqrt (x : ENNReal) : ENNReal := match x with
  | ENNReal.ofNNReal y => ENNReal.ofReal (Real.sqrt y)
  | ⊤ => ⊤

def hs_norm (f : E →L[ℂ] E) := ENNReal.sqrt (trace_norm (sq (abs f)))

/-- Proposition 18.6 item a) -/
lemma hs_norm_eq_sum_basis {ι : Type*} (B : HilbertBasis ι ℂ E) (f : E →L[ℂ] E) :
  hs_norm f = ENNReal.sqrt (sum_diag_norm B f) := by
  rw [hs_norm, trace_norm, sqrt_sq_eq_abs, ← sum_diag_norm_abs B f]
  rw [sum_diag_norm_independent]
  exact adjoint_abs f

/-- Proposition 18.6 item b) -/
lemma hs_norm_adjoint (f : E →L[ℂ] E) :
  hs_norm (ContinuousLinearMap.adjoint f) = hs_norm f := by
  rw [hs_norm, abs_adjoint, ← hs_norm]












def sum_diag_inner {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁), ⟪f (B₁ i₁), B₁ i₁⟫

def trace (f : E →L[ℂ] E) : ℂ := sum_diag_inner (stdHilbertBasis E) f

theorem sum_diag_inner_eq_trace {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) [IsTraceClass f] :
  HasSum (fun i₁ => ⟪f (B₁ i₁), B₁ i₁⟫) (trace f) := by
  -- The proof is not so easy and seems to require Hilbert-Schmidt and approximtion (see Conway)
  sorry

end

end Conway
