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

/- Definitions of diagonal and cross sums -/

def sum_diag_norm {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁), (‖f (B₁ i₁)‖₊^2 : ENNReal)

def sum_cross {ι₁ ι₂ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (B₂ : HilbertBasis ι₂ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁) (i₂ : ι₂), (‖⟪f (B₁ i₁), B₂ i₂⟫‖₊^2 : ENNReal)

/- Parseval -/

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

/- Definition of absolute value, square root, and trace -/

def sqrt_abs (f : E →L[ℂ] E) : E →L[ℂ] E := sorry

lemma adjoint_sqrt_abs (f : E →L[ℂ] E) : ContinuousLinearMap.adjoint (sqrt_abs f) = sqrt_abs f := by sorry

/-- The NNNorm of the conjugate is the NNNorm. -/
lemma nnnorm_conj (z : ℂ) : ‖(starRingEnd ℂ) z‖₊ = ‖z‖₊ := by
  apply NNReal.coe_injective
  exact (Complex.abs_conj z)

lemma sqrt_abs_comm (a b : E) (f : E →L[ℂ] E) : ‖⟪(sqrt_abs f) a, b⟫‖₊ = ‖⟪(sqrt_abs f) b, a⟫‖₊ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_sqrt_abs]
  rw [← InnerProductSpace.conj_symm]
  rw [nnnorm_conj]

/-- The diagonal sum of norms within any Hilbert basis is equal to the trace. -/
def sum_diag_norm_independent
  {ι₁ ι₂ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (B₂ : HilbertBasis ι₂ ℂ E) (f : E →L[ℂ] E) :
  sum_diag_norm B₁ (sqrt_abs f) = sum_diag_norm B₂ (sqrt_abs f) := by
  rw [sum_diag_eq_sum_cross B₁ B₂]
  rw [sum_diag_eq_sum_cross B₂ B₁]
  rw [sum_cross, sum_cross]
  rw [ENNReal.tsum_comm]
  conv =>
    enter [1, 1, b, 1, a, 1, 1]
    rw [sqrt_abs_comm]

/- Trace class and trace -/

open ENNReal

class IsTraceClass (f : E →L[ℂ] E) where
  finite_diag_norm : ∀ {ι : Type*} (B : HilbertBasis ι ℂ E), sum_diag_norm B (sqrt_abs f) ≠ ∞

theorem IsTraceClass.mk_of_exists {ι : Type*} (B : HilbertBasis ι ℂ E)
  (h : sum_diag_norm B (sqrt_abs f) ≠ ∞) : IsTraceClass f where
    finite_diag_norm := by
      intro ι' B'
      rw [sum_diag_norm_independent B' B]
      exact h

def sum_diag_inner {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁), ⟪f (B₁ i₁), B₁ i₁⟫

def trace (f : E →L[ℂ] E) : ℂ := sum_diag_inner (stdHilbertBasis E) f

theorem sum_diag_inner_eq_trace {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) [IsTraceClass f] :
  HasSum (fun i₁ => ⟪f (B₁ i₁), B₁ i₁⟫) (trace f) := by
  -- The proof is not so easy and seems to require Hilbert-Schmidt and approximtion (see Conway)
  sorry

end

end Conway
