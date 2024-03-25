import Mathlib.Topology.ContinuousFunction.FunctionalCalculus
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Module

namespace ContinuousLinearMap

noncomputable section

variable (𝕜 E : Type*) [IsROrC 𝕜] [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace 𝕜 E]

def stdHilbertIndex := Classical.choose (exists_hilbertBasis 𝕜 E)

lemma stdHilbertIndex_spec : ∃ (b : HilbertBasis (stdHilbertIndex 𝕜 E) 𝕜 E), b = ((↑) : stdHilbertIndex 𝕜 E → E) :=
  Classical.choose_spec <| exists_hilbertBasis 𝕜 E

def stdHilbertBasis : HilbertBasis (stdHilbertIndex 𝕜 E) 𝕜 E :=
  Classical.choose <| stdHilbertIndex_spec 𝕜 E

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The trace of a continuous linear map -/
def trace (f : E →L[𝕜] E) := ∑' (i : stdHilbertIndex 𝕜 E), ⟪ f i, i ⟫

lemma star_tsum {ι : Type*} (f : ι → 𝕜) : starRingEnd 𝕜 (∑' i, f i) = ∑' i, starRingEnd 𝕜 (f i) := by
  exact (starL 𝕜).map_tsum

/-- The trace of the adjoint is the star of the trace. -/
lemma trace_adjoint_eq_star_trace (f : E →L[𝕜] E) :
  trace 𝕜 E (adjoint f) = (starRingEnd 𝕜) (trace 𝕜 E f) := by
  unfold trace
  simp_rw [adjoint_inner_left]
  conv =>
    enter [1, 1, i]
    rw [← inner_conj_symm]
    rfl
  refine (star_tsum 𝕜 ?_).symm
  done

lemma trace_basis_eq_trace_basis (f : E →L[𝕜] E)
  {ι1 ι2 : Type*} (B1 : HilbertBasis ι1 𝕜 E) (B2 : HilbertBasis ι2 𝕜 E) :
  ∑' (i : ι1), ⟪ f (B1 i), (B1 i) ⟫ = ∑' (i : ι2), ⟪ f (B2 i), (B2 i) ⟫ := by
  conv =>
    enter [2, 1, i]
    rw [← HilbertBasis.tsum_inner_mul_inner B1]
  conv =>
    enter [1, 1, i]
    rw [← adjoint_inner_right, ← HilbertBasis.tsum_inner_mul_inner B2]
    conv =>
      enter [1, i]
      rw [adjoint_inner_right, mul_comm]
  rw [tsum_comm]
  rw [← summable_norm_iff]
  rw [summable_prod_of_nonneg]
  · constructor
    · intro a
      dsimp
      rw [summable_norm_iff]
      apply HilbertBasis.summable_inner_mul_inner
    · dsimp
      -- TODO
      sorry
  · intro x
    apply norm_nonneg

lemma trace_eq_sum_over_basis (f : E →L[𝕜] E) (ι : Type*) (b : HilbertBasis ι 𝕜 E) :
  ∑' (i : ι), ⟪ f (b i), (b i) ⟫ = trace 𝕜 E f := by
  -- TODO: I couldn't figure out why it works above with a general second basis but not here
  sorry

end

end ContinuousLinearMap
