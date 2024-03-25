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

lemma bla0 (a b : 𝕜) : (starRingEnd 𝕜) a * b = (starRingEnd 𝕜) (a * (starRingEnd 𝕜) b) := by
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]

lemma bla1 (f : E →L[𝕜] E) (xa xb : E) :
  ⟪ f xb, xa ⟫ * ⟪ xa, xb ⟫ = (starRingEnd 𝕜) (⟪ (adjoint f) xa, xb ⟫ * ⟪ xb, xa ⟫) := by
  rw [adjoint_inner_left]
  rw [← inner_conj_symm]
  rw [← inner_conj_symm xb]
  apply bla0
  done

lemma trace_eq_sum_over_basis (f : E →L[𝕜] E) (ι : Type*) (b : HilbertBasis ι 𝕜 E) :
  ∑' (i : ι), ⟪ f (b i), (b i) ⟫ = trace 𝕜 E f := by
  unfold trace
  conv =>
    enter [2, 1, i]
    rw [← HilbertBasis.tsum_inner_mul_inner b]
  rw [tsum_comm]
  conv =>
    enter [2, 1, b, 1, c]
    rw [bla1]
  simp_rw [← star_tsum 𝕜]


end

end ContinuousLinearMap
