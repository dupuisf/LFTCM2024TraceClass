import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Content about Hilbert bases

Could maybe be merged in `Mathlib/Analysis/InnerProductSpace/l2Space`
 -/

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace ℂ E]

/- Standard Hilbert basis -/

def stdHilbertIndex := Classical.choose (exists_hilbertBasis ℂ E)

lemma stdHilbertIndex_spec : ∃ (b : HilbertBasis (stdHilbertIndex E) ℂ E), b = ((↑) : (stdHilbertIndex E) → E) :=
  Classical.choose_spec <| exists_hilbertBasis ℂ E

def stdHilbertBasis : HilbertBasis (stdHilbertIndex E) ℂ E :=
  Classical.choose <| stdHilbertIndex_spec E

end

section

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

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

end
