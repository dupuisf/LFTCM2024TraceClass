import Mathlib.Topology.ContinuousFunction.FunctionalCalculus
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- The trace of a continuous linear map -/
def trace (f : E →L[𝕜] E) := sorry

end ContinuousLinearMap
