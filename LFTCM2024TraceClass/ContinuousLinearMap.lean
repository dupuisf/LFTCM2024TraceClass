import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.Positive

namespace ContinuousLinearMap

section PartialOrder

variable {𝕜 H : Type*} [IsROrC 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-
TODO:
+ add counterexample to the docstring of `inner_map_self_eq_zero`.
+ prove `ext_inner_map` with the operators on the other side.
-/


instance instLoewnerPartialOrder : PartialOrder (H →L[𝕜] H) where
  le f g := (g - f).IsPositive
  le_refl _ := by simpa using isPositive_zero
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero]
    have h_isSymm := isSelfAdjoint_iff_isSymmetric.mp h₂.isSelfAdjoint
    exact_mod_cast h_isSymm.inner_map_self_eq_zero.mp fun x ↦ by
      apply IsROrC.ext
      · rw [map_zero]
        apply le_antisymm
        · rw [← neg_nonneg, ← map_neg, ← inner_neg_left]
          simpa using h₁.inner_nonneg_left _
        · exact h₂.inner_nonneg_left _
      · rw [coe_sub, LinearMap.sub_apply, coe_coe, coe_coe, map_zero, ← sub_apply,
          ← h_isSymm.coe_reApplyInnerSelf_apply (T := f₁ - f₂) x, IsROrC.ofReal_im]

lemma le_def (f g : H →L[𝕜] H) : f ≤ g ↔ (g - f).IsPositive := Iff.rfl

lemma nonneg_iff_isPositive (f : H →L[𝕜] H) : 0 ≤ f ↔ f.IsPositive := by
  simpa using le_def 0 f

end PartialOrder

section Banach

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]

open NNReal
lemma closed_range_of_antilipschitz {f : E →L[𝕜] F} {c : ℝ≥0} (hf : AntilipschitzWith c f) :
    (LinearMap.range f).topologicalClosure = LinearMap.range f :=
  SetLike.ext'_iff.mpr <| (hf.isClosed_range f.uniformContinuous).closure_eq

/-
[Mathlib.Analysis.NormedSpace.Completion]
-/
--#find_home closed_range_of_antilipschitz

open Function -- does ContinuousLinearMap.ofBijective generalize to semilinear?
lemma bijective_iff_dense_range_and_antilipschitz (f : E →L[𝕜] F) :
    Bijective f ↔ (LinearMap.range f).topologicalClosure = ⊤ ∧ ∃ c, AntilipschitzWith c f := by
  refine ⟨fun h ↦ ⟨?eq_top, ?anti⟩, fun ⟨hd, c, hf⟩ ↦ ⟨hf.injective, ?surj⟩⟩
  case eq_top => simpa [SetLike.ext'_iff] using h.2.denseRange.closure_eq
  case anti =>
    have := ContinuousLinearEquiv.ofBijective f ?_ ?_ |>.antilipschitz
    · exact ⟨_, by simpa⟩
    all_goals simp only [LinearMap.range_eq_top, LinearMapClass.ker_eq_bot]
    exacts [h.1, h.2]
  case surj => rwa [← LinearMap.range_eq_top, ← closed_range_of_antilipschitz hf]

/-
[Mathlib.Analysis.InnerProductSpace.Symmetric]
-/
-- #find_home! bijective_iff_denseRange_and_antilipschitz

lemma _root_.AntilipschitzWith.completeSpace_range_clm {f : E →L[𝕜] F} {c : ℝ≥0}
    (hf : AntilipschitzWith c f) : CompleteSpace (LinearMap.range f) :=
  IsClosed.completeSpace_coe <| hf.isClosed_range f.uniformContinuous

-- I guess this could also be semilinear
lemma isUnit_iff_bijective {f : E →L[𝕜] E} : IsUnit f ↔ Bijective f := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ContinuousLinearEquiv.unitsEquiv 𝕜 E f |>.bijective
  · intro h
    let e := ContinuousLinearEquiv.ofBijective f ?_ ?_
    · exact ⟨ContinuousLinearEquiv.unitsEquiv 𝕜 E |>.symm e, rfl⟩
    all_goals simp only [LinearMap.range_eq_top, LinearMapClass.ker_eq_bot]
    exacts [h.1, h.2]

end Banach

section IsROrC

open IsROrC
open scoped NNReal


lemma antilipschitz_of_forall_le_inner_map
    {𝕜 H : Type*} [IsROrC 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (f : H →L[𝕜] H) {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ x, ‖x‖ ^ 2 * c ≤ ‖⟪f x, x⟫_𝕜‖) : AntilipschitzWith c⁻¹ f := by
  let e : NormedAddGroupHom H H := AddMonoidHom.mkNormedAddGroupHom f ‖f‖ f.le_opNorm
  apply NormedAddGroupHom.antilipschitz_of_norm_ge e fun x ↦ ?_
  rw [NNReal.coe_inv, inv_mul_eq_div, le_div_iff (by exact_mod_cast hc)]
  simp_rw [sq, mul_assoc] at h
  by_cases hx0 : x = 0
  · simp [hx0]
  · apply (map_le_map_iff <| OrderIso.mulLeft₀ ‖x‖ (norm_pos_iff'.mpr hx0)).mp
    simp only [OrderIso.mulLeft₀_apply]
    apply (h x).trans
    apply (norm_inner_le_norm _ _).trans
    simp [mul_comm ‖x‖, e]

lemma isUnit_of_forall_le_inner_map
    {𝕜 H : Type*} [IsROrC 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (f : H →L[𝕜] H) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, ‖x‖ ^ 2 * c ≤ ‖⟪f x, x⟫_𝕜‖) : IsUnit f := by
  rw [isUnit_iff_bijective, bijective_iff_dense_range_and_antilipschitz]
  lift c to ℝ≥0 using hc.le
  have h_anti : AntilipschitzWith c⁻¹ f := antilipschitz_of_forall_le_inner_map f hc h
  refine ⟨?_, ⟨_, h_anti⟩⟩
  have _inst := h_anti.completeSpace_range_clm
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  have : ‖x‖ ^ 2 * c = 0 := le_antisymm (by simpa only [hx (f x) ⟨x, rfl⟩, norm_zero] using h x)
    (by positivity)
  aesop

lemma IsPositive.spectrumRestricts
    {𝕜 H : Type*} [IsROrC 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] (f : H →L[𝕜] H) (hf : f.IsPositive) :
    SpectrumRestricts f ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff]
  intro c hc
  contrapose! hc
  rw [spectrum.not_mem_iff, IsUnit.sub_iff, sub_eq_add_neg, ← map_neg]
  rw [← neg_pos] at hc
  set c := -c
  exact isUnit_of_forall_le_inner_map _ hc fun x ↦ calc
    ‖x‖ ^ 2 * c = re ⟪algebraMap ℝ (H →L[𝕜] H) c x, x⟫_𝕜 := by
      rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul 𝕜 c (1 : (H →L[𝕜] H)), coe_smul',
        Pi.smul_apply, one_apply, inner_smul_left, IsROrC.algebraMap_eq_ofReal, conj_ofReal,
        re_ofReal_mul, inner_self_eq_norm_sq, mul_comm]
    _ ≤ re ⟪(f + (algebraMap ℝ (H →L[𝕜] H)) c) x, x⟫_𝕜 := by
      simpa only [add_apply, inner_add_left, map_add, le_add_iff_nonneg_left] using hf.inner_nonneg_left x
    _ ≤ ‖⟪(f + (algebraMap ℝ (H →L[𝕜] H)) c) x, x⟫_𝕜‖ := IsROrC.re_le_norm _

variable {𝕜 H : Type*} [IsROrC 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
variable [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : (H →L[𝕜] H) → Prop)]

lemma _root_.CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts {A : Type*} [Ring A] [TopologicalSpace A] [StarRing A]
    [TopologicalRing A] [ContinuousStar A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal) :
    ∃ x : A, IsSelfAdjoint x ∧ SpectrumRestricts x ContinuousMap.realToNNReal ∧ x ^ 2 = a := by
  use cfc a Real.sqrt, cfc_predicate a Real.sqrt
  constructor
  · simpa only [SpectrumRestricts.nnreal_iff, cfc_map_spectrum a Real.sqrt, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] using fun x _ ↦ Real.sqrt_nonneg x
  · rw [← cfc_pow ..]
    nth_rw 2 [← cfc_id ℝ a]
    apply cfc_congr a fun x hx ↦ ?_
    rw [SpectrumRestricts.nnreal_iff] at ha₂
    apply ha₂ x at hx
    simp [Real.sq_sqrt hx]

attribute [fun_prop] Real.continuous_sqrt

@[reducible]
noncomputable def instStarOrderedRingIsROrC : StarOrderedRing (H →L[𝕜] H) where
  le_iff f g := by
    constructor
    · intro h
      rw [le_def] at h
      obtain ⟨p, hp₁, -, hp₃⟩ :=
        _root_.CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts h.1 h.spectrumRestricts
      refine ⟨p ^ 2, ?_, by symm; rwa [add_comm, ← eq_sub_iff_add_eq]⟩
      exact AddSubmonoid.subset_closure ⟨p, by simp only [hp₁.star_eq, sq]⟩
    · rintro ⟨p, hp, rfl⟩
      rw [le_def, add_sub_cancel']
      induction hp using AddSubmonoid.closure_induction' with
      | Hs _ hf =>
        obtain ⟨f, rfl⟩ := hf
        simpa using ContinuousLinearMap.IsPositive.adjoint_conj isPositive_one f
      | H1 => exact isPositive_zero
      | Hmul f _ g _ hf hg => exact hf.add hg

lemma isPositive_iff_isSelfAdjoint_and_spectrumRestricts (f : H →L[𝕜] H) :
    f.IsPositive ↔ IsSelfAdjoint f ∧ SpectrumRestricts f ContinuousMap.realToNNReal := by
  constructor
  · exact fun h ↦ ⟨h.1, h.spectrumRestricts⟩
  · rintro ⟨h₁, h₂⟩
    let inst := instStarOrderedRingIsROrC (𝕜 := 𝕜) (H := H)
    rw [← sub_zero f, ← le_def, StarOrderedRing.nonneg_iff]
    apply AddSubmonoid.subset_closure
    obtain ⟨p, hp₁, -, hp₃⟩ := _root_.CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts h₁ h₂
    exact ⟨p, by simpa [hp₁.star_eq] using hp₃⟩

end IsROrC

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable instance instStarOrderedRing : StarOrderedRing (H →L[ℂ] H) :=
  instStarOrderedRingIsROrC

open scoped NNReal
instance instNNRealContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ≥0 ((0 : H →L[ℂ] H) ≤ ·) :=
  SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal isometry_subtype_coe
    (by simp_rw [le_def, sub_zero, isPositive_iff_isSelfAdjoint_and_spectrumRestricts, imp_true_iff])
    (fun _ _ ↦ inferInstance)

end Complex

end ContinuousLinearMap
