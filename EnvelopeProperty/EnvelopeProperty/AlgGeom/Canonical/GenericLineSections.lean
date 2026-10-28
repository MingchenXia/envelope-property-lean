import EnvelopeProperty.AlgGeom.Canonical.LineBundleSections
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-! # Actual line-bundle sections at the generic point

Integral-scheme geometry and genuine local sheaf frames imply injectivity of
restrictions and global generic evaluation. The function field is Mathlib's
actual generic structure-sheaf stalk, not an unrelated field supplied as data.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace EnvelopeProperty.CanonicalGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- Actual bundle sections use the usual scheme section ring. -/
instance schemeBundleSectionsModule (L : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (bundleSections L U) :=
  inferInstanceAs (Module (X.sheaf.obj.obj (op U)) (bundleSections L U))

/-- The top open is nonempty because an integral scheme has a generic point. -/
instance integralSchemeTopNonempty : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- Express a genuine frame on a smaller open with the ordinary section-ring notation. -/
def localFrameCoefficientsOn {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    bundleSections L V ≃ₗ[Γ(X, V)] Γ(X, V) := e.coefficients i

omit [IsIntegral X] in
/-- The genuine coefficient frames retain actual restriction compatibility. -/
theorem localFrameCoefficientsOn_restrict {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (j : W ⟶ V) (s : bundleSections L V) :
    localFrameCoefficientsOn e (j ≫ i) (L.val.map j.op s) =
      X.presheaf.map j.op (localFrameCoefficientsOn e i s) :=
  e.coefficients_restrict i j s

/-- Express a genuine frame using the ordinary section-ring notation. -/
def localFrameCoefficients {L : X.Modules} {U : X.Opens} (e : LocalBundleFrame L U) :
    bundleSections L U ≃ₗ[Γ(X, U)] Γ(X, U) := localFrameCoefficientsOn e (𝟙 U)

/-- The actual generic point belongs to every nonempty open. -/
theorem genericPoint_mem_nonempty_open (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- A genuine line-bundle atlas on an integral scheme derives injectivity of
restriction to every nonempty smaller open. -/
theorem LineBundleAtlas.restriction_injective {L : X.Modules} (a : LineBundleAtlas L)
    {U V : X.Opens} (i : V ⟶ U) [Nonempty V] : Function.Injective (L.val.map i.op) := by
  intro s t h
  apply TopCat.Presheaf.IsSheaf.section_ext (F := L.val.presheaf) L.isSheaf
  intro x hx
  obtain ⟨k, hk⟩ := a.covers x
  let W := U ⊓ a.opens k
  let Z := V ⊓ W
  let iw : W ⟶ U := homOfLE inf_le_left
  let jf : W ⟶ a.opens k := homOfLE inf_le_right
  let jz : Z ⟶ W := homOfLE inf_le_right
  let jv : Z ⟶ V := homOfLE inf_le_left
  have : Nonempty W := ⟨⟨x, hx, hk⟩⟩
  have : Nonempty Z := ⟨⟨genericPoint X,
    genericPoint_mem_nonempty_open V, genericPoint_mem_nonempty_open W⟩⟩
  refine ⟨W, inf_le_left, ⟨hx, hk⟩, ?_⟩
  apply ((a.frame k).coefficients jf).injective
  apply map_injective_of_isIntegral X jz
  change X.sheaf.obj.map jz.op
      ((a.frame k).coefficients jf (L.val.map iw.op s)) =
    X.sheaf.obj.map jz.op ((a.frame k).coefficients jf (L.val.map iw.op t))
  rw [← (a.frame k).coefficients_restrict jf jz,
    ← (a.frame k).coefficients_restrict jf jz]
  apply congrArg ((a.frame k).coefficients (jz ≫ jf))
  have hi : jz ≫ iw = jv ≫ i := Subsingleton.elim _ _
  have hz := congrArg (L.val.presheaf.map jv.op) h
  change L.val.presheaf.map jv.op (L.val.presheaf.map i.op s) =
    L.val.presheaf.map jv.op (L.val.presheaf.map i.op t) at hz
  change L.val.presheaf.map jz.op (L.val.presheaf.map iw.op s) =
    L.val.presheaf.map jz.op (L.val.presheaf.map iw.op t)
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hi] using hz

/-- Actual structure-ring germs commute with actual restrictions to nonempty opens. -/
theorem germToFunctionField_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : V ⟶ U) (r : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map i.op r) = X.germToFunctionField U r := by
  exact X.presheaf.germ_res_apply i (genericPoint X)
    (genericPoint_mem_nonempty_open V) r

/-- Coefficients in a genuine local frame give an actual linear map into the
scheme's function field. -/
def LocalBundleFrame.toFunctionField {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) : bundleSections L U →ₗ[Γ(X, U)] X.functionField :=
  (Algebra.linearMap Γ(X, U) X.functionField).comp (localFrameCoefficients e).toLinearMap

/-- Integral regular-germ injectivity and the actual frame derive faithful
local generic evaluation. -/
theorem LocalBundleFrame.toFunctionField_injective {L : X.Modules} {U : X.Opens}
    [Nonempty U] (e : LocalBundleFrame L U) : Function.Injective e.toFunctionField :=
  (X.germToFunctionField_injective U).comp (localFrameCoefficients e).injective

/-- Actual global sections are evaluated by restriction, a genuine local frame,
and the actual function-field germ. -/
def globalSectionToFunctionField {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) : bundleSections L ⊤ →ₗ[Γ(X, ⊤)] X.functionField where
  toFun s := e.toFunctionField (L.val.map (homOfLE le_top).op s)
  map_add' s t := by
    rw [(L.val.map (homOfLE le_top).op).hom.map_add, map_add]
  map_smul' r s := by
    change X.germToFunctionField U
      (localFrameCoefficients e (L.val.map (homOfLE le_top).op (r • s))) = _
    rw [L.val.map_smul]
    change X.germToFunctionField U
      (localFrameCoefficients e (X.presheaf.map (homOfLE le_top).op r •
        L.val.map (homOfLE le_top).op s)) = _
    rw [(localFrameCoefficients e).map_smul]
    change X.germToFunctionField U
      (X.presheaf.map (homOfLE le_top).op r *
        localFrameCoefficients e (L.val.map (homOfLE le_top).op s)) = _
    rw [map_mul, germToFunctionField_restrict]
    rfl

/-- Global faithful evaluation is derived, rather than supplied as a premise. -/
theorem globalSectionToFunctionField_injective {L : X.Modules} (a : LineBundleAtlas L)
    {U : X.Opens} [Nonempty U] (e : LocalBundleFrame L U) :
    Function.Injective (globalSectionToFunctionField e) :=
  e.toFunctionField_injective.comp (a.restriction_injective (homOfLE le_top))

/-- The atlas supplies an actual frame open containing the generic point. -/
theorem LineBundleAtlas.exists_generic_frame {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ (U : X.Opens) (_ : genericPoint X ∈ U), Nonempty (LocalBundleFrame L U) := by
  obtain ⟨i, hi⟩ := a.covers (genericPoint X)
  exact ⟨a.opens i, hi, ⟨a.frame i⟩⟩

/-- The generic fiber is the actual module-sheaf stalk at the actual generic point. -/
abbrev genericBundleFiber (L : X.Modules) : Type u := L.presheaf.stalk (genericPoint X)

/-- The generic fiber uses Mathlib's native module action by the generic structure stalk. -/
instance genericBundleFiberModule (L : X.Modules) :
    Module X.functionField (genericBundleFiber L) :=
  inferInstanceAs (Module (↑(X.presheaf.stalk (genericPoint X)))
    ↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint X)))

/-- The actual module-sheaf germ, semilinear along the actual function-field germ. -/
def bundleGenericGerm (L : X.Modules) (U : X.Opens) [Nonempty U] :
    bundleSections L U →ₛₗ[(X.germToFunctionField U).hom] genericBundleFiber L where
  toFun s := L.presheaf.germ U (genericPoint X) (genericPoint_mem_nonempty_open U) s
  map_add' s t := (L.presheaf.germ U (genericPoint X) _).hom.map_add s t
  map_smul' r s := L.val.germ_smul (R := X.presheaf) (genericPoint X) U _ r s

/-- The actual generic germ of the section with local coefficient one. -/
def genericFrameGenerator {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) : genericBundleFiber L :=
  bundleGenericGerm L U ((localFrameCoefficients e).symm 1)

/-- The generic generator is nonzero, derived from genuine local frame coefficients. -/
theorem genericFrameGenerator_ne_zero {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) : genericFrameGenerator e ≠ 0 := by
  intro h
  change L.presheaf.germ U (genericPoint X) (genericPoint_mem_nonempty_open U)
    ((localFrameCoefficients e).symm 1) = 0 at h
  have hz : L.presheaf.germ U (genericPoint X) (genericPoint_mem_nonempty_open U)
      ((localFrameCoefficients e).symm 1) =
    L.presheaf.germ U (genericPoint X) (genericPoint_mem_nonempty_open U) 0 := by
    simpa only [map_zero] using h
  obtain ⟨W, hW, i, j, heq⟩ := L.presheaf.germ_eq _ _ _ _ _ hz
  cases Subsingleton.elim i j
  have : Nonempty W := ⟨⟨genericPoint X, hW⟩⟩
  have hc := congrArg (localFrameCoefficientsOn e i) heq
  change localFrameCoefficientsOn e i (L.val.map i.op ((localFrameCoefficients e).symm 1)) =
    localFrameCoefficientsOn e i (L.val.map i.op 0) at hc
  have hn := localFrameCoefficientsOn_restrict e (𝟙 U) i ((localFrameCoefficients e).symm 1)
  have hi : i ≫ 𝟙 U = i := Category.comp_id i
  rw [hi] at hn
  rw [hn] at hc
  have hf : localFrameCoefficientsOn e (𝟙 U) ((localFrameCoefficients e).symm 1) = 1 :=
    (localFrameCoefficients e).apply_symm_apply 1
  rw [hf] at hc
  have : (1 : Γ(X, W)) = 0 := by simpa only [map_one, map_zero] using hc
  exact one_ne_zero this

/-- Actual stalk representatives and frame naturality make the generic fiber cyclic. -/
theorem genericBundleFiber_eq_smul_generator {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) (m : genericBundleFiber L) :
    ∃ r : X.functionField, m = r • genericFrameGenerator e := by
  obtain ⟨W, hW, t, ht⟩ := L.presheaf.exists_germ_eq m
  let Z := W ⊓ U
  let iw : Z ⟶ W := homOfLE inf_le_left
  let iu : Z ⟶ U := homOfLE inf_le_right
  have : Nonempty Z := ⟨⟨genericPoint X, hW, genericPoint_mem_nonempty_open U⟩⟩
  let m₀ := (localFrameCoefficients e).symm 1
  let r : Γ(X, Z) := localFrameCoefficientsOn e iu (L.val.map iw.op t)
  have hlocal : L.val.map iw.op t = r • L.val.map iu.op m₀ := by
    apply (localFrameCoefficientsOn e iu).injective
    have hn := localFrameCoefficientsOn_restrict e (𝟙 U) iu m₀
    rw [Category.comp_id] at hn
    rw [map_smul, hn]
    have hf : localFrameCoefficientsOn e (𝟙 U) m₀ = 1 :=
      (localFrameCoefficients e).apply_symm_apply 1
    rw [hf]
    change r = r * X.presheaf.map iu.op 1
    simp only [map_one, mul_one]
  refine ⟨X.germToFunctionField Z r, ?_⟩
  have hg := congrArg (bundleGenericGerm L Z) hlocal
  rw [(bundleGenericGerm L Z).map_smulₛₗ] at hg
  have hl : bundleGenericGerm L Z (L.val.map iw.op t) = m := by
    exact (L.presheaf.germ_res_apply iw (genericPoint X)
      (genericPoint_mem_nonempty_open Z) t).trans ht
  have hr : bundleGenericGerm L Z (L.val.map iu.op m₀) = genericFrameGenerator e := by
    exact L.presheaf.germ_res_apply iu (genericPoint X)
      (genericPoint_mem_nonempty_open Z) m₀
  rw [hl, hr] at hg
  exact hg

/-- The genuine generic frame identifies the actual stalk with the actual function field. -/
def genericBundleFiberFrame {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) : genericBundleFiber L ≃ₗ[X.functionField] X.functionField :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton X.functionField (genericBundleFiber L) (genericFrameGenerator e))
    ⟨by
      intro r s h
      change r • genericFrameGenerator e = s • genericFrameGenerator e at h
      exact (smul_left_injective X.functionField (genericFrameGenerator_ne_zero e)) h,
      by
        intro m
        obtain ⟨r, hr⟩ := genericBundleFiber_eq_smul_generator e m
        exact ⟨r, hr.symm⟩⟩).symm


/-- In the produced generic frame, the local coefficient is the actual germ scalar. -/
theorem bundleGenericGerm_eq_coefficient_smul_generator {L : X.Modules}
    {U : X.Opens} [Nonempty U] (e : LocalBundleFrame L U) (s : bundleSections L U) :
    bundleGenericGerm L U s = e.toFunctionField s • genericFrameGenerator e := by
  have hs : s = localFrameCoefficients e s • (localFrameCoefficients e).symm 1 := by
    apply (localFrameCoefficients e).injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact (mul_one _).symm
  have hg := congrArg (bundleGenericGerm L U) hs
  rw [(bundleGenericGerm L U).map_smulₛₗ] at hg
  exact hg

/-- The inverse actual generic frame sends a scalar to its multiple of the actual generator. -/
theorem genericBundleFiberFrame_symm_apply {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) (r : X.functionField) :
    (genericBundleFiberFrame e).symm r = r • genericFrameGenerator e := rfl

/-- Actual local germs have exactly their actual frame coefficients in the generic fiber. -/
theorem genericBundleFiberFrame_germ {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) (s : bundleSections L U) :
    genericBundleFiberFrame e (bundleGenericGerm L U s) = e.toFunctionField s := by
  rw [bundleGenericGerm_eq_coefficient_smul_generator e s,
    ← genericBundleFiberFrame_symm_apply]
  exact (genericBundleFiberFrame e).apply_symm_apply _

/-- The global coefficient representation is the actual global generic germ in its genuine frame. -/
theorem genericBundleFiberFrame_global_germ {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) (s : bundleSections L ⊤) :
    genericBundleFiberFrame e (bundleGenericGerm L ⊤ s) =
      globalSectionToFunctionField e s := by
  have hr : bundleGenericGerm L U (L.val.map (homOfLE le_top).op s) =
      bundleGenericGerm L ⊤ s :=
    L.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X)
      (genericPoint_mem_nonempty_open U) s
  rw [← hr, genericBundleFiberFrame_germ]
  rfl

/-- A genuine atlas derives injectivity of the actual global generic-stalk map. -/
theorem bundleGenericGerm_global_injective {L : X.Modules} (a : LineBundleAtlas L) :
    Function.Injective (bundleGenericGerm L ⊤) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := a.exists_generic_frame
  have : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  intro s t h
  apply globalSectionToFunctionField_injective a e
  simpa only [genericBundleFiberFrame_global_germ] using congrArg (genericBundleFiberFrame e) h

/-- The generic fiber's actual singleton basis is derived from its genuine local frame. -/
def genericBundleFiberBasis {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) : Module.Basis Unit X.functionField (genericBundleFiber L) :=
  (Module.Basis.singleton Unit X.functionField).map (genericBundleFiberFrame e).symm

/-- The actual generic fiber is finite free and one-dimensional over the actual function field. -/
theorem genericBundleFiber_finite_free_rank_one {L : X.Modules} {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) :
    Module.Finite X.functionField (genericBundleFiber L) ∧
      Module.Free X.functionField (genericBundleFiber L) ∧
      Module.finrank X.functionField (genericBundleFiber L) = 1 := by
  refine ⟨Module.Finite.of_basis (genericBundleFiberBasis e),
    Module.Free.of_basis (genericBundleFiberBasis e), ?_⟩
  simpa only [Fintype.card_unit] using Module.finrank_eq_card_basis (genericBundleFiberBasis e)

end
end EnvelopeProperty.CanonicalGeometry
