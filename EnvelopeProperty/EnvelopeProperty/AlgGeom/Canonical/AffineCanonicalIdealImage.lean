import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalFrame
import EnvelopeProperty.AlgGeom.SchemeFramedIdealImage

/-! # The original whole affine differential and actual ideal containment -/

open CategoryTheory AlgebraicGeometry Opposite

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual original top-wedge coordinate is EXACTLY the full original
volume coordinate used by the intrinsic all-source-functions Jacobian ideal. -/
theorem affineCanonicalTrivialization_eq_differentialVolumeEquiv
    {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    affineCanonicalTrivialization b = Char0.differentialVolumeEquiv b := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (exteriorPower.ιMulti_span A n (KaehlerDifferential k A))
  intro η
  change affineCanonicalTrivialization b (exteriorPower.ιMulti A n η) =
    Char0.differentialVolumeCoordinate b (exteriorPower.ιMulti A n η)
  rw [affineCanonicalTrivialization_apply_wedge]
  rw [Char0.differentialVolumeCoordinate, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Module.Basis.det_apply]
  change (b.toMatrix η).transpose.det = (b.toMatrix η).det
  exact Matrix.det_transpose _

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]

/-- ENTIRE factorization of the SAME original exterior differential through
an actual ideal tensor is exactly containment of EVERY original raw extended
form's genuine coefficient in the SAME original affine ideal. -/
theorem affineCanonicalMap_factorization_iff_rawCoefficients
    (bX : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (bY : letI := affineChartAlgebra (g ≫ f) ⊤
      Module.Basis (Fin n) Γ(Y, ⊤) (KaehlerDifferential k Γ(Y, ⊤)))
    (I : Y.IdealSheafData) :
    letI := affineChartAlgebra (g ≫ f) ⊤
    (∃ θ : (Scheme.Modules.pullback g).obj (canonicalLineSheaf f n) ⟶
        Scheme.Modules.tensorObj (canonicalLineSheaf (g ≫ f) n) I.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (canonicalLineSheaf (g ≫ f) n)
          I.toModules I.toModulesInclusion = exteriorCotangentSheafPullbackMap f g n) ↔
    ∀ z : (ModuleCat.extendScalars g.appTop.hom).obj
        ((exteriorCotangentPresheaf f n).obj (.op ⊤)),
      affineCanonicalTrivialization bY (exteriorCotangentRawBaseChangeMorphism f g n z) ∈
        I.ideal ⟨⊤, isAffineOpen_top Y⟩ := by
  let := affineChartAlgebra (g ≫ f) ⊤
  let A := (Scheme.Modules.pullback g).obj (canonicalLineSheaf f n)
  let B := canonicalLineSheaf (g ≫ f) n
  let : (canonicalLineSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : ((Scheme.Modules.pullback g).obj (exteriorCotangentSheaf f n)).IsQuasicoherent :=
    ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
  let : A.IsQuasicoherent := ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
  refine (SchemeFramedIdealImage.factorization_iff_affine_ideal B
    (affineCanonicalFrameIso (g ≫ f) n bY) I
      (exteriorCotangentSheafPullbackMap f g n)).trans ?_
  let uX := (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)
  have huX : Function.Bijective uX :=
    affineChartExteriorSheafificationMap_bijective f (isAffineOpen_top X) bX n
  let eX := (LinearEquiv.ofBijective uX.hom huX).toModuleIso
  let e := (ModuleCat.extendScalars g.appTop.hom).mapIso eX ≪≫
    Scheme.Modules.affinePullbackΓIso g (canonicalLineSheaf f n)
  have he : Function.Surjective e.hom := (ConcreteCategory.bijective_of_isIso e.hom).2
  have hcalc (z : (ModuleCat.extendScalars g.appTop.hom).obj
      ((exteriorCotangentPresheaf f n).obj (.op ⊤))) :
      (affineCanonicalFrameIso (g ≫ f) n bY).hom.app ⊤
        ((exteriorCotangentSheafPullbackMap f g n).app ⊤ (e.hom z)) =
      affineCanonicalTrivialization bY (exteriorCotangentRawBaseChangeMorphism f g n z) := by
    have hunit := ConcreteCategory.congr_hom (nativeAffineCanonicalDifferential_unit f g n) z
    change (exteriorCotangentSheafPullbackMap f g n).app ⊤ (e.hom z) =
      (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤)
        (exteriorCotangentRawBaseChangeMorphism f g n z) at hunit
    exact (congrArg ((affineCanonicalFrameIso (g ≫ f) n bY).hom.app ⊤) hunit).trans
      (affineCanonicalFrameIso_hom_unit (g ≫ f) n bY _)
  constructor
  · intro h z
    exact Eq.mp (congrArg (fun a : Γ(Y, ⊤) => a ∈ I.ideal ⟨⊤, isAffineOpen_top Y⟩)
      (hcalc z)) (h (e.hom z))
  · intro h x
    obtain ⟨z, rfl⟩ := he x
    exact Eq.mpr (congrArg (fun a : Γ(Y, ⊤) => a ∈ I.ideal ⟨⊤, isAffineOpen_top Y⟩)
      (hcalc z)) (h z)

/-- ENTIRE factorization of the SAME original canonical differential is
precisely inclusion of the SAME ALL-original-source-functions Jacobian ideal
in the SAME actual original affine ideal. No discrepancy/image-match premise. -/
theorem affineCanonicalMap_factorization_iff_jacobianIdeal
    (bX : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (bY : letI := affineChartAlgebra (g ≫ f) ⊤
      Module.Basis (Fin n) Γ(Y, ⊤) (KaehlerDifferential k Γ(Y, ⊤)))
    (I : Y.IdealSheafData) :
    letI := affineChartAlgebra (g ≫ f) ⊤
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    (∃ θ : (Scheme.Modules.pullback g).obj (canonicalLineSheaf f n) ⟶
        Scheme.Modules.tensorObj (canonicalLineSheaf (g ≫ f) n) I.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (canonicalLineSheaf (g ≫ f) n)
          I.toModules I.toModulesInclusion = exteriorCotangentSheafPullbackMap f g n) ↔
      Char0.affineRelativeJacobianIdeal (R := Γ(X, ⊤)) bY ≤ I.ideal ⟨⊤, isAffineOpen_top Y⟩ := by
  let : Algebra k Γ(X, ⊤) := affineChartAlgebra f ⊤
  let : Algebra k Γ(Y, ⊤) := affineChartAlgebra (g ≫ f) ⊤
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  refine (affineCanonicalMap_factorization_iff_rawCoefficients f g n bX bY I).trans ?_
  let c := (affineCanonicalTrivialization bY).toLinearMap.comp
    (exteriorCotangentRawBaseChangeMorphism f g n).hom
  have hc : LinearMap.range c =
      (Char0.affineRelativeJacobianIdeal (R := Γ(X, ⊤)) bY : Submodule Γ(Y, ⊤) Γ(Y, ⊤)) := by
    rw [LinearMap.range_comp, range_exteriorCotangentRawBaseChangeMorphism]
    change (Char0.affineCanonicalDifferentialImage (k := k) (R := Γ(X, ⊤)) (A := Γ(Y, ⊤)) n).map
      (affineCanonicalTrivialization bY).toLinearMap = _
    rw [affineCanonicalTrivialization_eq_differentialVolumeEquiv]
    exact Char0.map_affineCanonicalDifferentialImage bY
  constructor
  · intro h a ha
    have hr : a ∈ LinearMap.range c := Eq.mpr (congrArg (fun N => a ∈ N) hc) ha
    obtain ⟨z, hz⟩ := hr
    exact Eq.mp (congrArg (fun x : Γ(Y, ⊤) => x ∈ I.ideal ⟨⊤, isAffineOpen_top Y⟩) hz) (h z)
  · intro h z
    apply h
    exact Eq.mp (congrArg (fun N => c z ∈ N) hc) (LinearMap.mem_range_self c z)

end
end EnvelopeProperty.CanonicalGeometry
