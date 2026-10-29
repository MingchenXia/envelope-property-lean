import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalIdealImage
import EnvelopeProperty.AlgGeom.SchemeUnitScalarAction
import Mathlib.RingTheory.Ideal.Colon

/-! # Every original scalar times the entire canonical differential -/

open CategoryTheory AlgebraicGeometry Opposite

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]

/-- EVERY original scalar times the ENTIRE original exterior differential
factors through the SAME actual ideal tensor iff EVERY original raw image's
actual coefficient multiplied by SAME original scalar lies in SAME affine ideal. -/
theorem affineCanonicalScalar_factorization_iff_rawCoefficients
    (bX : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (bY : letI := affineChartAlgebra (g ≫ f) ⊤
      Module.Basis (Fin n) Γ(Y, ⊤) (KaehlerDifferential k Γ(Y, ⊤)))
    (I : Y.IdealSheafData) (a : Γ(Y, ⊤)) :
    letI := affineChartAlgebra (g ≫ f) ⊤
    (∃ θ : (Scheme.Modules.pullback g).obj (canonicalLineSheaf f n) ⟶
        Scheme.Modules.tensorObj (canonicalLineSheaf (g ≫ f) n) I.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (canonicalLineSheaf (g ≫ f) n)
          I.toModules I.toModulesInclusion =
        SchemeUnitScalarAction.globalScalarAction _ a ≫ exteriorCotangentSheafPullbackMap f g n) ↔
    ∀ z : (ModuleCat.extendScalars g.appTop.hom).obj
        ((exteriorCotangentPresheaf f n).obj (.op ⊤)),
      a * affineCanonicalTrivialization bY (exteriorCotangentRawBaseChangeMorphism f g n z) ∈
        I.ideal ⟨⊤, isAffineOpen_top Y⟩ := by
  let := affineChartAlgebra (g ≫ f) ⊤
  let A := (Scheme.Modules.pullback g).obj (canonicalLineSheaf f n)
  let B := canonicalLineSheaf (g ≫ f) n
  let : (canonicalLineSheaf f n).IsQuasicoherent := (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : (exteriorCotangentSheaf f n).IsQuasicoherent := (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : ((Scheme.Modules.pullback g).obj (exteriorCotangentSheaf f n)).IsQuasicoherent :=
    ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
  let : A.IsQuasicoherent := ((canonicalLineSheaf_isInvertible f n).pullback g).isQuasicoherent
  let φ := SchemeUnitScalarAction.globalScalarAction A a ≫ exteriorCotangentSheafPullbackMap f g n
  refine (SchemeFramedIdealImage.factorization_iff_affine_ideal B
    (affineCanonicalFrameIso (g ≫ f) n bY) I φ).trans ?_
  let uX := (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)
  have huX : Function.Bijective uX :=
    affineChartExteriorSheafificationMap_bijective f (isAffineOpen_top X) bX n
  let eX := (LinearEquiv.ofBijective uX.hom huX).toModuleIso
  let e := (ModuleCat.extendScalars g.appTop.hom).mapIso eX ≪≫
    Scheme.Modules.affinePullbackΓIso g (canonicalLineSheaf f n)
  have he : Function.Surjective e.hom := (ConcreteCategory.bijective_of_isIso e.hom).2
  have hcalc (z : (ModuleCat.extendScalars g.appTop.hom).obj
      ((exteriorCotangentPresheaf f n).obj (.op ⊤))) :
      (affineCanonicalFrameIso (g ≫ f) n bY).hom.app ⊤ (φ.app ⊤ (e.hom z)) =
      a * affineCanonicalTrivialization bY (exteriorCotangentRawBaseChangeMorphism f g n z) := by
    have hunit := ConcreteCategory.congr_hom (nativeAffineCanonicalDifferential_unit f g n) z
    change (exteriorCotangentSheafPullbackMap f g n).app ⊤ (e.hom z) =
      (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤)
        (exteriorCotangentRawBaseChangeMorphism f g n z) at hunit
    have hact : (SchemeUnitScalarAction.globalScalarAction A a).val.app (.op ⊤) (e.hom z) =
        a • (e.hom z) := by
      simpa using SchemeUnitScalarAction.globalScalarAction_apply A a ⊤ (e.hom z)
    change (affineCanonicalFrameIso (g ≫ f) n bY).hom.val.app (.op ⊤)
      ((exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)
        ((SchemeUnitScalarAction.globalScalarAction A a).val.app (.op ⊤) (e.hom z))) = _
    rw [hact, ((exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)).hom.map_smul,
      ((affineCanonicalFrameIso (g ≫ f) n bY).hom.val.app (.op ⊤)).hom.map_smul]
    have hcoeff := (congrArg ((affineCanonicalFrameIso (g ≫ f) n bY).hom.app ⊤) hunit).trans
      (affineCanonicalFrameIso_hom_unit (g ≫ f) n bY _)
    exact congrArg (fun c : Γ(Y, ⊤) => a * c) hcoeff
  constructor
  · intro h z
    exact Eq.mp (congrArg (fun c : Γ(Y, ⊤) => c ∈ I.ideal ⟨⊤, isAffineOpen_top Y⟩)
      (hcalc z)) (h (e.hom z))
  · intro h x
    obtain ⟨z, rfl⟩ := he x
    exact Eq.mpr (congrArg (fun c : Γ(Y, ⊤) => c ∈ I.ideal ⟨⊤, isAffineOpen_top Y⟩)
      (hcalc z)) (h z)

/-- EVERY original scalar's ENTIRE differential factorization is exactly
membership in the SAME actual affine ideal colon the FULL original-source Jacobian ideal. -/
theorem affineCanonicalScalar_factorization_iff_colon
    (bX : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (bY : letI := affineChartAlgebra (g ≫ f) ⊤
      Module.Basis (Fin n) Γ(Y, ⊤) (KaehlerDifferential k Γ(Y, ⊤)))
    (I : Y.IdealSheafData) (a : Γ(Y, ⊤)) :
    letI := affineChartAlgebra (g ≫ f) ⊤
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    (∃ θ : (Scheme.Modules.pullback g).obj (canonicalLineSheaf f n) ⟶
        Scheme.Modules.tensorObj (canonicalLineSheaf (g ≫ f) n) I.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (canonicalLineSheaf (g ≫ f) n)
          I.toModules I.toModulesInclusion =
        SchemeUnitScalarAction.globalScalarAction _ a ≫ exteriorCotangentSheafPullbackMap f g n) ↔
      a ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩).colon
        (Char0.affineRelativeJacobianIdeal (R := Γ(X, ⊤)) bY : Set Γ(Y, ⊤)) := by
  let : Algebra k Γ(Y, ⊤) := affineChartAlgebra (g ≫ f) ⊤
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  refine (affineCanonicalScalar_factorization_iff_rawCoefficients f g n bX bY I a).trans ?_
  let c := (affineCanonicalTrivialization bY).toLinearMap.comp
    (exteriorCotangentRawBaseChangeMorphism f g n).hom
  have hc : LinearMap.range c =
      (Char0.affineRelativeJacobianIdeal (R := Γ(X, ⊤)) bY : Submodule Γ(Y, ⊤) Γ(Y, ⊤)) := by
    rw [LinearMap.range_comp, range_exteriorCotangentRawBaseChangeMorphism]
    change (Char0.affineCanonicalDifferentialImage (k := k) (R := Γ(X, ⊤)) (A := Γ(Y, ⊤)) n).map
      (affineCanonicalTrivialization bY).toLinearMap = _
    rw [affineCanonicalTrivialization_eq_differentialVolumeEquiv]
    exact Char0.map_affineCanonicalDifferentialImage bY
  rw [Submodule.mem_colon]
  constructor
  · intro h b hb
    have hr : b ∈ LinearMap.range c := Eq.mpr (congrArg (fun N => b ∈ N) hc) hb
    obtain ⟨z, hz⟩ := hr
    exact Eq.mp (congrArg (fun x : Γ(Y, ⊤) => a * x ∈ I.ideal ⟨⊤, isAffineOpen_top Y⟩) hz) (h z)
  · intro h z
    exact h (c z) (Eq.mp (congrArg (fun N : Submodule Γ(Y, ⊤) Γ(Y, ⊤) => c z ∈ N) hc) (LinearMap.mem_range_self c z))

end
end EnvelopeProperty.CanonicalGeometry
