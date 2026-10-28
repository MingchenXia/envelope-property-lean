import EnvelopeProperty.Char0.RoundedCanonicalDifferentialFactorization
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalScalarImage

/-! # EVERY original function in the SAME rounded canonical quotient -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem originalSectionHom_eq_zero_iff {Y : Scheme.{u}} (M : Y.Modules)
    (s : Γ(M, ⊤)) : SchemeModuleGlobalSections.sectionHom M s = 0 ↔ s = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun e => e.val.app (.op (⊤ : Y.Opens)) (show Γ(Y, ⊤) from 1)) h
    change (1 : Γ(Y, ⊤)) • M.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op s = 0 at h1
    simpa using h1
  · rintro rfl
    apply Scheme.Modules.hom_ext
    intro U
    ext a
    change (show Γ(Y, U) from a) • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 0 = 0
    rw [map_zero, smul_zero]

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- EVERY actual original function is killed by the SAME original rounded
quotient differential iff its SAME actual whole scalar differential map
factors through the SAME original absolute rounded canonical module. -/
theorem quotientDifferentialSection_apply_eq_zero_iff_factorization
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a : Γ(Y, ⊤)) :
    (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) a = 0 ↔
      ∃ θ : (Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n) ⟶
          absolute (g ≫ f) n J hJ q,
        θ ≫ absoluteRoundedInclusion (g ≫ f) n J hJ q =
          SchemeUnitScalarAction.globalScalarAction _ a ≫
            CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n := by
  let A := (Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n)
  let B := CanonicalGeometry.canonicalLineSheaf (g ≫ f) n
  let hA := (CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g
  let r := SchemeModuleGlobalSections.sectionHom (Scheme.Modules.unitObj Y) a
  let d := differentialSection f g n
  let π := quotientProjection f g n J hJ q
  let inc := relativeRoundedInclusion f g n J hJ q
  let : Mono inc := mono_relativeRoundedInclusion f g n J hJ q
  let T := ShortComplex.mk inc π (relativeRoundedInclusion_quotientProjection f g n J hJ q)
  have he : T.Exact := ShortComplex.exact_cokernel _
  have hcomp : (r ≫ d) ≫ π = SchemeModuleGlobalSections.sectionHom
      (quotient f g n J hJ q)
      ((quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) a) :=
    by
      have h0 := SchemeModuleGlobalSections.sectionHom_comp (M := Scheme.Modules.unitObj Y)
        (show Γ(Scheme.Modules.unitObj Y, ⊤) from a) (quotientDifferentialSection f g n J hJ q)
      change r ≫ (d ≫ π) = _ at h0
      simpa only [Category.assoc] using h0
  have hz : (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) a = 0 ↔
      (r ≫ d) ≫ π = 0 := by
    constructor
    · intro h
      exact hcomp.trans ((originalSectionHom_eq_zero_iff _ _).mpr h)
    · intro h
      exact (originalSectionHom_eq_zero_iff _ _).mp (hcomp.symm.trans h)
  have hl : (r ≫ d) ≫ π = 0 ↔
      ∃ s : Scheme.Modules.unitObj Y ⟶ relativeRounded f g n J hJ q,
        s ≫ inc = r ≫ d := by
    constructor
    · intro h
      exact he.lift' (r ≫ d) h
    · rintro ⟨s, hs⟩
      rw [← hs, Category.assoc]
      have hzero : inc ≫ π = 0 := T.zero
      rw [hzero, comp_zero]
  have hf := SchemeInvertibleHomSection.equiv_ideal_lift_iff A hA B
    (idealModule J hJ q) (idealModuleInclusion J hJ q)
    (SchemeUnitScalarAction.globalScalarAction A a ≫
      CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)
  have hnat : SchemeInvertibleHomSection.equiv A hA B
      (SchemeUnitScalarAction.globalScalarAction A a ≫
        CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n) = r ≫ d :=
    SchemeUnitScalarAction.unitAction_equiv A hA B r
      (CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)
  rw [hnat] at hf
  exact hz.trans (hl.trans hf)

/-- On actual original affine smooth charts, the SAME original quotient
kills EVERY original function exactly when it belongs to SAME actual rounded
affine ideal colon the FULL ALL-original-source-functions Jacobian ideal. -/
theorem quotientDifferentialSection_apply_eq_zero_iff_affine_colon
    [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (bX : letI := CanonicalGeometry.affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (bY : letI := CanonicalGeometry.affineChartAlgebra (g ≫ f) ⊤
      Module.Basis (Fin n) Γ(Y, ⊤) (KaehlerDifferential k Γ(Y, ⊤)))
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a : Γ(Y, ⊤)) :
    letI := CanonicalGeometry.affineChartAlgebra (g ≫ f) ⊤
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) a = 0 ↔
      a ∈ ((RoundedSncIdealSheaf.rounded J hJ q).ideal ⟨⊤, isAffineOpen_top Y⟩).colon
        (affineRelativeJacobianIdeal (R := Γ(X, ⊤)) bY : Set Γ(Y, ⊤)) :=
  (quotientDifferentialSection_apply_eq_zero_iff_factorization f g n J hJ q a).trans
    (CanonicalGeometry.affineCanonicalScalar_factorization_iff_colon f g n bX bY
      (RoundedSncIdealSheaf.rounded J hJ q) a)

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
