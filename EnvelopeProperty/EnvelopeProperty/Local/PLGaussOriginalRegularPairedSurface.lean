import EnvelopeProperty.Local.PLGaussPairedSurfaceParameters
import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionClosedSurface
import DeJongAlterations.StableModificationBridge.AlterationUnconditional

/-! # The original model internally produces its genuine regular curve family

The normal horizontal surface, its closed finite curve lift, the actual full
altered pair and the actual SNC component/parameters are ALL produced here.
No curve family, alteration existence, parameter, field or norm certificate
is a premise. Every original map and whole base triangle is retained.
-/

noncomputable section
open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry
open EnvelopeProperty.ProjBerk

universe u

namespace EnvelopeProperty.PLGaussOriginalRegularPairedSurface

private theorem exists_actual_parameter_pair
    {k : Type u} [Field k] {n : ℕ} {N : Scheme.{u}} [IsIntegral N]
    (i : N ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)] :
    Nonempty (AlterationWithBoundary
      ((i ≫ nativeStructureMap) ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
      ((i ≫ nativeStructureMap) ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]))) := by
  let b := i ≫ nativeStructureMap
  let pN := b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  let : IsProper b :=
    (PLGaussVerticalCurveSurfaceSelectionNormalizedStep.original_structure_isProjectiveFactorization i).isProper
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : IsVariety pN := .mk
  let Z : Closeds N := ⟨b ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]),
    (PrimeSpectrum.isClosed_zeroLocus _).preimage b.continuous⟩
  let K := PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i
    (MvPolynomial.C (Polynomial.X : k[X]))
    (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
  have hs : K.support = Z := by
    apply Closeds.ext
    exact PLGaussVerticalCurveSurfaceSelectionCentralFiber.coefficientCut_support i Polynomial.X
  have hZ : Z ≠ ⊤ := by
    intro h
    exact PLGaussVerticalCurveSurfaceSelectionCentralFiber.coefficientCut_support_ne_top
      i Polynomial.X Polynomial.X_ne_zero (hs.trans h)
  exact DeJongAlterations.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem
    k N pN inferInstance Z hZ

/-- The original model and original central curve internally produce the actual regular family and every original local parameter. -/
theorem exists_original_regular_curve_over_model
    {k : Type u} [Field k] [Infinite k] {n : ℕ} {Y C : Scheme.{u}}
    [IsIntegral Y] [IsIntegral C]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hC : topologicalKrullDim C = 1) :
    ∃ (R A : Scheme.{u}) (hRI : IsIntegral R) (hAI : IsIntegral A),
      letI : IsIntegral R := hRI
      letI : IsIntegral A := hAI
      ∃ (F : R ⟶ Y) (j : A ⟶ R) (ν : A ⟶ C),
        IsRegularScheme R ∧ topologicalKrullDim R = 2 ∧
        IsRegularScheme A ∧ topologicalKrullDim A = 1 ∧
        (∀ x : A, IsIntegrallyClosed (A.presheaf.stalk x)) ∧
        IsClosedImmersion j ∧ IsFinite ν ∧ IsDominant ν ∧
        IsProjectiveFactorization (ν ≫ q) ∧ IsProper F ∧
        IsProper (F ≫ (i ≫ nativeStructureMap)) ∧
        IsDominant (F ≫ (i ≫ nativeStructureMap)) ∧
        Flat (F ≫ (i ≫ nativeStructureMap)) ∧
        j ≫ F = ν ≫ c ∧
        j ≫ (F ≫ (i ≫ nativeStructureMap)) =
          (ν ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
        (∃ x₀ : A, x₀ ≠ genericPoint A ∧ IsClosed ({x₀} : Set A)) ∧
        ∀ x : A, x ≠ genericPoint A →
          ∃ π z : R.presheaf.stalk (j x),
            RingHom.ker (j.stalkMap x).hom = Ideal.span {π} ∧
            IsLocalRing.maximalIdeal (R.presheaf.stalk (j x)) = Ideal.span {π, z} ∧
            Prime π ∧ ¬ π ∣ z ∧
            SchemeStalkCoefficients.coefficientMap
              (F ≫ (i ≫ nativeStructureMap)) (j x) Polynomial.X ≠ 0 ∧
            π ∣ SchemeStalkCoefficients.coefficientMap
              (F ≫ (i ≫ nativeStructureMap)) (j x) Polynomial.X ∧
            IsDiscreteValuationRing (A.presheaf.stalk x) ∧
            ∃ e : (R.presheaf.stalk (j x) ⧸ Ideal.span {π}) ≃+* A.presheaf.stalk x,
              ∀ a : R.presheaf.stalk (j x), e (Ideal.Quotient.mk _ a) = j.stalkMap x a := by
  classical
  obtain ⟨I, hI, rest⟩ :=
    PLGaussVerticalCurveSurfaceSelectionClosedSurface.exists_original_normalized_closed_surface
      i q hq c hc hC
  let : IsIntegral I.subscheme := hI
  let N := IntegralSchemeNormalization.normalization I.subscheme
  let η : N ⟶ I.subscheme := IntegralSchemeNormalization.projection I.subscheme
  obtain ⟨cZ, aC, C', hCI, rest⟩ := rest
  let : IsIntegral C' := hCI
  obtain ⟨G, hGF, hGD, rest⟩ := rest
  let : IsFinite G := hGF
  let : IsDominant G := hGD
  obtain ⟨cN, _hIdim, _hIdom, _hIproj, _hcZclosed, _hcZ, _haCclosed, _haC,
    _haCrange, hNI, hηF, hNdim, hNdom, hNproj, hcNclosed, hC'dim, hC'proj,
    _hGpos, _hcNη, hcNY, hcNbase, _hNnormal, _hLine⟩ := rest
  let : IsIntegral N := hNI
  let : IsFinite η := hηF
  let : IsClosedImmersion cN := hcNclosed
  let bY := i ≫ nativeStructureMap
  let bN : N ⟶ Spec (CommRingCat.of k[X]) := η ≫ (I.subschemeι ≫ bY)
  obtain ⟨m, iN₀, hiN, hiNbase⟩ := hNproj
  let iN : N ⟶ NativeProjectiveScheme k[X] m := iN₀
  let : IsClosedImmersion iN := hiN
  let bHat := iN ≫ nativeStructureMap
  have hHat : bHat = bN :=
    (congrArg (fun f ↦ iN ≫ f)
      (PLGaussVerticalCurveSurfaceSelectionFiniteSurface.nativeStructureMap_eq_homogeneousProjπ
        (R := k[X]) (n := m))).trans hiNbase
  let : IsDominant bHat := Eq.mp
    (congrArg (fun f : N ⟶ Spec (CommRingCat.of k[X]) ↦ IsDominant f) hHat.symm) hNdom
  have hcNHat : cN ≫ bHat =
      (G ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) :=
    (congrArg (fun f : N ⟶ Spec (CommRingCat.of k[X]) ↦ cN ≫ f) hHat).trans hcNbase
  obtain ⟨d⟩ := exists_actual_parameter_pair iN
  obtain ⟨hRreg, hRdim, _hBar, hbProper, hbDom, hbFlat, E, hAreg, hAdim,
    j, g, hj, hgF, hgD, hgProj, _hjfac, hjg, hjbase, _hfield, hpoint, hparams⟩ :=
    PLGaussPairedSurfaceGeometry.exists_regular_paired_surface_parameters
      iN hNdim (G ≫ q) hC'proj cN hC'dim hcNHat d
  let R := d.source
  let A := CartierBoundaryComponentDimension.componentScheme d.boundary E
  let : IsVariety d.sourceStructure := d.sourceVariety
  let : IsAlteration d.alteration := d.isAlteration
  let : IsIntegral A := inferInstance
  let : IsFinite g := hgF
  let : IsDominant g := hgD
  let : IsClosedImmersion j := hj
  let F : R ⟶ Y := d.alteration ≫ (η ≫ I.subschemeι)
  let ν : A ⟶ C := g ≫ G
  have hFbase : d.alteration ≫ bHat = F ≫ bY := by
    calc
      _ = d.alteration ≫ (η ≫ (I.subschemeι ≫ bY)) :=
        congrArg (fun f : N ⟶ Spec (CommRingCat.of k[X]) ↦ d.alteration ≫ f) hHat
      _ = d.alteration ≫ ((η ≫ I.subschemeι) ≫ bY) :=
        congrArg (fun f : N ⟶ Spec (CommRingCat.of k[X]) ↦ d.alteration ≫ f)
          (Category.assoc _ _ _).symm
      _ = _ := (Category.assoc _ _ _).symm
  have hFproper : IsProper F := by dsimp only [F]; infer_instance
  have hbFproper : IsProper (F ≫ bY) :=
    Eq.mp (congrArg (fun f : R ⟶ Spec (CommRingCat.of k[X]) ↦ IsProper f) hFbase) hbProper
  have hbFdom : IsDominant (F ≫ bY) :=
    Eq.mp (congrArg (fun f : R ⟶ Spec (CommRingCat.of k[X]) ↦ IsDominant f) hFbase) hbDom
  have hbFflat : Flat (F ≫ bY) :=
    Eq.mp (congrArg (fun f : R ⟶ Spec (CommRingCat.of k[X]) ↦ Flat f) hFbase) hbFlat
  have hνq : g ≫ (G ≫ q) = ν ≫ q := (Category.assoc _ _ _).symm
  have hνproj : IsProjectiveFactorization (ν ≫ q) :=
    Eq.mp (congrArg (fun f : A ⟶ Spec (CommRingCat.of k) ↦ IsProjectiveFactorization f) hνq) hgProj
  have htriangle : j ≫ F = ν ≫ c := by
    calc
      _ = (j ≫ d.alteration) ≫ (η ≫ I.subschemeι) := (Category.assoc _ _ _).symm
      _ = (g ≫ cN) ≫ (η ≫ I.subschemeι) :=
        congrArg (fun f ↦ f ≫ (η ≫ I.subschemeι)) hjg
      _ = g ≫ (cN ≫ (η ≫ I.subschemeι)) := Category.assoc _ _ _
      _ = g ≫ (G ≫ c) := congrArg (fun f ↦ g ≫ f) hcNY
      _ = _ := (Category.assoc _ _ _).symm
  have hcentral : j ≫ (F ≫ bY) =
      (ν ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) :=
    (congrArg (fun f : R ⟶ Spec (CommRingCat.of k[X]) ↦ j ≫ f) hFbase).symm.trans
      (hjbase.trans (congrArg (fun f : A ⟶ Spec (CommRingCat.of k) ↦
        f ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) hνq))
  have hAnormal : ∀ x : A, IsIntegrallyClosed (A.presheaf.stalk x) := by
    intro x
    by_cases hx : x = genericPoint A
    · subst x
      change IsIntegrallyClosed A.functionField
      infer_instance
    · obtain ⟨_, _, _, _, _, _, _, _, hQ, _⟩ := hparams x hx
      let : IsDiscreteValuationRing (A.presheaf.stalk x) := hQ
      infer_instance
  refine ⟨R, A, inferInstance, inferInstance, F, j, ν, hRreg, hRdim,
    hAreg, hAdim, hAnormal, hj, inferInstance, inferInstance, hνproj,
    hFproper, hbFproper, hbFdom, hbFflat, htriangle, hcentral, hpoint, ?_⟩
  intro x hx
  obtain ⟨π, z, hk, hmax, hπ, hnot, ht, hd, hQ, e, he⟩ := hparams x hx
  have hvalue : SchemeStalkCoefficients.coefficientMap (d.alteration ≫ bHat) (j x) Polynomial.X =
      SchemeStalkCoefficients.coefficientMap (F ≫ bY) (j x) Polynomial.X :=
    congrArg (fun f : R ⟶ Spec (CommRingCat.of k[X]) ↦
      SchemeStalkCoefficients.coefficientMap f (j x) Polynomial.X) hFbase
  exact ⟨π, z, hk, hmax, hπ, hnot, (fun h ↦ ht (hvalue.trans h)),
    Eq.mp (congrArg (fun t : R.presheaf.stalk (j x) ↦ π ∣ t) hvalue) hd, hQ, e, he⟩

end EnvelopeProperty.PLGaussOriginalRegularPairedSurface
