import EnvelopeProperty.Local.PLIdealNormalizedRatioPullback
import EnvelopeProperty.Global.NativeTestConfigurationData
import EnvelopeProperty.Local.PLOriginalModelCompatibilityFibreMaps

/-! # The actual original parameter-one fibre of the normalized PL model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
open scoped Polynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.PLOriginalModelCompatibility

/-- The fibre over a section `ε` of `c : S ⟶ B` of a model `P` which is (isomorphic over `S`
to) the base change `N ×_B S` of `N ⟶ B` is `N` itself. -/
def baseChangeFibreIso {N P B S : Scheme.{u}} (nat : N ⟶ B) (c : S ⟶ B) (ε : B ⟶ S)
    (hε : ε ≫ c = 𝟙 B) (p : P ⟶ S) (m : P ≅ pullback nat c)
    (hm : m.hom ≫ pullback.snd nat c = p) : pullback p ε ≅ N :=
  haveI := fibreMap_isIso ε p (pullback.snd nat c) m.hom hm
  asIso (fibreMap ε p (pullback.snd nat c) m.hom hm) ≪≫
    pullbackLeftPullbackSndIso nat c ε ≪≫
    pullback.congrHom rfl hε ≪≫ asIso (pullback.fst nat (𝟙 _))

/-- The base-change fibre isomorphism is the fibre inclusion followed by the projection. -/
theorem baseChangeFibreIso_hom {N P B S : Scheme.{u}} (nat : N ⟶ B) (c : S ⟶ B) (ε : B ⟶ S)
    (hε : ε ≫ c = 𝟙 B) (p : P ⟶ S) (m : P ≅ pullback nat c)
    (hm : m.hom ≫ pullback.snd nat c = p) :
    (baseChangeFibreIso nat c ε hε p m hm).hom =
      pullback.fst p ε ≫ m.hom ≫ pullback.fst nat c := by
  simp only [baseChangeFibreIso, pullback.congrHom, Iso.trans_hom, asIso_hom]
  rw [pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst,
    fibreMap_fst_assoc]

/-- The fibre of any scheme over `𝔸¹` at the parameter value one lies over the open `t ≠ 0`. -/
theorem range_fst_subset_basicOpen_X {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k[X])) (ε : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k[X]))
    (hε : ε = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : k)))) :
    Set.range (pullback.fst p ε) ⊆
      (p ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]) : Set Y) := by
  rintro _ ⟨z, rfl⟩
  change p (pullback.fst p ε z) ∈ PrimeSpectrum.basicOpen (Polynomial.X : k[X])
  have h : p (pullback.fst p ε z) = ε (pullback.snd p ε z) :=
    congrArg (fun f => f z) (pullback.condition (f := p) (g := ε))
  rw [h]
  have hx (x : Spec (CommRingCat.of k)) :
      ε x ∈ PrimeSpectrum.basicOpen (Polynomial.X : k[X]) := by
    subst hε
    change Polynomial.eval 1 Polynomial.X ∉ x.asIdeal
    simpa only [Polynomial.eval_X] using x.isPrime.one_notMem
  exact hx _

end EnvelopeProperty.PLOriginalModelCompatibility

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint NativeTestConfiguration
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k]

private theorem parameterOneFibreInclusion_range {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k[X])) :
    Set.range (pullback.fst p (pointOne k).left) ⊆
      (p ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]) : Set Y) :=
  PLOriginalModelCompatibility.range_fst_subset_basicOpen_X p _ (pointOne_left k)

variable {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The actual native scheme-theoretic fibre over the original parameter one,
before supplying any test-configuration action or fibre comparison. -/
abbrev normalizedSimultaneousFibreOne : Over (Spec (CommRingCat.of k)) :=
  fibreOneOver k (X.normalizedSimultaneousIdealBlowupStructure I J hfin)

/-- The canonical first projection of the same original parameter-one square. -/
def normalizedSimultaneousFibreOneInclusion :
    (X.normalizedSimultaneousFibreOne I J hfin).left ⟶
      X.normalizedSimultaneousIdealBlowup I J hfin :=
  (SchemeEquivariantPullback.firstProjection
    (structureOver k (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (pointOne k)).left

/-- Every point of the entire original fibre one lies in the original
noncentral open, by evaluation of the original parameter at one. -/
theorem normalizedSimultaneousFibreOneInclusion_range :
    Set.range (X.normalizedSimultaneousFibreOneInclusion I J hfin) ⊆
      (X.normalizedSimultaneousNoncentralOpen I J hfin :
        Set (X.normalizedSimultaneousIdealBlowup I J hfin)) := by
  exact parameterOneFibreInclusion_range _

/-- The canonical whole original fibre inclusion factors through the actual
noncentral open; no pointwise or fibre-trivialization hypothesis is supplied. -/
def normalizedSimultaneousFibreOneNoncentralLift :
    (X.normalizedSimultaneousFibreOne I J hfin).left ⟶
      (X.normalizedSimultaneousNoncentralOpen I J hfin).toScheme :=
  IsOpenImmersion.lift (X.normalizedSimultaneousNoncentralOpen I J hfin).ι
    (X.normalizedSimultaneousFibreOneInclusion I J hfin) (by
      rw [Scheme.Opens.range_ι]
      exact X.normalizedSimultaneousFibreOneInclusion_range I J hfin)

/-- The original fibre-one factorization retains exactly the canonical
first projection of the original native Cartesian square. -/
@[reassoc (attr := simp)]
theorem normalizedSimultaneousFibreOneNoncentralLift_inclusion :
    X.normalizedSimultaneousFibreOneNoncentralLift I J hfin ≫
      (X.normalizedSimultaneousNoncentralOpen I J hfin).ι =
        X.normalizedSimultaneousFibreOneInclusion I J hfin :=
  IsOpenImmersion.lift_fac _ _ _

omit I J hfin in
/-- The actual original product-model fibre over one is the original native
projective variety, through the same whole product-coordinate isomorphism. -/
def nativeProductFibreOneIso :
    (fibreOneOver k X.nativeProductStructure).left ≅ X.NativeScheme :=
  PLOriginalModelCompatibility.baseChangeFibreIso X.nativeStructure
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) (pointOne k).left (pointOne k).w
    X.nativeProductStructure X.nativeProductModelIso X.nativeProductModelIso_over_base

omit I J hfin in
/-- The original product fibre identification has exactly its original
fibre inclusion followed by its original product-to-variety projection. -/
theorem nativeProductFibreOneIso_hom :
    X.nativeProductFibreOneIso.hom =
      pullback.fst X.nativeProductStructure (pointOne k).left ≫
        X.nativeProductModelIso.hom ≫
          pullback.fst X.nativeStructure
            (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
  PLOriginalModelCompatibility.baseChangeFibreIso_hom _ _ _ _ _ _ _

omit I J hfin in
/-- The actual normalization and simultaneous-blowup composite induces an
isomorphism of the entire original parameter-one fibres, from original
normality and actual parameter-power membership alone. -/
def normalizedSimultaneousFibreOneProductIso
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥) (hX : X.IsProjNormal) :
    (X.normalizedSimultaneousFibreOne (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).left ≅
      (fibreOneOver k X.nativeProductStructure).left :=
  haveI : IsIso ((X.normalizedSimultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
        X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J)) ∣_
      (X.nativeProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]))) :=
    X.normalizedSimultaneousComposite_isIso_over_parameter I J A B hA hB hfin hX
  haveI := PLOriginalModelCompatibility.fibreMap_isIso_of_morphismRestrict (pointOne k).left
    (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) X.nativeProductStructure
    (X.normalizedSimultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
        X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J))
    (Category.assoc _ _ _) _ (parameterOneFibreInclusion_range _)
  asIso (PLOriginalModelCompatibility.fibreMap (pointOne k).left
    (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) X.nativeProductStructure
    (X.normalizedSimultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
        X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J))
    (Category.assoc _ _ _))

omit I J hfin in
/-- The fibre-one comparison of the normalized model with the product model is the
induced map of fibres. -/
theorem normalizedSimultaneousFibreOneProductIso_hom
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥) (hX : X.IsProjNormal) :
    (X.normalizedSimultaneousFibreOneProductIso I J A B hA hB hfin hX).hom =
      PLOriginalModelCompatibility.fibreMap (pointOne k).left
        (X.normalizedSimultaneousIdealBlowupStructure
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) X.nativeProductStructure
        (X.normalizedSimultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
            X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J))
        (Category.assoc _ _ _) :=
  rfl

omit I J hfin in
/-- The same actual normalized PL model has its original native fibre one
isomorphic to the same original variety, with no fibre comparison input. -/
def normalizedSimultaneousFibreOneNativeIso
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥) (hX : X.IsProjNormal) :
    (X.normalizedSimultaneousFibreOne (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).left ≅
      X.NativeScheme :=
  X.normalizedSimultaneousFibreOneProductIso I J A B hA hB hfin hX ≪≫ X.nativeProductFibreOneIso

omit I J hfin in
/-- The entire constructed original fibre-one isomorphism is exactly the
canonical original fibre inclusion followed by the original projection to X. -/
theorem normalizedSimultaneousFibreOneNativeIso_hom
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥) (hX : X.IsProjNormal) :
    (X.normalizedSimultaneousFibreOneNativeIso I J A B hA hB hfin hX).hom =
      X.normalizedSimultaneousFibreOneInclusion
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
      X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin := by
  rw [normalizedSimultaneousFibreOneNativeIso, Iso.trans_hom,
    normalizedSimultaneousFibreOneProductIso_hom, nativeProductFibreOneIso_hom,
    PLOriginalModelCompatibility.fibreMap_fst_assoc]
  simp only [Category.assoc]
  rfl

private theorem normalizedSimultaneousOriginalProjection_coefficient_square :
    X.normalizedSimultaneousOriginalProjection I J hfin ≫ X.nativeStructure =
      X.normalizedSimultaneousIdealBlowupStructure I J hfin ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) := by
  have he : X.nativeProductModelIso.hom ≫
      pullback.fst X.nativeStructure
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) ≫ X.nativeStructure =
      X.nativeProductStructure ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) := by
    rw [pullback.condition, ← Category.assoc, X.nativeProductModelIso_over_base]
  dsimp only [normalizedSimultaneousOriginalProjection, simultaneousOriginalProjection,
    normalizedSimultaneousIdealBlowupStructure, simultaneousIdealBlowupStructure]
  simp only [Category.assoc]
  rw [he]

omit I J hfin in
/-- The same original fibre-one comparison is genuinely over the original
coefficient field, with the original native fibre and coefficient maps. -/
def normalizedSimultaneousFibreOneOverIso
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥) (hX : X.IsProjNormal) :
    X.normalizedSimultaneousFibreOne (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≅
      Over.mk X.nativeStructure :=
  Over.isoMk (X.normalizedSimultaneousFibreOneNativeIso I J A B hA hB hfin hX) (by
    rw [X.normalizedSimultaneousFibreOneNativeIso_hom I J A B hA hB hfin hX]
    change (X.normalizedSimultaneousFibreOneInclusion
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
      X.normalizedSimultaneousOriginalProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) ≫ X.nativeStructure =
      X.normalizedSimultaneousFibreOneInclusion
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
      (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
    rw [Category.assoc, X.normalizedSimultaneousOriginalProjection_coefficient_square])

omit I J hfin in
/-- Original parameter-power membership trivializes the same normalized
ratio on the entire actual original native fibre over one. -/
def normalizedSimultaneousRatioFibreOneIso
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥) :
    (Scheme.Modules.pullback (X.normalizedSimultaneousFibreOneInclusion
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
        (X.normalizedSimultaneousRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) ≅
      unitObj (X.normalizedSimultaneousFibreOne
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).left :=
  let l := X.normalizedSimultaneousFibreOneNoncentralLift
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  let U := X.normalizedSimultaneousNoncentralOpen
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  let L := X.normalizedSimultaneousRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  ((pullbackCongr (X.normalizedSimultaneousFibreOneNoncentralLift_inclusion
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).app L).symm ≪≫
    ((pullbackComp l U.ι).app L).symm ≪≫
    (Scheme.Modules.pullback l).mapIso
      (X.normalizedSimultaneousRatioParameterIso I J A B hA hB hfin) ≪≫
    pullbackUnitIso l

omit I J hfin in
/-- The actual original polarized line has its entire original fibre-one
identification with the same projective twist along the original projection. -/
def normalizedSimultaneousTwistedRatioFibreOneIso
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (j : Fin (M+1)) (n A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥) :
    (Scheme.Modules.pullback (X.normalizedSimultaneousFibreOneInclusion
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
        (X.normalizedSimultaneousTwistedRatioLine
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j n) ≅
      (Scheme.Modules.pullback (X.normalizedSimultaneousFibreOneInclusion
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
          X.normalizedSimultaneousOriginalProjection
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
        (X.nativeTwistLineSheaf j n) :=
  canonicalTensorPullbackIso _ _ _ ≪≫
    tensorObjCongr (Iso.refl _)
      (X.normalizedSimultaneousRatioFibreOneIso I J A B hA hB hfin) ≪≫
    tensorObjUnitIso _ ≪≫ (pullbackComp _ _).app _

omit I J hfin in
/-- The actual original polarized line supplies precisely the fibre-one
line-identification input for the constructed original fibre-one isomorphism. -/
def normalizedSimultaneousTwistedRatioFibreOneIdentification
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (j : Fin (M+1)) (n A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥) (hX : X.IsProjNormal) :
    (Scheme.Modules.pullback (X.normalizedSimultaneousFibreOneInclusion
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
        (X.normalizedSimultaneousTwistedRatioLine
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j n) ≅
      (Scheme.Modules.pullback
        (X.normalizedSimultaneousFibreOneOverIso I J A B hA hB hfin hX).hom.left).obj
        (X.nativeTwistLineSheaf j n) :=
  X.normalizedSimultaneousTwistedRatioFibreOneIso I J j n A B hA hB hfin ≪≫
    (pullbackCongr
      (X.normalizedSimultaneousFibreOneNativeIso_hom I J A B hA hB hfin hX).symm).app
        (X.nativeTwistLineSheaf j n)

end EnvelopeProperty.ProjSubvariety
