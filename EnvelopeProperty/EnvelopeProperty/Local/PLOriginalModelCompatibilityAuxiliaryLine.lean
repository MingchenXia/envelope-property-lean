import EnvelopeProperty.Local.PLOriginalModelCompatibilityTestConfiguration
import EnvelopeProperty.Local.PLIdealNormalizedGlobalGeneration
import EnvelopeProperty.Projective.GaussProductModel

/-! # The tautological twist on the normalized simultaneous PL model: linearization and fibre one

On the normalized simultaneous blowup `ν : 𝒳 ⟶ Bl_{IJ}(X × 𝔸¹)` of the PL model (the normal test
configuration of the proof of FHX `lem:local-PL-positivity`) put
`K = ν^*(IJ · O_{Bl})` (an invertible ideal: the exceptional ideal of a blowup is Cartier and
Cartier ideals pull back to Cartier ideals along the dominant normalization of an integral
scheme) and the *tautological twist* `H_q = q_X^* O_X(q) ⊗ K`. This file constructs

* invertibility of `K` and `H_q`;
* when `I, J` are invariant under the scaling `t ↦ a t` (hypotheses `hI`, `hJ`), the
  `𝔾ₘ`-invariance of `K` and hence a `𝔾ₘ`-linearization of `H_q` for the action of the
  normalized test configuration;
* when `t^A ∈ I` and `t^B ∈ J`, the trivialization of `K` over `t ≠ 0` and so the identification
  of the restriction of `H_q` to the fibre over `1` with `O_X(q)`;
* the same data in the form used by the line API of
  `normalizedSimultaneousNativeTestConfiguration`.

Blueprint: `pl-original-model-compatibility-auxiliary-line.tex`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.Modules
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint NativeTestConfiguration
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The closed immersion of `X × 𝔸¹` into `ℙᴹ_{k[t]}` lies over `𝔸¹_k`. -/
theorem nativeProductPolynomialInclusion_over_originalParameter :
    X.nativeProductPolynomialInclusion ≫
        DeJongAlterations.projectiveSpaceStructure k[X] M = X.nativeProductStructure := by
  have h : DeJongAlterations.projectiveSpaceStructure k[X] M =
      nativeStructureMap (R := k[X]) (n := M) := by
    change (Proj.toSpecZero (ProjectiveGrading k[X] M) ≫
        Spec.map (DeJongAlterations.projectiveSpaceDegreeZeroEquiv k[X] M).toCommRingCatIso.hom) =
      (Proj.toSpecZero (ProjectiveGrading k[X] M) ≫
        Spec.map (CommRingCat.ofHom (homogeneousCoefficientZero k[X] M)))
    congr 2
  rw [h]
  dsimp only [nativeProductPolynomialInclusion]
  rw [Category.assoc, nativePolynomialLineProductIso_inv_over_base]
  rfl

variable (I J : HomogeneousIdeal (ProjectiveGrading k[X] M))
variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The ideal `K = ν^*(μ^*(IJ))` on the normalized simultaneous blowup. -/
def normalizedSimultaneousTautologicalProductIdeal :
    (X.normalizedSimultaneousIdealBlowup
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).IdealSheafData :=
  (((X.nativeProductIdeal I) * (X.nativeProductIdeal J)).comap
    (X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
      (X.normalizedSimultaneousIdealBlowupProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)

/-- The ideal `K = ν^*(IJ · O_{Bl})` is invertible. -/
theorem normalizedSimultaneousTautologicalProductIdeal_isInvertible :
    (X.normalizedSimultaneousTautologicalProductIdeal I J hfin).IsInvertible := by
  let : IsIntegral (X.simultaneousIdealBlowup (X.nativeProductIdeal I) (X.nativeProductIdeal J)) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
      (hfin X.triv).1 (hfin X.triv).2
  exact IntegralSchemeNormalization.cartier_comap _
    (Scheme.IdealSheafData.blowUp.isInvertible_comap_π
      ((X.nativeProductIdeal I) * (X.nativeProductIdeal J)))

/-- The tautological twist `H_q = q_X^* O_X(q) ⊗ K` on the normalized simultaneous blowup. -/
def normalizedSimultaneousTautologicalTwistLine (j : Fin (M+1)) (q : ℕ) :
    (X.normalizedSimultaneousIdealBlowup
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).Modules :=
  tensorObj
    ((Scheme.Modules.pullback (X.normalizedSimultaneousOriginalProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
        (X.nativeTwistLineSheaf j q))
    (X.normalizedSimultaneousTautologicalProductIdeal I J hfin).toModules

/-- The tautological twist is invertible. -/
theorem normalizedSimultaneousTautologicalTwistLine_isInvertible (j : Fin (M+1)) (q : ℕ) :
    IsInvertible (X.normalizedSimultaneousTautologicalTwistLine I J hfin j q) :=
  ((X.nativeTwistLineSheaf_isInvertible j q).pullback _).tensorObj
    (X.normalizedSimultaneousTautologicalProductIdeal_isInvertible
      I J hfin).isInvertibleModule_toModules

variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

/-- For scaling-invariant `I, J`, the ideal `K` is `𝔾ₘ`-invariant: its pullbacks along the action
and along the projection `𝔾ₘ × 𝒳 ⟶ 𝒳` agree. -/
theorem normalizedSimultaneousTautologicalProductIdeal_invariant :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    let N := totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    (X.normalizedSimultaneousTautologicalProductIdeal I J hfin).comap
        (cartierActionMap (nativeMultiplicativeGroup k) N) =
      (X.normalizedSimultaneousTautologicalProductIdeal I J hfin).comap
        (cartierProjectionMap (nativeMultiplicativeGroup k) N) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  dsimp only [normalizedSimultaneousTautologicalProductIdeal]
  simp only [Scheme.IdealSheafData.comap_mul]
  rw [X.normalizedSimultaneousNativeCartierFactor_invariant I J hI hJ I
      (hI k[T;T⁻¹] LaurentPolynomial.C (parameterLaurentUnit k)) hfin,
    X.normalizedSimultaneousNativeCartierFactor_invariant I J hI hJ J
      (hJ k[T;T⁻¹] LaurentPolynomial.C (parameterLaurentUnit k)) hfin]

/-- The canonical `𝔾ₘ`-linearization of the invariant invertible ideal `K`. -/
def normalizedSimultaneousTautologicalProductNativeGmComparison :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    let N := totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    (Scheme.Modules.pullback (cartierActionMap (nativeMultiplicativeGroup k) N)).obj
        (X.normalizedSimultaneousTautologicalProductIdeal I J hfin).toModules ≅
      (Scheme.Modules.pullback (cartierProjectionMap (nativeMultiplicativeGroup k) N)).obj
        (X.normalizedSimultaneousTautologicalProductIdeal I J hfin).toModules := by
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  have hK := X.normalizedSimultaneousTautologicalProductIdeal_isInvertible I J hfin
  have hinv := X.normalizedSimultaneousTautologicalProductIdeal_invariant I J hfin hI hJ
  exact cartierGroupLinearization (nativeMultiplicativeGroup k)
    (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) _ hK hinv

/-- The `𝔾ₘ`-linearization of the tautological twist `H_q`, the tensor product of those of
`q_X^* O_X(q)` and of `K`. -/
def normalizedSimultaneousTautologicalTwistNativeGmComparison (j : Fin (M+1)) (q : ℕ) :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    let N := totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    (Scheme.Modules.pullback (cartierActionMap (nativeMultiplicativeGroup k) N)).obj
        (X.normalizedSimultaneousTautologicalTwistLine I J hfin j q) ≅
      (Scheme.Modules.pullback (cartierProjectionMap (nativeMultiplicativeGroup k) N)).obj
        (X.normalizedSimultaneousTautologicalTwistLine I J hfin j q) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  exact canonicalTensorPullbackIso _ _ _ ≪≫
    tensorObjCongr
      (X.normalizedSimultaneousOriginalTwistNativeGmComparison I J hI hJ hfin j q)
      (X.normalizedSimultaneousTautologicalProductNativeGmComparison I J hfin hI hJ) ≪≫
    (canonicalTensorPullbackIso _ _ _).symm

omit hI hJ in
/-- If `t^A ∈ I` and `t^B ∈ J`, then `K` is trivial over `t ≠ 0`, so its restriction to the fibre
over `1` is the structure sheaf. -/
def normalizedSimultaneousTautologicalProductFibreOneIso (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) :
    (Scheme.Modules.pullback (X.normalizedSimultaneousFibreOneInclusion
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
        (X.normalizedSimultaneousTautologicalProductIdeal I J hfin).toModules ≅
      unitObj (X.normalizedSimultaneousFibreOne
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin).left := by
  let K := X.normalizedSimultaneousTautologicalProductIdeal I J hfin
  let U := X.normalizedSimultaneousNoncentralOpen
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  let l := X.normalizedSimultaneousFibreOneNoncentralLift
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  have hU : U ≤ K.support.compl := by
    intro y hy
    dsimp only [K, normalizedSimultaneousTautologicalProductIdeal]
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_mul]
    exact not_or.mpr
      ⟨X.parameterOpen_le_compl_nativeProductIdeal_support I A hA hy,
        X.parameterOpen_le_compl_nativeProductIdeal_support J B hB hy⟩
  exact ((pullbackCongr (X.normalizedSimultaneousFibreOneNoncentralLift_inclusion
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).app K.toModules).symm ≪≫
    ((pullbackComp l U.ι).app K.toModules).symm ≪≫
    (Scheme.Modules.pullback l).mapIso (K.pullbackModuleIsoOfLeComplSupport U hU) ≪≫
        pullbackUnitIso l

omit hI hJ in
/-- If `t^A ∈ I` and `t^B ∈ J`, the restriction of `H_q` to the fibre over `1` is `O_X(q)`, through
the fibre-one identification of the normalized model. -/
def normalizedSimultaneousTautologicalTwistFibreOneIso (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hX : X.IsProjNormal) (j : Fin (M+1)) (q : ℕ) :
    (Scheme.Modules.pullback (X.normalizedSimultaneousFibreOneInclusion
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
        (X.normalizedSimultaneousTautologicalTwistLine I J hfin j q) ≅
      (Scheme.Modules.pullback
          (X.normalizedSimultaneousFibreOneOverIso I J A B hA hB hfin hX).hom.left).obj
        (X.nativeTwistLineSheaf j q) :=
  canonicalTensorPullbackIso _ _ _ ≪≫
    tensorObjCongr (Iso.refl _)
      (X.normalizedSimultaneousTautologicalProductFibreOneIso I J hfin A B hA hB) ≪≫
    tensorObjUnitIso _ ≪≫ (pullbackComp _ _).app _ ≪≫
    (pullbackCongr
      (X.normalizedSimultaneousFibreOneNativeIso_hom I J A B hA hB hfin hX).symm).app _

section TestConfiguration

variable (A B : ℕ) (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
  (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) (hX : X.IsProjNormal)

/-- The tautological twist `H = q_X^* O_X(q) ⊗ ν^*(IJ · O_{Bl})` with its `𝔾ₘ`-linearization, in the
form consumed by the line API of the normalized test configuration
`normalizedSimultaneousNativeTestConfiguration`. -/
def normalizedSimultaneousNativeTestConfigurationTautologicalLineComparison
    (j : Fin (M+1)) (q : ℕ) :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    let H := X.normalizedSimultaneousTautologicalTwistLine I J hfin j q
    (Scheme.Modules.pullback C.lineActionMap).obj H ≅
        (Scheme.Modules.pullback C.lineProjectionMap).obj H :=
  X.normalizedSimultaneousTautologicalTwistNativeGmComparison I J hfin hI hJ j q

/-- The restriction of the tautological twist to the fibre over `1` of the normalized test
configuration is `O_X(q)`, through the fibre-one identification of the test configuration. -/
def normalizedSimultaneousNativeTestConfigurationTautologicalFibreOneLineIso
    (j : Fin (M+1)) (q : ℕ) :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    let H := X.normalizedSimultaneousTautologicalTwistLine I J hfin j q
    (Scheme.Modules.pullback C.fibreOneInclusion.left).obj H ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj (X.nativeTwistLineSheaf j q) :=
  X.normalizedSimultaneousTautologicalTwistFibreOneIso I J hfin A B hA hB hX j q

end TestConfiguration

end EnvelopeProperty.ProjSubvariety
