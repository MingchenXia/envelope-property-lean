import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeGlobalSections

/-!
# Actual native base constants, function field algebra and linear H0

The scalar action is induced by the ACTUAL native structure morphism via
Spec/global sections. Neither field nor H0 actions are transported through
the comparison equivalence. Full route: owned `native-base-scalars-route.tex`.
-/

open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open EnvelopeProperty.CanonicalGeometry
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalOpenRestriction_topIso {Y : Scheme.{u}} (U : Y.Opens) :
    U.ι.appTop ≫ U.topIso.hom = Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact congrArg Y.presheaf.map (Subsingleton.elim _ _)

private theorem actualRingMapSquare_apply {A B C D : CommRingCat.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (i : C ⟶ D)
    (he : f ≫ g = h ≫ i) (a : A) : g (f a) = i (h a) :=
  ConcreteCategory.congr_hom he a

private theorem actualConstants_onChart {B A : Type u} [CommRing B] [CommRing A]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B)) (U : Y.Opens)
    (e : U.toScheme ≅ Spec (.of A)) (α : B →+* A)
    (h : e.inv ≫ U.ι ≫ p = Spec.map (CommRingCat.ofHom α)) :
    ((Scheme.ΓSpecIso (.of B)).inv ≫ p.appTop) ≫
        Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op =
      CommRingCat.ofHom α ≫ (Scheme.ΓSpecIso (.of A)).inv ≫
        e.hom.appTop ≫ U.topIso.hom := by
  simp only [Category.assoc]
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← h]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  have hc : e.inv.appTop ≫ e.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]
  rw [← Category.assoc e.inv.appTop e.hom.appTop U.topIso.hom,
    hc, Category.id_comp, originalOpenRestriction_topIso U]

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- Genuine constants come from the ACTUAL native structure morphism. -/
def nativeRankOneBaseConstants : k →+* Γ(X.nativeRankOneScheme, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.nativeRankOneStructure.appTop).hom

/-- The ENTIRE native base-constant map restricts to the ORIGINAL chart
coefficient inclusion, through the genuine original section-ring isomorphism. -/
theorem nativeRankOneBaseConstants_chart (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) :
    CommRingCat.ofHom X.nativeRankOneBaseConstants ≫
        X.nativeRankOneScheme.presheaf.map
          (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op =
      CommRingCat.ofHom (algebraMap k (X.chartAlg i)) ≫
        (X.nativeRankOneOriginalSectionsIso i hi).hom := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ X.nativeRankOneStructure.appTop) ≫
    X.nativeRankOneScheme.presheaf.map
      (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op = _
  rw [X.nativeRankOneOriginalSectionsIso_eq i hi]
  exact actualConstants_onChart X.nativeRankOneStructure
    (X.nativeRankOneCoordinateOpen (i 0)) (X.nativeRankOneOriginalChartIso i hi)
    (algebraMap k (X.chartAlg i)) (X.nativeRankOneOriginalChartIso_structure i hi)

/-- Every original base coefficient has its literal actual native restriction. -/
theorem nativeRankOneBaseConstants_restrict (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (a : k) :
    X.nativeRankOneScheme.presheaf.map
        (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
        (X.nativeRankOneBaseConstants a) =
      (X.nativeRankOneOriginalSectionsIso i hi).hom (algebraMap k (X.chartAlg i) a) :=
  actualRingMapSquare_apply (CommRingCat.ofHom X.nativeRankOneBaseConstants)
    (X.nativeRankOneScheme.presheaf.map
      (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op)
    (CommRingCat.ofHom (algebraMap k (X.chartAlg i)))
    (X.nativeRankOneOriginalSectionsIso i hi).hom
    (X.nativeRankOneBaseConstants_chart i hi) a

/-- The true original field equivalence preserves the ACTUAL structural
base coefficient, not an algebra action transported through that equivalence. -/
theorem nativeRankOneFunctionFieldEquiv_baseConstants (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (a : k) :
    X.nativeRankOneFunctionFieldEquiv i hi (algebraMap k K a) =
      X.nativeRankOneScheme.germToFunctionField ⊤ (X.nativeRankOneBaseConstants a) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  calc
    X.nativeRankOneFunctionFieldEquiv i hi (algebraMap k K a) =
        X.nativeRankOneGenericGerm i hi
          ((X.nativeRankOneOriginalSectionsIso i hi).hom (algebraMap k (X.chartAlg i) a)) :=
      X.nativeRankOneFunctionFieldEquiv_coefficient i hi (algebraMap k (X.chartAlg i) a)
    _ = X.nativeRankOneGenericGerm i hi
        (X.nativeRankOneScheme.presheaf.map
          (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
          (X.nativeRankOneBaseConstants a)) :=
      congrArg (X.nativeRankOneGenericGerm i hi)
        (X.nativeRankOneBaseConstants_restrict i hi a).symm
    _ = _ := germToFunctionField_restrict
      (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤))
      (X.nativeRankOneBaseConstants a)

/-- The genuine native function-field k-algebra is induced by the actual
structure morphism and the actual generic germ. -/
abbrev nativeRankOneFunctionFieldBaseAlgebra : Algebra k X.nativeRankOneScheme.functionField :=
  ((X.nativeRankOneScheme.germToFunctionField ⊤).hom.comp X.nativeRankOneBaseConstants).toAlgebra

/-- The ORIGINAL model field and ACTUAL native function field are equivalent
over the SAME actual original base-field action. -/
def nativeRankOneFunctionFieldAlgEquiv (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) :
    letI := X.nativeRankOneFunctionFieldBaseAlgebra
    K ≃ₐ[k] X.nativeRankOneScheme.functionField := by
  letI := X.nativeRankOneFunctionFieldBaseAlgebra
  exact AlgEquiv.ofRingEquiv (f := X.nativeRankOneFunctionFieldEquiv i hi)
    (X.nativeRankOneFunctionFieldEquiv_baseConstants i hi)

/-- The actual base module on native H0 restricts its true global-function
action along the true native structure-constant homomorphism. -/
abbrev nativeRankOneH0BaseModule (j : Fin (X.M 0 + 1)) :
    Module k Γ(X.nativeRankOneCoordinateLine j, ⊤) :=
  Module.compHom Γ(X.nativeRankOneCoordinateLine j, ⊤) X.nativeRankOneBaseConstants

/-- The ORIGINAL coefficient of true native global sections is additive. -/
theorem nativeRankOneGlobalSectionCoefficient_add (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (s t : Γ(X.nativeRankOneCoordinateLine j, ⊤)) :
    X.nativeRankOneGlobalSectionCoefficient i hi j hj (s + t) =
      X.nativeRankOneGlobalSectionCoefficient i hi j hj s +
        X.nativeRankOneGlobalSectionCoefficient i hi j hj t := by
  simp only [nativeRankOneGlobalSectionCoefficient, map_add, mul_add]

/-- Exact compatibility with the ACTUAL original base action through the
native structure morphism, before introducing any k-linear comparison. -/
theorem nativeRankOneGlobalSectionCoefficient_base_smul (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (a : k) (s : Γ(X.nativeRankOneCoordinateLine j, ⊤)) :
    X.nativeRankOneGlobalSectionCoefficient i hi j hj (X.nativeRankOneBaseConstants a • s) =
      algebraMap k K a * X.nativeRankOneGlobalSectionCoefficient i hi j hj s := by
  unfold nativeRankOneGlobalSectionCoefficient
  rw [(sectionRatio (X.nativeRankOneCoordinateLine j) (X.nativeRankOneCoordinateLine_isInvertible j hj)
    (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneCoordinatePoleSection_ne_zero j hj)
    ⊤).map_smulₛₗ]
  simp only [smul_eq_mul]
  rw [← X.nativeRankOneFunctionFieldEquiv_baseConstants i hi a, map_mul,
    RingEquiv.symm_apply_apply]
  ring

/-- The full ORIGINAL saturated degree-one section space is the ACTUAL
native H0 as a vector space over its genuine native base-field action. -/
def nativeRankOneH0OriginalSectionsLinearEquiv (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    letI := X.nativeRankOneH0BaseModule j
    Γ(X.nativeRankOneCoordinateLine j, ⊤) ≃ₗ[k] X.sections (1 : Fin 1 → ℤ) := by
  letI := X.nativeRankOneH0BaseModule j
  let e := X.nativeRankOneH0OriginalSectionsEquiv i hi j hj
  let F : Γ(X.nativeRankOneCoordinateLine j, ⊤) →ₗ[k] X.sections (1 : Fin 1 → ℤ) := {
    toFun := e
    map_add' s t := by
      apply Subtype.ext
      exact X.nativeRankOneGlobalSectionCoefficient_add i hi j hj s t
    map_smul' a s := by
      apply Subtype.ext
      change X.nativeRankOneGlobalSectionCoefficient i hi j hj
        (X.nativeRankOneBaseConstants a • s) =
        a • X.nativeRankOneGlobalSectionCoefficient i hi j hj s
      rw [Algebra.smul_def]
      exact X.nativeRankOneGlobalSectionCoefficient_base_smul i hi j hj a s }
  exact LinearEquiv.ofBijective F e.bijective

/-- The actual k-linear comparison still has its literal original coefficient. -/
theorem nativeRankOneH0OriginalSectionsLinearEquiv_apply (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (s : Γ(X.nativeRankOneCoordinateLine j, ⊤)) :
    letI := X.nativeRankOneH0BaseModule j
    (X.nativeRankOneH0OriginalSectionsLinearEquiv i hi j hj s : K) =
      X.nativeRankOneGlobalSectionCoefficient i hi j hj s := rfl

/-- The actual k-linear inverse is still the SAME genuinely glued global section. -/
theorem nativeRankOneH0OriginalSectionsLinearEquiv_symm (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (f : X.sections (1 : Fin 1 → ℤ)) :
    letI := X.nativeRankOneH0BaseModule j
    (X.nativeRankOneH0OriginalSectionsLinearEquiv i hi j hj).symm f =
      X.nativeRankOneGlobalSectionOfOriginal j hj f := by
  have := X.nativeRankOneH0BaseModule j
  apply (X.nativeRankOneH0OriginalSectionsLinearEquiv i hi j hj).injective
  apply Subtype.ext
  exact (congrArg Subtype.val
    ((X.nativeRankOneH0OriginalSectionsLinearEquiv i hi j hj).apply_symm_apply f)).trans
      (X.nativeRankOneGlobalSectionOfOriginal_coefficient i hi j hj f).symm

end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.MultiModel.nativeRankOneBaseConstants
#print axioms EnvelopeProperty.MultiModel.nativeRankOneBaseConstants
#check @EnvelopeProperty.MultiModel.nativeRankOneBaseConstants_chart
#print axioms EnvelopeProperty.MultiModel.nativeRankOneBaseConstants_chart
#check @EnvelopeProperty.MultiModel.nativeRankOneBaseConstants_restrict
#print axioms EnvelopeProperty.MultiModel.nativeRankOneBaseConstants_restrict
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_baseConstants
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldEquiv_baseConstants
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldBaseAlgebra
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldBaseAlgebra
#check @EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldAlgEquiv
#print axioms EnvelopeProperty.MultiModel.nativeRankOneFunctionFieldAlgEquiv
#check @EnvelopeProperty.MultiModel.nativeRankOneH0BaseModule
#print axioms EnvelopeProperty.MultiModel.nativeRankOneH0BaseModule
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_add
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_add
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_base_smul
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_base_smul
#check @EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsLinearEquiv
#print axioms EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsLinearEquiv
#check @EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsLinearEquiv_apply
#print axioms EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsLinearEquiv_apply
#check @EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsLinearEquiv_symm
#print axioms EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsLinearEquiv_symm
