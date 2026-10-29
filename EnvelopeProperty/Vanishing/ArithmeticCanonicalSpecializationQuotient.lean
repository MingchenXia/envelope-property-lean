import EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationCohomology
import EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationQuotientGeometry

/-! # The literal quotient closed fibre supplies canonical specialization

The produced Witt point uses R/P, while geometric specialization uses the
localization residue field κ(P). Their real coefficient isomorphism transports
the actual model pullback cohomology through a genuine scheme isomorphism.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationQuotient

open CanonicalGeometry ArithmeticCanonicalGlobalBaseChange ArithmeticCanonicalGlobalComparison
open ArithmeticCanonicalSpecializationGeometry ArithmeticCanonicalSpecializationQuotientGeometry

set_option backward.isDefEq.respectTransparency false

private theorem subsingleton_H_iff_moduleIso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (j : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf j) ↔
      Subsingleton (CategoryTheory.Sheaf.H N.sheaf j) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) j).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  constructor
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology X) j).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology X) j).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))

private theorem nativeClosedModel_subsingleton_of_quotient
    (hp : IsProjectiveFactorization p) (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (P : Ideal R) [P.IsMaximal] (j : ℕ)
    (hclosed : letI : Field (R ⧸ P) := Ideal.Quotient.field P
      Subsingleton (CategoryTheory.Sheaf.H
        (Scheme.Modules.tensorObj
          (canonicalLineSheaf (Limits.pullback.snd p
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)))) n)
          ((Scheme.Modules.pullback (Limits.pullback.fst p
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))))).obj L)).sheaf (j + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (fiberProjection P.ResidueField p)).obj
        (canonicalModel p n L)).sheaf (j + 1)) := by
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  let φ : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ P) :=
    CommRingCat.ofHom (Ideal.Quotient.mk P)
  let πQ := Limits.pullback.fst p (Spec.map φ)
  let sQ := Limits.pullback.snd p (Spec.map φ)
  let e := residueFibreIso P p
  let M := canonicalModel p n L
  let N := (Scheme.Modules.pullback πQ).obj M
  have hM := canonicalModel_isInvertible p n L hL
  let : N.IsQuasicoherent := (hM.pullback πQ).isQuasicoherent
  have hQ : Subsingleton (CategoryTheory.Sheaf.H N.sheaf (j + 1)) :=
    (subsingleton_H_iff_moduleIso (nativeFieldCanonicalTensorIso p φ n L) (j + 1)).mpr hclosed
  have he : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback e.hom).obj N).sheaf (j + 1)) :=
    (SchemeIsoGeometry.pullback_subsingleton_H_iff e sQ
      (nativeField_isProjectiveFactorization p φ hp) N j).mpr hQ
  let E : (Scheme.Modules.pullback e.hom).obj N ≅
      (Scheme.Modules.pullback (fiberProjection P.ResidueField p)).obj M :=
    (Scheme.Modules.pullbackComp e.hom πQ).app M ≪≫
      (Scheme.Modules.pullbackCongr (residueFibreIso_fst P p)).app M
  exact (subsingleton_H_iff_moduleIso E (j + 1)).mp he

/-- Vanishing on the literal quotient field produces vanishing on the
native localization-residue fibre through the actual model comparison. -/
theorem nativeResidueCanonicalTensor_subsingleton_of_quotient
    (hp : IsProjectiveFactorization p) (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (P : Ideal R) [P.IsMaximal] (j : ℕ)
    (hclosed : letI : Field (R ⧸ P) := Ideal.Quotient.field P
      Subsingleton (CategoryTheory.Sheaf.H
        (Scheme.Modules.tensorObj
          (canonicalLineSheaf (Limits.pullback.snd p
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)))) n)
          ((Scheme.Modules.pullback (Limits.pullback.fst p
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))))).obj L)).sheaf (j + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf (fiberStructure P.ResidueField p) n)
        ((Scheme.Modules.pullback (fiberProjection P.ResidueField p)).obj L)).sheaf (j + 1)) :=
  (subsingleton_H_iff_moduleIso (fieldCanonicalTensorIso p n P.ResidueField L) (j + 1)).mp
    (nativeClosedModel_subsingleton_of_quotient p hp n L hL P j hclosed)

/-- The actual quotient-field closed vanishing reaches the prescribed
original injective ambient field square. All residue/model comparisons are
internally derived; the quotient and localization residue are retained. -/
theorem squareCanonicalTensor_subsingleton_of_quotient_of_injective [IsNoetherianRing R]
    (hp : IsProjectiveFactorization p) (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (P : Ideal R) [P.IsMaximal] (j : ℕ)
    (hclosed : letI : Field (R ⧸ P) := Ideal.Quotient.field P
      Subsingleton (CategoryTheory.Sheaf.H
        (Scheme.Modules.tensorObj
          (canonicalLineSheaf (Limits.pullback.snd p
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)))) n)
          ((Scheme.Modules.pullback (Limits.pullback.fst p
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))))).obj L)).sheaf (j + 1)))
    {F : Type u} [Field F] (φ : CommRingCat.of R ⟶ CommRingCat.of F)
    (hφ : Function.Injective φ.hom)
    {X : Scheme.{u}} (g : X ⟶ Y) (q : X ⟶ Spec (.of F))
    (H : IsPullback g q p (Spec.map φ)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf q n)
        ((Scheme.Modules.pullback g).obj L)).sheaf (j + 1)) :=
  ArithmeticCanonicalSpecializationCohomology.squareCanonicalTensor_subsingleton_of_closed_of_injective
    p hp n L hL P j
    (nativeResidueCanonicalTensor_subsingleton_of_quotient p hp n L hL P j hclosed)
    φ hφ g q H

end EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationQuotient
