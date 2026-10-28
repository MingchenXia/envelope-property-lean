import EnvelopeProperty.AlgGeom.SchemeAmpleClosedRestriction
import EnvelopeProperty.AlgGeom.ProjectiveTwistCoefficientPullback
import EnvelopeProperty.Projective.NativeBaseChange

/-! # Very ampleness and ampleness under base change of the coefficient ring

Let `p : X ⟶ Spec R` be a scheme over `R`, let `φ : R →+* S` be a ring map and let
```
Y --i--> X
|q       |p
v        v
Spec S --> Spec R
```
be a cartesian square. If `L` is very ample on `X` over `R`, witnessed by a closed immersion
`j : X ⟶ ℙⁿ_R` with `j^* O(1) ≅ L`, then the base change `i^* L` is very ample on `Y` over `S`:
the closed immersion is the base change of `j`, composed with the canonical identification
`ℙⁿ_R ×_{Spec R} Spec S ≅ ℙⁿ_S` (`ProjBerk.nativeCoefficientBaseChangeIso`), and `O(1)` on `ℙⁿ_S`
is the pullback of `O(1)` on `ℙⁿ_R` (`ProjectiveTwistCoefficientPullback`). Since ampleness is
the existence of a very ample positive tensor power and tensor powers commute with pullback, the
same holds for ampleness. No flatness of `φ` is needed.

This is used with `φ = ev₀ : k[t] →+* k` to restrict ampleness of a line on a model over `𝔸¹_k`
to its central fibre (blueprint `thm:pl-auxiliary-native-ampleness-base-change`).
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.PLModelAuxiliaryPolarization
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The structure morphism of `DeJongAlterations.projectiveSpace` is the native structure
morphism `ProjBerk.nativeStructureMap` of the same polynomial `Proj`. -/
theorem projectiveSpaceStructure_eq_nativeStructureMap (R : Type u) [CommRing R] (n : ℕ) :
    DeJongAlterations.projectiveSpaceStructure R n =
      ProjBerk.nativeStructureMap (R := R) (n := n) := by
  change Proj.toSpecZero (ProjBerk.ProjectiveGrading R n) ≫
        Spec.map (DeJongAlterations.projectiveSpaceDegreeZeroEquiv R n).toCommRingCatIso.hom =
      Proj.toSpecZero (ProjBerk.ProjectiveGrading R n) ≫
        Spec.map (CommRingCat.ofHom (ProjBerk.homogeneousCoefficientZero R n))
  congr 2

/-- Very ampleness is stable under an arbitrary base change `Spec S ⟶ Spec R`: the pullback of
a very ample line along the projection of a cartesian square is very ample. -/
theorem isVeryAmple_of_isPullback
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of S)) (i : Y ⟶ X)
    (H : IsPullback i q p (Spec.map (CommRingCat.ofHom φ)))
    (L : X.Modules) (hL : SchemeLineAmpleness.IsVeryAmple p L) :
    SchemeLineAmpleness.IsVeryAmple q ((Scheme.Modules.pullback i).obj L) := by
  obtain ⟨n, j, hj, hbase, ⟨eL⟩⟩ := hL
  let : IsClosedImmersion j := hj
  let π := ProjBerk.nativeStructureMap (R := R) (n := n)
  let b := Spec.map (CommRingCat.ofHom φ)
  have hjπ : j ≫ π = p :=
    (congrArg (fun f => j ≫ f) (projectiveSpaceStructure_eq_nativeStructureMap R n)).symm.trans
      hbase
  have hsq : (i ≫ j) ≫ π = q ≫ b := by
    rw [Category.assoc, hjπ]
    exact H.w
  let δ : Y ⟶ Limits.pullback π b := pullback.lift (i ≫ j) q hsq
  have hδfst : δ ≫ pullback.fst π b = i ≫ j := pullback.lift_fst _ _ _
  have hδsnd : δ ≫ pullback.snd π b = q := pullback.lift_snd _ _ _
  have hδsquare : IsPullback i δ j (pullback.fst π b) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd π b) (v₂₂ := π) ?_ hδfst.symm
      (IsPullback.of_hasPullback π b)
    rw [hδsnd, hjπ]
    exact H
  let : IsClosedImmersion δ := MorphismProperty.of_isPullback hδsquare inferInstance
  let E := ProjBerk.nativeCoefficientBaseChangeIso (n := n) φ
  have hEsnd : E.inv ≫ ProjBerk.nativeStructureMap (R := S) (n := n) = pullback.snd π b := by
    rw [Iso.inv_comp_eq]
    exact (ProjBerk.nativeCoefficientBaseChangeIso_hom_snd (n := n) φ).symm
  have hEcoeff : E.inv ≫ ProjBerk.nativeCoefficientMap φ = pullback.fst π b := by
    rw [Iso.inv_comp_eq]
    exact (ProjBerk.nativeCoefficientBaseChangeIso_hom_fst (n := n) φ).symm
  have hvbase : (δ ≫ E.inv) ≫ DeJongAlterations.projectiveSpaceStructure S n = q := by
    rw [projectiveSpaceStructure_eq_nativeStructureMap, Category.assoc, hEsnd, hδsnd]
  have hvcoeff : (δ ≫ E.inv) ≫ ProjBerk.nativeCoefficientMap φ = i ≫ j := by
    rw [Category.assoc, hEcoeff, hδfst]
  let ec : (Scheme.Modules.pullback (δ ≫ E.inv)).obj
      (MvPolynomial.coordinateHyperplaneTwist (R := S) (0 : Fin (n + 1)) 1) ≅
      (Scheme.Modules.pullback i).obj L :=
    (Scheme.Modules.pullback (δ ≫ E.inv)).mapIso
      (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso φ
        (0 : Fin (n + 1)) 1).symm ≪≫
      (pullbackComp (δ ≫ E.inv) (ProjBerk.nativeCoefficientMap φ)).app _ ≪≫
      (pullbackCongr hvcoeff).app _ ≪≫ ((pullbackComp i j).app _).symm ≪≫
      (Scheme.Modules.pullback i).mapIso eL
  exact ⟨n, δ ≫ E.inv, inferInstance, hvbase, ⟨ec⟩⟩

/-- Ampleness is stable under an arbitrary base change `Spec S ⟶ Spec R`: the pullback of an
ample line along the projection of a cartesian square is ample, with the same positive power
very ample. -/
theorem isAmple_of_isPullback
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of S)) (i : Y ⟶ X)
    (H : IsPullback i q p (Spec.map (CommRingCat.ofHom φ)))
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L) :
    SchemeLineAmpleness.IsAmple q ((Scheme.Modules.pullback i).obj L) := by
  obtain ⟨hInv, r, hr, hV⟩ := hL
  refine ⟨hInv.pullback i, r, hr, ?_⟩
  exact SchemeAmpleClosedRestriction.veryAmple_of_iso
    (isVeryAmple_of_isPullback φ p q i H (CanonicalGeometry.bundleTensorPower L r) hV)
    (BundleTensorPowerPullback.pullbackIso i L r)

end EnvelopeProperty.PLModelAuxiliaryPolarization
