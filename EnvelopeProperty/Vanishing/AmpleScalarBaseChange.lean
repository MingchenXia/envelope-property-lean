import EnvelopeProperty.AlgGeom.ProjectiveTwistCoefficientPullback
import EnvelopeProperty.AlgGeom.SchemeAmpleClosedRestriction

/-! # Actual scalar base change of the original geometric ample line

The original positive tensor power and whole projective twist are retained.
The coefficient map may be nonflat and noninjective.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.AmpleScalarBaseChange

open ProjBerk CanonicalGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Embedding

variable {R S : Type u} [CommRing R] [CommRing S] {N : ℕ} {X : Scheme.{u}}
    (j : X ⟶ NativeProjectiveScheme R N) (p : X ⟶ Spec (.of R))
    (hjp : j ≫ nativeStructureMap = p) (φ : R →+* S)

private def ambientMap :
    pullback p (Spec.map (CommRingCat.ofHom φ)) ⟶
      pullback (nativeStructureMap (R := R) (n := N)) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.map p (Spec.map (CommRingCat.ofHom φ)) nativeStructureMap
    (Spec.map (CommRingCat.ofHom φ)) j (𝟙 _) (𝟙 _) (by simpa using hjp.symm) (by simp)

private theorem ambientMap_fst :
    ambientMap j p hjp φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ j := by
  simp only [ambientMap, pullback.map, pullback.lift_fst]

private theorem ambientMap_snd :
    ambientMap j p hjp φ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [ambientMap, pullback.map, pullback.lift_snd, Category.comp_id]

private theorem ambientMap_isPullback :
    IsPullback (pullback.fst p (Spec.map (CommRingCat.ofHom φ))) (ambientMap j p hjp φ)
      j (pullback.fst _ _) := by
  apply IsPullback.of_bot
    (v₂₁ := pullback.snd (nativeStructureMap (R := R) (n := N))
      (Spec.map (CommRingCat.ofHom φ)))
    (v₂₂ := nativeStructureMap) ?_ (ambientMap_fst j p hjp φ).symm
    (IsPullback.of_hasPullback _ _)
  rw [ambientMap_snd, hjp]
  exact IsPullback.of_hasPullback _ _

/-- The actual closed embedding in the actual projective coefficient extension. -/
def embedding :
    pullback p (Spec.map (CommRingCat.ofHom φ)) ⟶ NativeProjectiveScheme S N :=
  ambientMap j p hjp φ ≫ (nativeCoefficientBaseChangeIso (n := N) φ).inv

/-- The constructed embedding is closed by the genuine Cartesian square. -/
theorem embedding_isClosedImmersion [IsClosedImmersion j] :
    IsClosedImmersion (embedding j p hjp φ) := by
  let : IsClosedImmersion (ambientMap j p hjp φ) :=
    MorphismProperty.of_isPullback (ambientMap_isPullback j p hjp φ) inferInstance
  change IsClosedImmersion
    (ambientMap j p hjp φ ≫ (nativeCoefficientBaseChangeIso (n := N) φ).inv)
  infer_instance

/-- The new structural morphism is precisely the actual second projection. -/
theorem embedding_projection :
    embedding j p hjp φ ≫ nativeStructureMap = pullback.snd _ _ := by
  have he : (nativeCoefficientBaseChangeIso (n := N) φ).inv ≫ nativeStructureMap =
      pullback.snd _ _ := by
    rw [← nativeCoefficientBaseChangeIso_hom_snd φ, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  change (ambientMap j p hjp φ ≫ (nativeCoefficientBaseChangeIso (n := N) φ).inv) ≫ _ = _
  rw [Category.assoc, he, ambientMap_snd]

/-- The same embedding retains its original ambient coefficient triangle. -/
theorem embedding_ambient :
    embedding j p hjp φ ≫ nativeCoefficientMap φ = pullback.fst _ _ ≫ j := by
  have he : (nativeCoefficientBaseChangeIso (n := N) φ).inv ≫ nativeCoefficientMap φ =
      pullback.fst _ _ := by
    rw [← nativeCoefficientBaseChangeIso_hom_fst φ, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  change (ambientMap j p hjp φ ≫ (nativeCoefficientBaseChangeIso (n := N) φ).inv) ≫ _ = _
  rw [Category.assoc, he, ambientMap_fst]

/-- Every original nonnegative projective twist has the whole actual pullback comparison. -/
def embedding_twistIso (d : ℕ) :
    (Scheme.Modules.pullback (embedding j p hjp φ)).obj
        (coordinateHyperplaneTwist (R := S) (0 : Fin (N + 1)) (d : ℤ)) ≅
      (Scheme.Modules.pullback (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))).obj
        ((Scheme.Modules.pullback j).obj
          (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (d : ℤ))) :=
  (Scheme.Modules.pullback (embedding j p hjp φ)).mapIso
      (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso φ
        (0 : Fin (N + 1)) d).symm ≪≫
    (Scheme.Modules.pullbackComp (embedding j p hjp φ) (nativeCoefficientMap φ)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (embedding_ambient j p hjp φ)).app _ ≪≫
    ((Scheme.Modules.pullbackComp (pullback.fst _ _) j).app _).symm

end Embedding

/-- Very ampleness of the original whole line survives arbitrary scalar extension. -/
theorem isVeryAmple {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (φ : R →+* S) (L : X.Modules)
    (hL : SchemeLineAmpleness.IsVeryAmple p L) :
    SchemeLineAmpleness.IsVeryAmple (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))
      ((Scheme.Modules.pullback (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))).obj L) := by
  obtain ⟨N, j, hj, hjp, ⟨e⟩⟩ := hL
  let : IsClosedImmersion j := hj
  refine ⟨N, embedding j p hjp φ, embedding_isClosedImmersion j p hjp φ,
    embedding_projection j p hjp φ, ?_⟩
  exact ⟨embedding_twistIso j p hjp φ 1 ≪≫
    (Scheme.Modules.pullback (pullback.fst _ _)).mapIso e⟩

/-- The SAME positive tensor power and actual invertible line prove ampleness
over the new coefficient ring, without a flatness or line-comparison input. -/
theorem isAmple {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (φ : R →+* S) (L : X.Modules)
    (hL : SchemeLineAmpleness.IsAmple p L) :
    SchemeLineAmpleness.IsAmple (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))
      ((Scheme.Modules.pullback (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))).obj L) := by
  refine ⟨hL.isInvertible.pullback _, ?_⟩
  obtain ⟨r, hr, hv⟩ := hL.2
  exact ⟨r, hr, SchemeAmpleClosedRestriction.veryAmple_of_iso
    (isVeryAmple p φ (bundleTensorPower L r) hv)
    (BundleTensorPowerPullback.pullbackIso (pullback.fst _ _) L r)⟩

/-- Any actual Cartesian scalar square retains very ampleness on its
original source and original structural morphism. -/
theorem isVeryAmple_of_isPullback {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} (g : Y ⟶ X) (p : X ⟶ Spec (.of R))
    (q : Y ⟶ Spec (.of S)) (φ : R →+* S)
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom φ)))
    (L : X.Modules) (hL : SchemeLineAmpleness.IsVeryAmple p L) :
    SchemeLineAmpleness.IsVeryAmple q ((Scheme.Modules.pullback g).obj L) := by
  obtain ⟨N, j, hj, hjp, ⟨eL⟩⟩ := hL
  let : IsClosedImmersion j := hj
  let E := H.isoPullback
  let jS := embedding j p hjp φ
  let : IsClosedImmersion jS := embedding_isClosedImmersion j p hjp φ
  refine ⟨N, E.hom ≫ jS, inferInstance, ?_, ?_⟩
  · exact (Category.assoc E.hom jS nativeStructureMap).trans
      ((congrArg (fun z => E.hom ≫ z) (embedding_projection j p hjp φ)).trans
        H.isoPullback_hom_snd)
  · exact ⟨((Scheme.Modules.pullbackComp E.hom jS).app _).symm ≪≫
      (Scheme.Modules.pullback E.hom).mapIso (embedding_twistIso j p hjp φ 1) ≪≫
      (Scheme.Modules.pullback E.hom).mapIso
        ((Scheme.Modules.pullback (pullback.fst _ _)).mapIso eL) ≪≫
      (Scheme.Modules.pullbackComp E.hom (pullback.fst _ _)).app L ≪≫
      (Scheme.Modules.pullbackCongr H.isoPullback_hom_fst).app L⟩

/-- The original ample line and positive exponent survive every actual
Cartesian coefficient square, including genuine residue fibres. -/
theorem isAmple_of_isPullback {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} (g : Y ⟶ X) (p : X ⟶ Spec (.of R))
    (q : Y ⟶ Spec (.of S)) (φ : R →+* S)
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom φ)))
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L) :
    SchemeLineAmpleness.IsAmple q ((Scheme.Modules.pullback g).obj L) := by
  refine ⟨hL.isInvertible.pullback g, ?_⟩
  obtain ⟨r, hr, hv⟩ := hL.2
  exact ⟨r, hr, SchemeAmpleClosedRestriction.veryAmple_of_iso
    (isVeryAmple_of_isPullback g p q φ H (bundleTensorPower L r) hv)
    (BundleTensorPowerPullback.pullbackIso g L r)⟩

end EnvelopeProperty.Vanishing.AmpleScalarBaseChange
