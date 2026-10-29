import EnvelopeProperty.Projective.NativeBaseChange
import EnvelopeProperty.Global.ReesNormalizedNative
import EnvelopeProperty.FlatGlobalSections
import ModularCurves.ForMathlib.ProjectiveFactorization

/-! # Genuine projective factorizations under arbitrary coefficient base change -/

open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.ProjectiveFactorizationBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual second projection of every coefficient base change has a genuine
projective factorization, constructed from the original closed immersion. -/
theorem baseChange (hf : IsProjectiveFactorization f) :
    IsProjectiveFactorization (FlatGlobalSections.structureMap (S := S) f) := by
  obtain ⟨d, i, hi, hif⟩ := hf
  let i' : X ⟶ ProjBerk.NativeProjectiveScheme R d := i
  let p := ProjBerk.nativeStructureMap (R := R) (n := d)
  let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hif' : i' ≫ p = f := hif
  let : IsClosedImmersion i' := hi
  rw [← hif']
  let j : pullback (i' ≫ p) b ⟶ pullback p b :=
    pullback.map (i' ≫ p) b p b i' (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hjfst : j ≫ pullback.fst p b = pullback.fst (i' ≫ p) b ≫ i' := by
    simp only [j, pullback.map, pullback.lift_fst]
  have hjsnd : j ≫ pullback.snd p b = pullback.snd (i' ≫ p) b := by
    simp only [j, pullback.map, pullback.lift_snd, Category.comp_id]
  have hj : IsPullback (pullback.fst (i' ≫ p) b) j i' (pullback.fst p b) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd p b) (v₂₂ := p) ?_ hjfst.symm
      (IsPullback.of_hasPullback p b)
    rw [hjsnd]
    exact IsPullback.of_hasPullback (i' ≫ p) b
  let : IsClosedImmersion j := MorphismProperty.of_isPullback hj inferInstance
  let E := ProjBerk.nativeCoefficientBaseChangeIso (n := d) (algebraMap R S)
  have hE : E.inv ≫ ProjBerk.nativeStructureMap (R := S) (n := d) =
      pullback.snd p b := by
    apply (cancel_epi E.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (ProjBerk.nativeCoefficientBaseChangeIso_hom_snd (n := d)
      (algebraMap R S)).symm
  refine ⟨d, j ≫ E.inv, inferInstance, ?_⟩
  change (j ≫ E.inv) ≫ ProjBerk.nativeStructureMap (R := S) (n := d) = _
  rw [Category.assoc, hE, hjsnd]

end EnvelopeProperty.ProjectiveFactorizationBaseChange

namespace EnvelopeProperty.ReesPresentation

variable {R : Type u} [CommRing R] {n : ℕ} (g : Fin (n+1) → R)

/-- The actual finite Rees quotient immersion is the required original
projective factorization; no projectivity premise is supplied. -/
theorem fcFiniteProjection_isProjectiveFactorization :
    IsProjectiveFactorization (fcFiniteProjection g) :=
  ⟨n, fcFiniteImmersion g, inferInstance, rfl⟩

end EnvelopeProperty.ReesPresentation
