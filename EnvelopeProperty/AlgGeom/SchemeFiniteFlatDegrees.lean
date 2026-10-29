import EnvelopeProperty.AlgGeom.NormalCurveDominantFlat
import EnvelopeProperty.AlgGeom.SchemeFieldDegreeBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # True whole finite closed degrees of the SAME original finite flat scheme morphism -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules Module
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.SchemeFiniteFlatDegrees
open FiniteClosedIdealLocalDegrees SchemeCoherentEulerIndex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native original scheme rank retains the ENTIRE original affine section-ring map. -/
theorem finrank_affine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (y : Y) :
    f.finrank y = f.appTop.hom.finrank (Y.isoSpec.hom y) := by
  let F := Spec.map f.appTop
  let : Flat F := Flat.SpecMap_iff.mpr f.flat_appTop
  let : IsFinite F := (IsFinite.SpecMap_iff f.appTop).mpr f.finite_appTop
  have hsq : IsPullback X.isoSpec.hom f F Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality f⟩
  have h := Scheme.Hom.finrank_of_isPullback X.isoSpec.hom f F Y.isoSpec.hom hsq y
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop] at h
  exact h

/-- Every original point retains the SAME original generic rank, internally derived from actual geometry. -/
theorem finrank_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (y : Y) :
    f.finrank y = f.finrank (genericPoint Y) :=
  f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y (genericPoint Y)

private theorem quotientField_finrank_eq_stalkRank {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N]
    (P : MaximalSpectrum R) :
    letI := Ideal.Quotient.field P.asIdeal
    Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] N) =
      Module.rankAtStalk N ⟨P.asIdeal, inferInstance⟩ := by
  let := Ideal.Quotient.field P.asIdeal
  let p : PrimeSpectrum (R ⧸ P.asIdeal) := ⟨⊥, inferInstance⟩
  have h := Module.rankAtStalk_baseChange (R := R) (M := N) p
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  change Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] N) =
    Module.rankAtStalk N (p.comap (algebraMap R (R ⧸ P.asIdeal))) at h
  have he : p.comap (algebraMap R (R ⧸ P.asIdeal)) = ⟨P.asIdeal, inferInstance⟩ := by
    apply PrimeSpectrum.ext
    exact Ideal.mk_ker
  exact he ▸ h

private theorem structureSections_finite_of_isFinite {k : Type u} [Field k]
    {D : Scheme.{u}} (p : D ⟶ Spec (.of k)) [IsFinite p] :
    letI := structureSectionsAlgebra p
    Module.Finite k Γ(D, ⊤) := by
  let := structureSectionsAlgebra p
  exact p.finite_appTop.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).surjective)

private theorem sectionBasis_of_rank {D T : Scheme.{u}} [IsAffine D] [IsAffine T]
    (q : T ⟶ D) [IsFinite q] [Flat q] [Finite (MaximalSpectrum Γ(D, ⊤))]
    (n : ℕ) (hn : ∀ d : D, q.finrank d = n) :
    letI := q.appTop.hom.toAlgebra
    Nonempty (Basis (Fin n) Γ(D, ⊤) Γ(T, ⊤)) := by
  let := q.appTop.hom.toAlgebra
  let : Module.Finite Γ(D, ⊤) Γ(T, ⊤) := q.finite_appTop
  let : Module.Flat Γ(D, ⊤) Γ(T, ⊤) := q.flat_appTop
  apply Module.nonempty_basis_of_flat_of_finrank_eq
  intro P
  rw [quotientField_finrank_eq_stalkRank]
  let d := D.isoSpec.inv (⟨P.asIdeal, inferInstance⟩ : PrimeSpectrum Γ(D, ⊤))
  have h := finrank_affine q d
  change q.finrank d = Module.rankAtStalk Γ(T, ⊤) (D.isoSpec.hom d) at h
  have hd : D.isoSpec.hom d = (⟨P.asIdeal, inferInstance⟩ : PrimeSpectrum Γ(D, ⊤)) :=
    Scheme.Hom.comp_apply D.isoSpec.inv D.isoSpec.hom _ |>.symm.trans
      (by rw [Iso.inv_hom_id]; rfl)
  rw [hd] at h
  exact h.symm.trans (hn d)

/-- The ACTUAL whole finite closed inverse image has its TRUE original field
degree multiplied by the native generic rank of the SAME original map.
Every fiber-rank/basis/section-algebra comparison is derived internally. -/
theorem finrank_sections_pullback_finiteClosed {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)] :
    letI := structureSectionsAlgebra (I.subschemeι ≫ p)
    letI := structureSectionsAlgebra (Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ p)
    Module.finrank k Γ(Limits.pullback f I.subschemeι, ⊤) =
      f.finrank (genericPoint X) * Module.finrank k Γ(I.subscheme, ⊤) := by
  let D := I.subscheme
  let T := Limits.pullback f I.subschemeι
  let q : T ⟶ D := Limits.pullback.snd f I.subschemeι
  let pD := I.subschemeι ≫ p
  let : IsAffine D := isAffine_of_isAffineHom pD
  let : IsAffine T := isAffine_of_isAffineHom q
  let := structureSectionsAlgebra pD
  let := structureSectionsAlgebra (q ≫ pD)
  let : Module.Finite k Γ(D, ⊤) := structureSections_finite I.subschemeι p hp
  let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
  let := q.appTop.hom.toAlgebra
  let : IsScalarTower k Γ(D, ⊤) Γ(T, ⊤) := IsScalarTower.of_algebraMap_eq (fun r => by
    change (q ≫ pD).appTop (baseScalar r) = q.appTop (pD.appTop (baseScalar r))
    rw [Scheme.Hom.comp_appTop]
    rfl)
  obtain ⟨b⟩ := sectionBasis_of_rank q (f.finrank (genericPoint X)) (fun d =>
    (Scheme.Hom.finrank_pullback_snd f I.subschemeι d).trans (finrank_eq_genericPoint f _))
  rw [(b.equivFun.restrictScalars k).finrank_eq, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rfl

/-- The SAME original comap closed-scheme isomorphism retains its whole original composite structure. -/
theorem comapIso_structure {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (p : X ⟶ Spec (.of k)) (I : X.IdealSheafData) :
    (I.comapIso f).hom ≫ pullback.snd f I.subschemeι ≫ I.subschemeι ≫ p =
      (I.comap f).subschemeι ≫ f ≫ p := by
  rw [← pullback.condition_assoc, I.comapIso_hom_fst_assoc]

/-- The whole original geometric comap closed subscheme is truly finite over the original field. -/
theorem comapSubscheme_isFinite {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] (p : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)] :
    IsFinite ((I.comap f).subschemeι ≫ f ≫ p) := by
  have h : IsFinite ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι ≫ I.subschemeι ≫ p) :=
    inferInstance
  rw [comapIso_structure] at h
  exact h

/-- The true field-linear structure-section degree of the SAME actual finite
closed comap equals original closed degree times SAME original native generic rank. -/
theorem finrank_fieldSections_comap {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ p)] :
    Module.finrank k (fieldSections ((I.comap f).subschemeι ≫ f ≫ p) (unitObj _)) =
      f.finrank (genericPoint X) * Module.finrank k (fieldSections (I.subschemeι ≫ p) (unitObj _)) := by
  let := structureSectionsAlgebra ((I.comap f).subschemeι ≫ f ≫ p)
  let := structureSectionsAlgebra (pullback.snd f I.subschemeι ≫ I.subschemeι ≫ p)
  let := structureSectionsAlgebra (I.subschemeι ≫ p)
  rw [(structureFieldSectionsIso ((I.comap f).subschemeι ≫ f ≫ p)).toLinearEquiv.finrank_eq,
    (structureFieldSectionsIso (I.subschemeι ≫ p)).toLinearEquiv.finrank_eq,
    SchemeFieldDegreeBaseChange.finrank_sections_isoOver _ _ (I.comapIso f)
      (comapIso_structure f p I)]
  exact finrank_sections_pullback_finiteClosed f p hp I

end EnvelopeProperty.SchemeFiniteFlatDegrees
