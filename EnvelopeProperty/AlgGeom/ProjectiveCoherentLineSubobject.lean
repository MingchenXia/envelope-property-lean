import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionProjectiveAnnihilator
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCoherentDevissage
import EnvelopeProperty.AlgGeom.SchemeModuleStalkLinearity
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorFiniteType
import EnvelopeProperty.AlgGeom.SchemeTensorUnitSections
import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso

/-! # Actual original invertible subobjects on integral projective strata -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCoherentLineSubobject

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- A nonzero actual generic stalk map from an original line is genuinely monic. -/
theorem mono_of_genericStalk_nonzero {X : Scheme.{u}} [IsIntegral X]
    (T : X.Modules) (hT : IsInvertible T) {M : X.Modules} (v : T ⟶ M)
    (hv : ∃ m : T.presheaf.stalk (genericPoint X),
      ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        (genericPoint X)).map v) m ≠ 0) : Mono v := by
  let a := CanonicalGeometry.invertibleLineAtlas T hT
  obtain ⟨U, hU, ⟨e⟩⟩ := a.exists_generic_frame
  let : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  let f : CanonicalGeometry.genericBundleFiber T →ₗ[X.functionField]
      CanonicalGeometry.genericBundleFiber M :=
    SchemeModuleStalkLinearity.stalkMapLinear v (genericPoint X)
  have hg : f (CanonicalGeometry.genericFrameGenerator e) ≠ 0 := by
    intro hg
    obtain ⟨m, hm⟩ := hv
    obtain ⟨r, hr⟩ := CanonicalGeometry.genericBundleFiber_eq_smul_generator e m
    apply hm
    change f m = 0
    rw [hr, f.map_smul, hg, smul_zero]
  apply SeshadriAmplenessCriterion.mono_of_genericStalk_injective T hT v
  intro m n hmn
  change f m = f n at hmn
  obtain ⟨r, hr⟩ := CanonicalGeometry.genericBundleFiber_eq_smul_generator e m
  obtain ⟨s, hs⟩ := CanonicalGeometry.genericBundleFiber_eq_smul_generator e n
  rw [hr, hs, f.map_smul, f.map_smul] at hmn
  have hrs : r = s := (smul_left_injective X.functionField hg) hmn
  exact hr.trans ((congrArg
    (fun c : X.functionField => c • CanonicalGeometry.genericFrameGenerator e) hrs).trans hs.symm)

/-- Original line frames and actual restriction-stalk isomorphisms preserve
nonzero elements in the SAME original stalk after tensoring by the line. -/
theorem exists_nativeStalk_tensorRight_ne_zero {X : Scheme.{u}}
    (M B : X.Modules) (hB : IsInvertible B) (x : X)
    (hM : ∃ m : M.presheaf.stalk x, m ≠ 0) :
    ∃ m : (M ⊗ B).presheaf.stalk x, m ≠ 0 := by
  obtain ⟨ι, U, hU, htriv⟩ := hB
  have hx : x ∈ ⨆ i : ι, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let y : (U i).toScheme := ⟨x, hi⟩
  let eB : B.restrict (U i).ι ≅ unitObj (U i).toScheme :=
    restrictIsoOfPullbackIso B (U i) (htriv i).some
  let eT := SchemeInvertibleTensorQuasicoherent.restrictTensorIsoOfFrame M B (U i) eB
  let F := Scheme.Modules.toPresheaf (U i).toScheme ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let S := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let E : S.obj (M ⊗ B) ≅ S.obj M :=
    ((Scheme.Modules.restrictStalkNatIso (U i).ι y).app (M ⊗ B)).symm ≪≫
      F.mapIso eT ≪≫ (Scheme.Modules.restrictStalkNatIso (U i).ι y).app M
  obtain ⟨m, hm⟩ := hM
  refine ⟨E.inv m, ?_⟩
  intro hz
  have he : E.inv m = E.inv (0 : M.presheaf.stalk x) :=
    hz.trans E.inv.hom.map_zero.symm
  exact hm ((ConcreteCategory.bijective_of_isIso E.inv).1 he)

/-- Some SAME original finite global generator has an actual nonzero
original generic stalk map, derived from its original affine spanning family. -/
theorem exists_generator_genericStalk_nonzero {X : Scheme.{u}} [IsIntegral X]
    (M : X.Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType]
    (hM : ∃ m : M.presheaf.stalk (genericPoint X), m ≠ 0) :
    ∃ i : G.I, ∃ m : (unitObj X).presheaf.stalk (genericPoint X),
      ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        (genericPoint X)).map (SchemeGeneratingSectionsUnit.generatorHom G i)) m ≠ 0 := by
  classical
  by_contra hz
  push Not at hz
  obtain ⟨m, hm⟩ := hM
  obtain ⟨U, hηU, s, hs⟩ := M.presheaf.exists_germ_eq m
  obtain ⟨V, hV, hηV, hVU⟩ := exists_isAffineOpen_mem_and_subset hηU
  let : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
  let E : Γ(M, V) →ₛₗ[(X.germToFunctionField V).hom]
      M.presheaf.stalk (genericPoint X) := CanonicalGeometry.bundleGenericGerm M V
  let t : Γ(M, V) := M.presheaf.map (homOfLE hVU).op s
  have ht : E t = m :=
    (M.presheaf.germ_res_apply (homOfLE hVU) (genericPoint X) hηV s).trans hs
  let S : Set Γ(M, V) := Set.range fun i : G.I =>
    (SchemeGeneratingSectionsUnit.generatorHom G i).val.app (op V) (1 : Γ(X, V))
  have hspan : Submodule.span Γ(X, V) S = ⊤ :=
    SeshadriAmplenessCriterion.finiteGenerator_span M G V hV
  have hle : Submodule.span Γ(X, V) S ≤ E.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let v := SchemeGeneratingSectionsUnit.generatorHom G i
    let w : (unitObj X).presheaf.stalk (genericPoint X) :=
      (unitObj X).presheaf.germ V (genericPoint X) hηV (1 : Γ(X, V))
    have hn := TopCat.Presheaf.stalkFunctor_map_germ_apply V (genericPoint X) hηV
      ((toPresheaf X).map v) (1 : Γ(X, V))
    have hc : E (v.val.app (op V) (1 : Γ(X, V))) =
        ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          (genericPoint X)).map v) w := hn.symm
    exact hc.trans (hz i w)
  have htspan : t ∈ Submodule.span Γ(X, V) S := by rw [hspan]; trivial
  have htzero : E t = 0 := hle htspan
  exact hm (ht.symm.trans htzero)

/-- Native projectivity and original QC/FT internally choose a genuine
invertible line and an ACTUAL whole monomorphism into the same original module.
Only nonzeroness of the original native generic stalk is assumed. -/
theorem exists_invertible_mono_of_isProjective
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of R)) [IsProjective p]
    (N : X.Modules) [N.IsQuasicoherent] [N.IsFiniteType]
    (hN : ∃ m : N.presheaf.stalk (genericPoint X), m ≠ 0) :
    ∃ T : X.Modules, IsInvertible T ∧ ∃ v : T ⟶ N, Mono v := by
  classical
  obtain ⟨d, i, hi, _⟩ := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsClosedImmersion i := hi
  let j : Fin (d + 1) := 0
  obtain ⟨n, hn⟩ := ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections i N j
  let B : X.Modules := (Scheme.Modules.pullback i).obj
    (MvPolynomial.coordinateHyperplaneTwist (R := R) j (n : ℤ))
  have hB : IsInvertible B :=
    (MvPolynomial.coordinateHyperplaneTwist_isInvertible j (n : ℤ)).pullback i
  obtain ⟨G, hG⟩ := hn n le_rfl
  let : G.IsFiniteType := hG
  let : (N ⊗ B).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight N B hB
  have hNB : ∃ m : (N ⊗ B).presheaf.stalk (genericPoint X), m ≠ 0 :=
    exists_nativeStalk_tensorRight_ne_zero N B hB (genericPoint X) hN
  obtain ⟨k, hk⟩ := exists_generator_genericStalk_nonzero (N ⊗ B) G hNB
  let g : unitObj X ⟶ N ⊗ B := SchemeGeneratingSectionsUnit.generatorHom G k
  let : Mono g := mono_of_genericStalk_nonzero (unitObj X) isInvertible_unit g hk
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence B hB
  have hmap : Mono (E.inverse.map g) :=
    CategoryTheory.preserves_mono_of_preservesLimit E.inverse g
  let D := dualObj B
  let a : E.inverse.obj (unitObj X) ≅ D := SchemeTensorUnitSections.leftUnitIso D
  let b : E.inverse.obj (N ⊗ B) ≅ N := (E.unitIso.app N).symm
  let v : D ⟶ N := a.inv ≫ E.inverse.map g ≫ b.hom
  have ha : Mono a.inv := by infer_instance
  have hb : Mono b.hom := by infer_instance
  refine ⟨D, hB.dual, v, ?_⟩
  exact mono_comp' ha (mono_comp' hmap hb)

end EnvelopeProperty.ProjectiveCoherentLineSubobject
