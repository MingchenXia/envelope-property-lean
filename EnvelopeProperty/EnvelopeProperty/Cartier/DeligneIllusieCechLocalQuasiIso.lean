import EnvelopeProperty.Cartier.DeligneIllusieCechTotalEvaluation

/-! Detection on the actual open cover for the final integer-complex comparison. -/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieCechLocalQuasiIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u v

variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)

/-- Isomorphisms of the original module sheaves are detected on an actual cover. -/
theorem isIso_of_restrictions (hU : ⨆ i, U i = ⊤) {M N : X.Modules}
    (a : M ⟶ N) (ha : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map a)) :
    IsIso a := by
  have : IsIso ((Scheme.Modules.toSheaf X).map a) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro x
    have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    let y : (U i).toScheme := ⟨x, hi⟩
    let e := Scheme.Modules.restrictStalkNatIso (U i).ι y
    let F := Scheme.Modules.restrictFunctor (U i).ι ⋙
      Scheme.Modules.toPresheaf (U i).toScheme ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    let G := Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((U i).ι y)
    let : IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map a) := ha i
    have : IsIso (F.map a) := by
      dsimp only [F, Functor.comp_map]
      infer_instance
    have h := e.hom.naturality a
    have : IsIso (e.hom.app M ≫ G.map a) := by
      rw [← h]
      infer_instance
    have : IsIso (G.map a) := IsIso.of_isIso_comp_left (e.hom.app M) _
    exact this
  exact isIso_of_reflects_iso a (Scheme.Modules.toSheaf X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degreewise criterion uses the canonical homology of the same restrictions. -/
theorem quasiIsoAt_of_restrictions (hU : ⨆ i, U i = ⊤)
    {K L : CochainComplex X.Modules ℤ} (a : K ⟶ L) (q : ℤ)
    (ha : ∀ i, QuasiIsoAt
      (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex (.up ℤ)).map a) q) :
    QuasiIsoAt a q := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_of_restrictions U hU
  intro i
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let : F.PreservesHomology := SchemeOpenRestrictionHomology.preservesHomology (U i).ι
  let b := (HomologicalComplex.shortComplexFunctor X.Modules (.up ℤ) q).map a
  have hb : ShortComplex.QuasiIso (F.mapShortComplex.map b) := (ha i).quasiIso
  have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map b)) :=
    (ShortComplex.quasiIso_iff _).mp hb
  have : IsIso ((K.sc q).mapHomologyIso F).hom := inferInstance
  have : IsIso (((K.sc q).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap b)) := by
    rw [← ShortComplex.mapHomologyIso_hom_naturality b F]
    infer_instance
  change IsIso (F.map (ShortComplex.homologyMap b))
  exact IsIso.of_isIso_comp_left ((K.sc q).mapHomologyIso F).hom _

/-- Whole quasi-isomorphisms of integer complexes are detected on the actual cover. -/
theorem quasiIso_of_restrictions (hU : ⨆ i, U i = ⊤)
    {K L : CochainComplex X.Modules ℤ} (a : K ⟶ L)
    (ha : ∀ i, QuasiIso
      (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex (.up ℤ)).map a)) :
    QuasiIso a := by
  rw [quasiIso_iff]
  intro q
  apply quasiIsoAt_of_restrictions U hU a q
  intro i
  exact (ha i).quasiIsoAt q

end EnvelopeProperty.Cartier.DeligneIllusieCechLocalQuasiIso
