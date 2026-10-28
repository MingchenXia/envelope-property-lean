import EnvelopeProperty.DeligneIllusie.WittTwoAffineResidueGeometry

/-! # SAME actual inverse-image opens of the genuine global Witt special fibre -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreOpens
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

private theorem appLE_top {Z W : Scheme.{u}} (g : Z ⟶ W) :
    g.appLE ⊤ ⊤ le_top = g.appTop := by
  simpa only [Scheme.Hom.preimage_top] using (g.appLE_eq_app (U := ⊤))

private def nativeSections {K D : Type u} [CommRing K] [CommRing D] [Algebra K D]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) (e : Z ≅ Spec (CommRingCat.of D))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K D)) = g) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra g ⊤
    D ≃ₐ[K] Γ(Z,⊤) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra g ⊤
  let l : D →+* Γ(Z,⊤) := e.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of D)).inv.hom
  have hc (c : K) : l (algebraMap K D c) = algebraMap K Γ(Z,⊤) c := by
    have hn := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K D))) c
    have ht : (Spec.map (CommRingCat.ofHom (algebraMap K D))).appTop ≫ e.hom.appTop = g.appTop :=
      congrArg (fun z => z.appTop) he
    have htval := ConcreteCategory.congr_hom ht ((Scheme.ΓSpecIso (.of K)).inv c)
    have hu := ConcreteCategory.congr_hom (appLE_top g).symm ((Scheme.ΓSpecIso (.of K)).inv c)
    exact (congrArg (fun z => e.hom.appTop z) hn).trans (htval.trans hu)
  let eg : Γ(Spec (CommRingCat.of D),⊤) ≅ Γ(Z,⊤) :=
    { hom := e.hom.appTop
      inv := e.inv.appTop
      hom_inv_id := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
      inv_hom_id := by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop] }
  exact AlgEquiv.ofBijective { l with commutes' := hc }
    (eg.commRingCatIsoToRingEquiv.bijective.comp
      (Scheme.ΓSpecIso (.of D)).symm.commRingCatIsoToRingEquiv.bijective)

private theorem open_structure {Z S : Scheme.{u}} (g : Z ⟶ S) (V : Z.Opens) :
    (V.ι ≫ g).appTop ≫ V.topIso.hom = g.appLE ⊤ V le_top := by
  change g.appLE ⊤ (V.ι ''ᵁ ⊤) le_top ≫ Z.presheaf.map (eqToHom V.ι_image_top.symm).op = _
  exact Scheme.Hom.appLE_map' g le_top V.ι_image_top.symm

private def nativeOpenSections {K : Type u} [CommRing K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra (V.ι ≫ g) ⊤
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra g V
    Γ(V.toScheme,⊤) ≃ₐ[K] Γ(Z,V) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra (V.ι ≫ g) ⊤
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra g V
  refine { V.topIso.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  have hs := ConcreteCategory.congr_hom (appLE_top (V.ι ≫ g)) ((Scheme.ΓSpecIso (.of K)).inv c)
  have ht := ConcreteCategory.congr_hom (open_structure g V) ((Scheme.ΓSpecIso (.of K)).inv c)
  exact (congrArg (fun z => V.topIso.hom z) hs).trans ht

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
attribute [local instance] WittTwoResidue.reductionAlgebra
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))

/-- The ACTUAL global special fibre is the native categorical pullback of the original reduction. -/
abbrev specialFibre := pullback (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f

/-- The literal original inverse-image open in the SAME actual global special fibre. -/
def residueOpen (U : Y.Opens) : (specialFibre p k f).Opens :=
  pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f ⁻¹ᵁ U

private theorem openPullback (U : Y.Opens) :
    IsPullback
      ((residueOpen p k f U).ι ≫ pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f)
      (pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f ∣_ U)
      (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) (U.ι ≫ f) :=
  ((isPullback_morphismRestrict
    (pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f) U).paste_vert
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f).flip).flip

/-- The actual original inverse-image open IS its genuine local categorical special fibre. -/
def openFibreIso (U : Y.Opens) :
    (residueOpen p k f U).toScheme ≅ WittTwoAffineResidueGeometry.fibre p k f (U := U) :=
  (openPullback p k f U).isoPullback

/-- The whole original global special-fibre structural projection is retained on the actual open. -/
theorem openFibreIso_fst (U : Y.Opens) :
    (openFibreIso p k f U).hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) (U.ι ≫ f) =
    (residueOpen p k f U).ι ≫ pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f :=
  (openPullback p k f U).isoPullback_hom_fst

/-- The actual original lifted-open restriction is retained as a whole scheme morphism. -/
theorem openFibreIso_snd (U : Y.Opens) :
    (openFibreIso p k f U).hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) (U.ι ≫ f) =
    pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f ∣_ U :=
  (openPullback p k f U).isoPullback_hom_snd

/-- SAME original inverse-image affine open and SAME entire original residue tensor spectrum. -/
def residueOpenIso {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (residueOpen p k f U).toScheme ≅ Spec (CommRingCat.of
      (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U))) :=
  openFibreIso p k f U ≪≫ WittTwoAffineResidueGeometry.residueAffineIso p k f hU

/-- Actual affine opens of the lifted scheme have genuinely affine original inverse-image opens. -/
theorem residueOpen_affine {U : Y.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (residueOpen p k f U) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  exact IsAffine.of_isIso (residueOpenIso p k f hU).hom

/-- The SAME whole original residue tensor is the ACTUAL global special-fibre open section algebra. -/
def residueOpenSections {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra
      (pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f) (residueOpen p k f U)
    WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U) ≃ₐ[k]
      Γ(specialFibre p k f,residueOpen p k f U) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let g := pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra ((residueOpen p k f U).ι ≫ g) ⊤
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra g (residueOpen p k f U)
  have he : (residueOpenIso p k f hU).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)))) =
      (residueOpen p k f U).ι ≫ g := by
    rw [residueOpenIso, Iso.trans_hom, Category.assoc,
      WittTwoAffineResidueGeometry.residueAffineIso_fst, openFibreIso_fst]
  exact (nativeSections _ (residueOpenIso p k f hU) he).trans
    (nativeOpenSections g (residueOpen p k f U))

/-- EVERY whole original residue element has its SAME actual geometric section-map value. -/
theorem residueOpenSections_value {U : Y.Opens} (hU : IsAffineOpen U)
    (b : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    residueOpenSections p k f hU b = (residueOpen p k f U).topIso.hom
      ((residueOpenIso p k f hU).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)))).inv b)) := by
  rfl

end EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreOpens
