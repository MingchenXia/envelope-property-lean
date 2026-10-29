import EnvelopeProperty.DeligneIllusie.WittTwoSchemeAffineRestrictions
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The actual geometric affine special fibre is the SAME original residue tensor -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoAffineResidueGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u

private theorem affine_structure {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y,U))) = U.ι ≫ f := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  have he : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y,U))) = hU.fromSpec ≫ f := h
  calc
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y,U))) =
        hU.isoSpec.hom ≫ (hU.fromSpec ≫ f) := congrArg (fun z => hU.isoSpec.hom ≫ z) he
    _ = U.ι ≫ f := by rw [← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

private theorem nativeTensorSnd {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    (pullbackSpecIso R S T).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom) =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
  pullbackSpecIso_hom_snd R S T

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

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
variable {U : Y.Opens} (hU : IsAffineOpen U)

/-- The ACTUAL geometric affine special fibre, not a supplied residue model. -/
abbrev fibre := pullback (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) (U.ι ≫ f)

private def affinePullbackMap :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    fibre p k f (U := U) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap (WittTwo.Ring p k) k)))
        (Spec.map (CommRingCat.ofHom (algebraMap (WittTwo.Ring p k) Γ(Y,U)))) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  exact pullback.map _ _ _ _ (𝟙 _) hU.isoSpec.hom (𝟙 _)
    (by simp only [Category.id_comp, Category.comp_id])
    (by simpa only [Category.comp_id] using (affine_structure f hU).symm)

private instance affinePullbackMap_isIso :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    IsIso (affinePullbackMap p k f hU) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  unfold affinePullbackMap
  infer_instance

/-- The SAME original tensor ring is the actual categorical affine special fibre. -/
def residueAffineIso :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    fibre p k f (U := U) ≅ Spec (CommRingCat.of
      (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U))) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  exact asIso (affinePullbackMap p k f hU) ≪≫ pullbackSpecIso (WittTwo.Ring p k) k Γ(Y,U)

omit [CharP k p] [PerfectRing k p] in
/-- The actual original geometric residue projection is retained by the SAME entire isomorphism. -/
theorem residueAffineIso_fst :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (residueAffineIso p k f hU).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)))) =
    pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) (U.ι ≫ f) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  simp only [residueAffineIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackSpecIso_hom_fst', affinePullbackMap, pullback.map, pullback.lift_fst, Category.comp_id]

omit [CharP k p] [PerfectRing k p] in
/-- The actual original lifted-open projection is retained by the SAME whole isomorphism. -/
theorem residueAffineIso_snd :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (residueAffineIso p k f hU).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(Y,U) →ₐ[WittTwo.Ring p k]
        WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)).toRingHom) =
    pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) (U.ι ≫ f) ≫ hU.isoSpec.hom := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  simp only [residueAffineIso, Iso.trans_hom, asIso_hom, Category.assoc,
    nativeTensorSnd, affinePullbackMap, pullback.map, pullback.lift_snd]

/-- The SAME ENTIRE original residue tensor is the actual geometric affine-fibre section algebra. -/
def residueSections :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra
      (pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) (U.ι ≫ f)) ⊤
    WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U) ≃ₐ[k] Γ(fibre p k f (U := U),⊤) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  exact nativeSections _ (residueAffineIso p k f hU) (residueAffineIso_fst p k f hU)

end EnvelopeProperty.DeligneIllusie.WittTwoAffineResidueGeometry
