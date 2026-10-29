import EnvelopeProperty.DeligneIllusie.WittTwoNativeTwistRestriction
import EnvelopeProperty.DeligneIllusie.DeligneIllusieWittGlobalDescent
import EnvelopeProperty.DI.CechDegreeOneLocalData
import EnvelopeProperty.Cartier.GeometricCotangentRestrictions
import EnvelopeProperty.Cartier.GeometricAffineHomology
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Actual geometric divided Frobenius and canonical homotopy sheaf maps -/
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy

section AffineSheafMaps
variable (R : CommRingCat.{u}) (M N : (Spec R).Modules) [M.IsQuasicoherent]

private def specHomOfSections
    (l : (moduleSpecΓFunctor (R := R)).obj M ⟶ (moduleSpecΓFunctor (R := R)).obj N) : M ⟶ N := by
  letI : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact inv M.fromTildeΓ ≫
    ((tilde.adjunction (R := R)).homEquiv ((moduleSpecΓFunctor (R := R)).obj M) N).symm l

private theorem specHomOfSections_map
    (l : (moduleSpecΓFunctor (R := R)).obj M ⟶ (moduleSpecΓFunctor (R := R)).obj N) :
    (moduleSpecΓFunctor (R := R)).map (specHomOfSections R M N l) = l := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let Γ₀ := moduleSpecΓFunctor (R := R)
  let adj := tilde.adjunction (R := R)
  change Γ₀.map (inv M.fromTildeΓ ≫ (adj.homEquiv (Γ₀.obj M) N).symm l) = l
  rw [Γ₀.map_comp]
  have hu : Γ₀.map (inv M.fromTildeΓ) = adj.unit.app (Γ₀.obj M) := by
    apply (cancel_mono (Γ₀.map M.fromTildeΓ)).1
    rw [← Γ₀.map_comp, IsIso.inv_hom_id, Γ₀.map_id]
    exact (adj.right_triangle_components M).symm
  rw [hu]
  simpa only [adj.homEquiv_unit] using (adj.homEquiv (Γ₀.obj M) N).apply_symm_apply l

end AffineSheafMaps

section ActualAffineRestriction
variable {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W) (M N : Z.Modules)
  [((Scheme.Modules.restrictFunctor hW.fromSpec).obj M).IsQuasicoherent]

private def affineSpecMap (l : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    (Scheme.Modules.restrictFunctor hW.fromSpec).obj M ⟶
      (Scheme.Modules.restrictFunctor hW.fromSpec).obj N :=
  specHomOfSections Γ(Z,W)
    ((Scheme.Modules.restrictFunctor hW.fromSpec).obj M)
    ((Scheme.Modules.restrictFunctor hW.fromSpec).obj N)
    ((Cartier.GeometricAffineHomology.moduleSectionsIso hW M).hom ≫ l ≫
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW N).inv)

private theorem affineSpecMap_sections (l : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    (Cartier.GeometricAffineHomology.moduleSectionsIso hW M).inv ≫
        (moduleSpecΓFunctor (R := Γ(Z,W))).map (affineSpecMap hW M N l) ≫
          (Cartier.GeometricAffineHomology.moduleSectionsIso hW N).hom = l := by
  rw [affineSpecMap, specHomOfSections_map]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private def chartRestrictionIso (P : Z.Modules) :
    P.restrict W.ι ≅
      (Scheme.Modules.restrictFunctor hW.isoSpec.hom).obj (P.restrict hW.fromSpec) :=
  (Scheme.Modules.restrictFunctorCongr hW.isoSpec_hom_fromSpec).symm.app P ≪≫
    (Scheme.Modules.restrictFunctorComp hW.isoSpec.hom hW.fromSpec).app P

private def affineLocalMap (l : M.val.obj (op W) ⟶ N.val.obj (op W)) :
    M.restrict W.ι ⟶ N.restrict W.ι :=
  (chartRestrictionIso hW M).hom ≫
    (Scheme.Modules.restrictFunctor hW.isoSpec.hom).map (affineSpecMap hW M N l) ≫
      (chartRestrictionIso hW N).inv

end ActualAffineRestriction

section ActualExteriorSource
variable {K : Type u} [Field K] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K))
  {W : Z.Opens} (hW : IsAffineOpen W)

private def affineExteriorSourceIso {I : Type*} [LinearOrder I]
    (b : letI := CanonicalGeometry.affineChartAlgebra f W
      Module.Basis I Γ(Z,W) (KaehlerDifferential K Γ(Z,W))) (q : ℕ) :
    letI := CanonicalGeometry.affineChartAlgebra f W
    (Scheme.Modules.restrictFunctor hW.fromSpec).obj (CanonicalGeometry.exteriorCotangentSheaf f q) ≅
      tilde (CanonicalGeometry.affineExteriorCotangentModule K Γ(Z,W) q) := by
  letI := CanonicalGeometry.affineChartAlgebra f W
  exact CanonicalGeometry.exteriorCotangentSheafOpenImmersionIso f hW.fromSpec q ≪≫
    eqToIso (congrArg (fun a => CanonicalGeometry.exteriorCotangentSheaf a q)
      (CanonicalGeometry.affineChartStructuralMap_eq_affineStructuralMap f hW)) ≪≫
    CanonicalGeometry.affineExteriorCotangentSheafIso K Γ(Z,W) b q

private theorem affineExteriorSource_quasicoherent {I : Type*} [LinearOrder I]
    (b : letI := CanonicalGeometry.affineChartAlgebra f W
      Module.Basis I Γ(Z,W) (KaehlerDifferential K Γ(Z,W))) (q : ℕ) :
    ((Scheme.Modules.restrictFunctor hW.fromSpec).obj
      (CanonicalGeometry.exteriorCotangentSheaf f q)).IsQuasicoherent := by
  let := CanonicalGeometry.affineChartAlgebra f W
  let M := (Scheme.Modules.restrictFunctor hW.fromSpec).obj (CanonicalGeometry.exteriorCotangentSheaf f q)
  have hc : IsIso M.fromTildeΓ :=
    isIso_fromTildeΓ_iff.mpr
      ⟨CanonicalGeometry.affineExteriorCotangentModule K Γ(Z,W) q,
        ⟨(affineExteriorSourceIso f hW b q).symm⟩⟩
  exact (isQuasicoherent_iff_isIso_fromTildeΓ M).mpr hc

end ActualExteriorSource

section TwistedSourceBasis
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
  {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (v : Fin n → Γ(X,U))
  (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U
    (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "g" => pullback.snd f (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "W" => Cartier.RelativeTwistedAffineBasis.twistedOpen f p U
local notation "T" => Cartier.RelativeFrobenius.twist (algebraMap k (X.presheaf.obj (op U))) p
attribute [local instance] Cartier.RelativeEtaleCartierDomain.coefficientAlgebra

private def twistedCotangentBasis :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    letI : Algebra k ((Y).presheaf.obj (op W)) := CanonicalGeometry.affineChartAlgebra g W
    Module.Basis (Fin n) ((Y).presheaf.obj (op W))
      (KaehlerDifferential k ((Y).presheaf.obj (op W))) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  letI := CanonicalGeometry.affineChartAlgebra g W
  let A : CommRingCat := (Y).presheaf.obj (op W)
  letI : Algebra k A := CanonicalGeometry.affineChartAlgebra g W
  let σ : A ≅ T := Cartier.RelativeTwistedAffineCharts.sectionsIso f p U hU
  let M := (ModuleCat.restrictScalars σ.hom.hom).obj
    (ModuleCat.of (T) (KaehlerDifferential k (T)))
  letI : Module A (KaehlerDifferential k (T)) := M.isModule
  let ρ : (T) ≃+* A :=
    { __ := σ.inv.hom
      invFun := σ.hom
      left_inv := Iso.inv_hom_id_apply σ
      right_inv := Iso.hom_inv_id_apply σ }
  let bT : Module.Basis (Fin n) A M :=
    (Cartier.RelativeEtaleCartierDomain.cotangentBasis v hv p).mapCoeffs ρ (by
      intro t x
      change σ.hom.hom (σ.inv.hom t) • x = t • x
      exact congrArg (fun a : T => a • x) (Iso.inv_hom_id_apply σ t))
  let e := Cartier.GeometricCotangentRestrictions.rawCotangentIso f p hU
  exact bT.map e.toLinearEquiv.symm

end TwistedSourceBasis

section WittGeometricMaps
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
  {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p k)))
  (n : ℕ) [SmoothOfRelativeDimension n f]
attribute [local instance] WittTwoResidue.reductionAlgebra
  Algebra.TensorProduct.rightAlgebra Cartier.RelativeEtaleCartierDomain.coefficientAlgebra

private abbrev fibre := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev fibreMap : fibre p k f ⟶ Spec (.of k) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
private abbrev fibreOpen (U : Xtilde.Opens) := WittTwoSpecialFibreOpens.residueOpen p k f U
private abbrev fibreSections (U : Xtilde.Opens) : CommRingCat :=
  (fibre p k f).presheaf.obj (op (fibreOpen p k f U))
private abbrev twistFibre := Cartier.SchemeRelativeFrobenius.twist p (fibreMap p k f)
private abbrev twistProjection : twistFibre p k f ⟶ Spec (.of k) :=
  pullback.snd (fibreMap p k f) (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)
private abbrev chartOpen (U : Xtilde.Opens) :=
  Cartier.RelativeTwistedAffineBasis.twistedOpen (fibreMap p k f) p (fibreOpen p k f U)
private abbrev wittResidue (U : Xtilde.Opens) :=
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Xtilde,U)
private abbrev sourceSheaf := CanonicalGeometry.exteriorCotangentSheaf (twistProjection p k f) 1
private abbrev targetSheaf (q : ℕ) :=
  Cartier.SchemeRelativeFrobeniusDeRham.formModule (fibreMap p k f) p q

variable {U : Xtilde.Opens} (hU : IsAffineOpen U)
  (v : Fin n → fibreSections p k f U)
  (hv : letI := CanonicalGeometry.cotangentOpenAlgebra (fibreMap p k f) (fibreOpen p k f U)
    (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
local notation "T" => Cartier.RelativeFrobenius.twist (algebraMap k (fibreSections p k f U)) p

private def transportSectionMap (q : ℕ)
    (φ : letI := CanonicalGeometry.cotangentOpenAlgebra (fibreMap p k f) (fibreOpen p k f U)
      ModuleCat.of (T) (KaehlerDifferential k (T)) ⟶
        Cartier.SchemeRelativeFrobeniusAffineDeRham.formModule
          (k := k) (B := fibreSections p k f U) p q) :
    (sourceSheaf p k f).val.obj (op (chartOpen p k f U)) ⟶
      (targetSheaf p k f q).val.obj (op (chartOpen p k f U)) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra (fibreMap p k f) (fibreOpen p k f U)
  letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let σ := Cartier.RelativeTwistedAffineCharts.sectionsIso
    (fibreMap p k f) p (fibreOpen p k f U) hU₀
  let one : ModuleCat.of (T) (⋀[T]^1 (KaehlerDifferential k (T))) ⟶
      ModuleCat.of (T) (KaehlerDifferential k (T)) :=
    ModuleCat.ofHom
      (X := ModuleCat.of (T) (⋀[T]^1 (KaehlerDifferential k (T))))
      (Y := ModuleCat.of (T) (KaehlerDifferential k (T)))
      (exteriorPower.oneEquiv (T) (KaehlerDifferential k (T))).toLinearMap
  exact (Cartier.GeometricLocalCartier.domainIso (fibreMap p k f) p hU₀ n v hv 1).hom ≫
    (ModuleCat.restrictScalars σ.hom.hom).map one ≫
    (ModuleCat.restrictScalars σ.hom.hom).map φ ≫
    (Cartier.GeometricComplexExchange.formIso (fibreMap p k f) p n hU₀ v hv q).hom

/-- The SAME actual canonical Witt one-form on the literal geometric sections, with original source and target units. -/
def xiSectionMap
    (F : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      WittTwoLiftDifference.Lift p k Γ(Xtilde,U))
    (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      ∀ t, algebraMap Γ(Xtilde,U) (wittResidue p k f U) (F t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t) :
    (sourceSheaf p k f).val.obj (op (chartOpen p k f U)) ⟶
      (targetSheaf p k f 1).val.obj (op (chartOpen p k f U)) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth n f
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  letI := CanonicalGeometry.cotangentOpenAlgebra (fibreMap p k f) (fibreOpen p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let Ξ := WittTwoNativeTwistRestriction.oneFormAlongEquiv p k e F hF
  exact transportSectionMap p k f n hU v hv 1
    (ModuleCat.ofHom
      (X := ModuleCat.of (T) (KaehlerDifferential k (T)))
      (Y := Cartier.SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := fibreSections p k f U) p 1) Ξ)

/-- The SAME original canonical Witt difference term on actual geometric zero-form sections. -/
def homotopySectionMap
    (F G : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      WittTwoLiftDifference.Lift p k Γ(Xtilde,U))
    (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      ∀ t, algebraMap Γ(Xtilde,U) (wittResidue p k f U) (F t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t)
    (hG : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      ∀ t, algebraMap Γ(Xtilde,U) (wittResidue p k f U) (G t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t) :
    (sourceSheaf p k f).val.obj (op (chartOpen p k f U)) ⟶
      (targetSheaf p k f 0).val.obj (op (chartOpen p k f U)) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth n f
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  letI := CanonicalGeometry.cotangentOpenAlgebra (fibreMap p k f) (fibreOpen p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let H := WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k e F G hF hG
  exact transportSectionMap p k f n hU v hv 0
    (ModuleCat.ofHom
      (X := ModuleCat.of (T) (KaehlerDifferential k (T)))
      (Y := Cartier.SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := fibreSections p k f U) p 0) H)

/-- A genuine local sheaf morphism induced by the SAME original geometric divided Frobenius sections. -/
def xiSheafMap
    (F : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      WittTwoLiftDifference.Lift p k Γ(Xtilde,U))
    (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      ∀ t, algebraMap Γ(Xtilde,U) (wittResidue p k f U) (F t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t) :
    (sourceSheaf p k f).restrict (chartOpen p k f U).ι ⟶
      (targetSheaf p k f 1).restrict (chartOpen p k f U).ι := by
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hW := Cartier.RelativeTwistedAffineBasis.twistedOpen_isAffine
    (fibreMap p k f) p (fibreOpen p k f U) hU₀
  letI : ((Scheme.Modules.restrictFunctor hW.fromSpec).obj (sourceSheaf p k f)).IsQuasicoherent :=
    affineExteriorSource_quasicoherent (twistProjection p k f) hW
      (twistedCotangentBasis (fibreMap p k f) p hU₀ v hv) 1
  exact affineLocalMap hW (sourceSheaf p k f) (targetSheaf p k f 1)
    (xiSectionMap p k f n hU v hv F hF)

/-- A genuine local sheaf morphism induced by the SAME canonical geometric Witt homotopy term. -/
def homotopySheafMap
    (F G : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      WittTwoLiftDifference.Lift p k Γ(Xtilde,U))
    (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      ∀ t, algebraMap Γ(Xtilde,U) (wittResidue p k f U) (F t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t)
    (hG : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      ∀ t, algebraMap Γ(Xtilde,U) (wittResidue p k f U) (G t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t) :
    (sourceSheaf p k f).restrict (chartOpen p k f U).ι ⟶
      (targetSheaf p k f 0).restrict (chartOpen p k f U).ι := by
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hW := Cartier.RelativeTwistedAffineBasis.twistedOpen_isAffine
    (fibreMap p k f) p (fibreOpen p k f U) hU₀
  letI : ((Scheme.Modules.restrictFunctor hW.fromSpec).obj (sourceSheaf p k f)).IsQuasicoherent :=
    affineExteriorSource_quasicoherent (twistProjection p k f) hW
      (twistedCotangentBasis (fibreMap p k f) p hU₀ v hv) 1
  exact affineLocalMap hW (sourceSheaf p k f) (targetSheaf p k f 0)
    (homotopySectionMap p k f n hU v hv F G hF hG)

end WittGeometricMaps

end EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
