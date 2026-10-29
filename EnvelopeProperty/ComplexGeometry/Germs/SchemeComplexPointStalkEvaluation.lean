import EnvelopeProperty.ComplexGeometry.Germs.SchemeAffineStalkGerm
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Canonical complex-point evaluation of the original scheme stalk

The existing Spec-field stalk isomorphism and original morphism stalk maps
manufacture evaluation. On the entire original stalk it agrees with native
holomorphic germ evaluation, via the existing affine localization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open scoped Topology Manifold

private def complexDefaultStalkIso :
    (Spec (.of ℂ)).presheaf.stalk (default : Spec (.of ℂ)) ≅ CommRingCat.of ℂ :=
  (Spec (.of ℂ)).presheaf.stalkCongr
    (.of_eq (Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ))) ≪≫
      stalkClosedPointIso (.of ℂ)

private theorem complexDefaultStalkIso_germ :
    (Spec (.of ℂ)).presheaf.germ ⊤ default trivial ≫ complexDefaultStalkIso.hom =
      (Scheme.ΓSpecIso (.of ℂ)).hom := by
  dsimp only [complexDefaultStalkIso, Iso.trans_hom]
  rw [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes]
  exact germ_stalkClosedPointIso_hom (.of ℂ)

private def complexPointStalkEvaluation {X : Scheme} (p : Spec (.of ℂ) ⟶ X) :
    X.presheaf.stalk (p default) ⟶ CommRingCat.of ℂ :=
  p.stalkMap default ≫ complexDefaultStalkIso.hom

private theorem complexPointStalkEvaluation_affine {A : CommRingCat}
    (z : Spec (.of ℂ) ⟶ Spec A) :
    (Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ (z default) trivial ≫
      complexPointStalkEvaluation z = Spec.preimage z := by
  unfold complexPointStalkEvaluation
  rw [← Category.assoc _ (z.stalkMap default), Scheme.Hom.germ_stalkMap]
  simp only [Category.assoc]
  rw [← Spec.map_preimage z, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  change Spec.preimage z ≫ (Scheme.ΓSpecIso (.of ℂ)).inv ≫
    (Spec (.of ℂ)).presheaf.germ ⊤ default trivial ≫ complexDefaultStalkIso.hom = _
  rw [complexDefaultStalkIso_germ, Iso.inv_hom_id, Category.comp_id, Spec.preimage_map]

private theorem complexPointStalkEvaluation_localization {X : Scheme} {A : CommRingCat}
    (c : Spec A ⟶ X) [IsOpenImmersion c] (z : Spec (.of ℂ) ⟶ Spec A)
    (y : Spec A) (hy : z default = y) (p : Spec (.of ℂ) ⟶ X) (hp : z ≫ c = p)
    (hxy : c y = p default) :
    CommRingCat.ofHom (algebraMap A (Localization.AtPrime y.asIdeal)) ≫
      ((Spec.stalkIso A y).symm ≪≫ (asIso (c.stalkMap y)).symm ≪≫
        X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫
          complexPointStalkEvaluation p = Spec.preimage z := by
  subst p
  subst y
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv,
    TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.assoc]
  rw [Spec.algebraMap_stalkIso_inv_assoc]
  unfold complexPointStalkEvaluation
  rw [Scheme.Hom.stalkMap_comp]
  simp only [Category.assoc]
  erw [Category.id_comp, IsIso.inv_hom_id_assoc]
  exact complexPointStalkEvaluation_affine z

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- The actual complex point canonically evaluates its entire original algebraic stalk. -/
def schemeComplexPointStalkEval (p : SchemeComplexPoint f) :
    X.presheaf.stalk (schemeComplexPointImage f p) →+* ℂ :=
  (complexPointStalkEvaluation p.val).hom

/-- The canonical original-stalk evaluation commutes with every original scheme morphism. -/
theorem schemeComplexPointStalkEval_comp {Y : Scheme} (g : Y ⟶ Spec (.of ℂ))
    (h : X ⟶ Y) (hh : h ≫ g = f) (p : SchemeComplexPoint f) :
    schemeComplexPointStalkEval g (schemeComplexPointMap f g h hh p) =
      (schemeComplexPointStalkEval f p).comp
        (h.stalkMap (schemeComplexPointImage f p)).hom := by
  change (complexPointStalkEvaluation (p.val ≫ h)).hom = _
  unfold complexPointStalkEvaluation
  rw [Scheme.Hom.stalkMap_comp, Category.assoc]
  rfl

/-- Every original affine coefficient has its literal value at the same actual point. -/
theorem schemeComplexPointStalkEval_affine (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (a : c.ring) :
    schemeComplexPointStalkEval f (complexAffineChartPointMap f c z)
      (schemeAffineOriginalRegularStalk f c z a) =
        affineSchemePointHomeomorphOfStructure (c.map ≫ f) z a := by
  have he :
      CommRingCat.ofHom (schemeAffineOriginalRegularStalk f c z) ≫
        complexPointStalkEvaluation (z.val ≫ c.map) = Spec.preimage z.val := by
    change ((Scheme.ΓSpecIso c.ring).inv ≫
      (Spec c.ring).presheaf.germ ⊤ (z.val default) trivial ≫
      inv (c.map.stalkMap (z.val default)) ≫
      (X.presheaf.stalkCongr (Inseparable.of_eq
        (schemeComplexPointImage_chart f c z).symm)).hom) ≫
          complexPointStalkEvaluation (z.val ≫ c.map) = _
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
    unfold complexPointStalkEvaluation
    rw [Scheme.Hom.stalkMap_comp]
    simp only [Category.assoc]
    erw [Category.id_comp, IsIso.inv_hom_id_assoc]
    exact complexPointStalkEvaluation_affine z.val
  exact (congrArg (fun k : c.ring ⟶ CommRingCat.of ℂ => k a) he).trans
    (affineSchemePointEquivOfStructure_apply (c.map ≫ f) z a).symm

variable (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance pointStalkEvalTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pointStalkEvalCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance pointStalkEvalManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

/-- On the ENTIRE original stalk, native germ evaluation is canonical point evaluation. -/
theorem schemeNativeStalkGerm_eval (p : SchemeComplexPoint f)
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    NativeHolGerm.eval (schemeNativeStalkGerm f n p a) = schemeComplexPointStalkEval f p a := by
  let R := SchemeCoordinateAffineRing f n p
  let : Algebra ℂ R := affinePointFieldAlgebra
    ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let e := schemeCoordinateStalkEquiv f n p
  have he : (NativeHolGerm.eval.comp (schemeNativeStalkGerm f n p)).comp e.toRingHom =
      (schemeComplexPointStalkEval f p).comp e.toRingHom := by
    apply IsLocalization.ringHom_ext (schemeCoordinatePointIdeal f n p).primeCompl
    ext b
    change NativeHolGerm.eval (schemeNativeStalkGerm f n p (e (algebraMap R _ b))) =
      schemeComplexPointStalkEval f p (e (algebraMap R _ b))
    rw [schemeNativeStalkGerm_regular, schemeNativeRegularGerm_eval]
    let c := (standardSmoothComplexAffineChart f n p).val
    let z := Spec.map (CommRingCat.ofHom (standardSmoothComplexAlgebraPoint f n p).toRingHom)
    have hp : z ≫ c.map = p.val :=
      (complexAffineAlgebraPointMap_val f c (standardSmoothComplexAlgebraPoint f n p)).symm.trans
        (congrArg Subtype.val (standardSmoothComplexAlgebraPoint_map f n p))
    have h := complexPointStalkEvaluation_localization c.map z
      (schemeCoordinateAlgebraicPoint f n p) (schemeCoordinateAlgebraicPoint_specMap f n p)
      p.val hp (schemeCoordinateAlgebraicPoint_map f n p)
    have hb := congrArg (fun k : R ⟶ CommRingCat.of ℂ => k b) h
    rw [Spec.preimage_map] at hb
    exact hb.symm
  have h := congrArg (fun k : SchemeCoordinateLocalRing f n p →+* ℂ => k (e.symm a)) he
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] using h

end HolomorphicGerms
