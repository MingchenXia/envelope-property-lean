import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf
import EnvelopeProperty.AlgGeom.Canonical.AffineExteriorSections

/-! # The SAME actual canonical sheafification units under open-immersion comparison -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace EnvelopeProperty.CanonicalGeometry

universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]

/-- The inverse genuine open-immersion sheafification comparison retains
the ENTIRE SAME original restricted sheafification unit. -/
theorem openImmersionSheafificationIso_inv_unit (P : X.PresheafOfModules) :
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        (openImmersionPresheafRestrict g P)) ≫
      (openImmersionSheafificationIso g P).inv.val =
        openImmersionSheafificationMap g P := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let S := (Scheme.Modules.restrictFunctor g).obj
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)
  have he : (openImmersionSheafificationIso g P).inv =
      (adj.homEquiv (openImmersionPresheafRestrict g P) S).symm
        (openImmersionSheafificationMap g P) := rfl
  change (adj.homEquiv (openImmersionPresheafRestrict g P) S)
    (openImmersionSheafificationIso g P).inv = _
  exact (congrArg (adj.homEquiv _ _) he).trans
    ((adj.homEquiv _ _).apply_symm_apply _)

variable {K : Type u} [Field K] (f : X ⟶ Spec (.of K))

/-- The inverse ORIGINAL canonical open-immersion isomorphism commutes
with BOTH SAME actual units and the SAME full raw coefficient isomorphism. -/
theorem exteriorCotangentSheafOpenImmersionIso_inv_unit (n : ℕ) :
    exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n ≫
        (exteriorCotangentSheafOpenImmersionIso f g n).inv.val =
      (exteriorCotangentPresheafOpenImmersionIso f g n).hom ≫
        openImmersionSheafificationMap g (exteriorCotangentPresheaf f n) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let r := (exteriorCotangentPresheafOpenImmersionIso f g n).hom
  let E := openImmersionSheafificationIso g (exteriorCotangentPresheaf f n)
  have hn : r ≫ adj.unit.app (openImmersionPresheafRestrict g
        (exteriorCotangentPresheaf f n)) =
      exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n ≫
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map r).val :=
    adj.unit.naturality r
  calc
    _ = (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n ≫
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map r).val) ≫ E.inv.val := rfl
    _ = (r ≫ adj.unit.app (openImmersionPresheafRestrict g
        (exteriorCotangentPresheaf f n))) ≫ E.inv.val := congrArg (· ≫ E.inv.val) hn.symm
    _ = r ≫ openImmersionSheafificationMap g (exteriorCotangentPresheaf f n) := by
      rw [Category.assoc, openImmersionSheafificationIso_inv_unit]

/-- Original unit bijectivity is preserved and reflected on the ORIGINAL
image open by the actual whole raw/sheaf open-immersion isomorphisms. -/
theorem exteriorCotangentSheafificationUnit_bijective_iff_openImmersion
    (n : ℕ) (U : Y.Opens) :
    Function.Bijective ((exteriorSheafificationMap
      (cotangentPresheaf (g ≫ f)) n).app (.op U)) ↔
    Function.Bijective ((exteriorSheafificationMap
      (cotangentPresheaf f) n).app (.op (g ''ᵁ U))) := by
  let r := (exteriorCotangentPresheafOpenImmersionIso f g n).hom.app (.op U)
  let s := (exteriorCotangentSheafOpenImmersionIso f g n).inv.val.app (.op U)
  let uY := (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op U)
  let uX := (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op (g ''ᵁ U))
  have hr : Function.Bijective r := exteriorCotangentOpenImmersionComponent_bijective f g n (.op U)
  have hs : Function.Bijective s := by
    let E := exteriorCotangentSheafOpenImmersionIso f g n
    have : IsIso (E.inv.app U) := Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance U
    exact ConcreteCategory.bijective_of_isIso (E.inv.app U)
  have hcomm : (fun z ↦ s (uY z)) = (fun z ↦ uX (r z)) := by
    funext z
    exact congr($(exteriorCotangentSheafOpenImmersionIso_inv_unit g f n).app (.op U) |>.hom z)
  exact (hs.of_comp_iff' uY).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective hcomm)).trans
      (Function.Bijective.of_comp_iff uX hr))

omit [IsOpenImmersion g] in
/-- The SAME original sheafification unit is bijective on the actual
original affine open whenever its actual coordinate cotangent module is free. -/
theorem affineChartExteriorSheafificationMap_bijective {V : X.Opens}
    (hV : IsAffineOpen V) {I : Type v} [LinearOrder I]
    (b : letI := affineChartAlgebra f V
      Module.Basis I Γ(X, V) (KaehlerDifferential K Γ(X, V))) (n : ℕ) :
    Function.Bijective ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op V)) := by
  let := affineChartAlgebra f V
  have hunit : Function.Bijective ((exteriorSheafificationMap
      (cotangentPresheaf (hV.fromSpec ≫ f)) n).app (.op ⊤)) := by
    let Q : (Spec (.of Γ(X, V)) ⟶ Spec (.of K)) → Prop := fun h ↦
      Function.Bijective ((exteriorSheafificationMap (cotangentPresheaf h) n).app (.op ⊤))
    exact Eq.mp (congrArg Q (affineChartStructuralMap_eq_affineStructuralMap f hV).symm)
      (affineExteriorSheafificationMap_top_bijective K (.of Γ(X, V)) b n)
  have himage :=
    (exteriorCotangentSheafificationUnit_bijective_iff_openImmersion hV.fromSpec f n ⊤).mp hunit
  have htop : hV.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, V))).Opens) = V :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hV.opensRange_fromSpec
  let P : X.Opens → Prop := fun W ↦
    Function.Bijective ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op W))
  exact Eq.mp (congrArg P htop) himage

omit [IsOpenImmersion g] in
/-- The actual original standard-smooth affine chart itself DERIVES the
basis, so ALL exterior-degree unit comparisons hold on that SAME original open. -/
theorem standardSmoothAffineChartExteriorSheafificationMap_bijective {V : X.Opens}
    (hV : IsAffineOpen V) (d : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension d
      ((schemeConstantPresheafMap f).app (.op V)).hom) (n : ℕ) :
    Function.Bijective ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op V)) := by
  let := affineChartAlgebra f V
  let : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, V) := hs
  exact affineChartExteriorSheafificationMap_bijective f hV
    (standardSmoothDifferentialBasis K Γ(X, V) d) n

end
end EnvelopeProperty.CanonicalGeometry
