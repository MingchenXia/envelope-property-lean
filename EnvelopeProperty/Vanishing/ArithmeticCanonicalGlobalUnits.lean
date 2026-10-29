import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalFrames
import EnvelopeProperty.AlgGeom.Canonical.OpenImmersionSheafUnits

/-! # Actual affine sheafification units over arithmetic bases

The original units themselves become bijective on the genuine free affine
charts. The comparisons are derived from the actual coordinate maps and
open-immersion coefficient isomorphisms; no unit comparison is assumed.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace PrimeSpectrum

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalUnits

open CanonicalGeometry ArithmeticCanonicalGlobal

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

section Open

variable {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]

theorem restrictIso_inv_unit (q : ℕ) :
    exteriorSheafificationMap (relativeCotangentPresheaf (g ≫ f)) q ≫
        (ArithmeticCanonicalGlobalRestriction.exteriorRestrictIso f g q).inv.val =
      (ArithmeticCanonicalGlobalRestriction.exteriorPresheafIso f g q).hom ≫
        openImmersionSheafificationMap g (relativeExteriorPresheaf f q) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let r := (ArithmeticCanonicalGlobalRestriction.exteriorPresheafIso f g q).hom
  let E := openImmersionSheafificationIso g (relativeExteriorPresheaf f q)
  have hn : r ≫ adj.unit.app (openImmersionPresheafRestrict g (relativeExteriorPresheaf f q)) =
      exteriorSheafificationMap (relativeCotangentPresheaf (g ≫ f)) q ≫
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map r).val :=
    adj.unit.naturality r
  calc
    _ = (exteriorSheafificationMap (relativeCotangentPresheaf (g ≫ f)) q ≫
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map r).val) ≫ E.inv.val := rfl
    _ = (r ≫ adj.unit.app (openImmersionPresheafRestrict g
        (relativeExteriorPresheaf f q))) ≫ E.inv.val := congrArg (· ≫ E.inv.val) hn.symm
    _ = r ≫ openImmersionSheafificationMap g (relativeExteriorPresheaf f q) := by
      rw [Category.assoc, openImmersionSheafificationIso_inv_unit]

theorem unit_bijective_iff_openImmersion (q : ℕ) (U : Y.Opens) :
    Function.Bijective ((exteriorSheafificationMap
      (relativeCotangentPresheaf (g ≫ f)) q).app (.op U)) ↔
    Function.Bijective ((exteriorSheafificationMap
      (relativeCotangentPresheaf f) q).app (.op (g ''ᵁ U))) := by
  let r := (ArithmeticCanonicalGlobalRestriction.exteriorPresheafIso f g q).hom.app (.op U)
  let s := (ArithmeticCanonicalGlobalRestriction.exteriorRestrictIso f g q).inv.val.app (.op U)
  let uY := (exteriorSheafificationMap (relativeCotangentPresheaf (g ≫ f)) q).app (.op U)
  let uX := (exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op (g ''ᵁ U))
  have hr : Function.Bijective r :=
    ArithmeticCanonicalGlobalRestriction.exteriorComponent_bijective f g q (.op U)
  have hs : Function.Bijective s := by
    let E := ArithmeticCanonicalGlobalRestriction.exteriorRestrictIso f g q
    have : IsIso (E.inv.app U) := Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance U
    exact ConcreteCategory.bijective_of_isIso (E.inv.app U)
  have hcomm : (fun z => s (uY z)) = (fun z => uX (r z)) := by
    funext z
    exact congr($(restrictIso_inv_unit f g q).app (.op U) |>.hom z)
  exact (hs.of_comp_iff' uY).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective hcomm)).trans
      (Function.Bijective.of_comp_iff uX hr))

end Open

section Affine

variable (R) (A : CommRingCat.{u}) [Algebra R A]

theorem affineUnit_bijective {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential R A)) (q : ℕ) (r : A) :
    Function.Bijective ((exteriorSheafificationMap
      (relativeCotangentPresheaf (affineStructure R A)) q).app (.op (basicOpen r))) := by
  let P := relativeExteriorPresheaf (affineStructure R A) q
  let M := ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A))
  let φ := ArithmeticCanonicalGlobalFrames.exteriorToOpen R A q
  let hφ : ∀ {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V),
      φ U ≫ (specPresheafToAModules A P).map i = φ V :=
    fun i => ArithmeticCanonicalGlobalFrames.exteriorToOpen_naturality R A q i
  let hloc := ArithmeticCanonicalGlobalFrames.exteriorToOpen_isLocalized R A b q
  let E := ArithmeticCanonicalGlobalFrames.affineExteriorSheafIso R A b q
  let F := (affineLocalizedBasisIso A P M φ hφ hloc).app (.op r)
  have hE : Function.Bijective (E.hom.val.app (.op (basicOpen r))) := by
    constructor
    · intro x y hxy
      exact (congr($(E.hom_inv_id).val.app (.op (basicOpen r)) |>.hom x)).symm.trans
        ((congrArg (E.inv.val.app (.op (basicOpen r))) hxy).trans
          (congr($(E.hom_inv_id).val.app (.op (basicOpen r)) |>.hom y)))
    · intro y
      exact ⟨E.inv.val.app (.op (basicOpen r)) y,
        congr($(E.inv_hom_id).val.app (.op (basicOpen r)) |>.hom y)⟩
  have hF : Function.Bijective F.hom := ConcreteCategory.bijective_of_isIso _
  have hunit (x : P.obj (.op (basicOpen r))) :
      E.hom.val.app (.op (basicOpen r))
          ((exteriorSheafificationMap (relativeCotangentPresheaf (affineStructure R A)) q).app
            (.op (basicOpen r)) x) = F.hom x :=
    affineLocalizedSheafificationHom_unit_apply A P M φ hφ hloc r x
  constructor
  · intro x y hxy
    apply hF.injective
    exact (hunit x).symm.trans ((congrArg (E.hom.val.app (.op (basicOpen r))) hxy).trans (hunit y))
  · intro y
    obtain ⟨x, hx⟩ := hF.surjective (E.hom.val.app (.op (basicOpen r)) y)
    exact ⟨x, hE.injective ((hunit x).trans hx)⟩

theorem affineUnit_top_bijective {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential R A)) (q : ℕ) :
    Function.Bijective ((exteriorSheafificationMap
      (relativeCotangentPresheaf (affineStructure R A)) q).app (.op ⊤)) := by
  have h := affineUnit_bijective R A b q (1 : A)
  have hone : (basicOpen (1 : A) : (Spec A).Opens) = ⊤ := PrimeSpectrum.basicOpen_one
  exact hone ▸ h

end Affine

theorem affineChartUnit_bijective {V : X.Opens} (hV : IsAffineOpen V)
    {I : Type v} [LinearOrder I]
    (b : letI : Algebra R Γ(X, V) := ((relativeConstants f).app (.op V)).hom.toAlgebra
      Module.Basis I Γ(X, V) (KaehlerDifferential R Γ(X, V))) (q : ℕ) :
    Function.Bijective ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op V)) := by
  let : Algebra R Γ(X, V) := ((relativeConstants f).app (.op V)).hom.toAlgebra
  have he : hV.fromSpec ≫ f = affineStructure R (.of Γ(X, V)) := affineChartStructure f hV
  have hunit : Function.Bijective ((exteriorSheafificationMap
      (relativeCotangentPresheaf (hV.fromSpec ≫ f)) q).app (.op ⊤)) := by
    let Q : (Spec (.of Γ(X, V)) ⟶ Spec (.of R)) → Prop := fun h =>
      Function.Bijective ((exteriorSheafificationMap (relativeCotangentPresheaf h) q).app (.op ⊤))
    exact Eq.mp (congrArg Q he.symm) (affineUnit_top_bijective R (.of Γ(X, V)) b q)
  have himage := (unit_bijective_iff_openImmersion f hV.fromSpec q ⊤).mp hunit
  have htop : hV.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, V))).Opens) = V :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hV.opensRange_fromSpec
  let P : X.Opens → Prop := fun W =>
    Function.Bijective ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op W))
  exact Eq.mp (congrArg P htop) himage

theorem standardSmoothChartUnit_bijective {V : X.Opens} (hV : IsAffineOpen V)
    (d : ℕ) (hs : RingHom.IsStandardSmoothOfRelativeDimension d
      ((relativeConstants f).app (.op V)).hom) (q : ℕ) :
    Function.Bijective ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op V)) := by
  let : Algebra R Γ(X, V) := ((relativeConstants f).app (.op V)).hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension d R Γ(X, V) := hs
  exact affineChartUnit_bijective f hV (standardSmoothDifferentialBasis R Γ(X, V) d) q

end EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalUnits
