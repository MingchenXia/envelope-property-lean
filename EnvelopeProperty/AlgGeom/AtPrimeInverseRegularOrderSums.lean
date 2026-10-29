import EnvelopeProperty.AlgGeom.AtPrimeInverseCurvePoints
import EnvelopeProperty.AlgGeom.SchemeRegularSectionOrders

/-! # ALL original finite-fibre weighted native section orders at the SAME local inverse -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.AtPrimeInverseRegularOrderSums
open FlatGlobalSections AtPrimeInverseCurvePoints
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A : Type u} [CommRing A] [IsDomain A] {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (.of A)) [IsFinite f] [IsDominant f] (p : PrimeSpectrum A)

omit [IsFinite f] in
/-- Every point in the SAME original fibre at a nonzero original prime
is genuinely nongeneric on the ORIGINAL curve. -/
theorem fibre_ne_generic (hp : p ≠ ⊥) (y : Y) (hy : f y = p) : y ≠ genericPoint Y := by
  intro he
  rw [he, DominantFunctionFieldMaps.genericPoint_map f, genericPoint_eq_bot_of_affine] at hy
  exact hp hy.symm

variable [IsNoetherianRing A]

omit [IsDomain A] [IsIntegral Y] [IsDominant f] in
include f in
private theorem sourceNoetherian : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f

private instance modelIntegral : IsIntegral (model f p) := model_isIntegral f p

private instance modelNoetherian : IsLocallyNoetherian (model f p) := by
  let : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (inferInstance : IsNoetherianRing A)
  exact LocallyOfFiniteType.isLocallyNoetherian (structureMap (S := Localization.AtPrime p.asIdeal) f)

/-- The TRUE original native weighted-order sum over ALL points of the
SAME original finite fibre equals the TRUE sum of the SAME actual pulled
original section over EVERY point of the SAME entire original local inverse.
ALL point/stalk/residue/order matches are internally derived. -/
theorem finsum_fibre_eq_localInverse {k : Type u} [Field k]
    (q : Y ⟶ Spec (.of k)) (hdim : topologicalKrullDim Y ≤ 1) (hp : p ≠ ⊥)
    (b : Γ(Y, ⊤)) (hb : b ≠ 0) :
    letI : IsLocallyNoetherian Y := sourceNoetherian f
    (∑ᶠ y : {y : Y // f y = p}, SchemeRegularSectionOrders.weightedOrder q b y.1) =
      ∑ᶠ z : model f p, SchemeRegularSectionOrders.weightedOrder
        (firstProjection (S := Localization.AtPrime p.asIdeal) f ≫ q)
          ((firstProjection (S := Localization.AtPrime p.asIdeal) f).appTop b) z := by
  let : IsLocallyNoetherian Y := sourceNoetherian f
  let T := model f p
  let π := firstProjection (S := Localization.AtPrime p.asIdeal) f
  let : IsAffine Y := isAffine_of_isAffineHom f
  have he : (∑ᶠ y : {y : Y // f y = p}, SchemeRegularSectionOrders.weightedOrder q b y.1) =
      ∑ᶠ z : {z : T // z ≠ genericPoint T}, SchemeRegularSectionOrders.weightedOrder q b (π z.1) := by
    symm
    apply finsum_eq_of_bijective (pointEquiv f p hdim hp) (pointEquiv f p hdim hp).bijective
    intro z
    rfl
  rw [he]
  calc
    _ = ∑ᶠ z : {z : T // z ≠ genericPoint T},
        SchemeRegularSectionOrders.weightedOrder (π ≫ q) (π.appTop b) z.1 := by
      apply finsum_congr
      intro z
      let : IsIso (π.stalkMap z.1) :=
        LocalizedInverseStalks.projection_stalkMap_isIso f p.asIdeal.primeCompl z.1
      exact SchemeRegularSectionOrders.weightedOrder_pullback π q hdim (dimension_le f p hdim)
        z.1 z.2 (fibre_ne_generic f p hp (π z.1) (projection_mem_fibre f p hdim z.1 z.2)) b hb
    _ = _ := (SchemeRegularSectionOrders.finsum_eq_nongeneric (π ≫ q) (π.appTop b)).symm

end EnvelopeProperty.AtPrimeInverseRegularOrderSums
