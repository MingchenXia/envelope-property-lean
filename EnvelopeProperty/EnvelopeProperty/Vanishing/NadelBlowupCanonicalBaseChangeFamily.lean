import EnvelopeProperty.Vanishing.NadelBlowupCanonicalBaseChangeTensor

/-! # Actual canonical lines on the literal etale Cartesian blowup family -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalBaseChangeFamily
open CoordinateSubspace CanonicalGeometry Scheme.IdealSheafData
open NadelBlowupCanonicalGluingWhole NadelBlowupCanonicalBaseChangeTensor
open NadelBlowupCanonicalEtalePolynomial NadelBlowupCanonicalEtaleModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n m : ℕ) {X : Scheme.{u}}
    (g : X ⟶ Spec (.of (MvPolynomial (Fin n) k)))

/-- The literal actual Cartesian family, with no supplied model square. -/
abbrev family : Scheme.{u} := pullback g (affineBlowUp.π (centerIdeal k n (m + 1)))
abbrev projection : family k n m g ⟶ X := pullback.fst _ _
abbrev modelMap : family k n m g ⟶ modelBlowUp k n (m + 1) := pullback.snd _ _
def sourceStructure := g ≫ affineStructuralMap k (.of (MvPolynomial (Fin n) k))
def familyStructure := projection k n m g ≫ sourceStructure k n g

/-- The ORIGINAL actual centre, first on the original source and then on
its SAME literal Cartesian family. -/
def exceptionalIdeal : (family k n m g).IdealSheafData :=
  ((ofIdealTop ((centerIdeal k n (m + 1)).map
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv.hom)).comap g).comap (projection k n m g)

theorem modelMap_structure :
    modelMap k n m g ≫ (affineBlowUp.π (centerIdeal k n (m + 1)) ≫
      affineStructuralMap k (.of (MvPolynomial (Fin n) k))) = familyStructure k n m g := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ affineStructuralMap k (.of (MvPolynomial (Fin n) k)))
      (pullback.condition (f := g) (g := affineBlowUp.π (centerIdeal k n (m + 1)))).symm).trans
        (Category.assoc _ _ _))

/-- The actual model exceptional power pulls to the SAME actual original
source-centre power on the literal Cartesian family; whole geometric ideals. -/
theorem exceptionalPower_comap :
    ((affineBlowUp.exceptionalIdeal (centerIdeal k n (m + 1))) ^ m).comap (modelMap k n m g) =
      exceptionalIdeal k n m g ^ m := by
  change ((affineBlowUp.exceptionalIdeal (centerIdeal k n (m + 1))) ^ m).comap
      (pullback.snd g (affineBlowUp.π (centerIdeal k n (m + 1)))) =
    (((ofIdealTop ((centerIdeal k n (m + 1)).map
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv.hom)).comap g).comap
        (pullback.fst g (affineBlowUp.π (centerIdeal k n (m + 1))))) ^ m
  rw [comap_pow, affineBlowUp.exceptionalIdeal, ← comap_comp, ← comap_comp, ← pullback.condition]

/-- The SAME literal Cartesian etale family has its actual native whole
canonical line comparison with the SAME original centre exceptional power.
The family, square, source/target differentials and ideal transport are
all produced internally from the original etale map and m+1 <= n. -/
def canonicalIso [Etale g] (hrn : m + 1 ≤ n) :
    (Scheme.Modules.pullback (projection k n m g)).obj
        (canonicalLineSheaf (sourceStructure k n g) n) ≅
      tensorObj (canonicalLineSheaf (familyStructure k n m g) n)
        (exceptionalIdeal k n m g ^ m).toModules := by
  let f := affineStructuralMap k (.of (MvPolynomial (Fin n) k))
  let π := affineBlowUp.π (centerIdeal k n (m + 1))
  let p := projection k n m g
  let v := modelMap k n m g
  let J := (affineBlowUp.exceptionalIdeal (centerIdeal k n (m + 1))) ^ m
  have hJ : J.IsInvertible := isInvertible_pow (affineBlowUp.isInvertible_exceptionalIdeal _) m
  let : Etale v := inferInstanceAs (Etale (pullback.snd g π))
  let : IsIso (exteriorCotangentSheafPullbackMap f g n) := polynomial_etale_isIso k n g
  let : IsIso (exteriorCotangentSheafPullbackMap (π ≫ f) v n) :=
    coordinateBlowup_etale_isIso k n (m + 1) v
  let a : (Scheme.Modules.pullback p).obj (canonicalLineSheaf (sourceStructure k n g) n) ≅
      (Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback π).obj (canonicalLineSheaf f n)) :=
    (Scheme.Modules.pullback p).mapIso (asIso (exteriorCotangentSheafPullbackMap f g n)).symm ≪≫
      (pullbackComp p g).app (canonicalLineSheaf f n) ≪≫
      (pullbackCongr (pullback.condition (f := g) (g := π))).app (canonicalLineSheaf f n) ≪≫
      (pullbackComp v π).symm.app (canonicalLineSheaf f n)
  let b : (Scheme.Modules.pullback v).obj (canonicalLineSheaf (π ≫ f) n) ≅
      canonicalLineSheaf (familyStructure k n m g) n :=
    asIso (exteriorCotangentSheafPullbackMap (π ≫ f) v n) ≪≫
      eqToIso (congrArg (fun a => canonicalLineSheaf a n) (modelMap_structure k n m g))
  let c := Classical.choose (exists_coordinate_blowup_canonical_ideal_iso k n m hrn)
  exact a ≪≫ (Scheme.Modules.pullback v).mapIso c ≪≫ flatCartierTensorIso v _ J hJ ≪≫
    tensorObjCongr b (Iso.refl _) ≪≫
      eqToIso (congrArg (fun I : (family k n m g).IdealSheafData =>
        tensorObj (canonicalLineSheaf (familyStructure k n m g) n) I.toModules)
          (exceptionalPower_comap k n m g))

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalBaseChangeFamily
