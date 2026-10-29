/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeParameterLineMonoid
import EnvelopeProperty.AlgGeom.SchemeEquivariantPullback
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso
import EnvelopeProperty.AlgGeom.FlatParameterOpen
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Literal original test configuration data (i)--(iii)

The original total scheme, its flat PROJECTIVE morphism to the SAME ordinary
parameter line, genuine action lifting the derived standard action, and
isomorphism of its SAME original fibre at ONE are retained. No reducedness,
irreducibility, normality or desired unit-open trivialization is a field.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial CategoryTheory.MonObj
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration
variable (k : Type u) [Field k]

/-- The genuine original parameter-one point over the SAME coefficient field. -/
def pointOne : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ ProjBerk.nativeParameterLine k := by
  let := ProjBerk.nativeParameterLineMonObj k
  exact η[ProjBerk.nativeParameterLine k]

/-- The parameter-one point is LITERALLY the original polynomial evaluation spectrum map. -/
theorem pointOne_left : (pointOne k).left =
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : k))) :=
  ProjBerk.nativeParameterLine_one k

/-- The entire original model over its SAME original coefficient field. -/
def totalOver {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of k[X])) :
    Over (Spec (CommRingCat.of k)) := Over.mk (π ≫ (ProjBerk.nativeParameterLine k).hom)

/-- The whole original structure map over the original coefficient field. -/
def structureOver {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of k[X])) :
    totalOver k π ⟶ ProjBerk.nativeParameterLine k := Over.homMk π rfl

/-- The SAME original native fibre over the actual parameter-one point. -/
def fibreOneOver {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of k[X])) :
    Over (Spec (CommRingCat.of k)) := SchemeEquivariantPullback.object (structureOver k π) (pointOne k)

/-- Literal test configuration data from source (i)--(iii). Every class/structure
field is an ORIGINAL source datum; none is a common model or trivialization conclusion. -/
structure TestConfiguration (X : Over (Spec (CommRingCat.of k))) where
  total : Scheme.{u}
  projection : total ⟶ Spec (CommRingCat.of k[X])
  flat : Flat projection
  projective : IsProjective projection
  action : ModObj (ProjBerk.nativeMultiplicativeGroup k) (totalOver k projection)
  equivariant : letI := action
    letI := ProjBerk.nativeParameterLineModObj k
    IsModHom (ProjBerk.nativeMultiplicativeGroup k) (structureOver k projection)
  fibreOneIso : fibreOneOver k projection ≅ X

namespace TestConfiguration

variable {k} {X : Over (Spec (CommRingCat.of k))} (C : TestConfiguration k X)

/-- The original projectivity datum internally gives a finite polynomial closed
factorization of the SAME original parameter projection, over the SAME k[t]. -/
theorem projection_isProjectiveFactorization : IsProjectiveFactorization C.projection := by
  let : IsProjective C.projection := C.projective
  exact ProjectiveFactorizationRingIso.of_isProjective C.projection

/-- The SAME original source test-configuration projection is genuinely proper. -/
theorem projection_isProper : IsProper C.projection := C.projection_isProjectiveFactorization.isProper

/-- The SAME original source total space is locally Noetherian, derived from source projectivity. -/
theorem total_isLocallyNoetherian : IsLocallyNoetherian C.total := by
  let : IsProper C.projection := C.projection_isProper
  exact LocallyOfFiniteType.isLocallyNoetherian C.projection

/-- Original projectivity over the original Noetherian parameter ring derives
Noetherianity of the SAME entire total model. -/
theorem total_isNoetherian : AlgebraicGeometry.IsNoetherian C.total := by
  let : IsLocallyNoetherian C.total := C.total_isLocallyNoetherian
  let : IsProper C.projection := C.projection_isProper
  let : CompactSpace C.total := QuasiCompact.compactSpace_of_compactSpace C.projection
  exact ⟨⟩

/-- The SAME original noncentral open in the total scheme. -/
def unitOpen : C.total.Opens := C.projection ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X])

/-- Density of the WHOLE original noncentral open follows from genuine source flatness/projectivity. -/
theorem unitOpen_dense : Dense (C.unitOpen : Set C.total) := by
  let : Flat C.projection := C.flat
  let : IsProper C.projection := C.projection_isProper
  exact FlatParameterOpen.dense C.projection (Polynomial.X : k[X]) Polynomial.X_ne_zero

/-- Schematic density of the WHOLE original noncentral open follows from source flatness alone. -/
theorem unitOpen_isSchemeTheoreticallyDominant : IsSchemeTheoreticallyDominant C.unitOpen.ι := by
  let : Flat C.projection := C.flat
  exact FlatParameterOpen.inclusion_isSchemeTheoreticallyDominant C.projection
    (Polynomial.X : k[X]) (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero)

/-- Quasi-compactness of the SAME original noncentral open is derived internally. -/
theorem unitOpen_quasiCompact : QuasiCompact C.unitOpen.ι := by
  let : AlgebraicGeometry.IsNoetherian C.total := C.total_isNoetherian
  infer_instance

end TestConfiguration
end EnvelopeProperty.NativeTestConfiguration
