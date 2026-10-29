import EnvelopeProperty.AlgGeom.CyclicSectionSNCAdaptedFramedAtlas
import EnvelopeProperty.AlgGeom.CyclicSectionSNCAffineRoundedCover

/-! # Literal actual rounded schemes of the original adapted framed atlas

The original chart data determine the literal generic and rounded algebras,
their actual basis and actual spectrum projections. Original base integrality
supplies the coefficient domain internally. No cyclic-cover integral or
normality assertion is assumed.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionSNCAdaptedRoundedCharts
open CyclicSectionSNCAdaptedFramedAtlas
variable {X : Scheme.{u}} [IsIntegral X]
variable {L : X.Modules} {n : ℕ} {s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L n}
variable {F : Scheme.DivisorFamily X} {a : F.ι → ℕ}

abbrev coefficientRing (c : ChartData L n s F a) : Type u := Γ(X, (chartAffine c).1)

/-- The original nonempty affine open, rather than its cyclic cover, gives the actual coefficient domain. -/
theorem coefficientDomain (c : ChartData L n s F a) : IsDomain (coefficientRing c) := by
  let : Nonempty (chartAffine c).1 := chart_nonempty c
  change IsDomain (Γ(X, (chartAffine c).1))
  infer_instance

/-- The SAME original literal generic quotient, with the actual full product coefficient. -/
abbrev genericRing (c : ChartData L n s F a) : Type u := by
  letI := coefficientDomain c
  exact CyclicSectionSNCNormalizationRounded.GenericRootRing
    (R := coefficientRing c) n a (chartUnit c) (chartBranches c)

/-- The SAME actual original rounded subalgebra in the actual original generic quotient. -/
abbrev roundedAlgebra (c : ChartData L n s F a) (hn : 0 < n) :
    Subalgebra (coefficientRing c) (genericRing c) := by
  letI := coefficientDomain c
  exact CyclicSectionSNCNormalizationRounded.roundedAlgebra
    (R := coefficientRing c) n a (chartUnit c) (chartBranches c) hn (chart_branches_nonzero c)

abbrev roundedRing (c : ChartData L n s F a) (hn : 0 < n) : Type u :=
  roundedAlgebra c hn

/-- The actual original rounded basis of the WHOLE actual chart algebra. -/
def basis (c : ChartData L n s F a) (hn : 0 < n) :
    Module.Basis (Fin n) (coefficientRing c) (roundedRing c hn) := by
  letI := coefficientDomain c
  exact CyclicSectionSNCNormalizationRounded.basis
    (R := coefficientRing c) n a (chartUnit c) (chartBranches c) hn (chart_branches_nonzero c)

/-- Every actual chart basis vector has its SAME literal original rounded generic value. -/
theorem basis_coe (c : ChartData L n s F a) (hn : 0 < n) (i : Fin n) :
    letI := coefficientDomain c
    (basis c hn i : genericRing c) = CyclicSectionSNCNormalizationRounded.roundedPower
      (R := coefficientRing c) n a (chartUnit c) (chartBranches c) (i : ℕ) := by
  let := coefficientDomain c
  exact CyclicSectionSNCNormalizationRounded.basis_apply
    (R := coefficientRing c) n a (chartUnit c) (chartBranches c) hn (chart_branches_nonzero c) i

/-- The actual spectrum of the SAME literal original chart rounded algebra. -/
abbrev chart (c : ChartData L n s F a) (hn : 0 < n) : Scheme.{u} :=
  Spec (CommRingCat.of (roundedRing c hn))

/-- The actual original rounded scalar projection to the SAME original section-ring spectrum. -/
def affineProjection (c : ChartData L n s F a) (hn : 0 < n) :
    chart c hn ⟶ Spec (CommRingCat.of (coefficientRing c)) := by
  letI := coefficientDomain c
  exact CyclicSectionSNCAffineRoundedCover.projection
    (R := coefficientRing c) n a (chartUnit c) (chartBranches c) hn (chart_branches_nonzero c)

/-- The SAME actual projection to the SAME original affine open. -/
def projection (c : ChartData L n s F a) (hn : 0 < n) : chart c hn ⟶ (chartAffine c).1.toScheme :=
  affineProjection c hn ≫ (chartAffine c).2.isoSpec.inv

/-- The entire native affine-identification/projection triangle commutes. -/
theorem projection_affine (c : ChartData L n s F a) (hn : 0 < n) :
    projection c hn ≫ (chartAffine c).2.isoSpec.hom = affineProjection c hn := by
  simp only [projection, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual original rounded chart structural map to the SAME original scheme X. -/
def toOriginal (c : ChartData L n s F a) (hn : 0 < n) : chart c hn ⟶ X :=
  projection c hn ≫ (chartAffine c).1.ι

end EnvelopeProperty.CyclicSectionSNCAdaptedRoundedCharts
