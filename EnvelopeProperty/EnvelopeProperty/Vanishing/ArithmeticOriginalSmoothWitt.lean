import EnvelopeProperty.Vanishing.ArithmeticOriginalSmoothFamily
import EnvelopeProperty.AlgGeom.ArithmeticProjectiveWittFamily

/-! # Actual Witt families retain the original prescribed relative dimension

All arithmetic stages, closed points and coefficient lifts are constructed
from the original n-smooth projective scheme. The residue comparison uses
the actual reduction square and canonical pullback symmetry.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalSmooth

open ProjBerk ArithmeticProjectiveOriginalFamily ArithmeticSmoothProjectiveOriginalFamily
open ArithmeticSmoothCoefficientBase ArithmeticProjectiveWittFamily DeligneIllusie

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
  (j : X ⟶ NativeProjectiveScheme k N) [IsClosedImmersion j] (extra : Finset k)

/-- The original n-smooth scheme produces an actual Witt stage of that
same relative dimension, at a genuinely produced prime greater than n. -/
theorem exists_relativeDimension_witt_stage [CharZero k] (p : X ⟶ Spec (.of k))
    (hjp : j ≫ nativeStructureMap = p) (n : ℕ) [SmoothOfRelativeDimension n p]
    (bound : ℕ) (hnb : n ≤ bound) :
    ∃ D : ProducedStage j extra bound,
      SmoothOfRelativeDimension n D.baseProjection ∧
      SmoothOfRelativeDimension n D.wittProjection ∧
      SmoothOfRelativeDimension n D.residueProjection ∧ n < D.prime := by
  obtain ⟨S, hRS, hBase, hFT, hn, -, -, -, -⟩ :=
    exists_relativeDimension_smooth_projective_arithmetic_family j extra p hjp n
  let : Algebra.FiniteType ℤ S := hFT
  have hSmooth : Smooth (scalarProjection j extra S hRS) := by
    let : SmoothOfRelativeDimension n (scalarProjection j extra S hRS) := hn
    exact SmoothOfRelativeDimension.smooth n _
  obtain ⟨r, hr, m, ell, hp, hBound, hc, hf, lifted, hred, -⟩ :=
    exists_produced_witt_point S bound
  let D : ProducedStage j extra bound :=
    ⟨S, hRS, hBase, hFT, hSmooth, r, hr, m, ell, hp, hBound, hc, hf, lifted, hred⟩
  have hbase : SmoothOfRelativeDimension n D.baseProjection :=
    relativeDimension_scalarProjection j extra S D.base hRS
      (le_localizedCoefficientRing S r hr) n hn
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have hwitt : SmoothOfRelativeDimension n D.wittProjection :=
    MorphismProperty.pullback_snd D.baseProjection
      (Spec.map (CommRingCat.ofHom D.coefficientLift)) hbase
  have hresidue : SmoothOfRelativeDimension n D.residueProjection :=
    MorphismProperty.pullback_snd D.baseProjection
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.point.asIdeal))) hbase
  exact ⟨D, hbase, hwitt, hresidue, hnb.trans_lt hBound⟩

variable {j extra} {bound : ℕ}

/-- The actual residue family is the literal DI special fibre, with the
factor order fixed by canonical symmetry of the original reduction square. -/
def residueSpecialFibreIso (D : ProducedStage j extra bound) :
    D.residueFamily ≅
      pullback (Spec.map (CommRingCat.ofHom (WittTwo.reduction D.prime D.residueField)))
        D.wittProjection :=
  D.reductionIso ≪≫ pullbackSymmetry _ _

/-- The literal special-fibre structure is exactly the same original
residue-field structural morphism under the actual comparison isomorphism. -/
theorem residueSpecialFibreIso_hom_structure (D : ProducedStage j extra bound) :
    (residueSpecialFibreIso D).hom ≫ pullback.fst _ _ = D.residueProjection := by
  simp only [residueSpecialFibreIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, D.reductionIso_hom_snd]

end EnvelopeProperty.Vanishing.ArithmeticOriginalSmooth
