import EnvelopeProperty.Vanishing.WittKodairaComparison
import EnvelopeProperty.Vanishing.ArithmeticOriginalSmoothWitt

/-! # Kodaira vanishing on the actual produced arithmetic residue fibre

The special-fibre comparison and separatedness come from the actual
arithmetic stage. The original relative dimension and prime bound are the
ones supplied by the proved relative-dimension stage producer.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section
universe u w w'

namespace EnvelopeProperty.Vanishing.WittKodairaComparison

open Cartier CanonicalGeometry ProjBerk ArithmeticProjectiveWittFamily
attribute [local instance] Scheme.Modules.monoidalCategory

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    {j : X ⟶ NativeProjectiveScheme k N} [IsClosedImmersion j] {extra : Finset k}
    {bound : ℕ} (D : ProducedStage j extra bound) (n : ℕ)
    [SmoothOfRelativeDimension n D.wittProjection]
    [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist D.prime
      (DeligneIllusieInput.specialFibreStructure D.prime D.residueField D.wittProjection)).Modules]
    [HasDerivedCategory.{w'} (TopCat.Sheaf AddCommGrpCat.{u}
      (SchemeRelativeFrobenius.twist D.prime
        (DeligneIllusieInput.specialFibreStructure D.prime D.residueField D.wittProjection)))]

/-- The original residue family and original ample line satisfy Kodaira
vanishing using only the actual stage's fixed-prime Witt DI input. -/
theorem kodaira_on_residueFamily (hn : n < D.prime)
    (hDI : DeligneIllusieInput.WittDecompositionInput.{u,w} D.prime D.residueField)
    (L : D.residueFamily.Modules)
    (hL : SchemeLineAmpleness.IsAmple D.residueProjection L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf D.residueProjection n ⊗ L : D.residueFamily.Modules).sheaf (q + 1)) := by
  let : PerfectRing D.residueField D.prime := inferInstance
  let : IsProper D.wittProjection := D.wittProjection_projective.isProper
  let : IsSeparated D.wittProjection := inferInstance
  exact kodaira_of_specialFibreIso D.prime hDI D.wittProjection n hn
    D.residueProjection (ArithmeticOriginalSmooth.residueSpecialFibreIso D)
    (ArithmeticOriginalSmooth.residueSpecialFibreIso_hom_structure D) L hL q

/-- The same original residue Kodaira group with its explicit sheafified
coherent tensor, retaining the actual original residue line. -/
theorem kodaira_tensorObj_on_residueFamily (hn : n < D.prime)
    (hDI : DeligneIllusieInput.WittDecompositionInput.{u,w} D.prime D.residueField)
    (L : D.residueFamily.Modules)
    (hL : SchemeLineAmpleness.IsAmple D.residueProjection L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf D.residueProjection n) L).sheaf (q + 1)) := by
  let : PerfectRing D.residueField D.prime := inferInstance
  let : IsProper D.wittProjection := D.wittProjection_projective.isProper
  let : IsSeparated D.wittProjection := inferInstance
  exact kodaira_tensorObj_of_specialFibreIso D.prime hDI D.wittProjection n hn
    D.residueProjection (ArithmeticOriginalSmooth.residueSpecialFibreIso D)
    (ArithmeticOriginalSmooth.residueSpecialFibreIso_hom_structure D) L hL q

/-- The produced stage's stored strict prime bound supplies the dimension
bound internally whenever the requested dimension is at most that bound. -/
theorem kodaira_on_residueFamily_of_bound (hnb : n ≤ bound)
    (hDI : DeligneIllusieInput.WittDecompositionInput.{u,w} D.prime D.residueField)
    (L : D.residueFamily.Modules)
    (hL : SchemeLineAmpleness.IsAmple D.residueProjection L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf D.residueProjection n ⊗ L : D.residueFamily.Modules).sheaf (q + 1)) :=
  kodaira_on_residueFamily D n (hnb.trans_lt D.prime_gt) hDI L hL q

end EnvelopeProperty.Vanishing.WittKodairaComparison
