import EnvelopeProperty.Vanishing.DeligneIllusieInputSource
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Topology.Sheaves.Abelian
import EnvelopeProperty.Vanishing.CartierConnection
import EnvelopeProperty.Vanishing.HypercohomologyExt
import EnvelopeProperty.DeligneIllusie.WittTwo
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import ModularCurves.ForMathlib.SchemeModuleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The global Deligne--Illusie decomposition interface

This module declares the type of the decomposition interface, with the
actual Witt model, special fibre, true relative Frobenius twist, original
de Rham complex and dimension bound. It introduces no axiom, instance or
value inhabiting that type. `Vanishing.ProvedDeligneIllusie` supplies a value
from the proved actual global Witt decomposition.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section
universe u w w'

namespace EnvelopeProperty.Vanishing.DeligneIllusieInput

open Cartier CanonicalGeometry DeligneIllusie
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]

variable (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The SAME original globally constructed relative-Frobenius de Rham
complex, extended by zero to integer degrees. -/
def target : CochainComplex (SchemeRelativeFrobenius.twist p f).Modules ℤ :=
  (SchemeRelativeFrobeniusBasisDifferential.complex f p n).extend ComplexShape.embeddingUpNat

/-- The original decomposition source as an integer-indexed complex of
underlying abelian sheaves, suitable for genuine sheaf hypercohomology. -/
def sheafSource : CochainComplex
    (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f)) ℤ :=
  ((Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (source f p n)

/-- The actual de Rham target as an integer-indexed complex of underlying
abelian sheaves, preserving the original target differential. -/
def sheafTarget : CochainComplex
    (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f)) ℤ :=
  ((Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (target f p n)

variable [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]

/-- The actual global derived isomorphism of the original complexes. -/
abbrev Decomposition :=
  (DerivedCategory.Q.obj (source f p n) ≅ DerivedCategory.Q.obj (target f p n))

/-- Tensoring a supplied actual decomposition by an actual line uses the
derived functor of the internally proved exact tensor equivalence. -/
def tensorDecomposition (L : (SchemeRelativeFrobenius.twist p f).Modules)
    (hL : Scheme.Modules.IsInvertible L) (hDI : Decomposition f p n) :
    DerivedCategory.Q.obj
        (((CartierConnection.tensorFunctor L hL).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (source f p n)) ≅
      DerivedCategory.Q.obj
        (((CartierConnection.tensorFunctor L hL).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (target f p n)) := by
  let F := CartierConnection.tensorFunctor L hL
  exact (F.mapDerivedCategoryFactors.app (source f p n)).symm ≪≫
    F.mapDerivedCategory.mapIso hDI ≪≫
      F.mapDerivedCategoryFactors.app (target f p n)

variable [HasDerivedCategory.{w'}
  (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))]

/-- Forgetting module scalars is exact, so an actual module-derived
decomposition induces the same derived isomorphism on abelian sheaves. -/
def sheafDecomposition (hDI : Decomposition f p n) :
    DerivedCategory.Q.obj (sheafSource f p n) ≅
      DerivedCategory.Q.obj (sheafTarget f p n) := by
  let F := Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)
  exact (F.mapDerivedCategoryFactors.app (source f p n)).symm ≪≫
    F.mapDerivedCategory.mapIso hDI ≪≫
      F.mapDerivedCategoryFactors.app (target f p n)

/-- The actual underlying-abelian decomposition after line tensoring.
Both tensoring and forgetting scalars use their proved exact functors. -/
def sheafTensorDecomposition (L : (SchemeRelativeFrobenius.twist p f).Modules)
    (hL : Scheme.Modules.IsInvertible L) (hDI : Decomposition f p n) :
    DerivedCategory.Q.obj
        (((Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((CartierConnection.tensorFunctor L hL).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (source f p n))) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((CartierConnection.tensorFunctor L hL).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (target f p n))) := by
  let T := (CartierConnection.tensorFunctor L hL).mapHomologicalComplex (ComplexShape.up ℤ)
  let F := Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)
  exact (F.mapDerivedCategoryFactors.app (T.obj (source f p n))).symm ≪≫
    F.mapDerivedCategory.mapIso (tensorDecomposition f p n L hL hDI) ≪≫
      F.mapDerivedCategoryFactors.app (T.obj (target f p n))


end EnvelopeProperty.Vanishing.DeligneIllusieInput

namespace EnvelopeProperty.Vanishing.DeligneIllusieInput

open Cartier DeligneIllusie

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

/-- The genuine categorical special fibre of the supplied Witt-two model.
This is definitionally the special fibre used by the independent DI proof. -/
abbrev specialFibre {Xtilde : Scheme.{u}}
    (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p k))) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f

/-- The original structural map of the ACTUAL special fibre of a supplied Witt model. -/
abbrev specialFibreStructure {Xtilde : Scheme.{u}}
    (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p k))) :
    specialFibre p k f ⟶ Spec (.of k) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f

omit [CharP k p] [PerfectRing k p] in
/-- Smoothness of the original relative dimension survives the actual
special-fibre pullback square. No local Cartier theorem is needed. -/
theorem specialFibre_smoothOfRelativeDimension {Xtilde : Scheme.{u}}
    (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p k))) (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (specialFibreStructure p k f) := by
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f).flip inferInstance

/-- The global decomposition interface: actual smooth Witt models of
dimension below p have the global derived decomposition on their actual
special fibres. There is deliberately no global instance of this proposition. -/
def WittDecompositionInput : Prop :=
  ∀ [PerfectRing k p] {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p k)))
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f]
    [HasDerivedCategory.{w}
      (SchemeRelativeFrobenius.twist p (specialFibreStructure p k f)).Modules],
    n < p →
      letI := specialFibre_smoothOfRelativeDimension p k f n
      Nonempty (Decomposition (specialFibreStructure p k f) p n)

/-- An explicit global decomposition interface is applied
to the genuine model and the genuine dimension bound, without adding any
cohomological vanishing assertion to that input. -/
def ofWittLift (hDI : WittDecompositionInput.{u,w} p k)
    {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p k)))
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f]
    [HasDerivedCategory.{w}
      (SchemeRelativeFrobenius.twist p (specialFibreStructure p k f)).Modules]
    (hn : n < p) :
    letI := specialFibre_smoothOfRelativeDimension p k f n
    Decomposition (specialFibreStructure p k f) p n :=
  (hDI f n hn).some

end EnvelopeProperty.Vanishing.DeligneIllusieInput
