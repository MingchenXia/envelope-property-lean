import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Topology.Sheaves.Abelian
import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf
import EnvelopeProperty.Vanishing.CartierConnectionTensor
import EnvelopeProperty.Vanishing.HypercohomologyExt
import EnvelopeProperty.Cartier.SchemeRelativeFrobenius
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import ModularCurves.ForMathlib.SchemeModuleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
/-! # The actual original finite Deligne--Illusie source and Hodge-summand extraction

The finite source consists of the original exterior sheaves on the actual
relative Frobenius twist in their original degrees. Its summands remain
actual retracts after extension, exact line tensoring, forgetting scalars,
and localization. The final extraction reaches native sheaf cohomology.
This file assumes no Deligne--Illusie decomposition.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section
universe u w w'

namespace EnvelopeProperty.Vanishing.DeligneIllusieInput

open Cartier CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The coefficient projection of the actual relative Frobenius twist. -/
def twistStructure : SchemeRelativeFrobenius.twist p f ⟶ Spec (.of k) :=
  pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)

/-- An actual original exterior sheaf in its unchanged natural degree. -/
def summandNat (n : ℕ) (i : Fin (n + 1)) :
    CochainComplex (SchemeRelativeFrobenius.twist p f).Modules ℕ :=
  (HomologicalComplex.single (SchemeRelativeFrobenius.twist p f).Modules
    (ComplexShape.up ℕ) i.val).obj (exteriorCotangentSheaf (twistStructure f p) i.val)

/-- The finite original exterior sheaves in their unchanged natural degrees.
This is definitionally the finite source used in 's dimension-source API. -/
def sourceNat (n : ℕ) : CochainComplex (SchemeRelativeFrobenius.twist p f).Modules ℕ :=
  ∐ summandNat f p n

/-- The actual inclusion of an original exterior-degree summand. -/
def summandInclusionNat (n : ℕ) (i : Fin (n + 1)) :
    summandNat f p n i ⟶ sourceNat f p n :=
  Sigma.ι (summandNat f p n) i

/-- The actual projection to one original exterior-degree summand. -/
def summandProjectionNat (n : ℕ) (i : Fin (n + 1)) :
    sourceNat f p n ⟶ summandNat f p n i :=
  Sigma.desc (fun j => if h : j = i then eqToHom (congrArg (summandNat f p n) h) else 0)

/-- The original summand is a genuine retract of the finite DI source. -/
theorem summandInclusion_projection_nat (n : ℕ) (i : Fin (n + 1)) :
    summandInclusionNat f p n i ≫ summandProjectionNat f p n i = 𝟙 _ := by
  classical
  dsimp only [summandInclusionNat, summandProjectionNat, sourceNat]
  rw [Sigma.ι_desc]
  simp only [dif_pos rfl, eqToHom_refl]

/-- The actual finite source extended by zero to integer degrees. -/
def source (n : ℕ) : CochainComplex (SchemeRelativeFrobenius.twist p f).Modules ℤ :=
  (sourceNat f p n).extend ComplexShape.embeddingUpNat

variable (n : ℕ) [SmoothOfRelativeDimension n f]
variable [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
variable [HasDerivedCategory.{w'}
  (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))]
omit [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
  [SmoothOfRelativeDimension n f] in
/-- The actual source-to-derived-abelian realization used to extract the
original finite Hodge summands after extension and line tensoring. -/
def realizationFunctor (L : (SchemeRelativeFrobenius.twist p f).Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    CochainComplex (SchemeRelativeFrobenius.twist p f).Modules ℕ ⥤
      DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f)) :=
  ComplexShape.embeddingUpNat.extendFunctor (SchemeRelativeFrobenius.twist p f).Modules ⋙
    (CartierConnection.tensorFunctor L hL).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

omit [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
  [SmoothOfRelativeDimension n f] in
/-- A realized actual exterior summand is precisely the corresponding
single underlying sheaf in its original integer degree. -/
def realizedSummandIso (L : (SchemeRelativeFrobenius.twist p f).Modules)
    (hL : Scheme.Modules.IsInvertible L) (i : Fin (n + 1)) :
    (realizationFunctor f p L hL).obj (summandNat f p n i) ≅
      (DerivedCategory.singleFunctor
        (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f)) (i.val : ℤ)).obj
          (exteriorCotangentSheaf (twistStructure f p) i.val ⊗ L).sheaf := by
  let M := exteriorCotangentSheaf (twistStructure f p) i.val
  let T := CartierConnection.tensorFunctor L hL
  let F := Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)
  let e₀ := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M
    i.val (i.val : ℤ) rfl
  let e₁ := (T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e₀
  let e₂ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ)
      (i.val : ℤ)).app M)
  let e₃ := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ)
    (i.val : ℤ)).app (M ⊗ L)
  exact DerivedCategory.Q.mapIso (e₁ ≪≫ e₂ ≪≫ e₃)

omit [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
  [SmoothOfRelativeDimension n f] in
/-- Every actual Hodge-degree summand remains a retract through the
original extension, tensor, underlying-sheaf and localization functors. -/
theorem realized_summand_retract (L : (SchemeRelativeFrobenius.twist p f).Modules)
    (hL : Scheme.Modules.IsInvertible L) (i : Fin (n + 1)) :
    (realizationFunctor f p L hL).map (summandInclusionNat f p n i) ≫
      (realizationFunctor f p L hL).map (summandProjectionNat f p n i) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, summandInclusion_projection_nat,
    CategoryTheory.Functor.map_id]

omit [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
  [SmoothOfRelativeDimension n f] in
/-- Vanishing of hypercohomology of the actual realized source forces
vanishing of each original realized exterior-degree summand. -/
theorem subsingleton_realized_summand_hom
    (L : (SchemeRelativeFrobenius.twist p f).Modules) (hL : Scheme.Modules.IsInvertible L)
    (i : Fin (n + 1))
    (A : DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f)))
    (h : Subsingleton (A ⟶ (realizationFunctor f p L hL).obj (sourceNat f p n))) :
    Subsingleton (A ⟶ (realizationFunctor f p L hL).obj (summandNat f p n i)) := by
  let := h
  constructor
  intro a b
  have he : a ≫ (realizationFunctor f p L hL).map (summandInclusionNat f p n i) =
      b ≫ (realizationFunctor f p L hL).map (summandInclusionNat f p n i) :=
    Subsingleton.elim _ _
  have ht := congrArg
    (fun z => z ≫ (realizationFunctor f p L hL).map (summandProjectionNat f p n i)) he
  simpa only [Category.assoc, realized_summand_retract, Category.comp_id] using ht

omit [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
  [SmoothOfRelativeDimension n f] in
/-- The original actual exterior sheaf, rather than an unconnected
single-complex proxy, is extracted from zero source hypercohomology. -/
theorem subsingleton_hodge_summand_hom
    (L : (SchemeRelativeFrobenius.twist p f).Modules) (hL : Scheme.Modules.IsInvertible L)
    (i : Fin (n + 1))
    (A : DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f)))
    (h : Subsingleton (A ⟶ (realizationFunctor f p L hL).obj (sourceNat f p n))) :
    Subsingleton (A ⟶
      (DerivedCategory.singleFunctor
        (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f)) (i.val : ℤ)).obj
          (exteriorCotangentSheaf (twistStructure f p) i.val ⊗ L).sheaf) := by
  let := subsingleton_realized_summand_hom f p n L hL i A h
  let e := realizedSummandIso f p n L hL i
  exact ⟨fun a b => (cancel_mono e.inv).mp (Subsingleton.elim _ _)⟩

omit [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
  [SmoothOfRelativeDimension n f] in
/-- Native sheaf cohomology of each ORIGINAL exterior summand is zero
when the realized source has zero hypercohomology in the same total degree.
The bridge is the proved actual displaced-single/Ext equivalence. -/
theorem subsingleton_hodge_H
    (L : (SchemeRelativeFrobenius.twist p f).Modules) (hL : Scheme.Modules.IsInvertible L)
    (i : Fin (n + 1))
    (t : ℤ) (q : ℕ) (hdegree : (i.val : ℤ) + q = t)
    (h : Subsingleton
      ((DerivedCategory.singleFunctor.{w'}
          (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f)) t).obj
          (HypercohomologyExt.constantIntegerSheaf (T := SchemeRelativeFrobenius.twist p f)) ⟶
        (realizationFunctor f p L hL).obj (sourceNat f p n))) :
    Subsingleton (CategoryTheory.Sheaf.H
      (exteriorCotangentSheaf (twistStructure f p) i.val ⊗ L).sheaf q) := by
  let : HasDerivedCategory.{w'}
      (CategoryTheory.Sheaf
        (_root_.Opens.grothendieckTopology (SchemeRelativeFrobenius.twist p f))
        AddCommGrpCat.{u}) := by
    change HasDerivedCategory.{w'}
      (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))
    infer_instance
  have hNative : Subsingleton
      ((DerivedCategory.singleFunctor.{w'}
          (CategoryTheory.Sheaf
            (_root_.Opens.grothendieckTopology (SchemeRelativeFrobenius.twist p f))
            AddCommGrpCat.{u}) t).obj
          (HypercohomologyExt.constantIntegerSheaf (T := SchemeRelativeFrobenius.twist p f)) ⟶
        (DerivedCategory.singleFunctor.{w'}
          (CategoryTheory.Sheaf
            (_root_.Opens.grothendieckTopology (SchemeRelativeFrobenius.twist p f))
            AddCommGrpCat.{u}) (i.val : ℤ)).obj
          (exteriorCotangentSheaf (twistStructure f p) i.val ⊗ L).sheaf) :=
    subsingleton_hodge_summand_hom f p n L hL i _ h
  let := hNative
  exact (HypercohomologyExt.singleHomEquivH.{u, u, w'} (T := SchemeRelativeFrobenius.twist p f) _ (i.val : ℤ) t q hdegree).symm.injective.subsingleton


end EnvelopeProperty.Vanishing.DeligneIllusieInput
