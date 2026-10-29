import EnvelopeProperty.DeligneIllusie.DeligneIllusieWittGlobalDescent
import EnvelopeProperty.DI.CechDegreeOneNative
import EnvelopeProperty.Cartier.DeligneIllusieCechTotalEvaluation
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
import EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiEquations
import EnvelopeProperty.DeligneIllusie.ActualWittGeometricSheafRestrictions

/-! # Canonical degree-one Cech descent from the actual original Witt geometry

The geometric maps are produced by the actual divided Frobenius/homotopy
layer.  This source owns the actual cover, tuple transports, native local
data and assembly, not another generic descent constructor.
-/
noncomputable section
namespace EnvelopeProperty.DI.ActualWittCechOneMap
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open DeligneIllusie CechDegreeOneDescent Cartier
universe u

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
variable {Xtilde : Scheme.{u}}
  (f : Xtilde ⟶ Spec (CommRingCat.of (WittTwo.Ring p κ)))
  (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra

/-- The actual original special fibre. -/
abbrev specialFibre := WittTwoSpecialFibreOpens.specialFibre p κ f

/-- Its original structural projection to the original residue field. -/
abbrev specialFibreMap : specialFibre p κ f ⟶ Spec (CommRingCat.of κ) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p κ))) f

/-- The actual original geometric relative-Frobenius twist. -/
abbrev twist := SchemeRelativeFrobenius.twist p (specialFibreMap p κ f)

/-- The SAME original structural map of the true twist. -/
abbrev twistMap : twist p κ f ⟶ Spec (CommRingCat.of κ) :=
  pullback.snd (specialFibreMap p κ f) (SchemeRelativeFrobenius.baseMap (k := κ) p)

/-- The original source of the degree-one Deligne--Illusie map. -/
def sourceModule : (twist p κ f).Modules :=
  CanonicalGeometry.exteriorCotangentSheaf (twistMap p κ f) 1

local instance specialFibre_smoothOfRelativeDimension :
    SmoothOfRelativeDimension n (specialFibreMap p κ f) :=
  WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n

/-- Retain the actual already proved fixed-dimension pushed de Rham complex. -/
def targetComplex : CochainComplex (twist p κ f).Modules ℕ :=
  SchemeRelativeFrobeniusBasisDifferential.complex (specialFibreMap p κ f) p n

/-- The actual internally indexed original lifted affine cover. -/
abbrev CoverIndex := DeligneIllusieWittGlobalDescent.CoverIndex p κ f n

/-- Its SAME original true-twist open family. -/
def cover : CoverIndex p κ f n → (twist p κ f).Opens :=
  DeligneIllusieWittGlobalDescent.coverOpen p κ f n

omit [PerfectRing κ p] [IsSeparated f] in
/-- The actual whole native cover equation is a conclusion of the original geometry. -/
theorem cover_iSup : (⨆ i, cover p κ f n i) = ⊤ :=
  DeligneIllusieWittGlobalDescent.coverOpen_iSup p κ f n

/-- The original finite intersection in the Witt lifting scheme. -/
def liftedTuple (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) : Xtilde.Opens :=
  DeligneIllusieWittGlobalDescent.liftedIntersection p κ f n q i

omit [CharP κ p] [PerfectRing κ p] [SmoothOfRelativeDimension n f] in
/-- Actual separated geometry gives affineness, with no supplied overlap certificate. -/
theorem liftedTuple_affine (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) :
    IsAffineOpen (liftedTuple p κ f n q i) :=
  DeligneIllusieWittGlobalDescent.liftedIntersection_affine p κ f n q i

/-- The SAME original special-fibre inverse image of the lifted tuple. -/
def residueTuple (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) :
    (specialFibre p κ f).Opens :=
  WittTwoSpecialFibreOpens.residueOpen p κ f (liftedTuple p κ f n q i)

/-- Its SAME original true-twist inverse image. -/
def twistedTuple (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) :
    (twist p κ f).Opens :=
  RelativeTwistedAffineBasis.twistedOpen (specialFibreMap p κ f) p
    (residueTuple p κ f n q i)

omit [PerfectRing κ p] [SmoothOfRelativeDimension n f] [IsSeparated f] in
/-- The native tuple product is exactly this original geometric intersection. -/
theorem tupleOpen_eq (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) :
    tupleOpen (cover p κ f n) q i = twistedTuple p κ f n q i :=
  DeligneIllusieWittGlobalDescent.cechTupleOpen_eq p κ f n q i

omit [PerfectRing κ p] [SmoothOfRelativeDimension n f] [IsSeparated f] in
/-- Singleton native tuples retain their original member open. -/
theorem singletonOpen_eq (i : Fin 1 → CoverIndex p κ f n) :
    tupleOpen (cover p κ f n) 0 i = cover p κ f n (i 0) := by
  apply le_antisymm
  · exact leOfHom (Pi.π (fun j : Fin 1 => cover p κ f n (i j)) 0)
  · apply leOfHom
    refine Pi.lift (fun j : Fin 1 => homOfLE ?_)
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact le_rfl

omit [CharP κ p] [PerfectRing κ p] [SmoothOfRelativeDimension n f] in
/-- Actual affine special-fibre geometry of every tuple. -/
theorem residueTuple_affine (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) :
    IsAffineOpen (residueTuple p κ f n q i) :=
  WittTwoSpecialFibreOpens.residueOpen_affine p κ f (liftedTuple_affine p κ f n q i)

/-- The original tuple-to-member inclusion in the lifting scheme. -/
def tupleInclusion (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) (j : Fin (q + 1)) :
    liftedTuple p κ f n q i ⟶ (i j).val :=
  homOfLE (iInf_le (fun j : Fin (q + 1) => (i j).val) j)

/-- The SAME actual residual open inclusion. -/
def residueTupleInclusion (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n)
    (j : Fin (q + 1)) :
    residueTuple p κ f n q i ⟶
      DeligneIllusieWittGlobalDescent.sourceOpen p κ f n (i j) :=
  WittTwoSpecialFibreReduction.residueInclusion p κ f (tupleInclusion p κ f n q i j)

/-- Actual intersection coordinates come from restricting the SAME first member tuple. -/
def tupleCoordinates (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) :
    Fin n → Γ(specialFibre p κ f, residueTuple p κ f n q i) :=
  fun a => (specialFibre p κ f).presheaf.map (residueTupleInclusion p κ f n q i 0).op
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n (i 0) a)

omit [CharP κ p] [PerfectRing κ p] [SmoothOfRelativeDimension n f] in
/-- The restricted original tuple is actually etale; no extra coordinate certificate is input. -/
theorem tupleCoordinates_etale (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) :
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p κ f)
      (residueTuple p κ f n q i)
    (MvPolynomial.aeval (R := κ) (tupleCoordinates p κ f n q i)).toRingHom.Etale := by
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p κ f)
    (DeligneIllusieWittGlobalDescent.sourceOpen p κ f n (i 0))
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p κ f)
    (residueTuple p κ f n q i)
  let r := residueTupleInclusion p κ f n q i 0
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p κ f) r).toAlgebra
  let : IsScalarTower κ
      Γ(specialFibre p κ f, DeligneIllusieWittGlobalDescent.sourceOpen p κ f n (i 0))
      Γ(specialFibre p κ f, residueTuple p κ f n q i) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p κ f) r).commutes a).symm
  have he : (algebraMap
      Γ(specialFibre p κ f, DeligneIllusieWittGlobalDescent.sourceOpen p κ f n (i 0))
      Γ(specialFibre p κ f, residueTuple p κ f n q i)).Etale :=
    WittTwoSchemeAffineRestrictions.restriction_etale (residueTuple_affine p κ f n q i)
      (DeligneIllusieWittGlobalDescent.sourceOpen_affine p κ f n (i 0)) r
  exact Char0.etale_aeval_algebraMap
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n (i 0))
    (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n (i 0)) he

/-- The original chosen member lift, restricted internally to the actual tuple. -/
def tupleLift (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) (j : Fin (q + 1)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedTuple p κ f n q i)
    WittTwoLiftDifference.Lift p κ Γ(Xtilde, liftedTuple p κ f n q i) :=
  DeligneIllusieWittGlobalDescent.overlapLift p κ f n q i j

/-- Its original entire residual Frobenius equation is derived, not a caller input. -/
theorem tupleLift_reduction (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n)
    (j : Fin (q + 1)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedTuple p κ f n q i)
    ∀ t, algebraMap Γ(Xtilde, liftedTuple p κ f n q i)
        (WittTwoSmoothDifferentials.ResidueAlgebra p κ Γ(Xtilde, liftedTuple p κ f n q i))
        (tupleLift p κ f n q i j t) =
      WittTwoRelativeLift.residueFrobenius p κ Γ(Xtilde, liftedTuple p κ f n q i) t :=
  DeligneIllusieWittGlobalDescent.overlapLift_reduction p κ f n q i j

/-- The original full intersection includes into every deleted-face intersection. -/
def faceTupleInclusion (q : ℕ) (k : Fin (q + 2))
    (i : Fin (q + 2) → CoverIndex p κ f n) :
    liftedTuple p κ f n (q + 1) i ⟶
      liftedTuple p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) := by
  refine homOfLE ?_
  apply le_iInf
  intro j
  exact iInf_le (fun a : Fin (q + 2) => (i a).val)
    ((SimplexCategory.δ k).toOrderHom.toFun j)

omit [CharP κ p] [PerfectRing κ p] [SmoothOfRelativeDimension n f] [IsSeparated f] in
/-- Both original inclusion routes are the SAME morphism in the original open category. -/
theorem faceTupleInclusion_comp (q : ℕ) (k : Fin (q + 2))
    (i : Fin (q + 2) → CoverIndex p κ f n) (j : Fin (q + 1)) :
    faceTupleInclusion p κ f n q k i ≫
        tupleInclusion p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) j =
      tupleInclusion p κ f n (q + 1) i ((SimplexCategory.δ k).toOrderHom.toFun j) :=
  Subsingleton.elim _ _

/-- The SAME actual member lift has equal direct and face-iterated restrictions. -/
theorem tupleLift_face_restrict (q : ℕ) (k : Fin (q + 2))
    (i : Fin (q + 2) → CoverIndex p κ f n) (j : Fin (q + 1)) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f
      (liftedTuple p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedTuple p κ f n (q + 1) i)
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f
      (liftedTuple_affine p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedTuple_affine p κ f n (q + 1) i)
    WittTwoEtaleRestrictionCoherence.restrictedLift p κ
        (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f (faceTupleInclusion p κ f n q k i))
        (tupleLift p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) j)
        (tupleLift_reduction p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) j)
        (WittTwoSchemeAffineRestrictions.restriction_etale
          (liftedTuple_affine p κ f n (q + 1) i)
          (liftedTuple_affine p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
          (faceTupleInclusion p κ f n q k i)) =
      tupleLift p κ f n (q + 1) i ((SimplexCategory.δ k).toOrderHom.toFun j) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let c := i ((SimplexCategory.δ k).toOrderHom.toFun j)
  let V := liftedTuple p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  let U := liftedTuple p κ f n (q + 1) i
  let a := faceTupleInclusion p κ f n q k i
  let b := tupleInclusion p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) j
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f c.val
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f
    (liftedTuple_affine p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedTuple_affine p κ f n (q + 1) i)
  have hcomp := DeligneIllusieWittGlobalDescent.coverLift_restriction_comp p κ f n c
    (liftedTuple_affine p κ f n (q + 1) i)
    (liftedTuple_affine p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) a b
  have hinc := faceTupleInclusion_comp p κ f n q k i j
  have hdirect := congrArg (fun t : U ⟶ c.val =>
    WittTwoEtaleRestrictionCoherence.restrictedLift p κ
      (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f t)
      (DeligneIllusieWittGlobalDescent.coverLift p κ f n c)
      (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n c)
      (WittTwoSchemeAffineRestrictions.restriction_etale
        (liftedTuple_affine p κ f n (q + 1) i) c.property.1 t)) hinc
  exact hcomp.trans hdirect

section OriginalOpenEquality
variable {Z : Scheme.{u}} {M N P : Z.Modules} {V W : Z.Opens}

private def localMapAlongEq (h : V = W) (φ : LocalMap M N W) : LocalMap M N V := h.symm ▸ φ

private theorem localMapAlongEq_zero (h : V = W) :
    localMapAlongEq h (0 : LocalMap M N W) = 0 := by cases h; rfl

private theorem localMapAlongEq_neg (h : V = W) (φ : LocalMap M N W) :
    localMapAlongEq h (-φ) = -localMapAlongEq h φ := by cases h; rfl

private theorem localMapAlongEq_add (h : V = W) (φ ψ : LocalMap M N W) :
    localMapAlongEq h (φ + ψ) = localMapAlongEq h φ + localMapAlongEq h ψ := by cases h; rfl

private theorem localMapAlongEq_comp (h : V = W) (φ : LocalMap M N W) (d : N ⟶ P) :
    localMapAlongEq h (φ ≫ (Scheme.Modules.restrictFunctor W.ι).map d) =
      localMapAlongEq h φ ≫ (Scheme.Modules.restrictFunctor V.ι).map d := by cases h; rfl

private theorem localMapAlongEq_restrict {V' W' : Z.Opens}
    (hV : V = V') (hW : W = W') (h : W ≤ V) (h' : W' ≤ V') (φ : LocalMap M N V') :
    localRestrict h (localMapAlongEq hV φ) = localMapAlongEq hW (localRestrict h' φ) := by
  cases hV
  cases hW
  rfl

end OriginalOpenEquality

set_option backward.isDefEq.respectTransparency false in
/-- The SAME original cover lift produces the actual original local ξ map. -/
def memberXi (i : CoverIndex p κ f n) :
    LocalMap (sourceModule p κ f) ((targetComplex p κ f n).X 1) (cover p κ f n i) :=
  ActualWittGeometricXiHomotopy.xiSheafMap p κ f n i.property.1
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
    (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i)

set_option backward.isDefEq.respectTransparency false in
/-- On an actual tuple, use the SAME original member lift's canonical restriction. -/
def intersectionXi (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) (j : Fin (q + 1)) :
    LocalMap (sourceModule p κ f) ((targetComplex p κ f n).X 1)
      (twistedTuple p κ f n q i) :=
  ActualWittGeometricXiHomotopy.xiSheafMap p κ f n (liftedTuple_affine p κ f n q i)
    (tupleCoordinates p κ f n q i) (tupleCoordinates_etale p κ f n q i)
    (tupleLift p κ f n q i j) (tupleLift_reduction p κ f n q i j)

set_option backward.isDefEq.respectTransparency false in
/-- The actual original difference homotopy of TWO canonically restricted original member lifts. -/
def intersectionHomotopy (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n)
    (a b : Fin (q + 1)) :
    LocalMap (sourceModule p κ f) ((targetComplex p κ f n).X 0)
      (twistedTuple p κ f n q i) :=
  ActualWittGeometricXiHomotopy.homotopySheafMap p κ f n (liftedTuple_affine p κ f n q i)
    (tupleCoordinates p κ f n q i) (tupleCoordinates_etale p κ f n q i)
    (tupleLift p κ f n q i a) (tupleLift p κ f n q i b)
    (tupleLift_reduction p κ f n q i a) (tupleLift_reduction p κ f n q i b)

/-- Native singleton tuple transport preserves the actual original cover ξ. -/
def canonicalXi (i : Fin 1 → CoverIndex p κ f n) :
    LocalMap (sourceModule p κ f) ((targetComplex p κ f n).X 1)
      (tupleOpen (cover p κ f n) 0 i) :=
  localMapAlongEq (singletonOpen_eq p κ f n i) (memberXi p κ f n (i 0))

/-- The ordinary Čech convention uses the NEGATIVE original geometric homotopy. -/
def canonicalH (i : Fin 2 → CoverIndex p κ f n) :
    LocalMap (sourceModule p κ f) ((targetComplex p κ f n).X 0)
      (tupleOpen (cover p κ f n) 1 i) :=
  -localMapAlongEq (tupleOpen_eq p κ f n 1 i) (intersectionHomotopy p κ f n 1 i 0 1)

/-- The actual original ξ maps assemble by the EXISTING native adjunction/product constructor. -/
def canonicalXiCochain :
    sourceModule p κ f ⟶
      ((DeligneIllusieLocalContinuationCechBicomplex.bicomplex
        (cover p κ f n) (targetComplex p κ f n)).X 1).X 0 :=
  localCochain (cover p κ f n) 0 (canonicalXi p κ f n)

/-- The actual negative original H maps assemble by the SAME existing native constructor. -/
def canonicalHCochain :
    sourceModule p κ f ⟶
      ((DeligneIllusieLocalContinuationCechBicomplex.bicomplex
        (cover p κ f n) (targetComplex p κ f n)).X 0).X 1 :=
  localCochain (cover p κ f n) 1 (canonicalH p κ f n)

omit [IsSeparated f] in
set_option backward.isDefEq.respectTransparency false in
/-- Every ξ-cochain component is the adjoint of the SAME actual produced local ξ. -/
theorem canonicalXiCochain_pi (i : Fin 1 → CoverIndex p κ f n) :
    canonicalXiCochain p κ f n ≫
      Pi.π (fun j => DeligneIllusieLocalContinuationCechModules.factor
        ((targetComplex p κ f n).X 1) (tupleOpen (cover p κ f n) 0 j)) i =
      localAdjoint (tupleOpen (cover p κ f n) 0 i) (canonicalXi p κ f n i) :=
  localCochain_pi (cover p κ f n) 0 (canonicalXi p κ f n) i

set_option backward.isDefEq.respectTransparency false in
/-- Every h-cochain component keeps exactly the NEGATIVE original geometric H. -/
theorem canonicalHCochain_pi (i : Fin 2 → CoverIndex p κ f n) :
    canonicalHCochain p κ f n ≫
      Pi.π (fun j => DeligneIllusieLocalContinuationCechModules.factor
        ((targetComplex p κ f n).X 0) (tupleOpen (cover p κ f n) 1 j)) i =
      localAdjoint (tupleOpen (cover p κ f n) 1 i) (canonicalH p κ f n i) :=
  localCochain_pi (cover p κ f n) 1 (canonicalH p κ f n) i

set_option backward.isDefEq.respectTransparency false in
private theorem localRestrict_neg {Z : Scheme.{u}} {M N : Z.Modules}
    {V W : Z.Opens} (h : W ≤ V) (φ : LocalMap M N V) :
    localRestrict h (-φ) = -localRestrict h φ := by
  let : (Scheme.Modules.restrictFunctor V.ι).Additive :=
    (Scheme.Modules.restrictAdjunction V.ι).left_adjoint_additive
  let : (Scheme.Modules.restrictFunctor W.ι).Additive :=
    (Scheme.Modules.restrictAdjunction W.ι).left_adjoint_additive
  change ((Scheme.Modules.restrictAdjunction W.ι).homAddEquiv M (N.restrict W.ι)).symm
      (((Scheme.Modules.restrictAdjunction V.ι).homAddEquiv M (N.restrict V.ι)) (-φ) ≫
        DeligneIllusieLocalContinuationCechModules.factorMap N h) =
    -((Scheme.Modules.restrictAdjunction W.ι).homAddEquiv M (N.restrict W.ι)).symm
      (((Scheme.Modules.restrictAdjunction V.ι).homAddEquiv M (N.restrict V.ι)) φ ≫
        DeligneIllusieLocalContinuationCechModules.factorMap N h)
  rw [map_neg, Preadditive.neg_comp, map_neg]

omit [IsSeparated f] in
private theorem canonicalXi_boundary_pair (i : Fin 2 → CoverIndex p κ f n) :
    localBoundary (cover p κ f n) 0 (canonicalXi p κ f n) i =
      localRestrict (tupleOpen_le_face (cover p κ f n) 0 0 i)
          (canonicalXi p κ f n (i ∘ (SimplexCategory.δ 0).toOrderHom.toFun)) -
        localRestrict (tupleOpen_le_face (cover p κ f n) 0 1 i)
          (canonicalXi p κ f n (i ∘ (SimplexCategory.δ 1).toOrderHom.toFun)) := by
  simp [localBoundary, Fin.sum_univ_two, sub_eq_add_neg]

private theorem canonicalH_boundary_triple (i : Fin 3 → CoverIndex p κ f n) :
    localBoundary (cover p κ f n) 1 (canonicalH p κ f n) i =
      localRestrict (tupleOpen_le_face (cover p κ f n) 1 0 i)
          (canonicalH p κ f n (i ∘ (SimplexCategory.δ 0).toOrderHom.toFun)) -
        localRestrict (tupleOpen_le_face (cover p κ f n) 1 1 i)
          (canonicalH p κ f n (i ∘ (SimplexCategory.δ 1).toOrderHom.toFun)) +
        localRestrict (tupleOpen_le_face (cover p κ f n) 1 2 i)
          (canonicalH p κ f n (i ∘ (SimplexCategory.δ 2).toOrderHom.toFun)) := by
  simp [localBoundary, Fin.sum_univ_three, sub_eq_add_neg]

omit [PerfectRing κ p] [SmoothOfRelativeDimension n f] [IsSeparated f] in
/-- The actual geometric tuple lies in each SAME original cover member. -/
theorem tupleCover_le (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) (j : Fin (q + 1)) :
    twistedTuple p κ f n q i ≤ cover p κ f n (i j) :=
  (tupleOpen_eq p κ f n q i).symm.le.trans
    (leOfHom (Pi.π (fun a : Fin (q + 1) => cover p κ f n (i a)) j))

omit [PerfectRing κ p] [SmoothOfRelativeDimension n f] [IsSeparated f] in
/-- The original geometric full tuple lies in its SAME original deleted face. -/
theorem twistedFace_le (q : ℕ) (k : Fin (q + 2))
    (i : Fin (q + 2) → CoverIndex p κ f n) :
    twistedTuple p κ f n (q + 1) i ≤
      twistedTuple p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) :=
  (tupleOpen_eq p κ f n (q + 1) i).symm.le.trans
    ((tupleOpen_le_face (cover p κ f n) q k i).trans
      (tupleOpen_eq p κ f n q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).le)

omit [IsSeparated f] in
private theorem canonicalXi_face_transport (i : Fin 2 → CoverIndex p κ f n) (k : Fin 2) :
    localRestrict (tupleOpen_le_face (cover p κ f n) 0 k i)
        (canonicalXi p κ f n (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) =
      localMapAlongEq (tupleOpen_eq p κ f n 1 i)
        (localRestrict (tupleCover_le p κ f n 1 i ((SimplexCategory.δ k).toOrderHom.toFun 0))
          (memberXi p κ f n (i ((SimplexCategory.δ k).toOrderHom.toFun 0)))) := by
  exact localMapAlongEq_restrict
    (singletonOpen_eq p κ f n (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
    (tupleOpen_eq p κ f n 1 i)
    (tupleOpen_le_face (cover p κ f n) 0 k i)
    (tupleCover_le p κ f n 1 i ((SimplexCategory.δ k).toOrderHom.toFun 0)) _

private theorem canonicalH_face_transport (i : Fin 3 → CoverIndex p κ f n) (k : Fin 3) :
    localRestrict (tupleOpen_le_face (cover p κ f n) 1 k i)
        (canonicalH p κ f n (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) =
      -localMapAlongEq (tupleOpen_eq p κ f n 2 i)
        (localRestrict (twistedFace_le p κ f n 1 k i)
          (intersectionHomotopy p κ f n 1 (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) 0 1)) := by
  unfold canonicalH
  rw [localRestrict_neg]
  congr 1
  exact localMapAlongEq_restrict
    (tupleOpen_eq p κ f n 1 (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
    (tupleOpen_eq p κ f n 2 i)
    (tupleOpen_le_face (cover p κ f n) 1 k i)
    (twistedFace_le p κ f n 1 k i) _

/-- The actual geometric degree-one total cochain, retaining ξ and the NEGATIVE H. -/
def canonicalOneComponent : sourceModule p κ f ⟶
    (DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex
      (cover p κ f n) (targetComplex p κ f n)).X 1 :=
  degreeOneComponent
    (DeligneIllusieLocalContinuationCechBicomplex.bicomplex (cover p κ f n) (targetComplex p κ f n))
    (canonicalXiCochain p κ f n) (canonicalHCochain p κ f n)

set_option backward.isDefEq.respectTransparency false in
/-- Total ξ projection returns the SAME actual original geometric ξ component. -/
theorem canonicalOneComponent_xi (i : Fin 1 → CoverIndex p κ f n) :
    canonicalOneComponent p κ f n ≫ HomologicalComplex₂.πTotalUpNat
        (DeligneIllusieLocalContinuationCechBicomplex.bicomplex
          (cover p κ f n) (targetComplex p κ f n)) 1 0 1 ≫
      Pi.π (fun j => DeligneIllusieLocalContinuationCechModules.factor
        ((targetComplex p κ f n).X 1) (tupleOpen (cover p κ f n) 0 j)) i =
      localAdjoint (tupleOpen (cover p κ f n) 0 i) (canonicalXi p κ f n i) := by
  simp only [canonicalOneComponent, degreeOneComponent_π_one_zero_assoc,
    canonicalXiCochain_pi]

set_option backward.isDefEq.respectTransparency false in
/-- Total h projection returns exactly the NEGATIVE original geometric H component. -/
theorem canonicalOneComponent_h (i : Fin 2 → CoverIndex p κ f n) :
    canonicalOneComponent p κ f n ≫ HomologicalComplex₂.πTotalUpNat
        (DeligneIllusieLocalContinuationCechBicomplex.bicomplex
          (cover p κ f n) (targetComplex p κ f n)) 0 1 1 ≫
      Pi.π (fun j => DeligneIllusieLocalContinuationCechModules.factor
        ((targetComplex p κ f n).X 0) (tupleOpen (cover p κ f n) 1 j)) i =
      localAdjoint (tupleOpen (cover p κ f n) 1 i) (canonicalH p κ f n i) := by
  simp only [canonicalOneComponent, degreeOneComponent_π_zero_one_assoc,
    canonicalHCochain_pi]


omit [IsSeparated f] in
set_option backward.isDefEq.respectTransparency false in
/-- Closedness of every actual original chosen member, derived from its actual lift. -/
theorem memberXi_closed (i : CoverIndex p κ f n) :
    memberXi p κ f n i ≫
      (Scheme.Modules.restrictFunctor (cover p κ f n i).ι).map
        ((targetComplex p κ f n).d 1 2) = 0 :=
  ActualWittGeometricXiHomotopy.xiSheafMap_closed p κ f n i.property.1
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
    (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i)

set_option backward.isDefEq.respectTransparency false in
/-- The actual original maps on every tuple satisfy their whole homotopy equation. -/
theorem intersectionXi_sub (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n)
    (a b : Fin (q + 1)) :
    intersectionXi p κ f n q i a - intersectionXi p κ f n q i b =
      intersectionHomotopy p κ f n q i a b ≫
        (Scheme.Modules.restrictFunctor (twistedTuple p κ f n q i).ι).map
          ((targetComplex p κ f n).d 0 1) :=
  ActualWittGeometricXiHomotopy.xiSheafMap_sub p κ f n
    (liftedTuple_affine p κ f n q i)
    (tupleCoordinates p κ f n q i) (tupleCoordinates_etale p κ f n q i)
    (tupleLift p κ f n q i a) (tupleLift p κ f n q i b)
    (tupleLift_reduction p κ f n q i a) (tupleLift_reduction p κ f n q i b)

set_option backward.isDefEq.respectTransparency false in
/-- Strict triple coherence of the SAME original restricted member lifts. -/
theorem intersectionHomotopy_cocycle (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n)
    (a b c : Fin (q + 1)) :
    intersectionHomotopy p κ f n q i a c =
      intersectionHomotopy p κ f n q i a b + intersectionHomotopy p κ f n q i b c :=
  ActualWittGeometricXiHomotopy.homotopySheafMap_cocycle p κ f n
    (liftedTuple_affine p κ f n q i)
    (tupleCoordinates p κ f n q i) (tupleCoordinates_etale p κ f n q i)
    (tupleLift p κ f n q i a) (tupleLift p κ f n q i b) (tupleLift p κ f n q i c)
    (tupleLift_reduction p κ f n q i a) (tupleLift_reduction p κ f n q i b)
    (tupleLift_reduction p κ f n q i c)

omit [IsSeparated f] in
/-- The actual native singleton ξ components are closed, with no closure input. -/
theorem canonicalXi_closed (i : Fin 1 → CoverIndex p κ f n) :
    canonicalXi p κ f n i ≫
      (Scheme.Modules.restrictFunctor (tupleOpen (cover p κ f n) 0 i).ι).map
        ((targetComplex p κ f n).d 1 2) = 0 := by
  unfold canonicalXi
  rw [← localMapAlongEq_comp, memberXi_closed, localMapAlongEq_zero]


private theorem localAdjoint_transport {Z : Scheme.{u}} {M N : Z.Modules}
    {V W : Z.Opens} (h : V = W) (φ : LocalMap M N W) (hWV : W ≤ V) :
    localAdjoint V (localMapAlongEq h φ) ≫
        DeligneIllusieLocalContinuationCechModules.factorMap N hWV = localAdjoint W φ := by
  cases h
  change localAdjoint V φ ≫
    DeligneIllusieLocalContinuationCechModules.factorMap N (le_refl V) = _
  rw [DeligneIllusieLocalContinuationCechModules.factorMap_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The original member evaluation of the actual total component is the original local adjoint. -/
theorem canonicalOneComponent_evaluation (i : CoverIndex p κ f n) :
    canonicalOneComponent p κ f n ≫
      (DeligneIllusieCechTotalEvaluation.evaluation (cover p κ f n) (targetComplex p κ f n) i).f 1 =
        localAdjoint (cover p κ f n i) (memberXi p κ f n i) := by
  let r := DeligneIllusieLocalContinuationCechModules.factorMap
    ((targetComplex p κ f n).X 1) (singletonOpen_eq p κ f n (fun _ => i)).symm.le
  have h := canonicalOneComponent_xi p κ f n (fun _ => i)
  calc
    _ = (canonicalOneComponent p κ f n ≫
        HomologicalComplex₂.πTotalUpNat
          (DeligneIllusieLocalContinuationCechBicomplex.bicomplex
            (cover p κ f n) (targetComplex p κ f n)) 1 0 1 ≫
        Pi.π (fun j => DeligneIllusieLocalContinuationCechModules.factor
          ((targetComplex p κ f n).X 1) (tupleOpen (cover p κ f n) 0 j))
          (fun _ => i)) ≫ r := by
      rw [DeligneIllusieCechTotalEvaluation.evaluation_f]
      simp only [Category.assoc]
      rfl
    _ = _ := (congrArg (fun a => a ≫ r) h).trans
      (localAdjoint_transport (singletonOpen_eq p κ f n (fun _ => i))
        (memberXi p κ f n i) _)

set_option backward.isDefEq.respectTransparency false in
/-- Whole original over-open evaluation recovers the SAME actual geometric local ξ map. -/
theorem canonicalOneComponent_localEvaluation (i : CoverIndex p κ f n) :
    (Scheme.Modules.restrictFunctor (cover p κ f n i).ι).map (canonicalOneComponent p κ f n) ≫
      (DeligneIllusieCechTotalEvaluation.localEvaluation
        (cover p κ f n) (targetComplex p κ f n) i).f 1 = memberXi p κ f n i := by
  let L := Scheme.Modules.restrictFunctor (cover p κ f n i).ι
  let adj := Scheme.Modules.restrictAdjunction (cover p κ f n i).ι
  change L.map (canonicalOneComponent p κ f n) ≫
    (L.map ((DeligneIllusieCechTotalEvaluation.evaluation
        (cover p κ f n) (targetComplex p κ f n) i).f 1) ≫
      adj.counit.app (L.obj ((targetComplex p κ f n).X 1))) = _
  rw [← Category.assoc, ← L.map_comp, canonicalOneComponent_evaluation]
  have ha := adj.homEquiv_counit (sourceModule p κ f)
    (L.obj ((targetComplex p κ f n).X 1))
    (localAdjoint (cover p κ f n i) (memberXi p κ f n i))
  exact ha.symm.trans ((adj.homEquiv (sourceModule p κ f)
    (L.obj ((targetComplex p κ f n).X 1))).symm_apply_apply (memberXi p κ f n i))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
/-- Same original member lift, canonically restricted to the actual original tuple. -/
theorem memberXi_restrict (q : ℕ) (i : Fin (q + 1) → CoverIndex p κ f n) (j : Fin (q + 1)) :
    localRestrict (tupleCover_le p κ f n q i j) (memberXi p κ f n (i j)) =
      intersectionXi p κ f n q i j := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (i j).val
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedTuple p κ f n q i)
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (i j).property.1
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedTuple_affine p κ f n q i)
  exact ActualWittGeometricXiHomotopy.xiSheafMap_restrict p κ f n
    (liftedTuple_affine p κ f n q i) (i j).property.1 (tupleInclusion p κ f n q i j)
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n (i j))
    (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n (i j))
    (tupleCoordinates p κ f n q i) (tupleCoordinates_etale p κ f n q i)
    (DeligneIllusieWittGlobalDescent.coverLift p κ f n (i j))
    (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n (i j))


private def faceRestrictedHomotopy (i : Fin 3 → CoverIndex p κ f n) (k : Fin 3) :
    LocalMap (sourceModule p κ f) ((targetComplex p κ f n).X 0) (twistedTuple p κ f n 2 i) := by
  let t := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedTuple p κ f n 1 t)
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedTuple p κ f n 2 i)
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedTuple_affine p κ f n 1 t)
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedTuple_affine p κ f n 2 i)
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f (faceTupleInclusion p κ f n 1 k i)
  let hβ := WittTwoSchemeAffineRestrictions.restriction_etale
    (liftedTuple_affine p κ f n 2 i) (liftedTuple_affine p κ f n 1 t)
    (faceTupleInclusion p κ f n 1 k i)
  let F := tupleLift p κ f n 1 t 0
  let G := tupleLift p κ f n 1 t 1
  let hF := tupleLift_reduction p κ f n 1 t 0
  let hG := tupleLift_reduction p κ f n 1 t 1
  exact ActualWittGeometricXiHomotopy.homotopySheafMap p κ f n
    (liftedTuple_affine p κ f n 2 i) (tupleCoordinates p κ f n 2 i)
    (tupleCoordinates_etale p κ f n 2 i)
    (WittTwoEtaleRestrictionCoherence.restrictedLift p κ β F hF hβ)
    (WittTwoEtaleRestrictionCoherence.restrictedLift p κ β G hG hβ)
    (WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p κ β F hF hβ)
    (WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p κ β G hG hβ)

private theorem intersectionHomotopy_face_raw (i : Fin 3 → CoverIndex p κ f n) (k : Fin 3) :
    localRestrict (twistedFace_le p κ f n 1 k i)
      (intersectionHomotopy p κ f n 1 (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) 0 1) =
        faceRestrictedHomotopy p κ f n i k := by
  let t := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedTuple p κ f n 1 t)
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedTuple p κ f n 2 i)
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedTuple_affine p κ f n 1 t)
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedTuple_affine p κ f n 2 i)
  exact ActualWittGeometricXiHomotopy.homotopySheafMap_restrict p κ f n
    (liftedTuple_affine p κ f n 2 i) (liftedTuple_affine p κ f n 1 t)
    (faceTupleInclusion p κ f n 1 k i)
    (tupleCoordinates p κ f n 1 t) (tupleCoordinates_etale p κ f n 1 t)
    (tupleCoordinates p κ f n 2 i) (tupleCoordinates_etale p κ f n 2 i)
    (tupleLift p κ f n 1 t 0) (tupleLift p κ f n 1 t 1)
    (tupleLift_reduction p κ f n 1 t 0) (tupleLift_reduction p κ f n 1 t 1)

private theorem faceRestrictedHomotopy_eq (i : Fin 3 → CoverIndex p κ f n) (k : Fin 3) :
    faceRestrictedHomotopy p κ f n i k =
      intersectionHomotopy p κ f n 2 i
        ((SimplexCategory.δ k).toOrderHom.toFun 0) ((SimplexCategory.δ k).toOrderHom.toFun 1) := by
  unfold faceRestrictedHomotopy
  dsimp only []
  simp only [tupleLift_face_restrict]
  rfl

/-- Same actual pair homotopy on a triple: direct and face-iterated lifts agree. -/
theorem intersectionHomotopy_face (i : Fin 3 → CoverIndex p κ f n) (k : Fin 3) :
    localRestrict (twistedFace_le p κ f n 1 k i)
      (intersectionHomotopy p κ f n 1 (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) 0 1) =
        intersectionHomotopy p κ f n 2 i
          ((SimplexCategory.δ k).toOrderHom.toFun 0) ((SimplexCategory.δ k).toOrderHom.toFun 1) :=
  (intersectionHomotopy_face_raw p κ f n i k).trans (faceRestrictedHomotopy_eq p κ f n i k)

private theorem localMapAlongEq_sub {Z : Scheme.{u}} {M N : Z.Modules}
    {V W : Z.Opens} (e : V = W) (a b : LocalMap M N W) :
    localMapAlongEq e (a - b) = localMapAlongEq e a - localMapAlongEq e b := by
  cases e
  rfl

/-- The actual native pair equation, with ordinary boundary and h = -H. -/
theorem canonicalXi_pair (i : Fin 2 → CoverIndex p κ f n) :
    localBoundary (cover p κ f n) 0 (canonicalXi p κ f n) i =
      canonicalH p κ f n i ≫
        (Scheme.Modules.restrictFunctor (tupleOpen (cover p κ f n) 1 i).ι).map
          ((targetComplex p κ f n).d 0 1) := by
  rw [canonicalXi_boundary_pair, canonicalXi_face_transport, canonicalXi_face_transport,
    memberXi_restrict, memberXi_restrict]
  change localMapAlongEq (tupleOpen_eq p κ f n 1 i) (intersectionXi p κ f n 1 i 1) -
      localMapAlongEq (tupleOpen_eq p κ f n 1 i) (intersectionXi p κ f n 1 i 0) = _
  have hp := congrArg (localMapAlongEq (tupleOpen_eq p κ f n 1 i))
    (intersectionXi_sub p κ f n 1 i 0 1)
  rw [localMapAlongEq_sub, localMapAlongEq_comp] at hp
  unfold canonicalH
  rw [Preadditive.neg_comp]
  rw [show localMapAlongEq (tupleOpen_eq p κ f n 1 i) (intersectionXi p κ f n 1 i 1) -
      localMapAlongEq (tupleOpen_eq p κ f n 1 i) (intersectionXi p κ f n 1 i 0) =
      -(localMapAlongEq (tupleOpen_eq p κ f n 1 i) (intersectionXi p κ f n 1 i 0) -
        localMapAlongEq (tupleOpen_eq p κ f n 1 i) (intersectionXi p κ f n 1 i 1)) by abel]
  rw [hp]

/-- The actual native triple equation for the SAME original selected lifts. -/
theorem canonicalH_triple (i : Fin 3 → CoverIndex p κ f n) :
    localBoundary (cover p κ f n) 1 (canonicalH p κ f n) i = 0 := by
  rw [canonicalH_boundary_triple, canonicalH_face_transport, canonicalH_face_transport,
    canonicalH_face_transport, intersectionHomotopy_face, intersectionHomotopy_face,
    intersectionHomotopy_face]
  change -localMapAlongEq (tupleOpen_eq p κ f n 2 i) (intersectionHomotopy p κ f n 2 i 1 2) -
      -localMapAlongEq (tupleOpen_eq p κ f n 2 i) (intersectionHomotopy p κ f n 2 i 0 2) +
      -localMapAlongEq (tupleOpen_eq p κ f n 2 i) (intersectionHomotopy p κ f n 2 i 0 1) = 0
  rw [intersectionHomotopy_cocycle p κ f n 2 i 0 1 2, localMapAlongEq_add]
  abel

/-- Canonical local data: all natural equations are produced from the actual Witt geometry. -/
def canonicalLocalData :
    LocalData (cover p κ f n) (sourceModule p κ f) (targetComplex p κ f n) where
  ξ := canonicalXi p κ f n
  h := canonicalH p κ f n
  closed := canonicalXi_closed p κ f n
  pair := canonicalXi_pair p κ f n
  triple := canonicalH_triple p κ f n

/-- Actual internally produced geometry gives the original native single-source Čech morphism. -/
def canonicalOneMap :
    (HomologicalComplex.single (twist p κ f).Modules (.up ℕ) 1).obj (sourceModule p κ f) ⟶
      DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex
        (cover p κ f n) (targetComplex p κ f n) :=
  descentMap (cover p κ f n) (canonicalLocalData p κ f n)

/-- The actual total component is closed by the internally derived local equations. -/
theorem canonicalOneComponent_closed :
    canonicalOneComponent p κ f n ≫
      (DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex
        (cover p κ f n) (targetComplex p κ f n)).d 1 2 = 0 :=
  degreeOneComponent_closed
    (DeligneIllusieLocalContinuationCechBicomplex.bicomplex
      (cover p κ f n) (targetComplex p κ f n))
    (canonicalXiCochain p κ f n) (canonicalHCochain p κ f n)
    (xiCochain_closed (cover p κ f n) (canonicalLocalData p κ f n))
    (cochain_pair (cover p κ f n) (canonicalLocalData p κ f n))
    (cochain_triple (cover p κ f n) (canonicalLocalData p κ f n))

/-- The native single-object source unit retains exactly the already defined actual component. -/
theorem canonicalOneMap_f :
    (canonicalOneMap p κ f n).f 1 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 1 (sourceModule p κ f)).hom ≫
        canonicalOneComponent p κ f n := by
  simp only [canonicalOneMap, descentMap, degreeOneMap, HomologicalComplex.mkHomFromSingle_f]
  rfl

/-- Whole original degree-one component readback from the SAME canonical complex morphism. -/
theorem canonicalOneMap_component :
    (HomologicalComplex.singleObjXSelf (.up ℕ) 1 (sourceModule p κ f)).inv ≫
      (canonicalOneMap p κ f n).f 1 = canonicalOneComponent p κ f n := by
  rw [canonicalOneMap_f, Iso.inv_hom_id_assoc]

/-- Whole over-open evaluation of the SAME actual canonical morphism. -/
theorem canonicalOneMap_localEvaluation (i : CoverIndex p κ f n) :
    (Scheme.Modules.restrictFunctor (cover p κ f n i).ι).map ((canonicalOneMap p κ f n).f 1) ≫
      (DeligneIllusieCechTotalEvaluation.localEvaluation
        (cover p κ f n) (targetComplex p κ f n) i).f 1 =
      (Scheme.Modules.restrictFunctor (cover p κ f n i).ι).map
        (HomologicalComplex.singleObjXSelf (.up ℕ) 1 (sourceModule p κ f)).hom ≫
          memberXi p κ f n i := by
  rw [canonicalOneMap_f, Functor.map_comp, Category.assoc, canonicalOneComponent_localEvaluation]

/-- The SAME actual native local representative, with its original adjunction and ξ. -/
theorem canonicalOneMap_localRepresentative (i : Fin 1 → CoverIndex p κ f n) :
    canonicalOneMap p κ f n ≫
      zeroRowProjection (DeligneIllusieLocalContinuationCechBicomplex.bicomplex
        (cover p κ f n) (targetComplex p κ f n)) ≫
      zeroRowFactorProjection (cover p κ f n) (targetComplex p κ f n) i =
        localRepresentative (cover p κ f n) (canonicalLocalData p κ f n) i :=
  descentMap_localRepresentative (cover p κ f n) (canonicalLocalData p κ f n) i

/-- Native homology of the actual canonical map has exactly its actual original ξ representative. -/
theorem canonicalOneMap_homology_local (i : Fin 1 → CoverIndex p κ f n) :
    HomologicalComplex.homologyMap (canonicalOneMap p κ f n) 1 ≫
      HomologicalComplex.homologyMap
        (zeroRowProjection (DeligneIllusieLocalContinuationCechBicomplex.bicomplex
          (cover p κ f n) (targetComplex p κ f n))) 1 ≫
      HomologicalComplex.homologyMap
        (zeroRowFactorProjection (cover p κ f n) (targetComplex p κ f n) i) 1 =
      HomologicalComplex.homologyMap
        (localRepresentative (cover p κ f n) (canonicalLocalData p κ f n) i) 1 :=
  descentMap_homology_local (cover p κ f n) (canonicalLocalData p κ f n) i

end EnvelopeProperty.DI.ActualWittCechOneMap


