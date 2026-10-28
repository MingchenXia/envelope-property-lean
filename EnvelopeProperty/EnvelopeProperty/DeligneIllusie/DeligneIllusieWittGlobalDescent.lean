import EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreEtaleBasis
import EnvelopeProperty.DeligneIllusie.WittTwoSchemeAffineRestrictions
import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineBasis
import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineFrobenius
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierNaturality
import EnvelopeProperty.AlgGeom.Canonical.CotangentMorphismFunctoriality
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The actual Witt-scheme cover and independently produced local lifts

Blueprint: `blueprint/src/deligne-illusie-witt-global-descent.tex`,
node `def:di-witt-global-geometric-components`. This first source slice constructs
the original cover and its actual lifts; canonical alpha/beta and their closure
equations are subsequent parts of the same still-notready node.

These are the geometric inputs constructed internally for canonical Cech descent.
No family of local maps or compatibility equations is accepted from the caller.
-/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.DeligneIllusieWittGlobalDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Cartier
universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable {Xtilde : Scheme.{u}}
  (f : Xtilde ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
  (n : ℕ) [SmoothOfRelativeDimension n f]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra

private abbrev X := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev g : X p k f ⟶ Spec (CommRingCat.of k) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
private abbrev Y := SchemeRelativeFrobenius.twist p (g p k f)

/-- Original lifted affine coordinate opens, retaining their genuine Witt-model source. -/
abbrev CoverIndex := WittTwoSpecialFibreEtaleBasis.coordinateOpens p k f n

/-- The actual special-fibre inverse image of an internally indexed original lifted affine. -/
def sourceOpen (i : CoverIndex p k f n) : (X p k f).Opens :=
  WittTwoSpecialFibreEtaleBasis.basisOpens p k f n i

/-- The original true-twist open attached to the SAME actual special-fibre chart. -/
def coverOpen (i : CoverIndex p k f n) : (Y p k f).Opens :=
  RelativeTwistedAffineBasis.twistedOpen (g p k f) p (sourceOpen p k f n i)

omit [CharP k p] [PerfectRing k p] [SmoothOfRelativeDimension n f] in
/-- Every actual source cover member is genuinely affine, with no coordinate certificate input. -/
theorem sourceOpen_affine (i : CoverIndex p k f n) : IsAffineOpen (sourceOpen p k f n i) :=
  WittTwoSpecialFibreOpens.residueOpen_affine p k f i.property.1

omit [PerfectRing k p] in
/-- The internally constructed true-twist family covers the ENTIRE actual original Y. -/
theorem coverOpen_iSup : (⨆ i, coverOpen p k f n i) = ⊤ := by
  apply le_antisymm le_top
  intro y _
  let π : Y p k f ⟶ X p k f :=
    pullback.fst (g p k f) (SchemeRelativeFrobenius.baseMap (k := k) p)
  obtain ⟨U,hU,_,hxU,_,v,hv⟩ :=
    WittTwoSpecialFibreEtaleBasis.exists_etale_affine_refinement p k f n
      (V := ⊤) (W := ⊤) (π.base y) (by trivial) (by trivial)
  let i : CoverIndex p k f n := ⟨U,hU,v,hv⟩
  exact Opens.mem_iSup.mpr ⟨i,hxU⟩

/-- The original source chart's actual residual etale tuple, chosen only inside the construction. -/
def coordinates (i : CoverIndex p k f n) : Fin n → Γ(X p k f,sourceOpen p k f n i) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (sourceOpen p k f n i)
  exact i.property.2.choose

omit [CharP k p] [PerfectRing k p] [SmoothOfRelativeDimension n f] in
/-- The internally selected residual tuple is genuinely etale for its ORIGINAL structural action. -/
theorem coordinates_etale (i : CoverIndex p k f n) :
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (sourceOpen p k f n i)
    (MvPolynomial.aeval (R := k) (coordinates p k f n i)).toRingHom.Etale := by
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (sourceOpen p k f n i)
  exact i.property.2.choose_spec

/-- A genuine actual relative Frobenius lift is internally produced on EACH lifted cover member.
No compatibility between different members is asserted or needed. -/
def coverLift (i : CoverIndex p k f n) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f i.val
    WittTwoLiftDifference.Lift p k Γ(Xtilde,i.val) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact (WittTwoSchemeAffineRestrictions.exists_affineLift p k f i.property.1).choose

/-- The same internally produced lift has the ENTIRE actual residue-Frobenius equation. -/
theorem coverLift_reduction (i : CoverIndex p k f n) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f i.val
    ∀ t, algebraMap Γ(Xtilde,i.val)
        (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Xtilde,i.val))
        (coverLift p k f n i t) =
      WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,i.val) t := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact (WittTwoSchemeAffineRestrictions.exists_affineLift p k f i.property.1).choose_spec

/-- The SAME nonempty finite intersection in the original lifting scheme. -/
def liftedIntersection (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n) : Xtilde.Opens :=
  ⨅ j, (i j).val

omit [CharP k p] [PerfectRing k p] [SmoothOfRelativeDimension n f] in
private theorem liftedIntersection_le (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n)
    (j : Fin (q+1)) : liftedIntersection p k f n q i ≤ (i j).val := iInf_le _ j

omit [CharP k p] [PerfectRing k p] [SmoothOfRelativeDimension n f] in
/-- Genuine separated geometry supplies affineness of EVERY original finite intersection. -/
theorem liftedIntersection_affine [IsSeparated f]
    (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n) :
    IsAffineOpen (liftedIntersection p k f n q i) := by
  let : IsSeparated (terminal.from Xtilde) := by
    have h : f ≫ terminal.from (Spec (CommRingCat.of (WittTwo.Ring p k))) =
        terminal.from Xtilde := Subsingleton.elim _ _
    rw [← h]
    infer_instance
  exact IsAffineOpen.iInf fun j => (i j).property.1

private def intersectionRestriction (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n)
    (j : Fin (q+1)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (i j).val
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedIntersection p k f n q i)
    Γ(Xtilde,(i j).val) →ₐ[WittTwo.Ring p k]
      Γ(Xtilde,liftedIntersection p k f n q i) :=
  WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f
    (homOfLE (liftedIntersection_le p k f n q i j))

omit [CharP k p] [PerfectRing k p] [SmoothOfRelativeDimension n f] in
private theorem intersectionRestriction_etale [IsSeparated f]
    (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n) (j : Fin (q+1)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (i j).val
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedIntersection p k f n q i)
    (intersectionRestriction p k f n q i j).toRingHom.Etale :=
  WittTwoSchemeAffineRestrictions.restriction_etale
    (liftedIntersection_affine p k f n q i) (i j).property.1
    (homOfLE (liftedIntersection_le p k f n q i j))

/-- Restriction of ONE original chosen member lift to an actual finite intersection.
Other member lifts remain independent. Both whole commuting equations are derived internally. -/
def overlapLift [IsSeparated f]
    (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n) (j : Fin (q+1)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedIntersection p k f n q i)
    WittTwoLiftDifference.Lift p k Γ(Xtilde,liftedIntersection p k f n q i) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (i j).val
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedIntersection p k f n q i)
  letI := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedIntersection_affine p k f n q i)
  exact WittTwoEtaleRestrictionCoherence.restrictedLift p k
    (intersectionRestriction p k f n q i j) (coverLift p k f n (i j))
    (coverLift_reduction p k f n (i j)) (intersectionRestriction_etale p k f n q i j)

/-- The internally produced intersection lift has its ENTIRE genuine residue Frobenius equation. -/
theorem overlapLift_reduction [IsSeparated f]
    (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n) (j : Fin (q+1)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedIntersection p k f n q i)
    ∀ t, algebraMap Γ(Xtilde,liftedIntersection p k f n q i)
        (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Xtilde,liftedIntersection p k f n q i))
        (overlapLift p k f n q i j t) =
      WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,liftedIntersection p k f n q i) t := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (i j).val
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedIntersection p k f n q i)
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedIntersection_affine p k f n q i)
  exact WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k
    (intersectionRestriction p k f n q i j) (coverLift p k f n (i j))
    (coverLift_reduction p k f n (i j)) (intersectionRestriction_etale p k f n q i j)

/-- The original whole cover lift really commutes with its internally constructed overlap lift. -/
theorem overlapLift_commutes [IsSeparated f]
    (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n) (j : Fin (q+1)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (i j).val
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedIntersection p k f n q i)
    ∀ t, (intersectionRestriction p k f n q i j) (coverLift p k f n (i j) t) =
      overlapLift p k f n q i j
        (WittTwoLiftDifferenceNaturality.twistMap p k (intersectionRestriction p k f n q i j) t) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (i j).val
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f (liftedIntersection p k f n q i)
  let := WittTwoSchemeAffineRestrictions.affine_smooth f (liftedIntersection_affine p k f n q i)
  exact WittTwoEtaleRestrictionCoherence.restrictedLift_commutes p k
    (intersectionRestriction p k f n q i j) (coverLift p k f n (i j))
    (coverLift_reduction p k f n (i j)) (intersectionRestriction_etale p k f n q i j)

private theorem pullbackMap_of_projections {C : Type*} [Category* C]
    {A B S U V : C} (a : A ⟶ S) (b : B ⟶ S) [HasPullback a b]
    (t : U ⟶ V) (jV : V ⟶ pullback a b) (jU : U ⟶ pullback a b)
    (sV : V ⟶ A) (sU : U ⟶ A) (cV : V ⟶ B) (cU : U ⟶ B)
    (hjV_source : jV ≫ pullback.fst a b = sV)
    (hjU_source : jU ≫ pullback.fst a b = sU)
    (hjV_coefficient : jV ≫ pullback.snd a b = cV)
    (hjU_coefficient : jU ≫ pullback.snd a b = cU)
    (hs : t ≫ sV = sU) (hc : t ≫ cV = cU) : t ≫ jV = jU := by
  apply pullback.hom_ext
  · exact (Category.assoc t jV (pullback.fst a b)).trans
      ((congrArg (fun z => t ≫ z) hjV_source).trans (hs.trans hjU_source.symm))
  · exact (Category.assoc t jV (pullback.snd a b)).trans
      ((congrArg (fun z => t ≫ z) hjV_coefficient).trans (hc.trans hjU_coefficient.symm))

omit [PerfectRing k p] in
private theorem nativeChartMap_restriction {Z : Scheme.{u}}
    (h : Z ⟶ Spec (CommRingCat.of k))
    {U V : Z.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : U ⟶ V) :
    letI := CanonicalGeometry.cotangentOpenAlgebra h V
    letI := CanonicalGeometry.cotangentOpenAlgebra h U
    letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom h i).toAlgebra
    letI : IsScalarTower k Γ(Z,V) Γ(Z,U) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((EtaleSchemeSectionDifferential.restrictionAlgebraHom h i).commutes a).symm
    Spec.map (RelativeEtaleCartierNaturality.twistMap
      (k := k) (A := Γ(Z,V)) (B := Γ(Z,U)) p) ≫
      RelativeTwistedAffineFrobenius.chartMap h p V hV =
    RelativeTwistedAffineFrobenius.chartMap h p U hU := by
  let := CanonicalGeometry.cotangentOpenAlgebra h V
  let := CanonicalGeometry.cotangentOpenAlgebra h U
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom h i).toAlgebra
  let : IsScalarTower k Γ(Z,V) Γ(Z,U) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((EtaleSchemeSectionDifferential.restrictionAlgebraHom h i).commutes a).symm
  let τ := RelativeEtaleCartierNaturality.twistMap (k := k) (A := Γ(Z,V)) (B := Γ(Z,U)) p
  let sV := RelativeFrobenius.sourceMap (algebraMap k Γ(Z,V)) p
  let sU := RelativeFrobenius.sourceMap (algebraMap k Γ(Z,U)) p
  let cV := RelativeFrobenius.coefficientMap (algebraMap k Γ(Z,V)) p
  let cU := RelativeFrobenius.coefficientMap (algebraMap k Γ(Z,U)) p
  let jV : Spec (RelativeFrobenius.twist (algebraMap k Γ(Z,V)) p) ⟶
      pullback h (SchemeRelativeFrobenius.baseMap (k := k) p) :=
    RelativeTwistedAffineFrobenius.chartMap h p V hV
  let jU : Spec (RelativeFrobenius.twist (algebraMap k Γ(Z,U)) p) ⟶
      pullback h (SchemeRelativeFrobenius.baseMap (k := k) p) :=
    RelativeTwistedAffineFrobenius.chartMap h p U hU
  have hjV_source : jV ≫ pullback.fst h (SchemeRelativeFrobenius.baseMap (k := k) p) =
      Spec.map sV ≫ hV.fromSpec :=
    RelativeTwistedAffineFrobenius.chartMap_source h p V hV
  have hjU_source : jU ≫ pullback.fst h (SchemeRelativeFrobenius.baseMap (k := k) p) =
      Spec.map sU ≫ hU.fromSpec :=
    RelativeTwistedAffineFrobenius.chartMap_source h p U hU
  have hjV_coefficient : jV ≫ pullback.snd h (SchemeRelativeFrobenius.baseMap (k := k) p) =
      Spec.map cV :=
    RelativeTwistedAffineFrobenius.chartMap_coefficient h p V hV
  have hjU_coefficient : jU ≫ pullback.snd h (SchemeRelativeFrobenius.baseMap (k := k) p) =
      Spec.map cU :=
    RelativeTwistedAffineFrobenius.chartMap_coefficient h p U hU
  change Spec.map τ ≫ jV = jU
  refine pullbackMap_of_projections h (SchemeRelativeFrobenius.baseMap (k := k) p)
    (Spec.map τ) jV jU (Spec.map sV ≫ hV.fromSpec) (Spec.map sU ≫ hU.fromSpec)
    (Spec.map cV) (Spec.map cU) hjV_source hjU_source hjV_coefficient hjU_coefficient ?_ ?_
  ·
    have hs := congrArg Spec.map
      (RelativeEtaleCartierNaturality.twistMap_source
        (k := k) (A := Γ(Z,V)) (B := Γ(Z,U)) p)
    rw [Spec.map_comp, Spec.map_comp] at hs
    change Spec.map τ ≫ (Spec.map sV ≫ hV.fromSpec) = Spec.map sU ≫ hU.fromSpec
    calc
      _ = (Spec.map τ ≫ Spec.map sV) ≫ hV.fromSpec := (Category.assoc _ _ _).symm
      _ = (Spec.map sU ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(Z,V) Γ(Z,U)))) ≫
          hV.fromSpec := congrArg (fun a => a ≫ hV.fromSpec) hs
      _ = Spec.map sU ≫
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(Z,V) Γ(Z,U))) ≫ hV.fromSpec) :=
        Category.assoc _ _ _
      _ = Spec.map sU ≫ hU.fromSpec := by
        apply congrArg (fun a => Spec.map sU ≫ a)
        change Spec.map (Z.presheaf.map i.op) ≫ hV.fromSpec = hU.fromSpec
        exact hV.map_fromSpec hU i.op
  · exact (Spec.map_comp cV τ).symm.trans
      (congrArg Spec.map (RelativeEtaleCartierNaturality.twistMap_coefficient
        (k := k) (A := Γ(Z,V)) (B := Γ(Z,U)) p))

omit [PerfectRing k p] [SmoothOfRelativeDimension n f] in
/-- The native true-twist charts of actual affine Witt-scheme restrictions commute as WHOLE
scheme maps. No principal-open presentation or desired chart square is supplied. -/
theorem chartMap_restriction {U V : Xtilde.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : U ⟶ V) :
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f)
      (WittTwoSpecialFibreOpens.residueOpen p k f V)
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f)
      (WittTwoSpecialFibreOpens.residueOpen p k f U)
    let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
    letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) r).toAlgebra
    letI : IsScalarTower k
        Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f V)
        Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f U) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) r).commutes a).symm
    Spec.map (RelativeEtaleCartierNaturality.twistMap
        (k := k)
        (A := Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f V))
        (B := Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f U)) p) ≫
      RelativeTwistedAffineFrobenius.chartMap (g p k f) p
        (WittTwoSpecialFibreOpens.residueOpen p k f V)
        (WittTwoSpecialFibreOpens.residueOpen_affine p k f hV) =
    RelativeTwistedAffineFrobenius.chartMap (g p k f) p
      (WittTwoSpecialFibreOpens.residueOpen p k f U)
      (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) :=
  nativeChartMap_restriction p k (g p k f)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hV)
    (WittTwoSpecialFibreReduction.residueInclusion p k f i)

/- Actual finite intersections and their genuine chart restriction maps. -/
omit [PerfectRing k p] [SmoothOfRelativeDimension n f] in
/-- The ACTUAL native twist map of any affine Witt restriction is itself an
open immersion, derived from the whole original chart square. -/
theorem chartRestriction_isOpenImmersion {U V : Xtilde.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : U ⟶ V) :
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f)
      (WittTwoSpecialFibreOpens.residueOpen p k f V)
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f)
      (WittTwoSpecialFibreOpens.residueOpen p k f U)
    let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
    letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) r).toAlgebra
    letI : IsScalarTower k
        Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f V)
        Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f U) :=
      IsScalarTower.of_algebraMap_eq fun d =>
        ((EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) r).commutes d).symm
    IsOpenImmersion (Spec.map (RelativeEtaleCartierNaturality.twistMap
      (k := k) (A := Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f V))
      (B := Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f U)) p)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f)
    (WittTwoSpecialFibreOpens.residueOpen p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f)
    (WittTwoSpecialFibreOpens.residueOpen p k f U)
  let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) r).toAlgebra
  let : IsScalarTower k
      Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f V)
      Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f U) :=
    IsScalarTower.of_algebraMap_eq fun d =>
      ((EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) r).commutes d).symm
  let τ := RelativeEtaleCartierNaturality.twistMap
    (k := k) (A := Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f V))
    (B := Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f U)) p
  let jV := RelativeTwistedAffineFrobenius.chartMap (g p k f) p
    (WittTwoSpecialFibreOpens.residueOpen p k f V)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hV)
  let jU := RelativeTwistedAffineFrobenius.chartMap (g p k f) p
    (WittTwoSpecialFibreOpens.residueOpen p k f U)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
  have hjV : IsOpenImmersion jV := RelativeTwistedAffineFrobenius.chartMap_isOpenImmersion
    (g p k f) p (WittTwoSpecialFibreOpens.residueOpen p k f V)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hV)
  have hjU : IsOpenImmersion jU := RelativeTwistedAffineFrobenius.chartMap_isOpenImmersion
    (g p k f) p (WittTwoSpecialFibreOpens.residueOpen p k f U)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
  have hsquare : Spec.map τ ≫ jV = jU := chartMap_restriction p k f hU hV i
  let P : (Spec (RelativeFrobenius.twist
      (algebraMap k Γ(X p k f,WittTwoSpecialFibreOpens.residueOpen p k f U)) p) ⟶
      Y p k f) → Prop := fun t => IsOpenImmersion t
  have hjcomp : IsOpenImmersion (Spec.map τ ≫ jV) :=
    Eq.mp (congrArg P hsquare.symm) hjU
  exact @IsOpenImmersion.of_comp _ _ _ (Spec.map τ) jV hjV hjcomp

omit [PerfectRing k p] [SmoothOfRelativeDimension n f] in
/-- The actual Cech tuple open is precisely the true-twist inverse image of the
SAME finite intersection in the Witt lifting scheme, including empty intersections. -/
theorem cechTupleOpen_eq (q : ℕ) (i : Fin (q+1) → CoverIndex p k f n) :
    (∏ᶜ fun j : Fin (q+1) => coverOpen p k f n (i j)) =
      RelativeTwistedAffineBasis.twistedOpen (g p k f) p
        (WittTwoSpecialFibreOpens.residueOpen p k f (liftedIntersection p k f n q i)) := by
  apply le_antisymm
  · intro y hy
    let π : Y p k f ⟶ X p k f :=
      pullback.fst (g p k f) (SchemeRelativeFrobenius.baseMap (k := k) p)
    let sp : X p k f ⟶ Xtilde :=
      pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
    change sp.base (π.base y) ∈ (↑(⨅ j : Fin (q+1), (i j).val) : Set Xtilde)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun j =>
      (leOfHom (Limits.Pi.π (fun a : Fin (q+1) => coverOpen p k f n (i a)) j)) hy
  · apply leOfHom
    refine Limits.Pi.lift fun j => homOfLE ?_
    intro y hy
    let π : Y p k f ⟶ X p k f :=
      pullback.fst (g p k f) (SchemeRelativeFrobenius.baseMap (k := k) p)
    let sp : X p k f ⟶ Xtilde :=
      pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
    change sp.base (π.base y) ∈ (↑(⨅ a : Fin (q+1), (i a).val) : Set Xtilde) at hy
    rw [Opens.coe_iInf] at hy
    exact Set.mem_iInter.mp hy j

omit [CharP k p] [PerfectRing k p] [SmoothOfRelativeDimension n f] in
private theorem sectionRestriction_comp {U V W : Xtilde.Opens} (a : U ⟶ V) (b : V ⟶ W) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f W
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f a).comp
        (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f b) =
      WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f (a ≫ b) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f W
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  apply AlgHom.ext
  intro t
  change Xtilde.presheaf.map a.op (Xtilde.presheaf.map b.op t) =
    Xtilde.presheaf.map (a ≫ b).op t
  exact (ConcreteCategory.congr_hom (Xtilde.presheaf.map_comp b.op a.op) t).symm

/-- Restricting ONE internally chosen original member lift along two successive
actual affine inclusions returns its SAME direct restriction. The original cover
lifts remain independent; this statement does not assert their mutual naturality. -/
theorem coverLift_restriction_comp (c : CoverIndex p k f n)
    {U V : Xtilde.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (a : U ⟶ V) (b : V ⟶ c.val) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f c.val
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hV
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f b
    let γ := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f a
    let hβ : β.toRingHom.Etale :=
      WittTwoSchemeAffineRestrictions.restriction_etale hV c.property.1 b
    let hγ : γ.toRingHom.Etale :=
      WittTwoSchemeAffineRestrictions.restriction_etale hU hV a
    WittTwoEtaleRestrictionCoherence.restrictedLift p k γ
      (WittTwoEtaleRestrictionCoherence.restrictedLift p k β
        (coverLift p k f n c) (coverLift_reduction p k f n c) hβ)
      (WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β
        (coverLift p k f n c) (coverLift_reduction p k f n c) hβ) hγ =
    WittTwoEtaleRestrictionCoherence.restrictedLift p k
      (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f (a ≫ b))
      (coverLift p k f n c) (coverLift_reduction p k f n c)
      (WittTwoSchemeAffineRestrictions.restriction_etale hU c.property.1 (a ≫ b)) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f c.val
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hV
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f b
  let γ := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f a
  have hβ : β.toRingHom.Etale :=
    WittTwoSchemeAffineRestrictions.restriction_etale hV c.property.1 b
  have hγ : γ.toRingHom.Etale :=
    WittTwoSchemeAffineRestrictions.restriction_etale hU hV a
  have hcomp := WittTwoEtaleRestrictionCoherence.restrictedLift_comp p k β γ
    (coverLift p k f n c) (coverLift_reduction p k f n c) hβ hγ
  have hsection : γ.comp β =
      WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f (a ≫ b) :=
    sectionRestriction_comp p k f a b
  have lift_congr
      (δ ε : Γ(Xtilde,c.val) →ₐ[WittTwo.Ring p k] Γ(Xtilde,U))
      (h : δ = ε) (hδ : δ.toRingHom.Etale) (hε : ε.toRingHom.Etale) :
      WittTwoEtaleRestrictionCoherence.restrictedLift p k δ
          (coverLift p k f n c) (coverLift_reduction p k f n c) hδ =
        WittTwoEtaleRestrictionCoherence.restrictedLift p k ε
          (coverLift p k f n c) (coverLift_reduction p k f n c) hε := by
    cases h
    rfl
  dsimp only
  exact hcomp.symm.trans (lift_congr (γ.comp β)
    (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f (a ≫ b)) hsection
    (RingHom.Etale.stableUnderComposition β.toRingHom γ.toRingHom hβ hγ)
    (WittTwoSchemeAffineRestrictions.restriction_etale hU c.property.1 (a ≫ b)))

/- Actual geometry for the target restriction exchange.  Append inside the
owned GlobalDescent namespace.  All code here is an unverified draft.

Only chart squares of the actual Witt special fibre occur in the public
statement.  No cartesian-square or native-beta compatibility premise is
accepted.  The generic native cartesian/exterior value infrastructure remains
owned by the associated-sheaf lane. -/

private theorem innerPullbackOfActualCharts {C : Type*} [Category* C]
    {X Y BU BV TU TV : C} (F : X ⟶ Y)
    (βU : BU ⟶ TU) (βV : BV ⟶ TV)
    (sU : BU ⟶ X) (sV : BV ⟶ X) (jU : TU ⟶ Y) (jV : TV ⟶ Y)
    (a : BU ⟶ BV) (b : TU ⟶ TV) (hMono : Mono jV)
    (HU : IsPullback βU sU jU F) (HV : IsPullback βV sV jV F)
    (hs : a ≫ sV = sU) (hj : b ≫ jV = jU) : IsPullback βU a b βV := by
  letI := hMono
  have hp : a ≫ βV = βU ≫ b := by
    apply (cancel_mono jV).mp
    calc
      (a ≫ βV) ≫ jV = a ≫ (sV ≫ F) :=
        (Category.assoc a βV jV).trans (congrArg (fun t => a ≫ t) HV.w)
      _ = (a ≫ sV) ≫ F := (Category.assoc a sV F).symm
      _ = sU ≫ F := congrArg (fun t => t ≫ F) hs
      _ = βU ≫ jU := HU.w.symm
      _ = βU ≫ (b ≫ jV) := congrArg (fun t => βU ≫ t) hj.symm
      _ = (βU ≫ b) ≫ jV := (Category.assoc βU b jV).symm
  have ho : IsPullback (a ≫ sV) βU F (b ≫ jV) := by
    rw [hs, hj]
    exact HU.flip
  exact (IsPullback.of_right ho hp HV.flip).flip

omit [PerfectRing k p] [SmoothOfRelativeDimension n f] in
/-- The genuine native geometric-beta square of an arbitrary affine Witt
restriction is cartesian, derived from the actual two Frobenius charts.
The proof includes empty opens and supplies no CharP hypothesis on sections. -/
theorem chartRestriction_isPullback {U V : Xtilde.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : U ⟶ V) :
    let V₀ := WittTwoSpecialFibreOpens.residueOpen p k f V
    let U₀ := WittTwoSpecialFibreOpens.residueOpen p k f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) V₀
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) U₀
    let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
    let ψ := EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) r
    letI := ψ.toAlgebra
    letI : IsScalarTower k Γ(X p k f,V₀) Γ(X p k f,U₀) :=
      IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
    let τ := RelativeEtaleCartierNaturality.twistMap
      (k := k) (A := Γ(X p k f,V₀)) (B := Γ(X p k f,U₀)) p
    IsPullback
      (SchemeRelativeFrobeniusAffineMap.affineMap (algebraMap k Γ(X p k f,U₀)) p)
      (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (Spec.map τ)
      (SchemeRelativeFrobeniusAffineMap.affineMap (algebraMap k Γ(X p k f,V₀)) p) := by
  let V₀ := WittTwoSpecialFibreOpens.residueOpen p k f V
  let U₀ := WittTwoSpecialFibreOpens.residueOpen p k f U
  let hV₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hV
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) V₀
  letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) U₀
  let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
  let ψ := EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) r
  letI := ψ.toAlgebra
  letI : IsScalarTower k Γ(X p k f,V₀) Γ(X p k f,U₀) :=
    IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
  let τ := RelativeEtaleCartierNaturality.twistMap
    (k := k) (A := Γ(X p k f,V₀)) (B := Γ(X p k f,U₀)) p
  let σ : CommRingCat.of Γ(X p k f,V₀) ⟶ CommRingCat.of Γ(X p k f,U₀) :=
    CommRingCat.ofHom ψ.toRingHom
  let jV := RelativeTwistedAffineFrobenius.chartMap (g p k f) p V₀ hV₀
  let jU := RelativeTwistedAffineFrobenius.chartMap (g p k f) p U₀ hU₀
  letI hjV : IsOpenImmersion jV :=
    RelativeTwistedAffineFrobenius.chartMap_isOpenImmersion (g p k f) p V₀ hV₀
  have hs : Spec.map σ ≫ hV₀.fromSpec = hU₀.fromSpec := by
    change Spec.map ((X p k f).presheaf.map r.op) ≫ hV₀.fromSpec = hU₀.fromSpec
    exact hV₀.map_fromSpec hU₀ r.op
  have hj : Spec.map τ ≫ jV = jU := chartMap_restriction p k f hU hV i
  exact innerPullbackOfActualCharts (SchemeRelativeFrobenius.map p (g p k f))
    (SchemeRelativeFrobeniusAffineMap.affineMap (algebraMap k Γ(X p k f,U₀)) p)
    (SchemeRelativeFrobeniusAffineMap.affineMap (algebraMap k Γ(X p k f,V₀)) p)
    hU₀.fromSpec hV₀.fromSpec jU jV (Spec.map σ) (Spec.map τ)
    (@IsOpenImmersion.mono _ _ jV hjV)
    (RelativeTwistedAffineFrobenius.chartIsPullback (g p k f) p U₀ hU₀)
    (RelativeTwistedAffineFrobenius.chartIsPullback (g p k f) p V₀ hV₀) hs hj

/- Draft support for the actual arbitrary-chart restriction producer.
Not a stand-alone module and not kernel evidence. Intended inside the owned
DeligneIllusieWittGlobalDescent namespace after its actual scheme chart square,
with the existing module-sheaf imports. Keeping this glue here avoids a reverse
import from the W2 ring-restriction module into its global consumer. -/
/- Required imports:
EnvelopeProperty.AlgGeom.Canonical.CotangentMorphismFunctoriality
-/
private def restrictionCompositeUnit {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ Y) [IsOpenImmersion g] [IsOpenImmersion h]
    (M : X.Modules) : M ⟶
      (Scheme.Modules.pushforward (h ≫ g)).obj (M.restrict (h ≫ g)) :=
    (Scheme.Modules.restrictAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.restrictAdjunction h).unit.app (M.restrict g)) ≫
      (Scheme.Modules.pushforwardComp h g).hom.app ((M.restrict g).restrict h) ≫
      (Scheme.Modules.pushforward (h ≫ g)).map
        ((Scheme.Modules.restrictFunctorComp h g).inv.app M)

private theorem presheaf_restriction_chain {X : Scheme.{u}} (M : X.Modules)
    {A B C D : X.Opens} (a : B ⟶ A) (b : C ⟶ B) (e : D = C) (d : D ⟶ A) :
    M.presheaf.map a.op ≫ M.presheaf.map b.op ≫ M.presheaf.map (eqToHom e).op =
      M.presheaf.map d.op := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact M.presheaf.congr_map (Subsingleton.elim _ _)

private theorem restrictionCompositeUnit_apply {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ Y) [IsOpenImmersion g] [IsOpenImmersion h]
    (M : X.Modules) (U : X.Opens) (s : Γ(M,U)) :
    (restrictionCompositeUnit g h M).app U s =
      ((Scheme.Modules.restrictAdjunction (h ≫ g)).unit.app M).app U s := by
  dsimp only [restrictionCompositeUnit]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app, Scheme.Modules.restrict_map]
  have hpre : (h ≫ g) ⁻¹ᵁ U = h ⁻¹ᵁ (g ⁻¹ᵁ U) := Scheme.Hom.comp_preimage h g U
  have hcut : (h ≫ g) ''ᵁ ((h ≫ g) ⁻¹ᵁ U) =
      g ''ᵁ (h ''ᵁ (h ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    (Scheme.Hom.comp_image h g _).trans
      (congrArg (fun W : Z.Opens => g ''ᵁ (h ''ᵁ W)) hpre)
  have hm := presheaf_restriction_chain M
    (homOfLE (g.image_preimage_le U))
    ((Scheme.Hom.opensFunctor g).map (homOfLE (h.image_preimage_le (g ⁻¹ᵁ U))))
    hcut (homOfLE ((h ≫ g).image_preimage_le U))
  exact ConcreteCategory.congr_hom hm s

private theorem restriction_unit_comp {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ Y) [IsOpenImmersion g] [IsOpenImmersion h]
    (M : X.Modules) :
    (Scheme.Modules.restrictAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.restrictAdjunction h).unit.app (M.restrict g)) ≫
      (Scheme.Modules.pushforwardComp h g).hom.app ((M.restrict g).restrict h) ≫
      (Scheme.Modules.pushforward (h ≫ g)).map
        ((Scheme.Modules.restrictFunctorComp h g).inv.app M) =
    (Scheme.Modules.restrictAdjunction (h ≫ g)).unit.app M := by
  change restrictionCompositeUnit g h M = _
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  exact restrictionCompositeUnit_apply g h M U s

private theorem mate_of_unit_comparison {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (A : L₁ ⊣ R₁) (B : L₂ ⊣ R₂)
    (e : L₂ ≅ L₁) (q : R₁ ≅ R₂) (M : C) (N : D)
    (hu : A.unit.app M ≫ q.hom.app (L₁.obj M) = B.unit.app M ≫ R₂.map (e.hom.app M))
    (z : L₁.obj M ⟶ N) :
    B.homEquiv M N (e.hom.app M ≫ z) = A.homEquiv M N z ≫ q.hom.app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, ← hu, Category.assoc, ← q.hom.naturality z, ← Category.assoc]

private theorem restriction_comp_mate {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ Y) [IsOpenImmersion g] [IsOpenImmersion h]
    (M : X.Modules) (N : Z.Modules) (z : (M.restrict g).restrict h ⟶ N) :
    (Scheme.Modules.restrictAdjunction (h ≫ g)).homEquiv M N
      ((Scheme.Modules.restrictFunctorComp h g).hom.app M ≫ z) =
    (Scheme.Modules.restrictAdjunction g).homEquiv M
      ((Scheme.Modules.pushforward h).obj N)
      ((Scheme.Modules.restrictAdjunction h).homEquiv (M.restrict g) N z) ≫
      (Scheme.Modules.pushforwardComp h g).hom.app N := by
  let A := Scheme.Modules.restrictAdjunction g
  let B := Scheme.Modules.restrictAdjunction h
  let D := Scheme.Modules.restrictAdjunction (h ≫ g)
  let E := Scheme.Modules.restrictFunctorComp h g
  let P := Scheme.Modules.pushforwardComp h g
  have hu : ((A.comp B).unit.app M ≫ P.hom.app ((M.restrict g).restrict h)) ≫
      (Scheme.Modules.pushforward (h ≫ g)).map (E.inv.app M) = D.unit.app M :=
    restriction_unit_comp g h M
  have hu' : (A.comp B).unit.app M ≫ P.hom.app ((M.restrict g).restrict h) =
      D.unit.app M ≫ (Scheme.Modules.pushforward (h ≫ g)).map (E.hom.app M) :=
    (Iso.comp_inv_eq ((Scheme.Modules.pushforward (h ≫ g)).mapIso (E.app M))).mp hu
  exact mate_of_unit_comparison (A.comp B) D E P M N hu' z

end EnvelopeProperty.DeligneIllusie.DeligneIllusieWittGlobalDescent
