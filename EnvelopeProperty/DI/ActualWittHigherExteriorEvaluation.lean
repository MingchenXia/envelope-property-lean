import EnvelopeProperty.DI.ActualWittHigherExteriorMaps
import EnvelopeProperty.DI.ActualWittHigherExteriorUnits
import EnvelopeProperty.DI.CechTotalCupEvaluation

/-! # Actual higher Witt maps retain the SAME whole original exterior values

The actual canonical degree-one map and honest total cup are evaluated on each
original affine member. The actual ordered-product induction, published
normalization recovery in degree < p, and ORIGINAL exterior-unit spanning prove
the entire original section-map equality. No leading/class/QI certificate is an
input. The induced sheaf-class and final derived assembly are separate consumers.
-/

noncomputable section
namespace EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Cartier DeligneIllusie
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p κ)))
  (n : ℕ) [SmoothOfRelativeDimension n f]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
  WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra

private abbrev X := WittTwoSpecialFibreOpens.specialFibre p κ f
private abbrev f₀ : X p κ f ⟶ Spec (.of κ) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p κ))) f
private abbrev U₀ (U : Xtilde.Opens) := WittTwoSpecialFibreOpens.residueOpen p κ f U
private abbrev Y := SchemeRelativeFrobenius.twist p (f₀ p κ f)
private abbrev g : Y p κ f ⟶ Spec (.of κ) :=
  pullback.snd (f₀ p κ f) (SchemeRelativeFrobenius.baseMap (k := κ) p)
private abbrev W (U : Xtilde.Opens) :=
  RelativeTwistedAffineBasis.twistedOpen (f₀ p κ f) p (U₀ p κ f U)
private abbrev fibreSections (U : Xtilde.Opens) : CommRingCat :=
  (X p κ f).presheaf.obj (op (U₀ p κ f U))

section CoverMembers
variable [IsSeparated f]

/-- The original exterior map made with this SAME internally selected cover lift. -/
def memberExterior (i : ActualWittCechOneMap.CoverIndex p κ f n) (q : ℕ) :
    (CanonicalGeometry.exteriorCotangentSheaf (g p κ f) q).val.obj
        (op (ActualWittCechOneMap.cover p κ f n i)) ⟶
      (SchemeRelativeFrobeniusDeRham.formModule (f₀ p κ f) p q).val.obj
        (op (ActualWittCechOneMap.cover p κ f n i)) :=
  ActualWittExteriorCartier.exteriorSections p κ f n i.property.1
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
    (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i) q

omit [PerfectRing κ p] [SmoothOfRelativeDimension n f] [IsSeparated f] in
private theorem memberAffine (i : ActualWittCechOneMap.CoverIndex p κ f n) :
    IsAffineOpen (ActualWittCechOneMap.cover p κ f n i) :=
  RelativeTwistedAffineBasis.twistedOpen_isAffine (f₀ p κ f) p
    (U₀ p κ f i.val) (WittTwoSpecialFibreOpens.residueOpen_affine p κ f i.property.1)

/-- The ENTIRE evaluated actual degree-one component equals the original affine
exterior map from the SAME selected lift. -/
theorem memberOne (i : ActualWittCechOneMap.CoverIndex p κ f n) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    (CechTotalCup.memberEvaluation (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n) 1 i).comp
      ((ActualWittHigherExteriorMaps.higherMap p κ f n 0).val.app
        (op (ActualWittCechOneMap.cover p κ f n i))).hom =
      (memberExterior p κ f n i 1).hom := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  have heval := ActualWittHigherExteriorMaps.higherMap_zero_localEvaluation p κ f n i
  have hread := CechTotalCup.memberEvaluation_sectionReadback (f₀ p κ f) p n
    (ActualWittCechOneMap.cover p κ f n) 1 i (memberAffine p κ f n i)
    (ActualWittCechOneMap.sourceModule p κ f) (ActualWittHigherExteriorMaps.higherMap p κ f n 0)
  have hc := congrArg (fun ψ => (AffineLocalMapRestriction.sectionReadback
    (memberAffine p κ f n i) (ActualWittCechOneMap.sourceModule p κ f)
    ((ActualWittCechOneMap.targetComplex p κ f n).X 1) ψ).hom) heval
  have hr := ActualWittGeometricXiHomotopy.xiSheafMap_sections p κ f n i.property.1
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
    (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i)
  have he := ActualWittExteriorCartier.exteriorSections_one_eq_xiSectionMap p κ f n i.property.1
    (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
    (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
    (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i)
  exact hread.trans (hc.trans (congrArg ModuleCat.Hom.hom (hr.trans he.symm)))

private theorem memberRawOne (i : ActualWittCechOneMap.CoverIndex p κ f n)
    (m : (CanonicalGeometry.cotangentPresheaf (g p κ f)).obj
      (op (ActualWittCechOneMap.cover p κ f n i))) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    CechTotalCup.memberEvaluation (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n) 1 i
      (CechHigherExteriorMaps.rawOne (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n)
        (ActualWittCechOneMap.canonicalLocalData p κ f n)
        (ActualWittCechOneMap.cover p κ f n i) m) =
      (memberExterior p κ f n i 1).hom
        (CanonicalGeometry.exteriorSheafSection (CanonicalGeometry.cotangentPresheaf (g p κ f))
          1 (ActualWittCechOneMap.cover p κ f n i) (fun _ => m)) := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  let Wi := ActualWittCechOneMap.cover p κ f n i
  let η := CanonicalGeometry.exteriorSheafSection (CanonicalGeometry.cotangentPresheaf (g p κ f))
    1 Wi (fun _ => m)
  have hzero : ActualWittHigherExteriorMaps.higherMap p κ f n 0 =
      CechHigherExteriorMaps.oneComponent (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n)
        (ActualWittCechOneMap.canonicalLocalData p κ f n) :=
    CechHigherExteriorMaps.higherMap_zero (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n)
      (ActualWittCechOneMap.canonicalLocalData p κ f n)
  have hη := congrArg (fun φ : ActualWittCechOneMap.sourceModule p κ f ⟶
      (DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex
        (ActualWittCechOneMap.cover p κ f n) (ActualWittCechOneMap.targetComplex p κ f n)).X 1 =>
      φ.val.app (op Wi) η) hzero.symm
  exact (congrArg
    (CechTotalCup.memberEvaluation (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n) 1 i) hη).trans
      (LinearMap.congr_fun (memberOne p κ f n i) η)


/-- The actual whole ordered expression evaluates to the SAME actual exterior map
on every ORIGINAL raw source tuple, without any factorial or degree bound. -/
theorem memberOrdered (i : ActualWittCechOneMap.CoverIndex p κ f n) (r : ℕ) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    ∀ m : Fin (r+1) → (CanonicalGeometry.cotangentPresheaf (g p κ f)).obj
      (op (ActualWittCechOneMap.cover p κ f n i)),
    CechTotalCup.memberEvaluation (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n) (r+1) i
      (CechHigherExteriorMaps.orderedPower (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n)
        (ActualWittCechOneMap.canonicalLocalData p κ f n) r
        (ActualWittCechOneMap.cover p κ f n i) m) =
      (memberExterior p κ f n i (r+1)).hom
        (CanonicalGeometry.exteriorSheafSection (CanonicalGeometry.cotangentPresheaf (g p κ f))
          (r+1) (ActualWittCechOneMap.cover p κ f n i) m) := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  induction r with
  | zero =>
    intro m
    have he := memberRawOne p κ f n i (m 0)
    have hm : (fun _ : Fin 1 => m 0) = m := by
      funext j
      exact congrArg m (Subsingleton.elim (0 : Fin 1) j)
    simpa only [CechHigherExteriorMaps.orderedPower_zero, hm] using he
  | succ r ih =>
    intro m
    rw [CechHigherExteriorMaps.orderedPower_succ]
    have he := CechTotalCup.memberEvaluation_totalCupSection (f₀ p κ f) p n
      (ActualWittCechOneMap.cover p κ f n) (r+1) 1 i
      (CechHigherExteriorMaps.orderedPower (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n)
        (ActualWittCechOneMap.canonicalLocalData p κ f n) r
        (ActualWittCechOneMap.cover p κ f n i) (Fin.init m))
      (CechHigherExteriorMaps.rawOne (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n)
        (ActualWittCechOneMap.canonicalLocalData p κ f n)
        (ActualWittCechOneMap.cover p κ f n i) (m (Fin.last (r+1))))
    have hp := model_rawUnit_product p κ f n i.property.1
      (DeligneIllusieWittGlobalDescent.coordinates p κ f n i)
      (DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i)
      (DeligneIllusieWittGlobalDescent.coverLift p κ f n i)
      (DeligneIllusieWittGlobalDescent.coverLift_reduction p κ f n i) (r+1) m
    exact he.trans ((congrArg
      (CechWholeSectionLeibniz.degreeCast (f₀ p κ f) p (Nat.add_comm 1 (r+1))
        (ActualWittCechOneMap.cover p κ f n i))
      (congrArg₂ (fun
        (x : Γ(SchemeRelativeFrobeniusDeRham.formModule (f₀ p κ f) p (r+1),
          ActualWittCechOneMap.cover p κ f n i))
        (y : Γ(SchemeRelativeFrobeniusDeRham.formModule (f₀ p κ f) p 1,
          ActualWittCechOneMap.cover p κ f n i)) =>
        DeligneIllusieCechCupProduct.formWedge (f₀ p κ f) p (r+1) 1
          (ActualWittCechOneMap.cover p κ f n i) x y)
        (ih (Fin.init m)) (memberRawOne p κ f n i (m (Fin.last (r+1)))))).trans hp.symm)

/-- The ACTUAL normalization retains the SAME local exterior representative
on every ORIGINAL raw wedge when r+1<p. -/
theorem memberHigher_raw (i : ActualWittCechOneMap.CoverIndex p κ f n)
    (r : ℕ) (hr : r+1<p)
    (m : Fin (r+1) → (CanonicalGeometry.cotangentPresheaf (g p κ f)).obj
      (op (ActualWittCechOneMap.cover p κ f n i))) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    CechTotalCup.memberEvaluation (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n) (r+1) i
      ((ActualWittHigherExteriorMaps.higherMap p κ f n r).val.app
        (op (ActualWittCechOneMap.cover p κ f n i))
        (CanonicalGeometry.exteriorSheafSection (CanonicalGeometry.cotangentPresheaf (g p κ f))
          (r+1) (ActualWittCechOneMap.cover p κ f n i) m)) =
      (memberExterior p κ f n i (r+1)).hom
        (CanonicalGeometry.exteriorSheafSection (CanonicalGeometry.cotangentPresheaf (g p κ f))
          (r+1) (ActualWittCechOneMap.cover p κ f n i) m) := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  let Wi := ActualWittCechOneMap.cover p κ f n i
  let μ := CechHigherExteriorMaps.orderedPower (f₀ p κ f) p n (ActualWittCechOneMap.cover p κ f n)
    (ActualWittCechOneMap.canonicalLocalData p κ f n) r Wi
  let ε := CechTotalCup.memberEvaluation (f₀ p κ f) p n
    (ActualWittCechOneMap.cover p κ f n) (r+1) i
  let a := (memberExterior p κ f n i (r+1)).hom.compAlternatingMap
    (CanonicalGeometry.exteriorSheafSection (CanonicalGeometry.cotangentPresheaf (g p κ f))
      (r+1) Wi)
  have hμ : ε.compMultilinearMap μ = a.toMultilinearMap := by
    ext z
    exact memberOrdered p κ f n i r z
  have hrec := DeligneIllusieAlternatingNormalization.normalizedAlternatization_recovery
    (CechHigherExteriorMaps.constantMap (f₀ p κ f) p Wi) (r+1) p hr ε μ a hμ
  have he := congrArg (fun z => z m) hrec
  exact (congrArg ε (ActualWittHigherExteriorMaps.higherMap_unit p κ f n r Wi m)).trans he

/-- ENTIRE original affine section map, obtained by ORIGINAL unit spanning. -/
theorem memberHigher (i : ActualWittCechOneMap.CoverIndex p κ f n)
    (r : ℕ) (hr : r+1<p) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    (CechTotalCup.memberEvaluation (f₀ p κ f) p n
      (ActualWittCechOneMap.cover p κ f n) (r+1) i).comp
      ((ActualWittHigherExteriorMaps.higherMap p κ f n r).val.app
        (op (ActualWittCechOneMap.cover p κ f n i))).hom =
      (memberExterior p κ f n i (r+1)).hom := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  let Wi := ActualWittCechOneMap.cover p κ f n i
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p κ f i.property.1
  let v := DeligneIllusieWittGlobalDescent.coordinates p κ f n i
  let hv := DeligneIllusieWittGlobalDescent.coordinates_etale p κ f n i
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f i.val)
  let u := GeometricLocalCartier.twistedUnitIso (f₀ p κ f) p hU₀ n v hv (r+1)
  let L := (CechTotalCup.memberEvaluation (f₀ p κ f) p n
      (ActualWittCechOneMap.cover p κ f n) (r+1) i).comp
      ((ActualWittHigherExteriorMaps.higherMap p κ f n r).val.app (op Wi)).hom
  let C := (memberExterior p κ f n i (r+1)).hom
  have hu : L.comp u.hom.hom = C.comp u.hom.hom := by
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (exteriorPower.ιMulti_span Γ(Y p κ f,Wi) (r+1)
        (CommRingCat.KaehlerDifferential
          (RelativeTwistedAffineSections.coefficientSectionMap (f₀ p κ f) p (U₀ p κ f i.val))))]
    rintro ⟨_, ⟨m, rfl⟩⟩
    exact memberHigher_raw p κ f n i r hr m
  apply LinearMap.ext
  intro x
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso u.hom).2 x
  exact (congrArg L hz.symm).trans ((LinearMap.congr_fun hu z).trans (congrArg C hz))

end CoverMembers

end EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation
