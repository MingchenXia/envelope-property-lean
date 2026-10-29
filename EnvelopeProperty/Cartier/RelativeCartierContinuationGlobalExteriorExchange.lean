import EnvelopeProperty.Cartier.RelativeCartierContinuationGlobalCotangentExchange

/-! # Actual all-degree exterior and original source-restricted twist evaluation

The actual inverse is derived from the same genuine cotangent maps and the
universal alternating range. No exterior or Cartier comparison is supplied.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeGlobalExteriorExchange
open AlgebraicGeometry CategoryTheory Opposite
universe u
section RingIso
variable {R A B : CommRingCat.{u}} (a : R ⟶ A) (b : R ⟶ B)
variable (e : A ≅ B) (h : a ≫ e.hom = b)
local notation "KA" => CommRingCat.KaehlerDifferential a
local notation "KB" => CommRingCat.KaehlerDifferential b

/-- The SAME actual universal cotangent map, regarded as its actual semilinear map. -/
def cotangentSemilinear : KA →ₛₗ[e.hom.hom] KB :=
  (ModuleCat.semilinearMapAddEquiv e.hom.hom KA KB).symm
    (RelativeGlobalCotangentExchange.cotangentMap a b e h)

/-- The actual all-degree exterior map of the SAME genuine universal cotangent map. -/
def exteriorMap (q : ℕ) : ModuleCat.of A (⋀[A]^q KA) ⟶
    (ModuleCat.restrictScalars e.hom.hom).obj (ModuleCat.of B (⋀[B]^q KB)) :=
  ModuleCat.semilinearMapAddEquiv e.hom.hom
    (ModuleCat.of A (⋀[A]^q KA)) (ModuleCat.of B (⋀[B]^q KB))
    (CanonicalGeometry.exteriorSemilinearMap e.hom.hom (cotangentSemilinear a b e h) q)

/-- Every entire original pure wedge has the wedge of the SAME actual cotangent images. -/
theorem exteriorMap_wedge (q : ℕ) (m : Fin q → KA) :
    exteriorMap a b e h q (exteriorPower.ιMulti A q (M := KA) m) =
      exteriorPower.ιMulti B q (M := KB)
        (fun i => cotangentSemilinear a b e h (m i)) := by
  change CanonicalGeometry.exteriorSemilinearMap e.hom.hom
    (cotangentSemilinear a b e h) q (exteriorPower.ιMulti A q (M := KA) m) = _
  rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti]
  rfl

private def undoLinear (q : ℕ) : ModuleCat.of A (⋀[A]^q KA) ⟶ ModuleCat.of A (⋀[A]^q KA) :=
  exteriorMap a b e h q ≫
    (ModuleCat.restrictScalars e.hom.hom).map
      (exteriorMap b a e.symm (RelativeGlobalCotangentExchange.inverseCoefficientSquare a b e h) q) ≫
    (ModuleCat.restrictScalarsComp' e.hom.hom e.inv.hom (RingHom.id A)
      (congrArg CommRingCat.Hom.hom e.hom_inv_id).symm).inv.app (ModuleCat.of A (⋀[A]^q KA)) ≫
    (ModuleCat.restrictScalarsId' (RingHom.id A) rfl).hom.app (ModuleCat.of A (⋀[A]^q KA))

/-- The true ring inverse gives an actual inverse on EVERY exterior form, in ALL degrees,
by the internally proved cotangent inverse and the universal alternating spanning range. -/
theorem exteriorMap_leftInverse (q : ℕ) : Function.LeftInverse
    (exteriorMap b a e.symm (RelativeGlobalCotangentExchange.inverseCoefficientSquare a b e h) q)
    (exteriorMap a b e h q) := by
  have hi : undoLinear a b e h q = 𝟙 (ModuleCat.of A (⋀[A]^q KA)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_on_range (exteriorPower.ιMulti_span A q KA)
    intro m
    change exteriorMap b a e.symm (RelativeGlobalCotangentExchange.inverseCoefficientSquare a b e h) q
      (exteriorMap a b e h q (exteriorPower.ιMulti A q (M := KA) m)) = exteriorPower.ιMulti A q (M := KA) m
    rw [exteriorMap_wedge, exteriorMap_wedge]
    congr 1
    funext i
    exact RelativeGlobalCotangentExchange.cotangentMap_leftInverse a b e h (m i)
  intro x
  exact congrArg (fun f : ModuleCat.of A (⋀[A]^q KA) ⟶ ModuleCat.of A (⋀[A]^q KA) => f x) hi

/-- Genuine bijectivity of the SAME actual exterior map, including degree zero. -/
theorem exteriorMap_bijective (q : ℕ) : Function.Bijective (exteriorMap a b e h q) := by
  have hl := exteriorMap_leftInverse a b e h q
  have hr := exteriorMap_leftInverse b a e.symm
    (RelativeGlobalCotangentExchange.inverseCoefficientSquare a b e h) q
  exact ⟨hl.injective, hr.surjective⟩

/-- Actual module equivalence in every exterior degree, with no basis or chart input. -/
def exteriorIso (q : ℕ) : ModuleCat.of A (⋀[A]^q KA) ≅
    (ModuleCat.restrictScalars e.hom.hom).obj (ModuleCat.of B (⋀[B]^q KB)) :=
  (LinearEquiv.ofBijective (exteriorMap a b e h q).hom (exteriorMap_bijective a b e h q)).toModuleIso

/-- The whole pure-wedge formula of the actual exterior equivalence. -/
theorem exteriorIso_wedge (q : ℕ) (m : Fin q → KA) :
    (exteriorIso a b e h q).hom (exteriorPower.ιMulti A q (M := KA) m) =
      exteriorPower.ιMulti B q (M := KB)
        (fun i => cotangentSemilinear a b e h (m i)) :=
  exteriorMap_wedge a b e h q m
end RingIso

section Global
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "TG" => RelativeGlobalCartierDomain.twistPresheaf f p
local notation "CG" => RelativeGlobalCartierDomain.coefficientMap f p
local notation "SG" => RelativeGlobalCartierDomain.sourceMap f p
local notation "E" => RelativeGlobalCartierDomain.evaluationIso f p
local notation "TN" U => RelativeFrobenius.twist (A := k)
  (CommRingCat.Hom.hom (NatTrans.app (CanonicalGeometry.schemeConstantPresheafMap f) U)) p
local notation "CN" U => RelativeFrobenius.coefficientMap (A := k)
  (CommRingCat.Hom.hom (NatTrans.app (CanonicalGeometry.schemeConstantPresheafMap f) U)) p
local notation "SN" U => RelativeFrobenius.sourceMap (A := k)
  (CommRingCat.Hom.hom (NatTrans.app (CanonicalGeometry.schemeConstantPresheafMap f) U)) p
local notation "KN" U => CommRingCat.KaehlerDifferential (CN U)

/-- Every evaluated actual exterior presheaf is the SAME native twist exterior module. -/
def evaluationExteriorIso (U : X.Opensᵒᵖ) (q : ℕ) :
    (RelativeGlobalCartierDomain.exteriorPresheaf f p q).obj U ≅
      (ModuleCat.restrictScalars (E U).hom.hom).obj (ModuleCat.of (TN U) (⋀[TN U]^q (KN U))) :=
  exteriorIso ((CG).app U) (CN U) (E U)
    (RelativeGlobalCartierDomain.coefficientMap_evaluationIso f p U) q

/-- The actual evaluation exterior comparison on EVERY pure wedge, including the empty one. -/
theorem evaluationExteriorIso_wedge (U : X.Opensᵒᵖ) (q : ℕ)
    (m : Fin q → (RelativeGlobalCartierDomain.cotangentPresheaf f p).obj U) :
    (evaluationExteriorIso f p U q).hom (exteriorPower.ιMulti ((TG).obj U) q m) =
      exteriorPower.ιMulti (TN U) q (M := KN U)
        (fun i => cotangentSemilinear ((CG).app U) (CN U) (E U)
          (RelativeGlobalCartierDomain.coefficientMap_evaluationIso f p U) (m i)) :=
  exteriorIso_wedge ((CG).app U) (CN U) (E U)
    (RelativeGlobalCartierDomain.coefficientMap_evaluationIso f p U) q m

/-- The PROVED original source-evaluation square gives the genuine entire scalar-functor
comparison, with no comparison certificate supplied. -/
def sourceScalarComparison (U : X.Opensᵒᵖ) :
    ModuleCat.restrictScalars (E U).hom.hom ⋙ ModuleCat.restrictScalars ((SG).app U).hom ≅
      ModuleCat.restrictScalars (SN U).hom :=
  (ModuleCat.restrictScalarsComp' ((SG).app U).hom (E U).hom.hom (SN U).hom
    (congrArg CommRingCat.Hom.hom (RelativeGlobalCartierDomain.sourceMap_evaluationIso f p U)).symm).symm

/-- The CORRECT original source-restricted global domain PRESHEAF evaluates to the SAME
native local source, in every degree and on every open, including zero section rings. -/
def domainEvaluationIso (U : X.Opensᵒᵖ) (q : ℕ) :
    (RelativeGlobalCartierDomain.domainPresheaf f p q).obj U ≅
      (ModuleCat.restrictScalars (SN U).hom).obj (ModuleCat.of (TN U) (⋀[TN U]^q (KN U))) :=
  (ModuleCat.restrictScalars ((SG).app U).hom).mapIso (evaluationExteriorIso f p U q) ≪≫
    (sourceScalarComparison f p U).app (ModuleCat.of (TN U) (⋀[TN U]^q (KN U)))

/-- EVERY original source-function wedge retains its SAME native source-inclusion
cotangent wedge under the actual corrected pointwise domain comparison, in all degrees. -/
theorem domainEvaluationIso_sourceWedge (U : X.Opensᵒᵖ) (q : ℕ) (t : Fin q → X.presheaf.obj U) :
    (ModuleCat.Hom.hom (R := X.presheaf.obj U) (domainEvaluationIso f p U q).hom)
      (exteriorPower.ιMulti ((TG).obj U) q
        (fun i => CommRingCat.KaehlerDifferential.d (((SG).app U) (t i)))) =
      exteriorPower.ιMulti (TN U) q (M := KN U)
        (fun i => CommRingCat.KaehlerDifferential.d ((SN U) (t i))) := by
  change (evaluationExteriorIso f p U q).hom
    (exteriorPower.ιMulti ((TG).obj U) q
      (fun i => CommRingCat.KaehlerDifferential.d (((SG).app U) (t i)))) = _
  erw [evaluationExteriorIso_wedge]
  congr 1
  funext i
  change RelativeGlobalCotangentExchange.cotangentMap ((CG).app U) (CN U) (E U)
    (RelativeGlobalCartierDomain.coefficientMap_evaluationIso f p U)
      (CommRingCat.KaehlerDifferential.d (((SG).app U) (t i))) = _
  erw [RelativeGlobalCotangentExchange.cotangentMap_D]
  exact congrArg CommRingCat.KaehlerDifferential.d
    (congrArg (fun g : X.presheaf.obj U ⟶ TN U => g (t i))
      (RelativeGlobalCartierDomain.sourceMap_evaluationIso f p U))
end Global
end EnvelopeProperty.Cartier.RelativeGlobalExteriorExchange
