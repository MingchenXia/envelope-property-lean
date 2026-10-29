import EnvelopeProperty.AlgGeom.SchemeModuleTensorFrames
import EnvelopeProperty.AlgGeom.SchemeModuleFrameGluing
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist

/-! # True tensor addition of the original projective twists -/
open CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveTwistTensorAddition
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem coordinateCover :
    ∀ x : Proj (homogeneousSubmodule σ R), ∃ i : σ, x ∈ coordinateOpen (R := R) i := by
  intro x
  have hx : x ∈ ⨆ i : σ, coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

private theorem commonTransitions_congr {X : Scheme.{u}} (M N : X.Modules)
    {U V W W' : X.Opens} (hW : W = W')
    (hU : W ≤ U) (hV : W ≤ V) (hU' : W' ≤ U) (hV' : W' ≤ V)
    (eU : M.restrict U.ι ≅ unitObj U.toScheme)
    (eV : M.restrict V.ι ≅ unitObj V.toScheme)
    (gU : N.restrict U.ι ≅ unitObj U.toScheme)
    (gV : N.restrict V.ι ≅ unitObj V.toScheme)
    (htrans : ∃ c : unitObj W.toScheme ⟶ unitObj W.toScheme,
      (restrictOpenTrivialization hU eU).hom = (restrictOpenTrivialization hV eV).hom ≫ c ∧
      (restrictOpenTrivialization hU gU).hom = (restrictOpenTrivialization hV gV).hom ≫ c) :
    ∃ c : unitObj W'.toScheme ⟶ unitObj W'.toScheme,
      (restrictOpenTrivialization hU' eU).hom = (restrictOpenTrivialization hV' eV).hom ≫ c ∧
      (restrictOpenTrivialization hU' gU).hom = (restrictOpenTrivialization hV' gV).hom ≫ c := by
  subst W'
  exact htrans

private theorem tensorFrame_transition {X : Scheme.{u}} (M N : X.Modules)
    {U V W : X.Opens} (hU : W ≤ U) (hV : W ≤ V)
    (eU : M.restrict U.ι ≅ unitObj U.toScheme)
    (eV : M.restrict V.ι ≅ unitObj V.toScheme)
    (gU : N.restrict U.ι ≅ unitObj U.toScheme)
    (gV : N.restrict V.ι ≅ unitObj V.toScheme)
    (r s t : Γ(W.toScheme, (⊤ : W.toScheme.Opens))) (hp : r*s=t)
    (he : (restrictOpenTrivialization hU eU).hom =
      (restrictOpenTrivialization hV eV).hom ≫ ModularCurves.unitEndomorphismOfTopSection r)
    (hg : (restrictOpenTrivialization hU gU).hom =
      (restrictOpenTrivialization hV gV).hom ≫ ModularCurves.unitEndomorphismOfTopSection s) :
    (restrictOpenTrivialization hU (SchemeModuleTensorFrames.tensorFrame M N U eU gU)).hom =
      (restrictOpenTrivialization hV (SchemeModuleTensorFrames.tensorFrame M N V eV gV)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection t := by
  have hleft := congrArg Iso.hom (SchemeModuleTensorFrames.tensorFrame_restrict M N hU eU gU)
  have hright := congrArg Iso.hom (SchemeModuleTensorFrames.tensorFrame_restrict M N hV eV gV)
  have ht := SchemeModuleTensorFrames.tensorFrame_hom_eq_comp_scalars M N W
    _ _ _ _ r s he hg
  have hs := congrArg (fun z =>
    (SchemeModuleTensorFrames.tensorFrame M N W
      (restrictOpenTrivialization hV eV) (restrictOpenTrivialization hV gV)).hom ≫
      ModularCurves.unitEndomorphismOfTopSection z) hp
  have hr := congrArg (fun f => f ≫ ModularCurves.unitEndomorphismOfTopSection t) hright.symm
  exact hleft.trans (ht.trans (hs.trans hr))

private def glueTensorCompatible {X : Scheme.{u}} (M N P : X.Modules)
    {ι : Type*} (U : ι → X.Opens) (hc : ∀ x : X, ∃ i, x ∈ U i)
    (W : ι → ι → X.Opens) (hW : ∀ i h, W i h = U i ⊓ U h)
    (hleft : ∀ i h, W i h ≤ U i) (hright : ∀ i h, W i h ≤ U h)
    (e : ∀ i, M.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (p : ∀ i, P.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (ht : ∀ i h, ∃ r s t : Γ((W i h).toScheme, (⊤ : (W i h).toScheme.Opens)),
      r*s=t ∧
      (restrictOpenTrivialization (hleft i h) (e i)).hom =
        (restrictOpenTrivialization (hright i h) (e h)).hom ≫
          ModularCurves.unitEndomorphismOfTopSection r ∧
      (restrictOpenTrivialization (hleft i h) (g i)).hom =
        (restrictOpenTrivialization (hright i h) (g h)).hom ≫
          ModularCurves.unitEndomorphismOfTopSection s ∧
      (restrictOpenTrivialization (hleft i h) (p i)).hom =
        (restrictOpenTrivialization (hright i h) (p h)).hom ≫
          ModularCurves.unitEndomorphismOfTopSection t) : M ⊗ N ≅ P := by
  apply SchemeModuleFrameGluing.glueOfFrames _ _ U hc
    (fun i => SchemeModuleTensorFrames.tensorFrame M N (U i) (e i) (g i)) p
  intro i h
  obtain ⟨r,s,t,hm,he,hg,hp⟩ := ht i h
  exact commonTransitions_congr (M ⊗ N) P (hW i h) (hleft i h) (hright i h)
    inf_le_left inf_le_right
    (SchemeModuleTensorFrames.tensorFrame M N (U i) (e i) (g i))
    (SchemeModuleTensorFrames.tensorFrame M N (U h) (e h) (g h))
    (p i) (p h)
    ⟨ModularCurves.unitEndomorphismOfTopSection t,
      tensorFrame_transition M N (hleft i h) (hright i h)
        (e i) (e h) (g i) (g h) r s t hm he hg, hp⟩

private theorem glueTensorCompatible_restrict {X : Scheme.{u}} (M N P : X.Modules)
    {ι : Type*} (U : ι → X.Opens) (hc : ∀ x : X, ∃ i, x ∈ U i)
    (W : ι → ι → X.Opens) (hW : ∀ i h, W i h = U i ⊓ U h)
    (hleft : ∀ i h, W i h ≤ U i) (hright : ∀ i h, W i h ≤ U h)
    (e : ∀ i, M.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (p : ∀ i, P.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (ht : ∀ i h, ∃ r s t : Γ((W i h).toScheme, (⊤ : (W i h).toScheme.Opens)),
      r*s=t ∧
      (restrictOpenTrivialization (hleft i h) (e i)).hom =
        (restrictOpenTrivialization (hright i h) (e h)).hom ≫
          ModularCurves.unitEndomorphismOfTopSection r ∧
      (restrictOpenTrivialization (hleft i h) (g i)).hom =
        (restrictOpenTrivialization (hright i h) (g h)).hom ≫
          ModularCurves.unitEndomorphismOfTopSection s ∧
      (restrictOpenTrivialization (hleft i h) (p i)).hom =
        (restrictOpenTrivialization (hright i h) (p h)).hom ≫
          ModularCurves.unitEndomorphismOfTopSection t) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).mapIso
        (glueTensorCompatible M N P U hc W hW hleft hright e g p ht) =
      SchemeModuleFrameGluing.frameComparison (M ⊗ N) P (U i)
        (SchemeModuleTensorFrames.tensorFrame M N (U i) (e i) (g i)) (p i) := by
  unfold glueTensorCompatible
  apply SchemeModuleFrameGluing.glueOfFrames_restrict

private theorem unit_zpow_mul {A : Type*} [CommRing A] (t : Aˣ) (a b : ℤ) :
    (↑(t^a) : A) * ↑(t^b) = ↑(t^(a+b)) := by
  rw [zpow_add, Units.val_mul]

private def tensorFrameComparison (j k l : σ) (a b : ℤ) (i : σ) :
    (coordinateHyperplaneTwist (R := R) j a ⊗ coordinateHyperplaneTwist (R := R) k b).over
        (coordinateOpen (R := R) i) ≅
      (coordinateHyperplaneTwist (R := R) l (a+b)).over (coordinateOpen (R := R) i) :=
  SchemeModuleFrameGluing.frameComparison _ _ (coordinateOpen (R := R) i)
    (SchemeModuleTensorFrames.tensorFrame _ _ (coordinateOpen (R := R) i)
      (coordinateHyperplaneTwistTrivialization (R := R) i j a)
      (coordinateHyperplaneTwistTrivialization (R := R) i k b))
    (coordinateHyperplaneTwistTrivialization (R := R) i l (a+b))

private theorem exists_tensorIso (j k l : σ) (a b : ℤ) :
    ∃ e : coordinateHyperplaneTwist (R := R) j a ⊗ coordinateHyperplaneTwist (R := R) k b ≅
      coordinateHyperplaneTwist (R := R) l (a+b), ∀ i : σ,
        (SheafOfModules.overFunctor (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (coordinateOpen (R := R) i)).mapIso e = tensorFrameComparison j k l a b i := by
  refine ⟨
  glueTensorCompatible _ _ _ (coordinateOpen (R := R)) coordinateCover
    (coordinateOpenOverlap (R := R))
    (coordinateOpenOverlap_eq (R := R))
    (coordinateOpenOverlap_le_left (R := R))
    (coordinateOpenOverlap_le_right (R := R))
    (fun i => coordinateHyperplaneTwistTrivialization (R := R) i j a)
    (fun i => coordinateHyperplaneTwistTrivialization (R := R) i k b)
    (fun i => coordinateHyperplaneTwistTrivialization (R := R) i l (a+b))
    (fun i h => ⟨↑(coordinateOpenTransitionTopUnit (R := R) i h ^ a),
      ↑(coordinateOpenTransitionTopUnit (R := R) i h ^ b),
      ↑(coordinateOpenTransitionTopUnit (R := R) i h ^ (a+b)),
      unit_zpow_mul (coordinateOpenTransitionTopUnit (R := R) i h) a b,
      coordinateHyperplaneTwistTrivialization_restrict_transition (R := R) i h j a,
      coordinateHyperplaneTwistTrivialization_restrict_transition (R := R) i h k b,
      coordinateHyperplaneTwistTrivialization_restrict_transition (R := R) i h l (a+b)⟩), ?_⟩
  intro i
  apply glueTensorCompatible_restrict

/-- The SAME original coordinate projective twists genuinely add under the
TRUE original tensor, deriving an actual whole isomorphism from the genuine
original standard-coordinate transitions without a comparison premise. -/
def tensorIso (j k l : σ) (a b : ℤ) :
    (coordinateHyperplaneTwist (R := R) j a) ⊗ (coordinateHyperplaneTwist (R := R) k b) ≅
      coordinateHyperplaneTwist (R := R) l (a+b) :=
  (exists_tensorIso (R := R) j k l a b).choose

/-- Tensor addition is the prescribed coefficient-preserving comparison on
every original standard coordinate chart. -/
theorem tensorIso_restrict (j k l : σ) (a b : ℤ) (i : σ) :
    (SheafOfModules.overFunctor (Proj (homogeneousSubmodule σ R)).ringCatSheaf
      (coordinateOpen (R := R) i)).mapIso (tensorIso j k l a b) =
      SchemeModuleFrameGluing.frameComparison
        (coordinateHyperplaneTwist (R := R) j a ⊗ coordinateHyperplaneTwist (R := R) k b)
        (coordinateHyperplaneTwist (R := R) l (a+b)) (coordinateOpen (R := R) i)
        (SchemeModuleTensorFrames.tensorFrame _ _ (coordinateOpen (R := R) i)
          (coordinateHyperplaneTwistTrivialization (R := R) i j a)
          (coordinateHyperplaneTwistTrivialization (R := R) i k b))
        (coordinateHyperplaneTwistTrivialization (R := R) i l (a+b)) := by
  exact (exists_tensorIso (R := R) j k l a b).choose_spec i

end EnvelopeProperty.ProjectiveTwistTensorAddition
