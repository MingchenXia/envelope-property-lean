import EnvelopeProperty.Global.FibreIdealPowerTransitions
import EnvelopeProperty.Global.FibreInfinitesimalH0Cech
import EnvelopeProperty.Global.FibreIdealPowerCechMaps
import EnvelopeProperty.InfinitesimalIdempotents
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Genuine infinitesimal sequence transitions and boundary naturality -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FibreInfinitesimalBoundaryTransitions

open InfinitesimalSchemes

private theorem compose_boundary_square {C : Type*} [Category C]
    {A B M N P Q : C} (a : A ⟶ M) (b : B ⟶ N) (v : A ⟶ B)
    (h : M ⟶ N) (c : M ⟶ P) (d : N ⟶ Q) (t : P ⟶ Q)
    (ha : a ≫ h = v ≫ b) (hc : c ≫ t = h ≫ d) :
    (a ≫ c) ≫ t = v ≫ (b ≫ d) := by
  rw [Category.assoc, hc, ← Category.assoc, ha, Category.assoc]

private theorem module_square_apply {A : Type*} [CommRing A]
    {S T P Q : ModuleCat A} (b : S ⟶ P) (c : T ⟶ Q)
    (v : S ⟶ T) (w : P ⟶ Q) (h : b ≫ w = v ≫ c)
    (s : S) (t : T) (ht : v.hom s = t) : w.hom (b.hom s) = c.hom t :=
  (congrArg (fun z => z.hom s) h).trans (congrArg c.hom ht)

private theorem module_transport_apply {A : Type*} [CommRing A]
    {M N P Q : ModuleCat A} (eM : M ⟶ P) (eN : N ⟶ Q)
    (i : M ⟶ N) (j : P ⟶ Q) (hi : i ≫ eN = eM ≫ j)
    (a : M) (b : N) (hab : i.hom a = b) : j.hom (eM.hom a) = eN.hom b :=
  (congrArg (fun z => z.hom a) hi).symm.trans (congrArg eN.hom hab)

private def unitTransition {A B C : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ C)
    (q : A ⟶ C) (h : g ≫ p = q) :
    (Scheme.Modules.pushforward p).obj (SheafOfModules.unit B.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward q).obj (SheafOfModules.unit A.ringCatSheaf) :=
  (Scheme.Modules.pushforward p).map
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp g p).hom.app (SheafOfModules.unit A.ringCatSheaf) ≫
    eqToHom (congrArg (fun t =>
      (Scheme.Modules.pushforward t).obj (SheafOfModules.unit A.ringCatSheaf)) h)

private theorem unitTransition_app {A B C : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ C)
    (q : A ⟶ C) (h : g ≫ p = q) (W : C.Opens)
    (hW : q ⁻¹ᵁ W ≤ g ⁻¹ᵁ (p ⁻¹ᵁ W)) (s : Γ(B, p ⁻¹ᵁ W)) :
    (show Γ(A, q ⁻¹ᵁ W) from (unitTransition g p q h).app W s) =
      g.appLE (p ⁻¹ᵁ W) (q ⁻¹ᵁ W) hW s := by
  subst q
  simp only [unitTransition, eqToHom_refl, Scheme.Modules.Hom.comp_app]
  change (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
    (op (p ⁻¹ᵁ W)) s = _
  have hu : (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
      (op (p ⁻¹ᵁ W)) s = g.app (p ⁻¹ᵁ W) s := rfl
  exact hu.trans (congrArg (fun t => t.hom s) (g.app_eq_appLE (U := p ⁻¹ᵁ W)))

private theorem unitSection_transition {A B C : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ C)
    (q : A ⟶ C) (h : g ≫ p = q) :
    SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫ unitTransition g p q h =
      SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom := by
  subst q
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

private theorem unitTransition_appTop {A B C : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ C)
    (q : A ⟶ C) (h : g ≫ p = q) (s : Γ(B, ⊤)) :
    (unitTransition g p q h).val.app (op ⊤) s = g.appTop s := by
  subst q
  rfl

private theorem unitTransition_baseSectionsMap {A B C S : Scheme.{u}}
    (g : A ⟶ B) (p : B ⟶ C) (q : A ⟶ C) (h : g ≫ p = q) (f : C ⟶ S)
    (s : Γ(B, ⊤)) :
    (baseSectionsMap f (unitTransition g p q h)).hom s = g.appTop s := by
  subst q
  rfl

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The ACTUAL original infinitesimal pushforward transition, obtained from
the literal original scheme transition and its genuine whole projection equality. -/
def quotientTransition {n m : ℕ} (h : n ≤ m) :
    (Scheme.Modules.pushforward (projection I f m)).obj
        (SheafOfModules.unit (model I f m).ringCatSheaf) ⟶
      (Scheme.Modules.pushforward (projection I f n)).obj
        (SheafOfModules.unit (model I f n).ringCatSheaf) :=
  unitTransition (transition I f h) (projection I f m) (projection I f n)
    (transition_projection I f h)

/-- On EVERY original open the WHOLE quotient-module transition is
precisely the literal original scheme pullback on the SAME inverse-image open. -/
theorem quotientTransition_app {n m : ℕ} (h : n ≤ m) (W : X.Opens)
    (s : Γ(model I f m, projection I f m ⁻¹ᵁ W)) :
    (show Γ(model I f n, projection I f n ⁻¹ᵁ W) from
      (quotientTransition I f h).app W s) =
      (transition I f h).appLE (projection I f m ⁻¹ᵁ W)
        (projection I f n ⁻¹ᵁ W) (FibreInfinitesimalSections.transition_preimage I f h W).symm.le s := by
  exact unitTransition_app (transition I f h) (projection I f m) (projection I f n)
    (transition_projection I f h) W
    (FibreInfinitesimalSections.transition_preimage I f h W).symm.le s

/-- The ENTIRE actual original structure-module projection square commutes
under the SAME genuine original infinitesimal transition. -/
theorem sectionMap_transition {n m : ℕ} (h : n ≤ m) :
    FibreInfinitesimalModules.sectionMap I f m ≫ quotientTransition I f h =
      FibreInfinitesimalModules.sectionMap I f n :=
  unitSection_transition (transition I f h) (projection I f m) (projection I f n)
    (transition_projection I f h)

/-- On whole original sections the actual pushforward transition is the
literal original infinitesimal scheme pullback. -/
theorem quotientTransition_appTop {n m : ℕ} (h : n ≤ m)
    (s : Γ(model I f m, ⊤)) :
    (quotientTransition I f h).val.app (op ⊤) s = (transition I f h).appTop s :=
  unitTransition_appTop (transition I f h) (projection I f m) (projection I f n)
    (transition_projection I f h) s

/-- The SAME literal original whole section transition is retained by the
actual base-linear global-sections functor. -/
theorem quotientTransition_baseSectionsMap {n m : ℕ} (h : n ≤ m)
    (s : Γ(model I f m, ⊤)) :
    (baseSectionsMap f (quotientTransition I f h)).hom s = (transition I f h).appTop s :=
  unitTransition_baseSectionsMap (transition I f h) (projection I f m) (projection I f n)
    (transition_projection I f h) f s

/-- The ACTUAL original whole ideal-power sequences form a genuine morphism
under every original infinitesimal transition. -/
def sequenceTransition {n m : ℕ} (h : n ≤ m) :
    FibreInfinitesimalModules.sequence I f m ⟶ FibreInfinitesimalModules.sequence I f n where
  τ₁ := FibreIdealPowerTransitions.inclusion I f h
  τ₂ := 𝟙 _
  τ₃ := quotientTransition I f h
  comm₁₂ := (FibreIdealPowerTransitions.inclusion_inclusion I f h).trans
    (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans (sectionMap_transition I f h).symm

variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The SAME genuine sequence morphism induces the actual original ordered
Cech short-complex transition. -/
def complexSequenceTransition {n m : ℕ} (h : n ≤ m) :
    FibreInfinitesimalCech.complexSequence I f U m ⟶
      FibreInfinitesimalCech.complexSequence I f U n :=
  (orderedBaseCechComplexFunctor f U).mapShortComplex.map (sequenceTransition I f h)

/-- EVERY original connecting map intertwines the actual original higher-to-lower
infinitesimal transition and the SAME actual original ideal-power inclusion. -/
theorem connecting_naturality (hUa : ∀ i, IsAffineOpen (U i)) {n m : ℕ}
    (h : n ≤ m) (p : ℕ) :
    FibreInfinitesimalCech.connecting I f U hUa m p ≫
        HomologicalComplex.homologyMap ((orderedBaseCechComplexFunctor f U).map
          (FibreIdealPowerTransitions.inclusion I f h)) (p+1) =
      HomologicalComplex.homologyMap ((orderedBaseCechComplexFunctor f U).map
          (quotientTransition I f h)) p ≫
        FibreInfinitesimalCech.connecting I f U hUa n p :=
  HomologicalComplex.HomologySequence.δ_naturality (complexSequenceTransition I f U h)
    (FibreInfinitesimalCech.complexSequence_shortExact I f U hUa m)
    (FibreInfinitesimalCech.complexSequence_shortExact I f U hUa n) p (p+1) rfl

/-- The actual obstruction of EVERY whole original infinitesimal section
commutes with the literal original higher-to-lower module transition. -/
theorem sectionBoundary_naturality (hcover : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) {n m : ℕ} (h : n ≤ m) :
    FibreInfinitesimalH0Cech.sectionBoundary f U hcover I hUa m ≫
        HomologicalComplex.homologyMap ((orderedBaseCechComplexFunctor f U).map
          (FibreIdealPowerTransitions.inclusion I f h)) 1 =
      baseSectionsMap f (quotientTransition I f h) ≫
        FibreInfinitesimalH0Cech.sectionBoundary f U hcover I hUa n :=
  compose_boundary_square _ _ _ _ _ _ _
    (FibreInfinitesimalH0Cech.globalSectionsIso_naturality f U hcover (quotientTransition I f h))
    (connecting_naturality I f U hUa h 0)

/-- In actual degree one, the obstruction of a literal original whole section
pulls back by the literal original infinitesimal scheme transition. -/
theorem sectionBoundary_transition_apply (hcover : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) {n m : ℕ} (h : n ≤ m)
    (s : Γ(model I f m, ⊤)) :
    HomologicalComplex.homologyMap ((orderedBaseCechComplexFunctor f U).map
        (FibreIdealPowerTransitions.inclusion I f h)) 1
        (FibreInfinitesimalH0Cech.sectionBoundary f U hcover I hUa m s) =
      FibreInfinitesimalH0Cech.sectionBoundary f U hcover I hUa n
        ((transition I f h).appTop s) :=
  module_square_apply _ _ _ _ (sectionBoundary_naturality I f U hcover hUa h)
    s _ (quotientTransition_baseSectionsMap I f h s)

variable [Fintype ι]

/-- The literal positive-order compatible infinitesimal sections give a
compatible family in the SAME original Rees degree-one cohomology, with
EVERY transition and every original coefficient action retained. -/
theorem compatible_sectionBoundary (hcover : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) (s : InfinitesimalIdempotents.compatibleSections I f)
    (n m : ℕ) (h : n ≤ m) :
    (FcReesCechDegreeTransitions.homologyLower I f U hUa (Nat.succ_le_succ h) 1).hom
        ((FcReesCechIdealPowerSections.homologyIso I f U hUa (m+1) 1).hom
          (FibreInfinitesimalH0Cech.sectionBoundary f U hcover I hUa (m+1) (s.1 m))) =
      (FcReesCechIdealPowerSections.homologyIso I f U hUa (n+1) 1).hom
        (FibreInfinitesimalH0Cech.sectionBoundary f U hcover I hUa (n+1) (s.1 n)) := by
  have hb := (sectionBoundary_transition_apply I f U hcover hUa (Nat.succ_le_succ h)
    (s.1 m)).trans (congrArg
      (FibreInfinitesimalH0Cech.sectionBoundary f U hcover I hUa (n+1)) (s.2 n m h))
  exact module_transport_apply _ _ _ _
    (FibreIdealPowerCechMaps.inclusion_homology I f U hUa (Nat.succ_le_succ h) 1)
    _ _ hb

end EnvelopeProperty.FibreInfinitesimalBoundaryTransitions
