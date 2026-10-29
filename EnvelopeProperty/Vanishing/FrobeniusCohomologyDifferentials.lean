import EnvelopeProperty.Cartier.SchemeRelativeFrobenius
import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf

/-! # Exterior differentials for the second-projection Frobenius structure

The first projection of the perfect-field Frobenius twist is semilinear over
the base field.  The comparison below keeps that automorphism explicitly:
precomposing structural constants with a field automorphism does not change
their image, and the universal derivations therefore have inverse comparisons.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.FrobeniusCohomologyDifferentials

open CanonicalGeometry Cartier
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

section SameConstantImage

variable (f g : X ⟶ Spec (.of k)) (σ : k ≃+* k)
    (h : ∀ (U : X.Opensᵒᵖ) (a : k),
      (schemeConstantPresheafMap f).app U a =
        (schemeConstantPresheafMap g).app U (σ a))

private def changeRelativeDerivation (M : X.PresheafOfModules)
    (d : M.Derivation' (schemeConstantPresheafMap g)) :
    M.Derivation' (schemeConstantPresheafMap f) where
  d := d.d
  d_mul := d.d_mul
  d_map := d.d_map
  d_app {X} a := by
    exact (congrArg d.d (h X a)).trans (d.d_app (σ a))

/-- The universal cotangent map when the structural constants differ by
the displayed actual field automorphism. -/
def cotangentMap : cotangentPresheaf f ⟶ cotangentPresheaf g :=
  (cotangentPresheafUniversal f).desc
    (changeRelativeDerivation f g σ h _ (cotangentPresheafDerivation g))

/-- Every actual differential is fixed by the comparison. -/
theorem cotangentMap_d (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (cotangentMap f g σ h).app U ((cotangentPresheafDerivation f).d a) =
      (cotangentPresheafDerivation g).d a := by
  exact PresheafOfModules.Derivation.congr_d
    ((cotangentPresheafUniversal f).fac
      (changeRelativeDerivation f g σ h _ (cotangentPresheafDerivation g))) a

include h in
private theorem inverseConstantRelation (U : X.Opensᵒᵖ) (a : k) :
    (schemeConstantPresheafMap g).app U a =
      (schemeConstantPresheafMap f).app U (σ.symm a) := by
  rw [h U (σ.symm a), σ.apply_symm_apply]

/-- The inverse field automorphism gives the actual inverse cotangent map. -/
def cotangentIso : cotangentPresheaf f ≅ cotangentPresheaf g where
  hom := cotangentMap f g σ h
  inv := cotangentMap g f σ.symm (inverseConstantRelation f g σ h)
  hom_inv_id := by
    ext1 U
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change (cotangentMap g f σ.symm (inverseConstantRelation f g σ h)).app U
      ((cotangentMap f g σ h).app U ((cotangentPresheafDerivation f).d a)) =
        (cotangentPresheafDerivation f).d a
    rw [cotangentMap_d, cotangentMap_d]
  inv_hom_id := by
    ext1 U
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change (cotangentMap f g σ h).app U
      ((cotangentMap g f σ.symm (inverseConstantRelation f g σ h)).app U
        ((cotangentPresheafDerivation g).d a)) = (cotangentPresheafDerivation g).d a
    rw [cotangentMap_d, cotangentMap_d]

end SameConstantImage

private def moduleIsoApp {P Q : X.PresheafOfModules} (e : P ≅ Q) (U : X.Opensᵒᵖ) :
    P.obj U ≅ Q.obj U where
  hom := e.hom.app U
  inv := e.inv.app U
  hom_inv_id := congrArg (fun φ : P ⟶ P => φ.app U) e.hom_inv_id
  inv_hom_id := congrArg (fun φ : Q ⟶ Q => φ.app U) e.inv_hom_id

local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

@[instance_reducible]
private def presheafSectionsModule (P : X.PresheafOfModules) (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) (P.obj U) := (P.obj U).isModule

attribute [local instance] presheafSectionsModule

set_option backward.isDefEq.respectTransparency false in
/-- An actual module-presheaf isomorphism induces the actual exterior
presheaf isomorphism; its naturality is checked on spanning pure wedges. -/
def exteriorPresheafIso {P Q : X.PresheafOfModules} (e : P ≅ Q) (q : ℕ) :
    exteriorPresheaf (R := X.presheaf) P q ≅ exteriorPresheaf (R := X.presheaf) Q q :=
  PresheafOfModules.isoMk
    (fun U => (exteriorLinearEquiv (moduleIsoApp e U).toLinearEquiv q).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext_on (exteriorPower.ιMulti_span (X.presheaf.obj U) q (P.obj U))
      rintro _ ⟨m, rfl⟩
      change exteriorLinearEquiv (moduleIsoApp e V).toLinearEquiv q
          ((exteriorPresheaf (R := X.presheaf) P q).map i
            (exteriorPower.ιMulti (X.presheaf.obj U) q m)) =
        (exteriorPresheaf (R := X.presheaf) Q q).map i
          (exteriorLinearEquiv (moduleIsoApp e U).toLinearEquiv q
            (exteriorPower.ιMulti (X.presheaf.obj U) q m))
      refine (congrArg (exteriorLinearEquiv (moduleIsoApp e V).toLinearEquiv q)
        (exteriorPresheaf_map_mk P q i m)).trans ?_
      refine (exteriorLinearEquiv_ιMulti (moduleIsoApp e V).toLinearEquiv q _).trans ?_
      refine Eq.trans ?_ ((congrArg ((exteriorPresheaf (R := X.presheaf) Q q).map i)
        (exteriorLinearEquiv_ιMulti (moduleIsoApp e U).toLinearEquiv q m)).symm)
      refine Eq.trans ?_ (exteriorPresheaf_map_mk Q q i _).symm
      congr 1
      funext j
      exact PresheafOfModules.naturality_apply e.hom i (m j))

section BaseAutomorphism

variable (f : X ⟶ Spec (.of k)) (σ : k ≃+* k)

/-- Composition with the actual scheme morphism of the field automorphism
precomposes the original structural constants by precisely that automorphism. -/
theorem constant_comp_spec (U : X.Opensᵒᵖ) (a : k) :
    (schemeConstantPresheafMap (f ≫ Spec.map (CommRingCat.ofHom (σ : k →+* k)))).app U a =
      (schemeConstantPresheafMap f).app U (σ a) := by
  have he := congrArg
    (fun z : CommRingCat.of k ⟶ Γ(Spec (.of k), ⊤) =>
      z ≫ f.appTop ≫ X.presheaf.map U.unop.leTop.op)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : k →+* k))).symm
  exact congrArg (fun z : CommRingCat.of k ⟶ Γ(X, U.unop) => z a) he

/-- Structural field automorphisms preserve the original cotangent
presheaf by the canonical map fixing every original differential. -/
def baseAutomorphismCotangentIso :
    cotangentPresheaf (f ≫ Spec.map (CommRingCat.ofHom (σ : k →+* k))) ≅
      cotangentPresheaf f :=
  cotangentIso _ f σ (constant_comp_spec f σ)

/-- The all-degree exterior sheaf comparison under the actual structural
field automorphism, obtained by sheafifying the whole presheaf isomorphism. -/
def baseAutomorphismExteriorIso (q : ℕ) :
    exteriorCotangentSheaf (f ≫ Spec.map (CommRingCat.ofHom (σ : k →+* k))) q ≅
      exteriorCotangentSheaf f q :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (exteriorPresheafIso (baseAutomorphismCotangentIso f σ) q)

end BaseAutomorphism

variable (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- The actual twist structure is the second projection, not the semilinear
first projection composed with the original structural morphism. -/
def twistStructure : SchemeRelativeFrobenius.twist p f ⟶ Spec (.of k) :=
  Limits.pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)

/-- Genuine cotangent/exterior base change for the actual perfect-field
Frobenius twist.  The first-projection pullback is identified with the
exterior differential sheaf relative to the second projection in every degree. -/
def twistExteriorIso (q : ℕ) :
    (Scheme.Modules.pullback
      (Limits.pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p))).obj
        (exteriorCotangentSheaf f q) ≅
      exteriorCotangentSheaf (twistStructure f p) q := by
  let π := Limits.pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p)
  let : IsIso π := SchemeRelativeFrobenius.twist_fst_isIso p f
  let e₁ := ((Scheme.Modules.restrictFunctorIsoPullback π).app
    (exteriorCotangentSheaf f q)).symm ≪≫ exteriorCotangentSheafOpenImmersionIso f π q
  have he : π ≫ f = twistStructure f p ≫
      Spec.map (CommRingCat.ofHom ((frobeniusEquiv k p) : k →+* k)) := by
    have hb : SchemeRelativeFrobenius.baseMap (k := k) p =
        Spec.map (CommRingCat.ofHom ((frobeniusEquiv k p) : k →+* k)) :=
      (SchemeRelativeFrobenius.baseMap_eq_spec p).trans (by rfl)
    exact (Limits.pullback.condition (f := f)
      (g := SchemeRelativeFrobenius.baseMap (k := k) p)).trans
      (congrArg (fun b => twistStructure f p ≫ b) hb)
  exact e₁ ≪≫ eqToIso (congrArg (fun g => exteriorCotangentSheaf g q) he) ≪≫
    baseAutomorphismExteriorIso (twistStructure f p) (frobeniusEquiv k p) q

end EnvelopeProperty.Vanishing.FrobeniusCohomologyDifferentials
