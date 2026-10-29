import EnvelopeProperty.Vanishing.NadelCanonicalMixedPureTrace
import EnvelopeProperty.AlgGeom.Canonical.AffineExteriorSections

/-! # The existing pure canonical counit in its actual affine sheaf sections

This is scalar/coordinate transport of the proved pure counit, not a second
trace construction.  Both comparisons are the genuine affine exterior
sheaf comparisons, with bases produced from the original coordinates.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
open NadelCanonicalBaseChange
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private def affineCanonicalSectionsRawIso (K : Type u) [Field K]
    (R : CommRingCat.{u}) [Algebra K R] {m : ℕ}
    (b : Module.Basis (Fin m) R (KaehlerDifferential K R)) :
    (moduleSpecΓFunctor (R := R)).obj
      (exteriorCotangentSheaf (affineStructuralMap K R) m) ≅
      ModuleCat.of R (affineCanonicalModule K R m) :=
  (moduleSpecΓFunctor (R := R)).mapIso
    (affineExteriorCotangentSheafIso K R b m) ≪≫
      (AlgebraicGeometry.tilde.isoTop (ModuleCat.of R (affineCanonicalModule K R m))).symm

/-- The genuine affine exterior comparison uses the SAME original raw map
and SAME sheafification unit on every original top form. -/
private theorem affineCanonicalSectionsRawIso_inv_unit (K : Type u) [Field K]
    (R : CommRingCat.{u}) [Algebra K R] {m : ℕ}
    (b : Module.Basis (Fin m) R (KaehlerDifferential K R))
    (w : affineCanonicalModule K R m) :
    (affineCanonicalSectionsRawIso K R b).inv w =
      (exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K R)) m).app (.op ⊤)
        (affineExteriorCotangentToOpen K R m (.op ⊤) w) := by
  let P := exteriorCotangentPresheaf (affineStructuralMap K R) m
  let M := affineExteriorCotangentModule K R m
  let φ := affineExteriorCotangentToOpen K R m
  let hφ := fun {U V : (Spec R).Opensᵒᵖ} (i : U ⟶ V) =>
    affineExteriorCotangentToOpen_naturality K R m i
  let hloc := affineExteriorCotangentToOpen_isLocalized K R b m
  have h := affineLocalizedSheafificationHom_unit_apply R P M φ hφ hloc (1 : R)
    (φ (.op (PrimeSpectrum.basicOpen (1 : R))) w)
  change (affineLocalizedSheafificationHom R P M φ hφ hloc).val.app
      (.op (PrimeSpectrum.basicOpen (1 : R)))
      ((affinePresheafSheafificationUnit R P).app (.op (PrimeSpectrum.basicOpen (1 : R)))
        (φ (.op (PrimeSpectrum.basicOpen (1 : R))) w)) =
    (IsLocalizedModule.linearEquiv (.powers (1 : R))
      (φ (.op (PrimeSpectrum.basicOpen (1 : R)))).hom
      (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen (1 : R))).hom)
      (φ (.op (PrimeSpectrum.basicOpen (1 : R))) w) at h
  rw [IsLocalizedModule.linearEquiv_apply] at h
  have htop : (affineExteriorCotangentSheafIso K R b m).hom.val.app (.op ⊤)
      ((exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K R)) m).app (.op ⊤)
        (affineExteriorCotangentToOpen K R m (.op ⊤) w)) =
      (AlgebraicGeometry.tilde.isoTop M).hom w := by
    have hone : (PrimeSpectrum.basicOpen (1 : R) : (Spec R).Opens) = ⊤ :=
      PrimeSpectrum.basicOpen_one
    rw [hone] at h
    exact h
  apply (affineCanonicalSectionsRawIso K R b).toLinearEquiv.injective
  change (affineCanonicalSectionsRawIso K R b).hom
      ((affineCanonicalSectionsRawIso K R b).inv w) =
    (affineCanonicalSectionsRawIso K R b).hom _
  rw [Iso.inv_hom_id_apply]
  change w = (AlgebraicGeometry.tilde.isoTop M).inv
    ((affineExteriorCotangentSheafIso K R b m).hom.val.app (.op ⊤)
      ((exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K R)) m).app (.op ⊤)
        (affineExteriorCotangentToOpen K R m (.op ⊤) w)))
  rw [htop, Iso.hom_inv_id_apply]

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n)
    (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] A) (ha : a.toRingHom.FormallyEtale)
    (htame : ∀ i, IsUnit (N i : A))
local notation "P" => NadelMixedKummer.Ring N (pureCoefficient (originalCoordinates a) I σ)

/-- The whole ORIGINAL base canonical sheaf sections with ORIGINAL A scalars,
identified with its actual exterior module through the proved affine comparison. -/
def baseCanonicalSectionsRawIso :
    (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n) ≅
      ModuleCat.of A (affineCanonicalModule k A n) :=
  affineCanonicalSectionsRawIso k (.of A) (baseDifferentialBasis a ha)

/-- The whole ORIGINAL pure canonical sheaf sections, using the internally
produced genuine pure differential basis rather than an incoming frame. -/
def pureCanonicalSectionsRawIso :
    (moduleSpecΓFunctor (R := .of P)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of P)) n) ≅
      ModuleCat.of P (affineCanonicalModule k P n) :=
  affineCanonicalSectionsRawIso k (.of P) (pureDifferentialBasis N I σ hN a ha htame)

omit [Nontrivial A] in
/-- Original base forms enter the actual canonical sheaf by their SAME
native affine map followed by the SAME sheafification unit. -/
theorem baseCanonicalSectionsRawIso_inv_unit (w : affineCanonicalModule k A n) :
    (baseCanonicalSectionsRawIso a ha).inv w =
      (exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap k (.of A))) n).app (.op ⊤)
        (affineExteriorCotangentToOpen k (.of A) n (.op ⊤) w) :=
  affineCanonicalSectionsRawIso_inv_unit k (.of A) (baseDifferentialBasis a ha) w

omit [Nontrivial A] in
/-- Original pure forms enter the actual canonical sheaf by their SAME
native affine map followed by the SAME sheafification unit. -/
theorem pureCanonicalSectionsRawIso_inv_unit (w : affineCanonicalModule k P n) :
    (pureCanonicalSectionsRawIso N I σ hN a ha htame).inv w =
      (exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap k (.of P))) n).app (.op ⊤)
        (affineExteriorCotangentToOpen k (.of P) n (.op ⊤) w) :=
  affineCanonicalSectionsRawIso_inv_unit k (.of P)
    (pureDifferentialBasis N I σ hN a ha htame) w

/-- The SAME native pure canonical counit on actual whole canonical sheaf
sections.  The finite algebra is the original P/A, retaining all factors. -/
def pureCanonicalSectionsCounit :
    (ModuleCat.restrictScalars (algebraMap A P)).obj
      ((moduleSpecΓFunctor (R := .of P)).obj
        (exteriorCotangentSheaf (affineStructuralMap k (.of P)) n)) ⟶
      (moduleSpecΓFunctor (R := .of A)).obj
        (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n) :=
  (ModuleCat.restrictScalars (algebraMap A P)).map
      (pureCanonicalSectionsRawIso N I σ hN a ha htame).hom ≫
    pureCanonicalCounit N I σ hN a ha htame ≫
      (baseCanonicalSectionsRawIso a ha).inv

/-- The entire transported counit retains the SAME original pure counit
through the actual original raw-to-canonical-section comparison. -/
theorem pureCanonicalSectionsCounit_raw :
    (ModuleCat.restrictScalars (algebraMap A P)).map
        (pureCanonicalSectionsRawIso N I σ hN a ha htame).inv ≫
      pureCanonicalSectionsCounit N I σ hN a ha htame =
    pureCanonicalCounit N I σ hN a ha htame ≫
      (baseCanonicalSectionsRawIso a ha).inv := by
  let e := (ModuleCat.restrictScalars (algebraMap A P)).mapIso
    (pureCanonicalSectionsRawIso N I σ hN a ha htame)
  change e.inv ≫ e.hom ≫ _ = _
  exact e.inv_hom_id_assoc _

/-- Exact all-coefficient/all-top-form normalization of the transported SAME
pure counit.  No auxiliary coefficient-cover trace is inserted. -/
theorem pureCanonicalSectionsCounit_pulled_topform
    (c : P) (w : affineCanonicalModule k A n) :
    pureCanonicalSectionsCounit N I σ hN a ha htame
      ((pureCanonicalSectionsRawIso N I σ hN a ha htame).inv
        (c • topPullback (R := k) (A := A) (B := P) n w)) =
      (baseCanonicalSectionsRawIso a ha).inv (Algebra.trace A P c • w) := by
  have h := ConcreteCategory.congr_hom
    (pureCanonicalSectionsCounit_raw N I σ hN a ha htame)
    (c • topPullback (R := k) (A := A) (B := P) n w)
  simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply] at h
  have hτ := pureCanonicalCounit_pulled_topform N I σ hN a ha htame c w
  generalize hβ : (baseCanonicalSectionsRawIso a ha).inv = β at h ⊢
  have hβτ := congrArg β hτ
  -- Build the ordinary Eq.trans term explicitly.  Both entire equations
  -- above are elaborated already; the standard kernel checks their middle
  -- conversion without recursively elaborating the affine isomorphisms.
  run_tac Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.getLCtx
    let findLocal (s : String) : Lean.MetaM Lean.Expr := do
      for d in ctx do
        if d.userName.eraseMacroScopes == Lean.Name.mkSimple s then
          return Lean.mkFVar d.fvarId
      throwError "missing local equality {s}"
    let h₁ ← findLocal "h"
    let h₂ ← findLocal "hβτ"
    let t₁ ← Lean.Meta.whnf (← Lean.Meta.inferType h₁)
    let t₂ ← Lean.Meta.whnf (← Lean.Meta.inferType h₂)
    unless t₁.isAppOfArity ``Eq 3 && t₂.isAppOfArity ``Eq 3 do
      throwError "expected two original equalities"
    let .const _ levels := t₁.getAppFn | throwError "first equality has no constant head"
    let a₁ := t₁.getAppArgs
    let a₂ := t₂.getAppArgs
    let proof := Lean.mkAppN (Lean.mkConst ``Eq.trans levels)
      #[a₁[0]!, a₁[1]!, a₁[2]!, a₂[2]!, h₁, h₂]
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
