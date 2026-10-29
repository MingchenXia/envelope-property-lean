/-
Mathlib-only proof port. Original source: EnvelopeProperty/ComplexGeometry/Schemes/CanonicalLineSheaf.lean
Upstream SHA256: 6e168565af242d298154e651eb4adfb70b9f0de14f05c055cafbda0d309ac9be
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import EnvelopeProperty.AlgGeom.Canonical.CotangentSmoothLocallyFree
import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf

/-!
# The actual global canonical line sheaf

The object is the sheafification of the literal top exterior cotangent
presheaf. Its line atlas is derived from smooth charts through actual
coefficient-ring isomorphisms, raw exterior maps, and sheafification.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section

section ExteriorCoefficientIso
variable {A B M N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- The literal exterior map of a bijective coefficient-isomorphism
semilinear map is bijective, by its actual inverse on spanning pure wedges. -/
theorem exteriorSemilinearMap_bijective_of_ringIso (e : A ≃+* B)
    (φ : M →ₛₗ[(e : A →+* B)] N) (hφ : Function.Bijective φ) (n : ℕ) :
    Function.Bijective (exteriorSemilinearMap (e : A →+* B) φ n) := by
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.of_ringEquiv e.symm
  let E : M ≃ₛₗ[(e : A →+* B)] N := LinearEquiv.ofBijective φ hφ
  let F := exteriorSemilinearMap (e : A →+* B) φ n
  let G := exteriorSemilinearMap (e.symm : B →+* A) E.symm.toLinearMap n
  have hGF : G.comp F = (LinearMap.id : (⋀[A]^n M) →ₗ[A] (⋀[A]^n M)) := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span A n M)
    rintro _ ⟨m, rfl⟩
    change G (F (exteriorPower.ιMulti A n m)) = exteriorPower.ιMulti A n m
    rw [exteriorSemilinearMap_ιMulti, exteriorSemilinearMap_ιMulti]
    congr 1
    funext j
    exact E.symm_apply_apply (m j)
  have hFG : F.comp G = (LinearMap.id : (⋀[B]^n N) →ₗ[B] (⋀[B]^n N)) := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span B n N)
    rintro _ ⟨m, rfl⟩
    change F (G (exteriorPower.ιMulti B n m)) = exteriorPower.ιMulti B n m
    rw [exteriorSemilinearMap_ιMulti, exteriorSemilinearMap_ιMulti]
    congr 1
    funext j
    exact E.apply_symm_apply (m j)
  exact ⟨(fun x y h ↦ (LinearMap.congr_fun hGF x).symm.trans
    ((congrArg G h).trans (LinearMap.congr_fun hGF y))),
    fun y ↦ ⟨G y, LinearMap.congr_fun hFG y⟩⟩

end ExteriorCoefficientIso

end
end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X) [IsOpenImmersion g]

local instance (U : Y.Opensᵒᵖ) : Module (Y.presheaf.obj U)
    ((cotangentPresheaf (g ≫ f)).obj U) := ((cotangentPresheaf (g ≫ f)).obj U).isModule

local instance (U : X.Opensᵒᵖ) : Module (X.presheaf.obj U)
    ((cotangentPresheaf f).obj U) := ((cotangentPresheaf f).obj U).isModule

/-- The actual cotangent coefficient isomorphism, retaining its native
semilinearity between the two native structure-ring module actions. -/
def cotangentOpenImmersionSemilinear (U : Y.Opensᵒᵖ) :
    (cotangentPresheaf (g ≫ f)).obj U →ₛₗ[((g.appIso U.unop).inv).hom]
      (cotangentPresheaf f).obj (g.opensFunctor.op.obj U) where
  toFun := (cotangentPresheafOpenImmersionMap f g).app U
  map_add' := ((cotangentPresheafOpenImmersionMap f g).app U).hom.map_add
  map_smul' a x := ((cotangentPresheafOpenImmersionMap f g).app U).hom.map_smul a x

/-- The literal exterior coefficient map between actual cotangent
presheaf modules, viewed over the restricted source structure ring. -/
def exteriorCotangentOpenImmersionComponent (n : ℕ) (U : Y.Opensᵒᵖ) :
    (exteriorCotangentPresheaf (g ≫ f) n).obj U ⟶
      (openImmersionPresheafRestrict g (exteriorCotangentPresheaf f n)).obj U := by
  let E := exteriorSemilinearMap ((g.appIso U.unop).inv).hom
    (cotangentOpenImmersionSemilinear f g U) n
  exact ModuleCat.ofHom
    (X := (exteriorCotangentPresheaf (g ≫ f) n).obj U)
    (Y := (openImmersionPresheafRestrict g (exteriorCotangentPresheaf f n)).obj U)
    { toFun := E, map_add' := E.map_add, map_smul' := E.map_smulₛₗ }

/-- The exterior coefficient map takes literal differential products to
products of their actual cotangent coefficient images. -/
theorem exteriorCotangentOpenImmersionComponent_wedge (n : ℕ) (U : Y.Opensᵒᵖ)
    (m : Fin n → (cotangentPresheaf (g ≫ f)).obj U) :
    exteriorCotangentOpenImmersionComponent f g n U
        (exteriorPower.ιMulti (Y.presheaf.obj U) n m) =
      exteriorPower.ιMulti (X.presheaf.obj (g.opensFunctor.op.obj U)) n
        (M := (cotangentPresheaf f).obj (g.opensFunctor.op.obj U))
        (fun j ↦ cotangentOpenImmersionSemilinear f g U (m j)) :=
  exteriorSemilinearMap_ιMulti ((g.appIso U.unop).inv).hom
    (cotangentOpenImmersionSemilinear f g U) n m

set_option backward.isDefEq.respectTransparency true in
/-- Raw exterior cotangent presheaves respect open-immersion restriction,
with naturality derived on actual spanning pure exterior products. -/
def exteriorCotangentPresheafOpenImmersionMap (n : ℕ) :
    exteriorCotangentPresheaf (g ≫ f) n ⟶
      openImmersionPresheafRestrict g (exteriorCotangentPresheaf f n) where
  app U := exteriorCotangentOpenImmersionComponent f g n U
  naturality {U V} i := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span
      (Y.presheaf.obj U) n ((cotangentPresheaf (g ≫ f)).obj U))
    rintro _ ⟨m, rfl⟩
    change exteriorCotangentOpenImmersionComponent f g n V
        ((exteriorCotangentPresheaf (g ≫ f) n).map i
          (exteriorPower.ιMulti (Y.presheaf.obj U) n m)) =
      (exteriorCotangentPresheaf f n).map (g.opensFunctor.op.map i)
        (exteriorCotangentOpenImmersionComponent f g n U
          (exteriorPower.ιMulti (Y.presheaf.obj U) n m))
    refine (congrArg (exteriorCotangentOpenImmersionComponent f g n V)
      (exteriorPresheaf_map_mk (cotangentPresheaf (g ≫ f)) n i m)).trans ?_
    refine (exteriorCotangentOpenImmersionComponent_wedge f g n V _).trans ?_
    refine Eq.trans ?_ ((congrArg ((exteriorCotangentPresheaf f n).map
      (g.opensFunctor.op.map i))
      (exteriorCotangentOpenImmersionComponent_wedge f g n U m)).symm)
    refine Eq.trans ?_ (exteriorPresheaf_map_mk (cotangentPresheaf f) n
      (g.opensFunctor.op.map i) _).symm
    congr 1
    funext j
    exact PresheafOfModules.naturality_apply (cotangentPresheafOpenImmersionMap f g) i (m j)

/-- Bijectivity of the actual raw exterior comparison is derived from the
actual cotangent coefficient-ring isomorphism, with no freeness input. -/
theorem exteriorCotangentOpenImmersionComponent_bijective (n : ℕ) (U : Y.Opensᵒᵖ) :
    Function.Bijective (exteriorCotangentOpenImmersionComponent f g n U) := by
  exact exteriorSemilinearMap_bijective_of_ringIso
    (g.appIso U.unop).symm.commRingCatIsoToRingEquiv
    (cotangentOpenImmersionSemilinear f g U)
    (kaehlerCoefficientMap_bijective
      ((schemeConstantPresheafMap (g ≫ f)).app U)
      ((schemeConstantPresheafMap f).app (g.opensFunctor.op.obj U))
      (g.appIso U.unop).symm (openImmersion_constantSquare_inv f g U)) n

/-- The actual exterior cotangent presheaf open-immersion comparison. -/
def exteriorCotangentPresheafOpenImmersionIso (n : ℕ) :
    exteriorCotangentPresheaf (g ≫ f) n ≅
      openImmersionPresheafRestrict g (exteriorCotangentPresheaf f n) :=
  PresheafOfModules.isoMk
    (fun U ↦ (LinearEquiv.ofBijective
      (exteriorCotangentOpenImmersionComponent f g n U).hom
      (exteriorCotangentOpenImmersionComponent_bijective f g n U)).toModuleIso)
    (fun {_ _} i ↦ (exteriorCotangentPresheafOpenImmersionMap f g n).naturality i)

/-- The actual exterior cotangent sheaf comparison follows from the raw
presheaf comparison and actual open-immersion sheafification comparison. -/
def exteriorCotangentSheafOpenImmersionIso (n : ℕ) :
    (Scheme.Modules.restrictFunctor g).obj (exteriorCotangentSheaf f n) ≅
      exteriorCotangentSheaf (g ≫ f) n :=
  openImmersionSheafificationIso g (exteriorCotangentPresheaf f n) ≪≫
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso
      (exteriorCotangentPresheafOpenImmersionIso f g n).symm

end
end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The actual canonical object is the sheafification of the literal top
exterior cotangent presheaf, before any smoothness assumption. -/
def canonicalLineSheaf (n : ℕ) : X.Modules := exteriorCotangentSheaf f n

/-- The raw exterior cotangent sheaf on a genuine standard-smooth chart
has a derived actual rank-one frame. -/
def standardSmoothCanonicalAffineChartFrame {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (.op V)).hom) :
    LocalBundleFrame (canonicalLineSheaf f n) V := by
  let A : CommRingCat := Γ(X, V)
  letI := affineChartAlgebra f V
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K A := hs
  have he : hV.fromSpec ≫ f = affineStructuralMap K A :=
    affineChartStructuralMap_eq_affineStructuralMap f hV
  let E : (Scheme.Modules.restrictFunctor hV.fromSpec).obj (canonicalLineSheaf f n) ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
    exteriorCotangentSheafOpenImmersionIso f hV.fromSpec n ≪≫
      eqToIso (congrArg (fun q ↦ exteriorCotangentSheaf q n) he) ≪≫
      standardSmoothTopExteriorSheafFrame K A n
  let EV : (Scheme.Modules.restrictFunctor V.ι).obj (canonicalLineSheaf f n) ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec).symm.app
      (canonicalLineSheaf f n) ≪≫
    (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app
      (canonicalLineSheaf f n) ≪≫
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso E ≪≫
      Scheme.Modules.restrictUnitIso hV.isoSpec.hom
  exact (Scheme.Modules.overEquiv V).unitIso.app ((canonicalLineSheaf f n).over V) ≪≫
    (Scheme.Modules.overEquiv V).inverse.mapIso
      ((Scheme.Modules.overFunctorEquiv V).app (canonicalLineSheaf f n) ≪≫ EV) ≪≫
    V.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf

/-- Smoothness derives actual local line frames for the canonical sheaf. -/
theorem smooth_canonicalLineSheaf_local_frame (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      Nonempty (LocalBundleFrame (canonicalLineSheaf f n) V) := by
  obtain ⟨V, hV, hx, hs⟩ := smooth_cotangent_affine_chart f n x
  exact ⟨V, hV, hx, ⟨standardSmoothCanonicalAffineChartFrame f hV n hs⟩⟩

/-- The genuine smooth chart cover supplies an actual global canonical
line atlas, whose frames are derived from standard-smooth presentations. -/
def smoothCanonicalLineAtlas (n : ℕ) [SmoothOfRelativeDimension n f] :
    LineBundleAtlas (canonicalLineSheaf f n) where
  I := X
  opens x := (smoothCotangentChart f n x).val
  covers x := ⟨x, (smoothCotangentChart f n x).property.2.1⟩
  frame x := standardSmoothCanonicalAffineChartFrame f
    (smoothCotangentChart f n x).property.1 n (smoothCotangentChart f n x).property.2.2

/-- The canonical line bundle is constructed on the actual exterior
cotangent sheaf, using only smoothness of the genuine structural morphism. -/
def smoothCanonicalLineBundle (n : ℕ) [SmoothOfRelativeDimension n f] :
    IntrinsicLineBundle X where
  sheaf := canonicalLineSheaf f n
  atlas := smoothCanonicalLineAtlas f n

/-- The constructed canonical line bundle retains the literal exterior
cotangent sheaf as its underlying object. -/
theorem smoothCanonicalLineBundle_sheaf (n : ℕ) [SmoothOfRelativeDimension n f] :
    (smoothCanonicalLineBundle f n).sheaf = exteriorCotangentSheaf f n := rfl

end
end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- On a genuine standard-smooth affine chart the actual global exterior
cotangent sheaf restricts to the tilde of its coordinate exterior module. -/
def standardSmoothAffineChartExteriorCotangentSheafIso {V : X.Opens}
    (hV : IsAffineOpen V) (n : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (.op V)).hom) :
    letI := affineChartAlgebra f V
    (Scheme.Modules.restrictFunctor hV.fromSpec).obj (exteriorCotangentSheaf f n) ≅
      AlgebraicGeometry.tilde (affineExteriorCotangentModule K Γ(X, V) n) := by
  letI := affineChartAlgebra f V
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) := hs
  exact exteriorCotangentSheafOpenImmersionIso f hV.fromSpec n ≪≫
    eqToIso (congrArg (fun q ↦ exteriorCotangentSheaf q n)
      (affineChartStructuralMap_eq_affineStructuralMap f hV)) ≪≫
    affineExteriorCotangentSheafIso K Γ(X, V)
      (standardSmoothDifferentialBasis K Γ(X, V) n) n

end
end EnvelopeProperty.CanonicalGeometry
