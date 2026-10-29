import EnvelopeProperty.Source.SignedProjectiveLines
import EnvelopeProperty.AlgGeom.OriginalProjectiveWholeTensorModelSections
import EnvelopeProperty.AlgGeom.SchemePulledPowerFrames
import EnvelopeProperty.AlgGeom.SchemeLineFramePullbackCoherence

/-! # Chart frames and the pivot coefficient of signed-degree sections

Setting: an integral scheme `X` with a presentation `q c: X → ℙ^{d_c}` over `k`
(`q 0` a closed immersion), the line `L(n) = ⨂_c q_c^* 𝒪(n_c)` for `n ∈ ℤ^{r+1}`
(`signedProjectiveLine`), and the joint charts `U_j = ⋂_c q_c^{-1} D₊(X_{j_c})`, the preimages
of the Segre charts (`signedJointOpen`).

On `U_j` the line has the frame `e_j = ⨂_c q_c^* (X_{j_c}^{n_c})`, pulled back from the
standard frames of `𝒪(n_c)` (`signedFrame`, `signedChartFrame`); the coefficient of a global
section `s` in this frame is `s_j ∈ Γ(X, U_j)` (`signedChartCoefficient`). For `n ≥ 0` the frame
generator is a global section (the `normalizer`); for negative degrees it is only a section
over `U_j`, so the coefficient of `s` in `K(X)` is defined through the generic fibre: it is the
coordinate of the germ of `s` in the generic frame of the pivot chart `z` (`signedCoefficient`).

Main result (`lem:pm-pivot-coefficient`, `germ_signedChartCoefficient`): for every chart `j`
with all `U_j` nonempty,

  `s_j = signedCoefficient s / z̃_j^n` in `K(X)`, where `z̃_j^n = ∏_c (X_{j_c}/X_{z_c})^{n_c}`.

*Proof.* On `W = U_j ∩ U_z` the two frames differ by the unit `∏_c (X_{z_c}/X_{j_c})^{n_c}`:
this is the AINTLIB transition `coordinateHyperplaneTwistTrivialization_restrict_transition`
of `𝒪(n_c)`, pulled back along `q_c` (`signedFrame_transition`). Hence the generators satisfy
`ε_z = κ ε_j` on `W`, with germ `κ = ∏_c (X_{z_c}/X_{j_c})^{n_c} = (z̃_j^n)^{-1}`
(`germ_signedTransition`). Expanding `s = s_j ε_j` on `U_j` and taking the generic coordinate
relative to `ε_z` gives the formula.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial Opposite
open Scheme.Modules Alterations
noncomputable section
universe u
namespace EnvelopeProperty.Variety
open FiniteOriginalProjectivePowerFrames CanonicalGeometry SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable local instance pivotMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance pivotPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

/-! ### General frame calculus -/

section FrameCalculus

/-- A scalar transition between two frames is transported along `frameViaFactor`. -/
theorem frameViaFactor_hom_eq_comp_scalar {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules}
    (A A' : (pullback b).obj M ≅ unitObj C) (w : Γ(C, ⊤))
    (h : A.hom = A'.hom ≫ ModularCurves.unitEndomorphismOfTopSection w) :
    (frameViaFactor g b f hg A).hom =
      (frameViaFactor g b f hg A').hom ≫
        ModularCurves.unitEndomorphismOfTopSection (g.appTop.hom w) := by
  have hu : (pullback g).map (ModularCurves.unitEndomorphismOfTopSection w) ≫
      (pullbackUnitIso g).hom =
        (pullbackUnitIso g).hom ≫ ModularCurves.unitEndomorphismOfTopSection (g.appTop.hom w) := by
    rw [← ModularCurves.pullback_unitEndomorphismOfTopSection g w, Iso.hom_inv_id_assoc]
  simp only [frameViaFactor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, h,
    Functor.map_comp, Category.assoc, hu]

private theorem frameViaFactor_congr {B C D : Scheme.{u}} {g g' : B ⟶ C} (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) (hg' : g' ≫ b = f) (h : g = g') {M : D.Modules}
    (e : (pullback b).obj M ≅ unitObj C) :
    frameViaFactor g b f hg e = frameViaFactor g' b f hg' e := by
  subst h
  rfl

/-- A subopen frame factors through any smaller open of the target. -/
theorem subopenFrame_eq_through {Y Z : Scheme.{u}} (g : Y ⟶ Z) {U O : Z.Opens} (hOU : O ≤ U)
    {V : Y.Opens} (hU : V ≤ g ⁻¹ᵁ U) (hO : V ≤ g ⁻¹ᵁ O) {M : Z.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    SchemePullbackSubopenFrames.frame g U V hU e =
      (pullbackComp V.ι g).app M ≪≫ frameViaFactor (g.resLE O V hO) O.ι (V.ι ≫ g)
        (g.resLE_comp_ι hO) (frameViaFactor (Z.homOfLE hOU) U.ι O.ι (Z.homOfLE_ι hOU) e) := by
  unfold SchemePullbackSubopenFrames.frame
  rw [frameViaFactor_comp (g.resLE O V hO) (Z.homOfLE hOU) U.ι O.ι (Z.homOfLE_ι hOU) (V.ι ≫ g)
    (g.resLE_comp_ι hO)]
  exact congrArg (fun z => (pullbackComp V.ι g).app M ≪≫ z)
    (frameViaFactor_congr _ _ _ _ (Scheme.Hom.resLE_map g hO hOU).symm e)

/-- A scalar transition between two frames on a smaller open `O` of the target pulls back to the
subopen frames on any `V ⊆ g⁻¹ O`, the scalar being pulled back along `g`. -/
theorem subopenFrame_transition {Y Z : Scheme.{u}} (g : Y ⟶ Z) {U U' O : Z.Opens}
    (hOU : O ≤ U) (hOU' : O ≤ U') {V : Y.Opens} (hU : V ≤ g ⁻¹ᵁ U) (hU' : V ≤ g ⁻¹ᵁ U')
    (hO : V ≤ g ⁻¹ᵁ O) {M : Z.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (e' : (pullback U'.ι).obj M ≅ unitObj U'.toScheme) (w : Γ(O.toScheme, ⊤))
    (h : (frameViaFactor (Z.homOfLE hOU) U.ι O.ι (Z.homOfLE_ι hOU) e).hom =
      (frameViaFactor (Z.homOfLE hOU') U'.ι O.ι (Z.homOfLE_ι hOU') e').hom ≫
        ModularCurves.unitEndomorphismOfTopSection w) :
    (SchemePullbackSubopenFrames.frame g U V hU e).hom =
      (SchemePullbackSubopenFrames.frame g U' V hU' e').hom ≫
        ModularCurves.unitEndomorphismOfTopSection ((g.resLE O V hO).appTop.hom w) := by
  rw [subopenFrame_eq_through g hOU hU hO, subopenFrame_eq_through g hOU' hU' hO]
  simp only [Iso.trans_hom, Category.assoc]
  rw [frameViaFactor_hom_eq_comp_scalar _ _ _ _ _ _ _ h]

/-- Restricting a subopen frame to a smaller source open is the subopen frame there. -/
theorem frameViaFactor_subopenFrame {Y Z : Scheme.{u}} (g : Y ⟶ Z) (U : Z.Opens)
    {V W : Y.Opens} (hWV : W ≤ V) (h : V ≤ g ⁻¹ᵁ U) {M : Z.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    frameViaFactor (Y.homOfLE hWV) V.ι W.ι (Y.homOfLE_ι hWV)
        (SchemePullbackSubopenFrames.frame g U V h e) =
      SchemePullbackSubopenFrames.frame g U W (hWV.trans h) e := by
  unfold SchemePullbackSubopenFrames.frame
  rw [frameViaFactor_pullbackComp (Y.homOfLE hWV) V.ι W.ι (Y.homOfLE_ι hWV) g,
    frameViaFactor_comp]
  exact congrArg (fun z => (pullbackComp W.ι g).app M ≪≫ z)
    (frameViaFactor_congr _ _ _ _ (Scheme.Hom.map_resLE g h hWV) e)

/-- Scalar transitions of tensor frames multiply. -/
theorem tensorFrame_hom_eq_comp_scalar {X : Scheme.{u}} (U : X.Opens) : {r : ℕ} →
    (M : Fin (r + 1) → X.Modules) → (e e' : ∀ c, (pullback U.ι).obj (M c) ≅ unitObj U.toScheme) →
    (w : Fin (r + 1) → Γ(U.toScheme, ⊤)) →
    (∀ c, (e c).hom = (e' c).hom ≫ ModularCurves.unitEndomorphismOfTopSection (w c)) →
    (tensorFrame U M e).hom =
      (tensorFrame U M e').hom ≫ ModularCurves.unitEndomorphismOfTopSection (∏ c, w c)
  | 0, _, _, _, w, h => by
      rw [Fin.prod_univ_one]
      exact h 0
  | r + 1, M, e, e', w, h => by
      have ih := tensorFrame_hom_eq_comp_scalar U (fun c : Fin (r + 1) => M c.succ)
        (fun c => e c.succ) (fun c => e' c.succ) (fun c => w c.succ) (fun c => h c.succ)
      change (Functor.Monoidal.μIso (pullback U.ι) (M 0)
          (tensorLine (fun c : Fin (r + 1) => M c.succ))).inv ≫
          ((e 0).hom ⊗ₘ (tensorFrame U (fun c : Fin (r + 1) => M c.succ)
            (fun c => e c.succ)).hom) ≫ (ModularCurves.unitObjTensorIso U.toScheme).hom =
        ((Functor.Monoidal.μIso (pullback U.ι) (M 0)
          (tensorLine (fun c : Fin (r + 1) => M c.succ))).inv ≫
          ((e' 0).hom ⊗ₘ (tensorFrame U (fun c : Fin (r + 1) => M c.succ)
            (fun c => e' c.succ)).hom) ≫ (ModularCurves.unitObjTensorIso U.toScheme).hom) ≫
          ModularCurves.unitEndomorphismOfTopSection (∏ c, w c)
      rw [h 0, ih, ← tensorHom_comp_tensorHom]
      simp only [Category.assoc, ModularCurves.unitObjTensorIso_hom_comp_scalars,
        Fin.prod_univ_succ]

/-- Restricting a tensor frame to a smaller open is the tensor frame of the restrictions. -/
theorem frameViaFactor_tensorFrame {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    {r : ℕ} → (M : Fin (r + 1) → X.Modules) →
    (e : ∀ c, (pullback U.ι).obj (M c) ≅ unitObj U.toScheme) →
    frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) (tensorFrame U M e) =
      tensorFrame V M (fun c => frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) (e c))
  | 0, _, _ => rfl
  | r + 1, M, e => by
      have ih := frameViaFactor_tensorFrame hVU (fun c : Fin (r + 1) => M c.succ)
        (fun c => e c.succ)
      change frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU)
          ((Functor.Monoidal.μIso (pullback U.ι) (M 0)
            (tensorLine (fun c : Fin (r + 1) => M c.succ))).symm ≪≫
            SchemeTensorPowerFrames.tensorFrame (e 0)
              (tensorFrame U (fun c : Fin (r + 1) => M c.succ) (fun c => e c.succ))) =
        (Functor.Monoidal.μIso (pullback V.ι) (M 0)
          (tensorLine (fun c : Fin (r + 1) => M c.succ))).symm ≪≫
          SchemeTensorPowerFrames.tensorFrame
            (frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) (e 0))
            (tensorFrame V (fun c : Fin (r + 1) => M c.succ)
              (fun c => frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) (e c.succ)))
      rw [SchemePulledPowerFrames.frameViaFactor_tensor, ih]

private theorem pullbackCongr_inv_app {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b)
    (M : Y.Modules) : (pullbackCongr h).inv.app M = (pullbackCongr h.symm).hom.app M := by
  subst h
  rfl

/-- Restriction of a pullback frame along an open inclusion is `frameViaFactor`. -/
theorem restrictTrivialization_eq_frameViaFactor {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (hVU : V ≤ U) (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    restrictTrivialization hVU e = frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) e := by
  apply Iso.ext
  simp only [restrictTrivialization, frameViaFactor, frameFactorIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc,
    pullbackCongr_inv_app]

/-- The restriction-formalism restriction of a frame, in the pullback formalism. -/
theorem pullbackIsoOfRestrictIso_restrictOpenTrivialization {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (hVU : V ≤ U) (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    pullbackIsoOfRestrictIso M V (restrictOpenTrivialization hVU e) =
      frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) (pullbackIsoOfRestrictIso M U e) := by
  rw [restrictOpenTrivialization_eq_pullback, ← restrictTrivialization_eq_frameViaFactor]
  apply Iso.ext
  simp only [restrictOpenTrivializationPullback, pullbackIsoOfRestrictIso, Iso.trans_hom,
    Iso.app_hom, Iso.symm_hom, Iso.inv_hom_id_app_assoc]

theorem pullbackIsoOfRestrictIso_restrictIsoOfPullbackIso {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    pullbackIsoOfRestrictIso M U (restrictIsoOfPullbackIso M U e) = e := by
  apply Iso.ext
  simp [restrictIsoOfPullbackIso, pullbackIsoOfRestrictIso]

theorem restrictIsoOfPullbackIso_pullbackIsoOfRestrictIso {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    restrictIsoOfPullbackIso M U (pullbackIsoOfRestrictIso M U e) = e := by
  apply Iso.ext
  simp [restrictIsoOfPullbackIso, pullbackIsoOfRestrictIso]

private theorem openTopSection_eq_topIso {Y : Scheme.{u}} (U : Y.Opens) (c : Γ(Y, U)) :
    openTopSection U c = U.topIso.inv c := by
  rw [openTopSection, Scheme.Opens.ι_appIso]
  rfl

/-- The restricted morphism acts on top sections by `appLE`. -/
theorem resLE_appTop_openTopSection {Y Z : Scheme.{u}} (f : Y ⟶ Z) (U : Z.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (s : Γ(Z, U)) :
    (f.resLE U V e).appTop.hom (openTopSection U s) = openTopSection V ((f.appLE U V e).hom s) := by
  rw [openTopSection_eq_topIso, openTopSection_eq_topIso]
  change ((f.resLE U V e).app ⊤) (U.topIso.inv s) = V.topIso.inv ((f.appLE U V e) s)
  rw [Scheme.Hom.resLE_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply,
    CommRingCat.hom_inv_apply]
  rfl

theorem openTopSection_prod {Y : Scheme.{u}} (U : Y.Opens) {ι : Type*} (s : Finset ι)
    (c : ι → Γ(Y, U)) : openTopSection U (∏ i ∈ s, c i) = ∏ i ∈ s, openTopSection U (c i) := by
  simp only [openTopSection_eq_topIso]
  exact map_prod U.topIso.inv.hom c s

/-- A ring map to a field sends integer powers of units to integer powers. -/
theorem ringHom_unit_zpow {A F : Type*} [CommRing A] [Field F] (ψ : A →+* F) (w : Aˣ) (e : ℤ) :
    ψ ((w ^ e : Aˣ) : A) = ψ w ^ e := by
  have h1 : ψ ((w ^ e : Aˣ) : A) =
      ((Units.map ψ.toMonoidHom (w ^ e) : Fˣ) : F) := (Units.coe_map _ _).symm
  rw [h1, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
  rfl

variable {X : Scheme.{u}} [IsIntegral X]

/-- Sections of an invertible module over a nonempty open are determined by their generic germ. -/
theorem bundleGenericGerm_injective {L : X.Modules} (hL : IsInvertible L) (U : X.Opens)
    [Nonempty U] : Function.Injective (bundleGenericGerm L U) := by
  intro s t h
  change L.presheaf.germ U (genericPoint X) (genericPoint_mem_nonempty_open U) s =
    L.presheaf.germ U (genericPoint X) (genericPoint_mem_nonempty_open U) t at h
  obtain ⟨V, hV, i, j, heq⟩ := L.presheaf.germ_eq _ _ _ _ _ h
  cases Subsingleton.elim i j
  let : Nonempty V := ⟨⟨genericPoint X, hV⟩⟩
  exact (invertibleLineAtlas L hL).restriction_injective i heq

/-- The generic generator of an over-site frame is the germ of its local unit section. -/
theorem genericFrameGenerator_eq {L : X.Modules} {U : X.Opens} [Nonempty U]
    (E : LocalBundleFrame L U) :
    genericFrameGenerator E =
      bundleGenericGerm L U (ModularCurves.overTrivializationSection L U E 1) := rfl

/-- A generic frame takes the value one on its own generator. -/
theorem genericBundleFiberFrame_generator {L : X.Modules} {U : X.Opens} [Nonempty U]
    (E : LocalBundleFrame L U) : genericBundleFiberFrame E (genericFrameGenerator E) = 1 := by
  rw [← one_smul X.functionField (genericFrameGenerator E), ← genericBundleFiberFrame_symm_apply,
    LinearEquiv.apply_symm_apply]

omit [IsIntegral X] in
/-- The over-site coefficients of a restricted global section are its affine
local-trivialization coefficients. -/
theorem localFrameCoefficients_restrict_top {L : X.Modules} (U : X.affineOpens) [Nonempty U.1]
    (e : L.restrict U.1.ι ≅ unitObj U.1.toScheme) (s : Γ(L, ⊤)) :
    localFrameCoefficients (overTrivializationOfRestrictIso L U.1 e)
        (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) =
      ModularCurves.localTrivializationCoefficient L U e s :=
  ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso L U e s

end FrameCalculus

/-! ### Frames of signed lines -/

section SignedFrames

variable {k : Type u} [Field k] {X : Scheme.{u}} {r : ℕ} (d : Fin (r + 1) → ℕ)
  (q : ∀ c, X ⟶ Proj (homogeneousSubmodule (Fin (d c + 1)) k)) (t : ∀ c, Fin (d c + 1))
  (n : Fin (r + 1) → ℤ)

/-- The standard frame of `𝒪(n_c)` on the chart `D₊(X_i)`, in the pullback formalism. -/
def twistChartFrame (c : Fin (r + 1)) (i : Fin (d c + 1)) :
    (pullback (coordinateOpen (R := k) i).ι).obj
        (coordinateHyperplaneTwist (R := k) (t c) (n c)) ≅
      unitObj (coordinateOpen (R := k) i).toScheme :=
  pullbackIsoOfRestrictIso _ _ (coordinateHyperplaneTwistTrivialization (R := k) i (t c) (n c))

/-- The frame of the factor `q_c^* 𝒪(n_c)` on an open `V ⊆ q_c^{-1} D₊(X_i)`. -/
def signedFactorFrame (c : Fin (r + 1)) (i : Fin (d c + 1)) (V : X.Opens)
    (h : V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) i) :
    (pullback V.ι).obj ((pullback (q c)).obj (coordinateHyperplaneTwist (R := k) (t c) (n c))) ≅
      unitObj V.toScheme :=
  SchemePullbackSubopenFrames.frame (q c) (coordinateOpen (R := k) i) V h (twistChartFrame d t n c i)

/-- The tensor frame `⨂_c q_c^* X_{a_c}^{n_c}` of the signed line on an open `V` contained in the
chart `a` (`def:pm-chart-frame`). -/
def signedFrame (a : ∀ c, Fin (d c + 1)) (V : X.Opens)
    (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c)) :
    (pullback V.ι).obj (signedProjectiveLine d q t n) ≅ unitObj V.toScheme :=
  tensorFrame V _ (fun c => signedFactorFrame d q t n c (a c) V (hV c))

/-- Restricting the frame of a chart to a smaller open gives the frame there. -/
theorem frameViaFactor_signedFrame (a : ∀ c, Fin (d c + 1)) {U V : X.Opens} (hVU : V ≤ U)
    (hU : ∀ c, U ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c)) :
    frameViaFactor (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU) (signedFrame d q t n a U hU) =
      signedFrame d q t n a V (fun c => hVU.trans (hU c)) := by
  unfold signedFrame
  rw [frameViaFactor_tensorFrame]
  congr 1
  funext c
  exact frameViaFactor_subopenFrame (q c) _ hVU (hU c) _

private theorem twistChartFrame_transition (c : Fin (r + 1)) (i i' : Fin (d c + 1)) :
    (frameViaFactor ((Proj (homogeneousSubmodule (Fin (d c + 1)) k)).homOfLE
        (coordinateOpenOverlap_le_left (R := k) i i')) (coordinateOpen (R := k) i).ι
        (coordinateOpenOverlap (R := k) i i').ι
        (Scheme.homOfLE_ι _ (coordinateOpenOverlap_le_left (R := k) i i'))
        (twistChartFrame d t n c i)).hom =
      (frameViaFactor ((Proj (homogeneousSubmodule (Fin (d c + 1)) k)).homOfLE
        (coordinateOpenOverlap_le_right (R := k) i i')) (coordinateOpen (R := k) i').ι
        (coordinateOpenOverlap (R := k) i i').ι
        (Scheme.homOfLE_ι _ (coordinateOpenOverlap_le_right (R := k) i i'))
        (twistChartFrame d t n c i')).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          ((coordinateOpenTransitionTopUnit (R := k) i i' ^ n c :
              Γ((coordinateOpenOverlap (R := k) i i').toScheme, ⊤)ˣ) :
            Γ((coordinateOpenOverlap (R := k) i i').toScheme, ⊤)) := by
  rw [twistChartFrame, twistChartFrame, ← pullbackIsoOfRestrictIso_restrictOpenTrivialization,
    ← pullbackIsoOfRestrictIso_restrictOpenTrivialization]
  simp only [pullbackIsoOfRestrictIso, Iso.trans_hom, Category.assoc,
    coordinateHyperplaneTwistTrivialization_restrict_transition (R := k) i i' (t c) (n c)]

/- The kernel check of this instantiation of `subopenFrame_transition` at the concrete coordinate
charts of projective space takes about 300s (the generic lemma itself checks instantly); hence the
raised heartbeat budget on this single declaration. -/
set_option maxHeartbeats 800000 in
/-- Factor frames of two charts differ by the pulled-back integer power of the coordinate ratio. -/
theorem signedFactorFrame_transition (c : Fin (r + 1)) (i i' : Fin (d c + 1)) (V : X.Opens)
    (h : V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) i) (h' : V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) i')
    (hO : V ≤ q c ⁻¹ᵁ coordinateOpenOverlap (R := k) i i') :
    (signedFactorFrame d q t n c i V h).hom = (signedFactorFrame d q t n c i' V h').hom ≫
      ModularCurves.unitEndomorphismOfTopSection
        (((q c).resLE (coordinateOpenOverlap (R := k) i i') V hO).appTop.hom
          ((coordinateOpenTransitionTopUnit (R := k) i i' ^ n c :
              Γ((coordinateOpenOverlap (R := k) i i').toScheme, ⊤)ˣ) :
            Γ((coordinateOpenOverlap (R := k) i i').toScheme, ⊤))) := by
  exact subopenFrame_transition (q c) (coordinateOpenOverlap_le_left (R := k) i i')
    (coordinateOpenOverlap_le_right (R := k) i i') h h' hO _ _ _
    (twistChartFrame_transition d t n c i i')

/-- The transition function between the frames of the charts `a` and `b` on `V`, as a section of
`𝒪_X` over `V`: `∏_c q_c^* (X_{b_c}/X_{a_c})^{n_c}`. -/
def signedTransition (a b : ∀ c, Fin (d c + 1)) (V : X.Opens)
    (hO : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpenOverlap (R := k) (a c) (b c)) : Γ(X, V) :=
  ∏ c, ((q c).appLE (coordinateOpenOverlap (R := k) (a c) (b c)) V (hO c)).hom
    ((coordinateOpenTransitionUnit (R := k) (a c) (b c) ^ n c :
        Γ(Proj (homogeneousSubmodule (Fin (d c + 1)) k),
          coordinateOpenOverlap (R := k) (a c) (b c))ˣ) :
      Γ(Proj (homogeneousSubmodule (Fin (d c + 1)) k), coordinateOpenOverlap (R := k) (a c) (b c)))

private theorem transitionTopUnit_zpow_coe {m : ℕ} (i i' : Fin (m + 1)) (e : ℤ) :
    ((coordinateOpenTransitionTopUnit (R := k) i i' ^ e :
        Γ((coordinateOpenOverlap (R := k) i i').toScheme, ⊤)ˣ) :
      Γ((coordinateOpenOverlap (R := k) i i').toScheme, ⊤)) =
      openTopSection (coordinateOpenOverlap (R := k) i i')
        ((coordinateOpenTransitionUnit (R := k) i i' ^ e :
            Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k), coordinateOpenOverlap (R := k) i i')ˣ) :
          Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k), coordinateOpenOverlap (R := k) i i')) := by
  rw [coordinateOpenTransitionTopUnit, ← map_zpow, Units.coe_map]
  rfl

/-- **Frame transition** (`lem:pm-frame-transition`): on an open `V` contained in the charts `a`
and `b`, `e_a = e_b · ∏_c q_c^* (X_{b_c}/X_{a_c})^{n_c}`. -/
theorem signedFrame_transition (a b : ∀ c, Fin (d c + 1)) (V : X.Opens)
    (ha : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c))
    (hb : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (b c))
    (hO : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpenOverlap (R := k) (a c) (b c)) :
    (signedFrame d q t n a V ha).hom = (signedFrame d q t n b V hb).hom ≫
      ModularCurves.unitEndomorphismOfTopSection
        (openTopSection V (signedTransition d q n a b V hO)) := by
  rw [signedTransition, openTopSection_prod]
  refine tensorFrame_hom_eq_comp_scalar V _ _ _ _ (fun c => ?_)
  show (signedFactorFrame d q t n c (a c) V (ha c)).hom =
    (signedFactorFrame d q t n c (b c) V (hb c)).hom ≫ _
  rw [signedFactorFrame_transition d q t n c (a c) (b c) V (ha c) (hb c) (hO c),
    transitionTopUnit_zpow_coe, resLE_appTop_openTopSection]

/-- An open contained in two charts of one factor lies in their overlap. -/
theorem le_preimage_overlap {Y : Scheme.{u}} {m : ℕ}
    (g : Y ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k))
    (i i' : Fin (m + 1)) {V : Y.Opens} (h : V ≤ g ⁻¹ᵁ coordinateOpen (R := k) i)
    (h' : V ≤ g ⁻¹ᵁ coordinateOpen (R := k) i') :
    V ≤ g ⁻¹ᵁ coordinateOpenOverlap (R := k) i i' := by
  intro x hx
  change g x ∈ coordinateOpenOverlap (R := k) i i'
  rw [coordinateOpenOverlap_eq]
  exact ⟨h hx, h' hx⟩

variable [IsIntegral X]

/-- The generic value of the pulled coordinate transition is the generic coordinate ratio. -/
theorem germ_appLE_transitionUnit {m : ℕ} (g : X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k))
    (i i' : Fin (m + 1))
    [Nonempty (g ⁻¹ᵁ coordinateOpen (R := k) i)] (V : X.Opens) [Nonempty V]
    (hO : V ≤ g ⁻¹ᵁ coordinateOpenOverlap (R := k) i i') (e : ℤ) :
    X.germToFunctionField V ((g.appLE (coordinateOpenOverlap (R := k) i i') V hO).hom
      ((coordinateOpenTransitionUnit (R := k) i i' ^ e :
          Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k), coordinateOpenOverlap (R := k) i i')ˣ) :
        Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k), coordinateOpenOverlap (R := k) i i'))) =
      ProjectiveChartFunctionFieldGeneration.coordinate g i i' ^ e := by
  let ψ := (X.germToFunctionField V).hom.comp (g.appLE (coordinateOpenOverlap (R := k) i i') V hO).hom
  have hψ := ringHom_unit_zpow ψ (coordinateOpenTransitionUnit (R := k) i i') e
  refine hψ.trans (congrArg (fun z => z ^ e) ?_)
  have hu : ((coordinateOpenTransitionUnit (R := k) i i' :
      Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k), coordinateOpenOverlap (R := k) i i')ˣ) :
        Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k), coordinateOpenOverlap (R := k) i i')) =
      (Proj (homogeneousSubmodule (Fin (m + 1)) k)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := k) i i')).op
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X i')
          (MvPolynomial.isHomogeneous_X k i')) := by
    rw [ProjectiveHomogeneousSections.coefficient_X]
    rfl
  have hle : V ≤ g ⁻¹ᵁ coordinateOpen (R := k) i :=
    hO.trans (fun x hx => coordinateOpenOverlap_le_left (R := k) i i' hx)
  change X.germToFunctionField V ((g.appLE (coordinateOpenOverlap (R := k) i i') V hO).hom
    ((coordinateOpenTransitionUnit (R := k) i i' :
      Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k), coordinateOpenOverlap (R := k) i i')ˣ) :
        Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k), coordinateOpenOverlap (R := k) i i'))) = _
  let coef := ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X i')
    (MvPolynomial.isHomogeneous_X k i')
  have hmap := congrArg (fun φ => φ.hom coef) (Scheme.Hom.map_appLE g hO
    (homOfLE (coordinateOpenOverlap_le_left (R := k) i i')).op)
  rw [hu]
  exact (congrArg (X.germToFunctionField V) hmap).trans
    (germToFunctionField_restrict (homOfLE hle) ((g.app (coordinateOpen (R := k) i)) coef))

end SignedFrames


/-! ### Frames on arbitrary opens, the pivot coefficient and joint charts -/

section Pivot

variable {k : Type u} [Field k] {X : Scheme.{u}} {r : ℕ} (d : Fin (r + 1) → ℕ)
  (q : ∀ c, X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = p) (t : ∀ c, Fin (d c + 1))
  (n : Fin (r + 1) → ℤ)

/-- The frame of `L(n)` on an open `V` contained in the chart `a`, in the restriction
formalism. -/
def signedChartFrameOn (a : ∀ c, Fin (d c + 1)) (V : X.Opens)
    (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c)) :
    (signedProjectiveLine d q t n).restrict V.ι ≅ unitObj V.toScheme :=
  restrictIsoOfPullbackIso _ _ (signedFrame d q t n a V hV)

/-- The same frame on the over-site of `V`. -/
def signedOverFrameOn (a : ∀ c, Fin (d c + 1)) (V : X.Opens)
    (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c)) :
    LocalBundleFrame (signedProjectiveLine d q t n) V :=
  overTrivializationOfRestrictIso _ _ (signedChartFrameOn d q t n a V hV)

/-- The generator `ε_a = ∏_c X_{a_c}^{n_c} ∈ Γ(V, L(n))` of the frame of the chart `a`. -/
def signedGeneratorOn (a : ∀ c, Fin (d c + 1)) (V : X.Opens)
    (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c)) :
    Γ(signedProjectiveLine d q t n, V) :=
  ModularCurves.overTrivializationSection _ _ (signedOverFrameOn d q t n a V hV) 1

/-- The restriction of a chart frame to a smaller open is the frame built there. -/
theorem restrictOpenTrivialization_signedChartFrameOn (a : ∀ c, Fin (d c + 1)) {V W : X.Opens}
    (hWV : W ≤ V) (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c)) :
    restrictOpenTrivialization hWV (signedChartFrameOn d q t n a V hV) =
      signedChartFrameOn d q t n a W (fun c => hWV.trans (hV c)) := by
  rw [← restrictIsoOfPullbackIso_pullbackIsoOfRestrictIso _ W
      (restrictOpenTrivialization hWV (signedChartFrameOn d q t n a V hV)),
    pullbackIsoOfRestrictIso_restrictOpenTrivialization, signedChartFrameOn,
    pullbackIsoOfRestrictIso_restrictIsoOfPullbackIso, frameViaFactor_signedFrame d q t n a hWV hV]
  rfl

/-- **Generators of two charts** (`lem:pm-pivot-coefficient`): on `W ⊆ V ∩ V'`,
`ε_b = κ ε_a` with `κ = ∏_c q_c^* (X_{b_c}/X_{a_c})^{n_c}`. -/
theorem signedGeneratorOn_transition (a b : ∀ c, Fin (d c + 1)) {V V' W : X.Opens}
    (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c))
    (hV' : ∀ c, V' ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (b c)) (hWV : W ≤ V) (hWV' : W ≤ V') :
    signedTransition d q n a b W (fun c => le_preimage_overlap (q c) (a c) (b c)
        (hWV.trans (hV c)) (hWV'.trans (hV' c))) •
      (signedProjectiveLine d q t n).presheaf.map (homOfLE hWV).op (signedGeneratorOn d q t n a V hV) =
    (signedProjectiveLine d q t n).presheaf.map (homOfLE hWV').op
      (signedGeneratorOn d q t n b V' hV') := by
  let L := signedProjectiveLine d q t n
  let hO := fun c => le_preimage_overlap (q c) (a c) (b c) (hWV.trans (hV c)) (hWV'.trans (hV' c))
  let κ := signedTransition d q n a b W hO
  have hopen : (restrictOpenTrivialization hWV (signedChartFrameOn d q t n a V hV)).hom =
      (restrictOpenTrivialization hWV' (signedChartFrameOn d q t n b V' hV')).hom ≫
        ModularCurves.unitEndomorphismOfTopSection (openTopSection W κ) := by
    rw [restrictOpenTrivialization_signedChartFrameOn, restrictOpenTrivialization_signedChartFrameOn]
    simp only [signedChartFrameOn, restrictIsoOfPullbackIso, Iso.trans_hom, Category.assoc]
    rw [signedFrame_transition d q t n a b W _ _ hO]
  have hover := ModularCurves.overTrivializationOfRestrictIso_hom_eq_comp_scalar L W _ _ κ hopen
  rw [overTrivializationOfRestrictOpenTrivialization hWV,
    overTrivializationOfRestrictOpenTrivialization hWV'] at hover
  have hsec := ModularCurves.overTrivializationSection_eq_of_transition L W _ _ κ κ 1 hover
    (one_mul κ).symm
  rw [signedGeneratorOn, signedGeneratorOn, ModularCurves.overTrivializationSection_restrict,
    ModularCurves.overTrivializationSection_restrict, map_one, map_one,
    ModularCurves.overTrivializationSection_smul, mul_one]
  exact hsec

variable [IsIntegral X]

/-- The pivot chart `z`, the generic chart of every factor. -/
abbrev signedPivot : ∀ c, Fin (d c + 1) := FiniteProjectiveNativeFieldModels.pivot q

theorem signedPivot_nonempty (c : Fin (r + 1)) :
    Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (signedPivot d q c)) :=
  (FiniteProjectiveNativeFieldModels.chartSite (q c)).property

/-- The pivot open `⋂_c q_c^{-1} D₊(X_{z_c})`. -/
def signedPivotOpen : X.Opens := ⨅ c, q c ⁻¹ᵁ coordinateOpen (R := k) (signedPivot d q c)

theorem signedPivotOpen_le (c : Fin (r + 1)) :
    signedPivotOpen d q ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (signedPivot d q c) :=
  iInf_le (fun c => q c ⁻¹ᵁ coordinateOpen (R := k) (signedPivot d q c)) c


/-- The generic value of the transition function. -/
theorem germ_signedTransition (a b : ∀ c, Fin (d c + 1))
    (ha : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (a c))) (V : X.Opens) [Nonempty V]
    (hO : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpenOverlap (R := k) (a c) (b c)) :
    X.germToFunctionField V (signedTransition d q n a b V hO) =
      ∏ c, (letI := ha c; ProjectiveChartFunctionFieldGeneration.coordinate (q c) (a c) (b c)) ^ n c := by
  rw [signedTransition, map_prod]
  apply Finset.prod_congr rfl
  intro c _
  let := ha c
  exact germ_appLE_transitionUnit (q c) (a c) (b c) V (hO c) (n c)

instance signedPivotOpen_nonempty : Nonempty (signedPivotOpen d q) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change genericPoint X ∈
    ((⨅ c, q c ⁻¹ᵁ coordinateOpen (R := k) (signedPivot d q c) : X.Opens) : Set X)
  rw [TopologicalSpace.Opens.coe_iInf]
  apply Set.mem_iInter.mpr
  intro c
  let := signedPivot_nonempty d q c
  exact genericPoint_mem_nonempty_open _

/-- The pivot frame. -/
def signedPivotFrame : LocalBundleFrame (signedProjectiveLine d q t n) (signedPivotOpen d q) :=
  signedOverFrameOn d q t n (signedPivot d q) (signedPivotOpen d q) (signedPivotOpen_le d q)

/-- The generic frame relative to the pivot generator `ε_z`. -/
def signedGenericFrame :
    genericBundleFiber (signedProjectiveLine d q t n) ≃ₗ[X.functionField] X.functionField :=
  genericBundleFiberFrame (signedPivotFrame d q t n)

/-- **The pivot coefficient** of a global section of `L(n)` (`def:pm-pivot-coefficient`): the
generic coordinate of `s` relative to the pivot generator. It depends only on the presentation,
not on the structure morphism. -/
def signedCoefficient (s : Γ(signedProjectiveLine d q t n, ⊤)) : X.functionField :=
  signedGenericFrame d q t n (bundleGenericGerm _ ⊤ s)

theorem signedCoefficient_injective : Function.Injective (signedCoefficient d q t n) :=
  (signedGenericFrame d q t n).injective.comp
    (bundleGenericGerm_global_injective
      (invertibleLineAtlas _ (signedProjectiveLine_isInvertible d q t n)))

theorem signedCoefficient_zero : signedCoefficient d q t n 0 = 0 := by
  rw [signedCoefficient, map_zero, map_zero]

/-- The generic value of a chart generator relative to the pivot generator. -/
theorem signedGenericFrame_generatorOn (a : ∀ c, Fin (d c + 1))
    (ha : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (a c))) (V : X.Opens) [Nonempty V]
    (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c)) :
    signedGenericFrame d q t n (genericFrameGenerator (signedOverFrameOn d q t n a V hV)) =
      (∏ c, (letI := ha c;
        ProjectiveChartFunctionFieldGeneration.coordinate (q c) (a c) (signedPivot d q c)) ^ n c)⁻¹ := by
  let L := signedProjectiveLine d q t n
  let z := signedPivot d q
  let P := signedPivotOpen d q
  let : Nonempty P := signedPivotOpen_nonempty d q
  let W := V ⊓ P
  have hWV : W ≤ V := inf_le_left
  have hWP : W ≤ P := inf_le_right
  let : Nonempty W := ⟨⟨genericPoint X, genericPoint_mem_nonempty_open V,
    genericPoint_mem_nonempty_open P⟩⟩
  let hO := fun c => le_preimage_overlap (q c) (a c) (z c) (hWV.trans (hV c))
    (hWP.trans (signedPivotOpen_le d q c))
  have hrel := signedGeneratorOn_transition d q t n a z hV (signedPivotOpen_le d q) hWV hWP
  have hgen : genericFrameGenerator (signedPivotFrame d q t n) =
      X.germToFunctionField W (signedTransition d q n a z W hO) •
        genericFrameGenerator (signedOverFrameOn d q t n a V hV) := by
    rw [genericFrameGenerator_eq, genericFrameGenerator_eq]
    have h₁ := L.presheaf.germ_res_apply (homOfLE hWP) (genericPoint X)
      (genericPoint_mem_nonempty_open W) (signedGeneratorOn d q t n z P (signedPivotOpen_le d q))
    have h₂ := L.presheaf.germ_res_apply (homOfLE hWV) (genericPoint X)
      (genericPoint_mem_nonempty_open W) (signedGeneratorOn d q t n a V hV)
    change L.presheaf.germ P (genericPoint X) _
        (signedGeneratorOn d q t n z P (signedPivotOpen_le d q)) =
      X.germToFunctionField W (signedTransition d q n a z W hO) •
        L.presheaf.germ V (genericPoint X) _ (signedGeneratorOn d q t n a V hV)
    rw [← h₁, ← h₂, ← hrel]
    exact (bundleGenericGerm L W).map_smulₛₗ _ _
  have hone : signedGenericFrame d q t n (genericFrameGenerator (signedPivotFrame d q t n)) = 1 :=
    genericBundleFiberFrame_generator _
  rw [hgen, LinearEquiv.map_smul, smul_eq_mul, germ_signedTransition d q n a z ha W hO] at hone
  exact eq_inv_of_mul_eq_one_right hone

/-- The pivot coefficient of a local section computed in the frame of a chart. -/
theorem signedGenericFrame_eq_chartOn (a : ∀ c, Fin (d c + 1))
    (ha : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (a c))) (V : X.Opens) [Nonempty V]
    (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c))
    (σ : Γ(signedProjectiveLine d q t n, V)) :
    signedGenericFrame d q t n (bundleGenericGerm _ _ σ) =
      X.germToFunctionField V (localFrameCoefficients (signedOverFrameOn d q t n a V hV) σ) *
        (∏ c, (letI := ha c;
          ProjectiveChartFunctionFieldGeneration.coordinate (q c) (a c) (signedPivot d q c)) ^ n c)⁻¹ := by
  rw [bundleGenericGerm_eq_coefficient_smul_generator (signedOverFrameOn d q t n a V hV) σ,
    LinearEquiv.map_smul, smul_eq_mul,
    signedGenericFrame_generatorOn d q t n a ha V hV]
  rfl

/-- The pivot coefficient of the local section with a prescribed chart coefficient. -/
theorem signedGenericFrame_sectionOn (a : ∀ c, Fin (d c + 1))
    (ha : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (a c))) (V : X.Opens) [Nonempty V]
    (hV : ∀ c, V ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (a c)) (x : Γ(X, V)) :
    signedGenericFrame d q t n (bundleGenericGerm _ _
        (ModularCurves.overTrivializationSection _ _ (signedOverFrameOn d q t n a V hV) x)) =
      X.germToFunctionField V x *
        (∏ c, (letI := ha c;
          ProjectiveChartFunctionFieldGeneration.coordinate (q c) (a c) (signedPivot d q c)) ^ n c)⁻¹ := by
  have hx : localFrameCoefficients (signedOverFrameOn d q t n a V hV)
      (ModularCurves.overTrivializationSection _ _ (signedOverFrameOn d q t n a V hV) x) = x :=
    ModularCurves.overTrivializationSection_coefficient (signedProjectiveLine d q t n) V
      (signedOverFrameOn d q t n a V hV) x
  rw [signedGenericFrame_eq_chartOn d q t n a ha V hV, hx]

/-- The model's chart denominator is the inverse of the generic transition to the pivot. -/
theorem chartDenZ_eq_inv_prod [IsClosedImmersion (q 0)] (j : ∀ c, Fin (d c + 1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    letI := p.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q p hp).chartDenZ j n =
      (∏ c, (letI := hj c;
        ProjectiveChartFunctionFieldGeneration.coordinate (q c) (j c) (signedPivot d q c)) ^ n c)⁻¹ := by
  let := p.stalkAlgebra (genericPoint X)
  rw [MultiModel.chartDenZ, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro c _
  let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (signedPivot d q c)) := signedPivot_nonempty d q c
  let := hj c
  change ProjectiveChartFunctionFieldGeneration.coordinate (q c) (signedPivot d q c) (j c) ^ n c = _
  have hinv : ProjectiveChartFunctionFieldGeneration.coordinate (q c) (signedPivot d q c) (j c) =
      (ProjectiveChartFunctionFieldGeneration.coordinate (q c) (j c) (signedPivot d q c))⁻¹ := by
    rw [← ProjectiveChartGenericTransitions.coordinate_div (q c) (j c) (signedPivot d q c) (j c),
      ProjectiveChartFunctionFieldGeneration.coordinate_self, one_div]
  rw [hinv, inv_zpow]

theorem prod_coordinate_ne_zero (j : ∀ c, Fin (d c + 1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    (∏ c, (letI := hj c;
      ProjectiveChartFunctionFieldGeneration.coordinate (q c) (j c) (signedPivot d q c)) ^ n c) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun c _ => zpow_ne_zero _ (by
    let := hj c
    let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (signedPivot d q c)) := signedPivot_nonempty d q c
    exact ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero (q c) (j c) (signedPivot d q c)))

/-! #### The joint (Segre) charts -/

/-- The joint chart `U_j = ⋂_c q_c^{-1} D₊(X_{j_c})`, the preimage of a Segre chart. -/
def signedJointOpen (j : ∀ c, Fin (d c + 1)) : X.Opens :=
  FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
    coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)

omit [IsIntegral X] in
theorem signedJointOpen_le (j : ∀ c, Fin (d c + 1)) (c : Fin (r + 1)) :
    signedJointOpen d q p hp j ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (j c) := by
  rw [signedJointOpen, OriginalProjectiveFamilyChartAlgebras.morphism_preimage_coordinateOpen]
  exact iInf_le (fun c => q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) c

omit [IsIntegral X] in
theorem signedJointOpen_isAffineOpen [IsClosedImmersion (q 0)] (j : ∀ c, Fin (d c + 1)) :
    IsAffineOpen (signedJointOpen d q p hp j) := by
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  exact (coordinateOpen_isAffineOpen (FiniteSegreOriginalProjectiveMaps.index d j)).preimage
    (FiniteSegreOriginalProjectiveMaps.morphism d q p hp)

theorem signedJointOpen_nonempty (j : ∀ c, Fin (d c + 1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    Nonempty (signedJointOpen d q p hp j) :=
  FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hj

omit [IsIntegral X] in
/-- The joint charts cover `X`. -/
theorem exists_mem_signedJointOpen (x : X) :
    ∃ j : ∀ c, Fin (d c + 1), x ∈ signedJointOpen d q p hp j := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  have hx : f x ∈ ⨆ a : Fin (FiniteSegreOriginalProjectiveMaps.dimension d + 1),
      coordinateOpen (R := k) a := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨j, hj⟩ := (FiniteSegreOriginalProjectiveMaps.index_bijective d).surjective a
  refine ⟨j, ?_⟩
  change f x ∈ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)
  rwa [hj]

/-- The frame of the signed line on the joint chart `U_j`. -/
abbrev signedChartFrame (j : ∀ c, Fin (d c + 1)) :
    (signedProjectiveLine d q t n).restrict (signedJointOpen d q p hp j).ι ≅
      unitObj (signedJointOpen d q p hp j).toScheme :=
  signedChartFrameOn d q t n j _ (signedJointOpen_le d q p hp j)

/-- The coefficient `s_j ∈ Γ(X, U_j)` of a global section in the chart frame. -/
def signedChartCoefficient [IsClosedImmersion (q 0)] (j : ∀ c, Fin (d c + 1))
    (s : Γ(signedProjectiveLine d q t n, ⊤)) : Γ(X, signedJointOpen d q p hp j) :=
  ModularCurves.localTrivializationCoefficient _ ⟨_, signedJointOpen_isAffineOpen d q p hp j⟩
    (signedChartFrame d q p hp t n j) s

/-- **The chart coefficients** (`lem:pm-pivot-coefficient`): for every chart `j` whose factor
charts are nonempty, `s_j = signedCoefficient s / z̃_j^n` in `K(X)`. -/
theorem germ_signedChartCoefficient [IsClosedImmersion (q 0)] (j : ∀ c, Fin (d c + 1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (s : Γ(signedProjectiveLine d q t n, ⊤)) :
    letI := signedJointOpen_nonempty d q p hp j hj
    letI := p.stalkAlgebra (genericPoint X)
    X.germToFunctionField (signedJointOpen d q p hp j) (signedChartCoefficient d q p hp t n j s) =
      signedCoefficient d q t n s /
        (FiniteProjectiveNativeFieldModels.model q p hp).chartDenZ j n := by
  let := signedJointOpen_nonempty d q p hp j hj
  let := p.stalkAlgebra (genericPoint X)
  let U : X.affineOpens := ⟨_, signedJointOpen_isAffineOpen d q p hp j⟩
  let : Nonempty U.1 := signedJointOpen_nonempty d q p hp j hj
  let L := signedProjectiveLine d q t n
  have hres : bundleGenericGerm L ⊤ s =
      bundleGenericGerm L U.1 (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) :=
    (L.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X)
      (genericPoint_mem_nonempty_open U.1) s).symm
  have h := signedGenericFrame_eq_chartOn d q t n j hj U.1 (signedJointOpen_le d q p hp j)
    (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s)
  rw [← hres] at h
  have hc : localFrameCoefficients (signedOverFrameOn d q t n j U.1 (signedJointOpen_le d q p hp j))
      (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) = signedChartCoefficient d q p hp t n j s :=
    localFrameCoefficients_restrict_top U (signedChartFrame d q p hp t n j) s
  rw [hc] at h
  change signedCoefficient d q t n s = _ at h
  rw [chartDenZ_eq_inv_prod d q p hp n j hj, h, div_inv_eq_mul, mul_assoc,
    inv_mul_cancel₀ (prod_coordinate_ne_zero d q n j hj), mul_one]

end Pivot

end EnvelopeProperty.Variety
