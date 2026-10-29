import Lean
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartPullbackRestriction
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareForward
import ModularCurves.Picard.DualPullback.Square

/-! # The fixed native pullback differential square on a whole chart

The already checked native forward square is applied with its two sides
exchanged. The reverse pullback congruence is the original inverse map;
only the final equality-to-hom factors are composed. Every source and
base comparison remains the fixed original native one.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
universe u v w
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Use the original category-to-quiver projection at every native map
-- interface. A reflexive-quiver instance would introduce a different
-- definitional spelling of these same arrow types.
local notation:10 A " ⟶ₙ " B =>
  @Quiver.Hom _ (@CategoryStruct.toQuiver _ (@Category.toCategoryStruct _ inferInstance)) A B

/-- Cancel the original equality-to-hom maps in an abstract category.
The equality proofs themselves are retained as inputs, so native transports
are never rebuilt through a different family of module objects. -/
private theorem swapped_forward_transport
    {E : Type v} [Category.{w} E] {L L₁ L₂ A B C T₀ T₁ T₂ T₃ : E}
    (s : L ⟶ₙ L₁) (r r' : L₁ ⟶ₙ L₂) (z : L₂ ⟶ₙ A)
    (a : A ⟶ₙ B) (P : B ⟶ₙ T₃) (D : L ⟶ₙ C) (V : C ⟶ₙ T₀)
    (hr : r = r') (h₀ : T₀ = T₁) (h₁ : T₁ = T₂) (h₂ : T₃ = T₂)
    (hfield : T₀ = T₃)
    (hf : (s ≫ r ≫ z) ≫ a ≫ P ≫ eqToHom h₂ =
      D ≫ V ≫ eqToHom h₀ ≫ eqToHom h₁) :
    D ≫ V ≫ eqToHom hfield = (s ≫ r' ≫ z ≫ a) ≫ P := by
  subst r'
  have ht := congrArg (fun q => q ≫ eqToHom h₂.symm) hf
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id, Category.id_comp] using ht.symm

/-- Keep the composed-functor domains of the native comparison word and
the nested-functor domains of the native differential maps separately.
Their conversion takes place with opaque functors in this lemma. -/
private theorem swapped_forward_transport_original_indices
    {C₀ C₁ C₂ E : Type v} [Category.{w} C₀] [Category.{w} C₁]
    [Category.{w} C₂] [Category.{w} E]
    (Fg : C₀ ⥤ C₁) (Fp : C₁ ⥤ E) (Fπ : C₀ ⥤ C₂) (Fv : C₂ ⥤ E) (M : C₀)
    {L₁ L₂ A C T₀ T₁ T₂ T₃ : E}
    (s : (Fπ ⋙ Fv).obj M ⟶ₙ L₁) (r r' : L₁ ⟶ₙ L₂)
    (z : L₂ ⟶ₙ (Fg ⋙ Fp).obj M)
    (a : Fp.obj (Fg.obj M) ⟶ₙ A) (P : A ⟶ₙ T₃)
    (D : Fv.obj (Fπ.obj M) ⟶ₙ C) (V : C ⟶ₙ T₀)
    (hr : r = r') (h₀ : T₀ = T₁) (h₁ : T₁ = T₂) (h₂ : T₃ = T₂)
    (hfield : T₀ = T₃)
    (hf : CategoryStruct.comp (X := (Fπ ⋙ Fv).obj M)
        (Y := (Fg ⋙ Fp).obj M) (Z := T₂)
        (CategoryStruct.comp (X := (Fπ ⋙ Fv).obj M) (Y := L₁)
          (Z := (Fg ⋙ Fp).obj M) s
          (CategoryStruct.comp (X := L₁) (Y := L₂) (Z := (Fg ⋙ Fp).obj M) r z))
        (CategoryStruct.comp (X := (Fg ⋙ Fp).obj M) (Y := A) (Z := T₂) a
          (CategoryStruct.comp (X := A) (Y := T₃) (Z := T₂)
            P (eqToHom h₂))) =
      CategoryStruct.comp (X := Fv.obj (Fπ.obj M)) (Y := C) (Z := T₂)
        D (CategoryStruct.comp (X := C) (Y := T₀) (Z := T₂) V
          (CategoryStruct.comp (X := T₀) (Y := T₁) (Z := T₂)
            (eqToHom h₀) (eqToHom h₁)))) :
    CategoryStruct.comp (X := Fv.obj (Fπ.obj M)) (Y := C) (Z := T₃)
        D (CategoryStruct.comp (X := C) (Y := T₀) (Z := T₃)
          V (eqToHom hfield)) =
      CategoryStruct.comp (X := (Fπ ⋙ Fv).obj M) (Y := A) (Z := T₃)
        (CategoryStruct.comp (X := (Fπ ⋙ Fv).obj M) (Y := L₁) (Z := A) s
          (CategoryStruct.comp (X := L₁) (Y := L₂) (Z := A) r'
            (CategoryStruct.comp (X := L₂) (Y := (Fg ⋙ Fp).obj M) (Z := A) z a))) P := by
  exact swapped_forward_transport s r r' z a P D V hr h₀ h₁ h₂ hfield hf

/-- Equality of the original natural transformations is evaluated before
any concrete pullback functor or exterior module is specialized. -/
private theorem native_app_of_eq {C D : Type v} [Category.{w} C] [Category.{w} D]
    {F G : C ⥤ D} {a b : F ⟶ₙ G} (h : a = b) (M : C) : a.app M = b.app M :=
  congrArg (fun e => e.app M) h

/-- Read only the type of the actual original proof application. The
returned type and the proof below are still checked by the declaration kernel. -/
elab "nativeDifferentialType%(" proof:term ")" : term => do
  let proof ← Lean.Elab.Term.elabTerm proof none
  Lean.Meta.inferType proof

/-- The same native raw pullback square with its actual inverse comparison.
Its proposition is the unchanged result of the original-index application,
so no second concrete spelling of its module indices is introduced. -/
theorem fixed_pullback_differential_square
    {k : Type u} [Field k] {X Y A B : Scheme.{u}}
    (f : X ⟶ₙ Spec (.of k)) (g : A ⟶ₙ X) (π : Y ⟶ₙ X)
    (p : B ⟶ₙ A) (v : B ⟶ₙ Y) (w : p ≫ g = v ≫ π) (n : ℕ) :
    nativeDifferentialType%(
  swapped_forward_transport_original_indices
    (pullback g) (pullback p) (pullback π) (pullback v) (exteriorCotangentSheaf f n)
    ((pullbackComp v π).hom.app (exteriorCotangentSheaf f n))
    ((pullbackCongr w.symm).hom.app (exteriorCotangentSheaf f n))
    ((pullbackCongr w).inv.app (exteriorCotangentSheaf f n))
    ((pullbackComp p g).inv.app (exteriorCotangentSheaf f n))
    ((pullback p).map (exteriorCotangentSheafPullbackMap f g n))
    (exteriorCotangentSheafPullbackMap (g ≫ f) p n)
    ((pullback v).map (exteriorCotangentSheafPullbackMap f π n))
    (exteriorCotangentSheafPullbackMap (π ≫ f) v n)
    (native_app_of_eq (pullbackCongr_inv w).symm (exteriorCotangentSheaf f n))
    (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc v π f).symm)
    (congrArg (fun a => exteriorCotangentSheaf (a ≫ f) n) w.symm)
    (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc p g f).symm)
    (congrArg (fun a => exteriorCotangentSheaf a n)
      (show v ≫ (π ≫ f) = p ≫ (g ≫ f) by
        rw [← Category.assoc, ← w, Category.assoc]))
    (NadelBlowupCanonicalSquareForward.whole_forward_square f π g v p w.symm n)
    ) :=
  swapped_forward_transport_original_indices
    (pullback g) (pullback p) (pullback π) (pullback v) (exteriorCotangentSheaf f n)
    ((pullbackComp v π).hom.app (exteriorCotangentSheaf f n))
    ((pullbackCongr w.symm).hom.app (exteriorCotangentSheaf f n))
    ((pullbackCongr w).inv.app (exteriorCotangentSheaf f n))
    ((pullbackComp p g).inv.app (exteriorCotangentSheaf f n))
    ((pullback p).map (exteriorCotangentSheafPullbackMap f g n))
    (exteriorCotangentSheafPullbackMap (g ≫ f) p n)
    ((pullback v).map (exteriorCotangentSheafPullbackMap f π n))
    (exteriorCotangentSheafPullbackMap (π ≫ f) v n)
    (native_app_of_eq (pullbackCongr_inv w).symm (exteriorCotangentSheaf f n))
    (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc v π f).symm)
    (congrArg (fun a => exteriorCotangentSheaf (a ≫ f) n) w.symm)
    (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc p g f).symm)
    (congrArg (fun a => exteriorCotangentSheaf a n)
      (show v ≫ (π ≫ f) = p ≫ (g ≫ f) by
        rw [← Category.assoc, ← w, Category.assoc]))
    (NadelBlowupCanonicalSquareForward.whole_forward_square f π g v p w.symm n)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
