import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

universe v u u₂

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {W X Y R : C} (f : X ⟶ Y) (a b : Y ⟶ R)

abbrev IsCokernelPair := IsPushout f f a b

namespace IsCokernelPair

/-- The data expressing that `(a, b)` is a kernel pair is subsingleton. -/
instance : Subsingleton (IsCokernelPair f a b) :=
  ⟨fun P Q => by
    cases P
    cases Q
    congr ⟩

/-- If `f` is a monomorphism, then `(𝟙 _, 𝟙 _)` is a kernel pair for `f`. -/
theorem id_of_epi [Epi f] : IsCokernelPair f (𝟙 _) (𝟙 _) :=
  ⟨⟨rfl⟩, ⟨PushoutCocone.isColimitMkIdId _⟩⟩

instance [Epi f] : Inhabited (IsCokernelPair f (𝟙 _) (𝟙 _)) :=
  ⟨id_of_epi f⟩

variable {f a b}

-- Porting note: `lift` and the two following simp lemmas were introduced to ease the port
/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
noncomputable def desc {S : C} (k : IsCokernelPair f a b) (p q : Y ⟶ S) (w : f ≫ p = f ≫ q) :
    R ⟶ S :=
  PushoutCocone.IsColimit.desc k.isColimit _ _ w

@[reassoc (attr := simp)]
lemma inl_desc {S : C} (k : IsCokernelPair f a b) (p q : Y ⟶ S) (w : f ≫ p = f ≫ q) :
    a ≫ k.desc p q w = p :=
  PushoutCocone.IsColimit.inl_desc k.isColimit p q w

@[reassoc (attr := simp)]
lemma lift_snd {S : C} (k : IsCokernelPair f a b) (p q : Y ⟶ S) (w : f ≫ p = f ≫ q) :
    b ≫ k.desc p q w = q :=
  PushoutCocone.IsColimit.inr_desc k.isColimit p q w
/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
noncomputable def desc' {S : C} (k : IsCokernelPair f a b) (p q : Y ⟶ S) (w : f ≫ p = f ≫ q) :
    { t : R ⟶ S // a ≫ t = p ∧ b ≫ t = q } :=
  ⟨k.desc p q w, by simp⟩

/--
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `a ≫ f₁ = b ≫ f₁`, then `(a,b)` is a kernel pair for
just `f₁`.
That is, to show that `(a,b)` is a kernel pair for `f₁` it suffices to only show the square
commutes, rather than to additionally show it's a pullback.
-/
theorem cancel_left {f₁ : X ⟶ Y} {f₂ : W ⟶ X} (comm : f₁ ≫ a = f₁ ≫ b)
    (big_k : IsCokernelPair (f₂ ≫ f₁) a b) : IsCokernelPair f₁ a b :=
  { w := comm
    isColimit' :=
      ⟨PushoutCocone.isColimitAux' _ fun s => by
        let s' : PushoutCocone (f₂ ≫ f₁) (f₂ ≫ f₁) :=
          PushoutCocone.mk s.inl s.inr (by {rw[assoc, assoc]; exact congrArg (CategoryStruct.comp f₂) s.condition})
        refine ⟨big_k.isColimit.desc s', big_k.isColimit.fac _ WalkingCospan.left,
          big_k.isColimit.fac _ WalkingCospan.right, fun m₁ m₂ => ?_⟩
        apply big_k.isColimit.hom_ext
        refine (PushoutCocone.mk a b ?_ : PushoutCocone (f₂ ≫ f₁) _).coequalizer_ext ?_ ?_
        · rw[assoc, assoc]; exact congrArg (CategoryStruct.comp f₂) comm
        · apply m₁.trans (big_k.isColimit.fac s' WalkingCospan.left).symm
        · apply m₂.trans (big_k.isColimit.fac s' WalkingCospan.right).symm⟩ }

/-- If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `f₂` is mono, then `(a,b)` is a kernel pair for
just `f₁`.
The converse of `comp_of_mono`.
-/
theorem cancel_left_of_epi {f₁ : X ⟶ Y} {f₂ : W ⟶ X} [Epi f₂]
    (big_k : IsCokernelPair (f₂ ≫ f₁) a b) : IsCokernelPair f₁ a b :=
  cancel_left (by rw [← cancel_epi f₂, ← assoc, ← assoc, big_k.w]) big_k

/--
If `(a,b)` is a kernel pair for `f₁` and `f₂` is mono, then `(a,b)` is a kernel pair for `f₁ ≫ f₂`.
The converse of `cancel_right_of_mono`.
-/
theorem comp_of_epi {f₁ : X ⟶ Y} {f₂ : W ⟶ X} [Epi f₂] (small_k : IsCokernelPair f₁ a b) :
    IsCokernelPair (f₂ ≫ f₁) a b :=
  { w := by rw [assoc, assoc, small_k.w]
    isColimit' := ⟨by
      refine PushoutCocone.isColimitAux _
        (fun s => small_k.desc s.inl s.inr (by rw [← cancel_epi f₂, ← assoc, s.condition, assoc]))
        (by simp) (by simp) ?_
      intro s m hm
      apply small_k.isColimit.hom_ext
      apply PushoutCocone.coequalizer_ext small_k.cocone _ _
      · exact (hm WalkingCospan.left).trans (by simp)
      · exact (hm WalkingCospan.right).trans (by simp)⟩ }

/--
If `(a,b)` is the kernel pair of `f`, and `f` is a coequalizer morphism for some parallel pair, then
`f` is a coequalizer morphism of `a` and `b`.
-/
def toEqualizer (k : IsCokernelPair f a b) [r : RegularMono f] : IsLimit (Fork.ofι f k.w) := by
  let t := k.isColimit.desc (PushoutCocone.mk _ _ r.w)
  have ht : a ≫ t = r.left := k.isColimit.fac _ WalkingCospan.left
  have kt : b ≫ t = r.right := k.isColimit.fac _ WalkingCospan.right
  refine Fork.IsLimit.mk _
    (fun s => Fork.IsLimit.lift r.isLimit s.ι
      (by rw [← ht, ← assoc, s.condition, assoc, kt]))
    (fun s => ?_) (fun s m w => ?_)
  · apply Fork.IsLimit.lift_ι' r.isLimit
  · apply Fork.IsLimit.hom_ext r.isLimit
    exact w.trans (Fork.IsLimit.lift_ι' r.isLimit _ _).symm



/- If `a₁ a₂ : A ⟶ Y` is a kernel pair for `g : Y ⟶ Z`, then `a₁ ×[Z] X` and `a₂ ×[Z] X`
(`A ×[Z] X ⟶ Y ×[Z] X`) is a kernel pair for `Y ×[Z] X ⟶ X`.

protected theorem pushout {W X Y A : C} {g : W ⟶ X} {a₁ a₂ : X ⟶ A} (h : IsCokernelPair g a₁ a₂)
    (f : W ⟶ Y) [HasPushout f g] [HasPushout f (g ≫ a₁)] :
    IsCokernelPair (pushout.inl f g)
      (pushout.map f _ f _ (𝟙 Y) a₁ (𝟙 W) (by simp) <| Eq.symm (id_comp _))
      (pushout.map _ _ _ _ (𝟙 Y) a₂ (𝟙 W) (by simp) <| (Eq.symm (id_comp _)).trans (by rw [h.1.1])) := by
  refine ⟨⟨by rw [pullback.lift_fst, pullback.lift_fst]⟩, ⟨PullbackCone.isLimitAux _
    (fun s => pullback.lift (s.fst ≫ pullback.fst _ _)
      (h.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.snd _ _) ?_ ) ?_) (fun s => ?_)
        (fun s => ?_) (fun s m hm => ?_)⟩⟩
  · simp_rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition]
  · simp only [assoc, lift_fst_assoc, pullback.condition]
  · ext <;> simp
  · ext
    · simp [s.condition]
    · simp
  · #adaptation_note /-- nightly-2024-04-01
    This `symm` (or the following ones that undo it) wasn't previously necessary. -/
    symm
    apply pullback.hom_ext
    · symm
      simpa using hm WalkingCospan.left =≫ pullback.fst f g
    · symm
      apply PullbackCone.IsLimit.hom_ext h.isLimit
      · simpa using hm WalkingCospan.left =≫ pullback.snd f g
      · simpa using hm WalkingCospan.right =≫ pullback.snd f g

theorem mono_of_isIso_fst (h : IsKernelPair f a b) [IsIso a] : Mono f := by
  obtain ⟨l, h₁, h₂⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit (𝟙 _) (𝟙 _) (by simp [h.w])
  rw [IsPullback.cone_fst, ← IsIso.eq_comp_inv, Category.id_comp] at h₁
  rw [h₁, IsIso.inv_comp_eq, Category.comp_id] at h₂
  constructor
  intro Z g₁ g₂ e
  obtain ⟨l', rfl, rfl⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit _ _ e
  rw [IsPullback.cone_fst, h₂]

theorem isIso_of_mono (h : IsKernelPair f a b) [Mono f] : IsIso a := by
  rw [←
    show _ = a from
      (Category.comp_id _).symm.trans
        ((IsKernelPair.id_of_mono f).isLimit.conePointUniqueUpToIso_inv_comp h.isLimit
          WalkingCospan.left)]
  infer_instance

theorem of_isIso_of_mono [IsIso a] [Mono f] : IsKernelPair f a a := by
  change IsPullback _ _ _ _
  convert (IsPullback.of_horiz_isIso ⟨(rfl : a ≫ 𝟙 X = _ )⟩).paste_vert (IsKernelPair.id_of_mono f)
  all_goals { simp }
-/

end IsCokernelPair

end CategoryTheory
