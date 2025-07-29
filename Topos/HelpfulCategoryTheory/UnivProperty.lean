import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Topos.HelpfulCategoryTheory.IsEqualizer

namespace CategoryTheory.Limits

open CategoryTheory Limits IsPullback IsPushout

variable {C : Type*} [Category C]

namespace IsPullback

abbrev UnivProp {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) :=
  (fst ≫ f = snd ≫ g) ∧ ∀ {S : C} (s_fst : S ⟶ X) (s_snd : S ⟶ Y), (s_fst ≫ f = s_snd ≫ g) → (∃! (lift : S ⟶ P), (lift ≫ fst = s_fst) ∧ (lift ≫ snd = s_snd))

lemma IsPullbackImpUnivProp {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : IsPullback fst snd f g → UnivProp fst snd f g := by {
  intro h
  apply And.intro
  · exact h.w
  · intro S s_fst s_snd w
    use h.lift s_fst s_snd w
    simp
    intro y h_fst h_snd
    rw [← h.lift_fst s_fst s_snd w] at h_fst
    rw [← h.lift_snd s_fst s_snd w] at h_snd
    exact IsPullback.hom_ext h h_fst h_snd
}

lemma UnivPropImpIsPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : UnivProp fst snd f g → IsPullback fst snd f g := fun h ↦ {
  w := h.1
  isLimit' := ⟨PullbackCone.IsLimit.mk h.1 (fun (s : PullbackCone f g) ↦ (h.2 s.fst s.snd s.condition).choose) (fun s ↦ ((fun (s : PullbackCone f g) ↦ (h.2 s.fst s.snd s.condition).choose_spec) s).1.1) (fun s ↦ ((fun (s : PullbackCone f g) ↦ (h.2 s.fst s.snd s.condition).choose_spec) s).1.2) (fun s m hm_fst hm_snd ↦ ((fun (s : PullbackCone f g) ↦ (h.2 s.fst s.snd s.condition).choose_spec) s).2 m ⟨hm_fst, hm_snd⟩)⟩
}

theorem IsPullbackIffUnivProp {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : IsPullback fst snd f g ↔ UnivProp fst snd f g :=
  Iff.intro (IsPullbackImpUnivProp fst snd f g) (UnivPropImpIsPullback fst snd f g)

end IsPullback

namespace IsEqualizer

abbrev UnivProp {I X Y : C} (ι : I ⟶ X) (f g : X ⟶ Y) :=
  (ι ≫ f = ι ≫ g) ∧ ∀ {S : C} (s_ι : S ⟶ X), (s_ι ≫ f = s_ι ≫ g) → (∃! (lift : S ⟶ I), (lift ≫ ι = s_ι))

lemma IsEqualizerImpUnivProp {I X Y : C} (ι : I ⟶ X) (f g : X ⟶ Y) : IsEqualizer ι f g → UnivProp ι f g := by {
  intro h
  apply And.intro
  · exact h.w
  · intro S s_ι w
    use h.lift s_ι w
    simp
    intro y h_ι
    rw [← h.lift_ι s_ι w] at h_ι
    exact IsEqualizer.hom_ext h h_ι
}

lemma UnivPropImpIsPullback {I X Y : C} (ι : I ⟶ X) (f g : X ⟶ Y) : UnivProp ι f g → IsEqualizer ι f g := fun h ↦ {
  w := h.1
  isLimit' := ⟨Fork.IsLimit.mk (Fork.ofι ι h.1) (fun (s : Fork f g) ↦ (h.2 s.ι s.condition).choose) (fun s ↦ ((fun (s : Fork f g) ↦ (h.2 s.ι s.condition).choose_spec) s).1) (fun s m hm ↦ ((fun (s : Fork f g) ↦ (h.2 s.ι s.condition).choose_spec) s).2 m hm)⟩
}

theorem IsEqualizerIffUnivProp {I X Y : C} (ι : I ⟶ X) (f g : X ⟶ Y) : IsEqualizer ι f g ↔ UnivProp ι f g :=
  Iff.intro (IsEqualizerImpUnivProp ι f g) (UnivPropImpIsPullback ι f g)

theorem PushoutUnivPropEqualizerUnivProp {I X Y : C} (ι : I ⟶ X) (f g : X ⟶ Y) : IsPullback.UnivProp ι ι f g → UnivProp ι f g := by {
  intro h
  refine ⟨h.1, ?_⟩
  intro s s_ι w
  refine ⟨(h.2 _ _ w).choose, ?_⟩
  apply And.intro (h.2 _ _ w).choose_spec.1.1
  intro y hy
  exact (h.2 _ _ w).choose_spec.2 y (And.intro hy hy)
}
