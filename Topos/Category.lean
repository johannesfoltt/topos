import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.CommSq


namespace CategoryTheory

open CategoryTheory Category Limits


universe u v
variable {C : Type u} [Category.{v} C]
variable {J : Type v} [SmallCategory J]

variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

#check IsPullback

structure HasPullbackTop (left : W ⟶ Y) (bottom : Y ⟶ Z) (right : X ⟶ Z) where
  top : W ⟶ X
  comm : top ≫ right = left ≫ bottom
  pb : IsLimit (PullbackCone.mk top left comm)

attribute [reassoc] HasPullbackTop.comm


section HasPullbackTop

noncomputable def ofIsPullback
  {left : W ⟶ Y} {bottom : Y ⟶ Z} {top : W ⟶ X} {right : X ⟶ Z}
  {comm : top ≫ right = left ≫ bottom }
  (pb : IsPullback top left right bottom) :
  HasPullbackTop left bottom right where
    top := top
    comm := comm
    pb := Classical.choice pb.isLimit'


def uniqueTop (left : W ⟶ Y) (bottom : Y ⟶ Z) (right : X ⟶ Z) [Mono right]
  (P Q : HasPullbackTop left bottom right) : P.top = Q.top := by
    rw [←cancel_mono right]
    rw [P.comm, Q.comm]


end HasPullbackTop

namespace IsLimit

def mk' (t : PullbackCone f g)
  (create : Π (s : PullbackCone f g), {l : s.pt ⟶ t.pt // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd ∧ ∀ {m : s.pt ⟶ t.pt}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l}) :
  IsLimit t :=
    PullbackCone.isLimitAux' t create

def mk'' (t : PullbackCone f g) [Mono f]
  (create : Π (s : PullbackCone f g), {l : s.pt ⟶ t.pt // l ≫ t.snd = s.snd ∧ ∀ {m : s.pt ⟶ t.pt}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l}) :
  IsLimit t :=
    mk' t <| by
      intro s
      refine ⟨(create s).1, ?_, (create s).2.1, @λ m m₁ m₂ => (create s).2.2 m₁ m₂⟩
      rw [← cancel_mono f, assoc, t.condition, s.condition, reassoc_of% (create s).2.1]


def mk''' (t : PullbackCone f g) [Mono f] (q : Mono t.snd)
  (create : Π (s : PullbackCone f g), {l : s.pt ⟶ t.pt // l ≫ t.snd = s.snd}) :
  IsLimit t :=
    mk' t <| by
      intro s
      refine ⟨(create s).1, ?_, (create s).2, @λ m _ m₂ => ?_⟩
      rw [← cancel_mono f, assoc, t.condition, s.condition, reassoc_of% (create s).2]
      rw [← cancel_mono t.snd, m₂, (create s).2]

end IsLimit


theorem PullbackMonoIsMono (c : PullbackCone f g) [Mono f] (t : IsLimit c) : Mono c.snd :=
  ⟨@λ Z h k eq => by
    apply t.hom_ext
    apply PullbackCone.equalizer_ext
    rw [← cancel_mono f, assoc, c.condition, reassoc_of% eq, assoc, c.condition]
    assumption
  ⟩

theorem PullbackSquareOfLeftIsIso {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z) [Mono h] [IsIso g] (comm : f ≫ h = g ≫ k) :
  IsLimit (PullbackCone.mk _ _ comm) := by
    apply IsLimit.mk'''
    dsimp [PullbackCone.mk]
    simp only [IsIso.mono_of_iso]
    intro s
    exact ⟨s.snd ≫ inv g, by erw [assoc, IsIso.inv_hom_id g, comp_id]⟩

theorem left_iso_has_pullback_top {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z) [Mono h] [IsIso g] (comm : f ≫ h = g ≫ k) :
  HasPullbackTop g k h where
    top := f
    comm := comm
    pb := PullbackSquareOfLeftIsIso f g h k comm
