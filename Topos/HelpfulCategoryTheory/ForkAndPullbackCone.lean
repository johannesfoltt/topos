import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive


namespace CategoryTheory.Limits

open Category Limits

def WalkingCospanToWalkingParallelPair : WalkingCospan ⥤ WalkingParallelPair where
  obj
    | WalkingCospan.left => WalkingParallelPair.zero
    | WalkingCospan.right => WalkingParallelPair.zero
    | WalkingCospan.one => WalkingParallelPair.one
  map
    | WalkingCospan.Hom.inl => WalkingParallelPairHom.left
    | WalkingCospan.Hom.inr => WalkingParallelPairHom.right
    | WalkingCospan.Hom.id _ => WalkingParallelPairHom.id _
  map_comp := by
    intro X Y Z f g
    rcases f
    · rfl
    · rcases g
      · simp

def WalkingSpanToWalkingParallelPair : WalkingSpan ⥤ WalkingParallelPair where
  obj
    | WalkingSpan.left => WalkingParallelPair.one
    | WalkingSpan.right => WalkingParallelPair.one
    | WalkingSpan.zero => WalkingParallelPair.zero
  map
    | WalkingSpan.Hom.fst => WalkingParallelPairHom.left
    | WalkingSpan.Hom.snd => WalkingParallelPairHom.right
    | WalkingSpan.Hom.id _ => WalkingParallelPairHom.id _
  map_comp := by
    intro X Y Z f g
    rcases f
    · rfl
    · rcases g
      · simp

variable {C : Type*} [Category C]
variable {X Y : C} {f g : X ⟶ Y}

def ParallelPairCospanIso_app : (j : WalkingCospan) → (WalkingCospanToWalkingParallelPair ⋙ parallelPair f g).obj j ≅ (cospan f g).obj j := fun j ↦
  match j with
    | WalkingCospan.left => by {rfl}
    | WalkingCospan.right => by {rfl}
    | WalkingCospan.one => by {rfl}

def ParallelPairCospanIso_naturality :  ∀ {j k : WalkingCospan} (m : j ⟶ k), (WalkingCospanToWalkingParallelPair ⋙ parallelPair f g).map m ≫ (ParallelPairCospanIso_app k).hom = (ParallelPairCospanIso_app j).hom ≫ (cospan f g).map m := fun m ↦
  match m with
    | WalkingCospan.Hom.inl => by {unfold ParallelPairCospanIso_app; simp; rfl}
    | WalkingCospan.Hom.inr => by {unfold ParallelPairCospanIso_app; simp; rfl}
    | WalkingCospan.Hom.id _ => by {unfold ParallelPairCospanIso_app; simp}

variable (f g)

def ParallelPairCospanIso : WalkingCospanToWalkingParallelPair ⋙ parallelPair f g ≅ cospan f g :=
  NatIso.ofComponents ParallelPairCospanIso_app ParallelPairCospanIso_naturality

variable {f g}

def help_Iso_Cospan (c : Cone (WalkingCospanToWalkingParallelPair ⋙ parallelPair f g)) := IsLimit.equivOfNatIsoOfIso (ParallelPairCospanIso f g) c ((CategoryTheory.Limits.Cones.postcomposeEquivalence (ParallelPairCospanIso f g)).functor.obj c) (by rfl)

def help_IsLimit_Whisker_Of_IsLimit {c : Fork f g} (hc : IsLimit c) : IsLimit (Cone.whisker WalkingCospanToWalkingParallelPair c) where
  lift := sorry

def ParallelPairSpanIso_app : (j : WalkingSpan) → (WalkingSpanToWalkingParallelPair ⋙ parallelPair f g).obj j ≅ (span f g).obj j := fun j ↦
  match j with
    | WalkingCospan.left => by {rfl}
    | WalkingCospan.right => by {rfl}
    | WalkingCospan.one => by {rfl}

def ParallelPairSpanIso_naturality :  ∀ {j k : WalkingSpan} (m : j ⟶ k), (WalkingSpanToWalkingParallelPair ⋙ parallelPair f g).map m ≫ (ParallelPairSpanIso_app k).hom = (ParallelPairSpanIso_app j).hom ≫ (span f g).map m := fun m ↦
  match m with
    | WalkingSpan.Hom.fst => by {unfold ParallelPairSpanIso_app; simp; rfl}
    | WalkingSpan.Hom.snd => by {unfold ParallelPairSpanIso_app; simp; rfl}
    | WalkingSpan.Hom.id _ => by {unfold ParallelPairSpanIso_app; simp}

variable (f g)

def ParallelPairSpanIso : WalkingSpanToWalkingParallelPair ⋙ parallelPair f g ≅ span f g :=
  NatIso.ofComponents ParallelPairSpanIso_app ParallelPairSpanIso_naturality

variable {f g}

def help_Iso_Span (c : Cocone (WalkingSpanToWalkingParallelPair ⋙ parallelPair f g)) := IsColimit.equivOfNatIsoOfIso (ParallelPairSpanIso f g) c ((CategoryTheory.Limits.Cocones.precomposeEquivalence (ParallelPairSpanIso f g)).inverse.obj c) (by rfl)

def PullbackCone.ofFork (c : Fork f g) : PullbackCone f g :=
  (CategoryTheory.Limits.Cones.postcomposeEquivalence (ParallelPairCospanIso f g)).functor.obj (Cone.whisker WalkingCospanToWalkingParallelPair c)

def Cofork.mkPushoutCocone (c : Cofork f g) : PushoutCocone f g :=
  PushoutCocone.mk c.π c.π c.condition

@[simp]
lemma Cofork.help {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : (Cofork.ofπ π w).mkPushoutCocone = PushoutCocone.mk π π w := rfl

def Cofork.IsLimitofmkPushoutCocone (c : Cofork f g) (h : IsColimit c.mkPushoutCocone) : IsColimit c := by {
  apply Cofork.IsColimit.mk c (fun s ↦ h.desc s.mkPushoutCocone)
  · intro s
    #check h.desc
    sorry
  sorry
}

lemma PushoutCocone.EqOfIsReflexivePair (h : IsReflexivePair f g) (s : PushoutCocone f g) : s.inl = s.inr := by {
  calc s.inl = h.common_section'.choose ≫ f ≫ s.inl := by rw [← assoc, h.common_section'.choose_spec.1, id_comp]
  _ = h.common_section'.choose ≫ g ≫ s.inr := by rw [s.condition]
  _ = s.inr := by rw [← assoc, h.common_section'.choose_spec.2, id_comp]
}

lemma PushoutCocone.ConditionOfReflexivePair (h : IsReflexivePair f g) (s : PushoutCocone f g) : f ≫ s.inl = g ≫ s.inl := by {nth_rewrite 2 [PushoutCocone.EqOfIsReflexivePair h s]; exact s.condition}
