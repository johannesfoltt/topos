import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Topos.ForkAndPullbackCone


namespace CategoryTheory.Limits

open CategoryTheory Limits

variable {C : Type*} [Category C]

@[simps!]
def Fork.isoOfι {F : WalkingParallelPair ⥤ C} (c : Cone F) :
    (Cones.postcompose (diagramIsoParallelPair F).hom).obj c ≅
      Fork.ofι (c.π.app WalkingParallelPair.zero) (by simp_rw [Cone.w]) :=
  Cones.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;>
      · dsimp
        simp

structure IsEqualizer {I X Y : C} (ι : I ⟶ X) (f g : X ⟶ Y) : Prop where
  w : ι ≫ f = ι ≫ g
  isLimit' : Nonempty (Limits.IsLimit (Limits.Fork.ofι _ w))

@[simps!]
def Cofork.isoOfπ {F : WalkingParallelPair ⥤ C} (c : Cocone F) :
    (Cocones.precompose (diagramIsoParallelPair F).inv).obj c ≅
      Cofork.ofπ (c.ι.app WalkingParallelPair.one) (by simp_rw [Cocone.w]) :=
  Cocones.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;>
      · dsimp
        simp

structure IsCoequalizer {X Y P : C} (f g : X ⟶ Y) (π : Y ⟶ P): Prop where
  w : f ≫ π = g ≫ π
  isColimit' : Nonempty (Limits.IsColimit (Limits.Cofork.ofπ _ w))

namespace IsEqualizer

variable {I X Y : C} {ι : I ⟶ X} {f g : X ⟶ Y}

def cone (h : IsEqualizer ι f g) : Fork f g := Fork.ofι _ h.w

@[simp]
theorem cone_ι (h : IsEqualizer ι f g) : h.cone.ι = ι := rfl

noncomputable def isLimit (h : IsEqualizer ι f g) : IsLimit h.cone := h.isLimit'.some

noncomputable def lift (hE : IsEqualizer ι f g) {W : C} (k : W ⟶ X) (w : k ≫ f = k ≫ g) : W ⟶ I := Fork.IsLimit.lift hE.isLimit k w

@[reassoc (attr := simp)]
lemma lift_ι (hE : IsEqualizer ι f g) {W : C} (k : W ⟶ X) (w : k ≫ f = k ≫ g) : hE.lift k w ≫ ι = k :=
  Fork.IsLimit.lift_ι' hE.isLimit k w


lemma hom_ext (hE : IsEqualizer ι f g) {W : C} {k l : W ⟶ I}
    (h : k ≫ ι = l ≫ ι) : k = l := Fork.IsLimit.hom_ext hE.isLimit h

theorem mono_ι (hE : IsEqualizer ι f g) : Mono ι where
  right_cancellation _ _ w := hom_ext hE w

/-- If `c` is a limiting fork, then we have an `IsEqualizer c.ι f g`. -/
theorem of_isLimit {c : Fork f g} (h : Limits.IsLimit c) : IsEqualizer c.ι f g :=
  { w := c.condition
    isLimit' := ⟨h.ofIsoLimit c.isoForkOfι⟩}


/-- A variant of `of_isLimit` that is more useful with `apply`. -/
theorem of_isLimit' (w : ι ≫ f = ι ≫ g) (h : Limits.IsLimit (Fork.ofι _ w)) :
    IsEqualizer ι f g := of_isLimit h


/-- Variant of `of_isLimit` for an arbitrary cone on a diagram `WalkingCospan ⥤ C`. -/
lemma of_isLimit_cone {D : WalkingParallelPair ⥤ C} {c : Cone D} (hc : IsLimit c) :
    IsEqualizer ((c.π.app) .zero) (D.map WalkingParallelPairHom.left)
      (D.map WalkingParallelPairHom.right) where
  w := by simp_rw [Cone.w]
  isLimit' := ⟨IsLimit.equivOfNatIsoOfIso _ _ _ (Fork.isoOfι c) hc⟩

lemma hasEqualizer (h : IsEqualizer ι f g) : HasEqualizer f g where
  exists_limit := ⟨⟨h.cone, h.isLimit⟩⟩


/-- The equalizer provided by `HasEqualizer f g` fits into an `IsEqualizer`. -/
theorem of_hasEqualizer (f : X ⟶ Y) (g : X ⟶ Y) [HasEqualizer f g] :
    IsEqualizer (equalizer.ι f g) f g := of_isLimit (limit.isLimit (parallelPair f g))

class PreservesIsEqualizer (f g : X ⟶ Y) {D : Type*} [Category D] (F : C ⥤ D) : Prop where
  preserves {I : C} {ι : I ⟶ X} (h : IsEqualizer ι f g) : IsEqualizer (F.map ι) (F.map f) (F.map g)

end IsEqualizer

namespace IsCoequalizer

variable {P X Y : C} {π : Y ⟶ P} {f g : X ⟶ Y}

def cocone (h : IsCoequalizer f g π) : Cofork f g := Cofork.ofπ _ h.w

@[simp]
theorem cocone_π (h : IsCoequalizer f g π) : h.cocone.π = π := rfl

noncomputable def isColimit (h : IsCoequalizer f g π) : IsColimit h.cocone := h.isColimit'.some

noncomputable def desc (hC : IsCoequalizer f g π) {W : C} (k : Y ⟶ W) (w : f ≫ k = g ≫ k) : P ⟶ W := Cofork.IsColimit.desc hC.isColimit k w

@[reassoc (attr := simp)]
lemma desc_π (hC : IsCoequalizer f g π) {W : C} (k : Y ⟶ W)
    (w : f ≫ k = g ≫ k) : π ≫ hC.desc k w = k :=
  Cofork.IsColimit.π_desc' hC.isColimit k w


lemma hom_ext (hC : IsCoequalizer f g π) {W : C} {k l : P ⟶ W}
    (h : π ≫ k = π ≫ l) : k = l := Cofork.IsColimit.hom_ext hC.isColimit h

theorem epi_π (hC : IsCoequalizer f g π) : Epi π where
  left_cancellation _ _ w := hom_ext hC w

/-- If `c` is a colimiting cofork, then we have an `IsCoequalizer f g c.π`. -/
theorem of_isColimit {c : Cofork f g} (h : Limits.IsColimit c) : IsCoequalizer f g c.π :=
  { w := c.condition
    isColimit' := ⟨h.ofIsoColimit c.isoCoforkOfπ⟩}


/-- A variant of `of_isColimit` that is more useful with `apply`. -/
theorem of_isColimit' (w : f ≫ π = g ≫ π) (h : Limits.IsColimit (Cofork.ofπ _ w)) :
    IsCoequalizer f g π := of_isColimit h


/-- Variant of `of_isColimit` for an arbitrary cone on a diagram `WalkingCospan ⥤ C`. -/
lemma of_isColimit_cocone {D : WalkingParallelPair ⥤ C} {c : Cocone D} (hc : IsColimit c) :
    IsCoequalizer (D.map WalkingParallelPairHom.left) (D.map WalkingParallelPairHom.right) ((c.ι.app) .one) where
  w := by simp_rw [Cocone.w]
  isColimit' := ⟨IsColimit.equivOfNatIsoOfIso _ _ _ (Cofork.isoOfπ c) hc⟩
  --⟨IsLimit.equivOfNatIsoOfIso _ _ _ c hc⟩


lemma hasCoequalizer (h : IsCoequalizer f g π) : HasCoequalizer f g where
  exists_colimit := ⟨⟨h.cocone, h.isColimit⟩⟩


/-- The equalizer provided by `HasEqualizer f g` fits into an `IsEqualizer`. -/
theorem of_hasEqualizer (f : X ⟶ Y) (g : X ⟶ Y) [HasCoequalizer f g] :
  IsCoequalizer f g (coequalizer.π f g) := of_isColimit (colimit.isColimit (parallelPair f g))

theorem IsPushoutOfReflexivePairAndIsCoequalizer (hR : IsReflexivePair f g) (hC : IsCoequalizer f g π) : IsPushout f g π π where
  w := hC.w
  isColimit' := by {
    apply Nonempty.intro
    let desc := fun (s : PushoutCocone f g) ↦ hC.desc s.inl (PushoutCocone.ConditionOfReflexivePair hR s)
    apply PushoutCocone.IsColimit.mk hC.w desc
    · intro s
      exact desc_π hC s.inl (PushoutCocone.ConditionOfReflexivePair hR s)
    · intro s
      rw [← PushoutCocone.EqOfIsReflexivePair hR s]
      exact desc_π hC s.inl (PushoutCocone.ConditionOfReflexivePair hR s)
    · intro s m h_inl h_inr
      rw [← (desc_π hC s.inl (PushoutCocone.ConditionOfReflexivePair hR s))] at h_inl
      exact hom_ext hC h_inl
  }

end IsCoequalizer

def IsSplitCoequalizer.IsCoequalizer {X Y P : C} {f g : X ⟶ Y} {π : Y ⟶ P} (h : IsSplitCoequalizer f g π) : IsCoequalizer f g π where
  w := h.condition
  isColimit' := ⟨IsSplitCoequalizer.isCoequalizer h⟩


--def Cofork. {X Y P : C} {f g : X ⟶ Y} {π : Y ⟶ P} : (IsCoequalizer f g π) ≃ (IsPushout f g π π) := sorry


/-
theorem op {P : C} {π : Y ⟶ P} (h : IsCoequalizer f g π) : IsEqualizer π.op f.op g.op :=
  IsEqualizer.of_isLimit ()


theorem unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback inr.unop inl.unop g.unop f.unop :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeUnop)
-/
