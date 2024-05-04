
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Topos.Power
import Topos.SubobjectClassifier

namespace CategoryTheory

open Category Limits Classifier Power

universe u v

variable (C : Type u) [Category.{v} C]

class Topos where
  [has_terminal : HasTerminal C]
  [finite_limits : HasPullbacks C]
  [subobject_classifier : HasSubobjectClassifier C]
  [cartesian_closed : HasPowerObjects C]

attribute [instance] Topos.has_terminal Topos.finite_limits Topos.subobject_classifier Topos.cartesian_closed

variable [Topos C] {C}

namespace Topos

noncomputable section

def Predicate.true_ (B : C) : B ⟶ Ω C := terminal.from B ≫ (t C)

/--
  The equality predicate on `B ⨯ B`.
-/
def Predicate.eq (B : C) : B ⨯ B ⟶ Ω C := ClassifierOf (diag B)

-- B ⟶ P(B)
-- b ↦ {b' ∈ B | (b', b) ↦ 1} = {b' ∈ B | b' = b } = {b}

-- B ⨯ A ⟶ Ω
-- A ⟶ P(B)
-- a ↦ Uₐ

-- B ⨯ {a} ⟶ Ω
--  Uₐ ↣ B

/--
  The "singleton" map {•}_B : B ⟶ Pow B.
  In Set, this map sends b ∈ B to the singleton set {b}.
-/
def singleton (B : C) : B ⟶ Pow B := P_transpose (Predicate.eq B)

lemma PullbackDiagRight {B X : C} (b : X ⟶ B) : IsLimit (PullbackCone.mk b (prod.lift b (𝟙 _)) (by
    show b ≫ diag B = prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b
    simp only [prod.comp_lift, comp_id, prod.lift_map, id_comp]
  )) := by
    apply PullbackCone.IsLimit.mk _ (fun s ↦ (PullbackCone.snd s) ≫ prod.snd)
    -- fac_left
    intro s
    have h₁ : (PullbackCone.snd s ≫ prod.map (𝟙 B) b) ≫ prod.snd = (PullbackCone.fst s ≫ diag B) ≫ prod.snd := by rw [PullbackCone.condition s]
    simp at h₁
    rw [assoc]; exact h₁
    -- fac_right
    intro s
    have h₀ : (PullbackCone.snd s ≫ prod.map (𝟙 B) b) ≫ prod.fst = (PullbackCone.fst s ≫ diag B) ≫ prod.fst := by rw [PullbackCone.condition s]
    have h₁ : (PullbackCone.snd s ≫ prod.map (𝟙 B) b) ≫ prod.snd = (PullbackCone.fst s ≫ diag B) ≫ prod.snd := by rw [PullbackCone.condition s]
    ext
    simp
    simp at h₀
    simp at h₁
    exact h₁.trans h₀.symm
    simp only [prod.comp_lift, assoc, comp_id, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd]
    -- uniq
    intro s m _ h'
    have k₁ : (m ≫ prod.lift b (𝟙 X)) ≫ prod.snd = (PullbackCone.snd s) ≫ prod.snd := by rw [h']
    simp only [prod.comp_lift, comp_id, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd] at k₁
    assumption



/-- The singleton map {•}_B : B ⟶ Pow B is a monomorphism. -/
instance singletonMono (B : C) : Mono (singleton B) where
  right_cancellation := by
    intro X b b' h
    rw [singleton] at h
    have h₁ : prod.map (𝟙 _) (b ≫ P_transpose (Predicate.eq B)) ≫ in_ B = prod.map (𝟙 _) (b' ≫ P_transpose (Predicate.eq B)) ≫ in_ B :=
      congrFun (congrArg CategoryStruct.comp (congrArg (prod.map (𝟙 B)) h)) (in_ B)
    have sq_right := (Classifies (diag B)).pb
    have big_square_b := bigSquareIsPullback b _ _ _ _ _ _ _ _ sq_right (PullbackCone.flipIsLimit (PullbackDiagRight b))
    have big_square_b' := bigSquareIsPullback b' _ _ _ _ _ _ _ _ sq_right (PullbackCone.flipIsLimit (PullbackDiagRight b'))
    simp at big_square_b
    simp at big_square_b'

    sorry

def Predicate.isSingleton (B : C) : Pow B ⟶ Ω C := ClassifierOf (singleton B)

/-- The name ⌈φ⌉ : ⊤_ C ⟶ Pow B of a predicate `φ : B ⟶ Ω C`. -/
def Name {B} (φ : B ⟶ Ω C) : ⊤_ C ⟶ Pow B := P_transpose ((prod.rightUnitor B).hom ≫ φ)

def Predicate.fromName {B} (φ' : ⊤_ C ⟶ Pow B) := (prod.map (𝟙 _) φ') ≫ in_ B

def Predicate.NameDef {B} (φ : B ⟶ Ω C) : (prod.rightUnitor B).hom ≫ φ = (prod.map (𝟙 _) (Name φ)) ≫ (in_ B) :=
  Pow_powerizes _ _

-- TODO: prove equivalence of the types (B ⟶ Ω C), (T_ C ⟶ Pow B), and (Subobject B).



end
end Topos
end CategoryTheory
