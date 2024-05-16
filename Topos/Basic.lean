
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

/--
  The "singleton" map {•}_B : B ⟶ Pow B.
  In Set, this map sends b ∈ B to the singleton set {b}.
-/
def singleton (B : C) : B ⟶ Pow B := P_transpose (Predicate.eq B)

-- example (B X : C) (b b' : X ⟶ B) (h : b)

-- TODO: Clean up proofs in this file so that this lemma is no longer necessary.
lemma PullbackLimitTransfer_eq_right {W X Y Z : C} {k : Y ⟶ Z} {h h' : X ⟶ Z} {f : W ⟶ X} {g : W ⟶ Y} (eq : h = h') (comm : f ≫ h = g ≫ k)
  (lim : IsLimit (PullbackCone.mk f g comm)) : IsLimit (PullbackCone.mk f g (by
    show f ≫ h' = g ≫ k
    rw [←eq]
    assumption
  )) := by
    subst eq
    assumption

lemma PullbackDiagRightComm {B X : C} (b : X ⟶ B) : b ≫ diag B = prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b := by
  rw [prod.comp_diag, prod.lift_map, id_comp, comp_id]


lemma PullbackDiagRight {B X : C} (b : X ⟶ B) : IsLimit (PullbackCone.mk b (prod.lift b (𝟙 _)) (PullbackDiagRightComm b)) := by
    apply PullbackCone.IsLimit.mk _ (fun s ↦ s.snd ≫ prod.snd)
    -- fac_left
    intro s
    rw [assoc, ←prod.map_snd (𝟙 _), ←s.condition_assoc prod.snd, ←assoc, prod.comp_diag, prod.lift_snd]
    -- fac_right
    intro s
    ext
    rw [assoc, prod.lift_fst, assoc]
    calc
      s.snd ≫ prod.snd ≫ b
        = (s.snd ≫ prod.map (𝟙 B) b) ≫ prod.snd := by rw [assoc, prod.map_snd]
      _ = (s.fst ≫ diag B) ≫ prod.snd := by rw [s.condition]
      _ = s.fst := by rw [assoc, prod.lift_snd, comp_id]
      _ = (s.fst ≫ diag B) ≫ prod.fst := by rw [assoc, prod.lift_fst, comp_id]
      _ = (s.snd ≫ prod.map (𝟙 B) b) ≫ prod.fst := by rw [s.condition]
      _ = s.snd ≫ prod.fst := by rw [assoc, prod.map_fst, comp_id]
    calc
      ((s.snd ≫ prod.snd) ≫ prod.lift b (𝟙 X)) ≫ prod.snd
        = (s.snd ≫ prod.snd) ≫ (𝟙 X) := by rw [assoc, prod.lift_snd]
      _ = (s.snd ≫ prod.snd) := by rw [comp_id]
    -- uniq
    intro s m _ h
    have k : (m ≫ prod.lift b (𝟙 X)) ≫ prod.snd = PullbackCone.snd s ≫ prod.snd := congrArg (fun r ↦ r ≫ prod.snd) h
    rw [assoc, prod.lift_snd, comp_id] at k
    assumption

lemma _BigSquare_comm {B X : C} (b : X ⟶ B) : (prod.lift b (𝟙 _)) ≫ ((prod.map (𝟙 _) b) ≫ (Predicate.eq B)) = terminal.from X ≫ (t C) := by
  have sq_left_comm_b : b ≫ diag B = prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b := by simp only [prod.comp_lift, comp_id, prod.lift_map, id_comp]
  calc
    prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b ≫ Predicate.eq B
      = b ≫ diag B ≫ Predicate.eq B := by rw [←assoc, ←assoc, sq_left_comm_b]
    _ = b ≫ (terminal.from B) ≫ (t C) := by
      dsimp only [Predicate.eq]
      rw [(Classifies (diag B)).comm]
    _ = terminal.from X ≫ t C := by rw [←assoc, terminal.comp_from b]

lemma _BigSquare_pb {B X : C} (b : X ⟶ B) : IsLimit (PullbackCone.mk (prod.lift b (𝟙 _)) (terminal.from X) (_BigSquare_comm b)) := by
  let BigSquare_pb := bigSquareIsPullback _ _ _ _ _ _ _
    (by simp only [PullbackCone.mk_pt, PullbackCone.mk_π_app, prod.lift_map, comp_id, id_comp, prod.comp_lift]) (Classifies (diag B)).comm
    (Classifies (diag B)).pb (PullbackCone.flipIsLimit (PullbackDiagRight b))
  simp only [Unique.eq_default] at BigSquare_pb; assumption

/-- The singleton map {•}_B : B ⟶ Pow B is a monomorphism. -/
instance singletonMono (B : C) : Mono (singleton B) where
  right_cancellation := by
    intro X b b' h
    rw [singleton] at h
    have h₁ : prod.map (𝟙 _) (b ≫ P_transpose (Predicate.eq B)) ≫ in_ B = prod.map (𝟙 _) (b' ≫ P_transpose (Predicate.eq B)) ≫ in_ B :=
      congrFun (congrArg CategoryStruct.comp (congrArg (prod.map (𝟙 B)) h)) (in_ B)
    repeat rw [prod.map_id_comp, assoc, ←(Pow_powerizes B (Predicate.eq B))] at h₁
    have big_square_b := _BigSquare_pb b
    have big_square_b'_comm : (prod.lift b' (𝟙 _)) ≫ ((prod.map (𝟙 _) b) ≫ (Predicate.eq B)) = terminal.from X ≫ (t C) := by
      rw [h₁]
      exact _BigSquare_comm b'
    have big_square_b' : IsLimit (PullbackCone.mk (prod.lift b' (𝟙 _)) (terminal.from X) big_square_b'_comm) :=
      PullbackLimitTransfer_eq_right h₁.symm _ (_BigSquare_pb b')

    let cone_iso := IsLimit.conePointUniqueUpToIso big_square_b big_square_b'
    have triangle : cone_iso.hom ≫ (prod.lift b' (𝟙 _)) = (prod.lift b (𝟙 _)) :=
      IsLimit.conePointUniqueUpToIso_hom_comp big_square_b big_square_b' (some WalkingPair.left)
    rw [prod.comp_lift, comp_id] at triangle
    have t₁ : prod.lift (cone_iso.hom ≫ b') cone_iso.hom ≫ prod.fst = prod.lift b (𝟙 X) ≫ prod.fst := by rw [triangle]; rfl
    have t₂ : prod.lift (cone_iso.hom ≫ b') cone_iso.hom ≫ prod.snd = prod.lift b (𝟙 X) ≫ prod.snd := by rw [triangle]; rfl
    simp at t₁
    simp at t₂
    rw [t₂, id_comp] at t₁
    exact t₁.symm

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
