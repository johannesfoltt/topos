import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Topos.Basic
import Topos.Category


namespace CategoryTheory

open Category Limits Classifier Power Topos

universe u v

variable {C : Type u} [Category.{v} C] [Topos C]

/-!
# Exponential Objects

Proves that a topos has exponential objects (internal homs).
Consequently, every topos is Cartesian closed.
-/


namespace Topos

noncomputable section

/-- The exponential object B^A. -/
def Exp (A B : C) : C :=
  pullback
    (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B))
    (Name (Predicate.true_ A))

/-- The map which, in Set, sends a function (A → B) ∈ B^A to its graph as a subset of B ⨯ A. -/
def Exp_toGraph (A B : C) : Exp A B ⟶ Pow (B ⨯ A) := pullback.fst

@[simp]
lemma ExpConeSnd_Terminal (A B : C) : pullback.snd = terminal.from (Exp A B) := Unique.eq_default _

def Exp_comm (A B : C) : Exp_toGraph A B ≫ (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B))
  = terminal.from (Exp A B) ≫ Name (Predicate.true_ A) := by
    rw [←ExpConeSnd_Terminal]; exact pullback.condition

/-- The evaluation map eval : A ⨯ B^A ⟶ B. -/
def eval (A B : C) : A ⨯ (Exp A B) ⟶ B := by
  let id_uniq : A ⨯ Exp A B ⟶ A ⨯ ⊤_ C := prod.map (𝟙 _) (terminal.from _)
  let id_m : A ⨯ Exp A B ⟶ A ⨯ Pow (B ⨯ A) := prod.map (𝟙 _) (Exp_toGraph A B)
  let id_nameOfTrue : A ⨯ ⊤_ C ⟶ A ⨯ Pow A := prod.map (𝟙 _) (Name (Predicate.true_ A))
  -- #check in_ (A ⨯ B)
  let σ_B : Pow B ⟶ Ω C := Predicate.isSingleton B
  let v : A ⨯ Pow (B ⨯ A) ⟶ Pow B := P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
  let u : Pow (B ⨯ A) ⟶ Pow A := P_transpose (v ≫ Predicate.isSingleton B)
  let id_u : A ⨯ Pow (B ⨯ A) ⟶ A ⨯ Pow A := prod.map (𝟙 _) u
  have comm_middle : v ≫ σ_B = id_u ≫ (in_ A) := Pow_powerizes A (v ≫ σ_B)
  have comm_left : id_m ≫ id_u =  id_uniq ≫ id_nameOfTrue := by
    rw [prod.map_map, prod.map_map]
    ext; simp
    rw [prod.map_snd, prod.map_snd, Exp_comm]
  -- checking commutativity of the big rectangle.
  have h_terminal : (prod.map (𝟙 A) (terminal.from (Exp A B)) ≫ prod.fst) ≫ terminal.from A = terminal.from _ :=
      Unique.eq_default _
  have comm : (id_m ≫ v) ≫ σ_B = Predicate.true_ (A ⨯ Exp A B) := by
    rw [assoc, comm_middle, ←assoc, comm_left, assoc, Predicate.true_, ←Predicate.NameDef]
    dsimp [Predicate.true_]
    rw [←assoc, ←assoc, h_terminal]
  exact ClassifierCone_into (singleton B) (id_m ≫ v) comm



abbrev Exponentiates {A B X HomAB : C}  (e : A ⨯ HomAB ⟶ B) (f : A ⨯ X ⟶ B) (f_exp : X ⟶ HomAB) :=
  f = (prod.map (𝟙 _) f_exp) ≫ e

structure IsExponentialObject {A B HomAB : C} (e : A ⨯ HomAB ⟶ B) where
  exp : ∀ {X} (_ : A ⨯ X ⟶ B), X ⟶ HomAB
  exponentiates : ∀ {X} (f : A ⨯ X ⟶ B), Exponentiates e f (exp f)
  unique' : ∀ {X} {f : A ⨯ X ⟶ B} {exp' : X ⟶ HomAB}, Exponentiates e f exp' → exp f = exp'

class HasExponentialObject (A B : C) where
  HomAB : C
  e : A ⨯ HomAB ⟶ B
  is_exp : IsExponentialObject e

variable (C)

class HasExponentialObjects where
  has_exponential_object : ∀ (A B : C), HasExponentialObject A B

variable {C}

attribute [instance] HasExponentialObjects.has_exponential_object

-- ## TODO
-- exhibit the type class instance `HasExponentialObjects C` for a topos `C`.

abbrev h {A B X : C} (f : A ⨯ X ⟶ B) := P_transpose ((prod.associator _ _ _).hom ≫ prod.map (𝟙 _) f ≫ Predicate.eq _)

lemma ExpMapSquareComm {A B X : C} (f : A ⨯ X ⟶ B) :
  h f ≫ P_transpose (P_transpose ((prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B) =
  terminal.from X ≫ Name (Predicate.true_ A) := by
    -- consider (1⨯f) ≫ (eq B) : B ⨯ A ⨯ X ⟶ Ω C.
    let id_f'eq : B ⨯ A ⨯ X ⟶ Ω C := prod.map (𝟙 _) f ≫ Predicate.eq _
    -- h is the map that, in `Set`, takes an element of X to the graph of the corresponding function.
    -- We want to lift this to a map X ⟶ Exp A B.
    -- The idea is to show that this map actually "maps elements of X to graphs of functions", which,
    -- in an arbitrary topos, is the same as checking commutativity of the obvious square.
    let h : X ⟶ Pow (B ⨯ A) := P_transpose ((prod.associator _ _ _).hom ≫ id_f'eq)
    -- h is by definition a P-transpose
    have h_condition : (prod.associator _ _ _).hom ≫ id_f'eq = (prod.map (prod.map (𝟙 _) (𝟙 _)) h) ≫ in_ _ := by
      rw [prod.map_id_id]
      apply Pow_powerizes
    -- moving the associator to the rhs of `h_condition`.
    have h_condition₂ : id_f'eq = (prod.associator _ _ _).inv ≫ (prod.map (prod.map (𝟙 _) (𝟙 _)) h) ≫ in_ _ := by
      rw [←h_condition, ←assoc, (prod.associator _ _ _).inv_hom_id, id_comp]
    -- this is the map v: A ⨯ P(B⨯A) ⟶ P(B) which was used in the definition of `Exp A B`.
    let v : A ⨯ Pow (B ⨯ A) ⟶ Pow B := P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
    -- v is by definition a P-transpose
    have v_condition : (prod.associator _ _ _).inv ≫ in_ (B ⨯ A) = prod.map (𝟙 _) v ≫ in_ _ := Pow_powerizes _ _
    have lhs : P_transpose (prod.map (𝟙 A) h ≫ v ≫ Predicate.isSingleton B) = h ≫ P_transpose (v ≫ Predicate.isSingleton B) := by
      apply Pow_unique
      dsimp only [Powerizes]
      rw [prod.map_id_comp, assoc _ _ (in_ A), ←Pow_powerizes _ _, ←assoc]
    rw [←lhs]
    -- Claim that f ≫ {•}_B = (1⨯h) ≫ v.
    -- This is obtained by showing that both maps are the P-transpose of (1⨯f) ≫ (eq B).
    -- There might be a slightly faster way to do this.
    have transpose₁ : P_transpose id_f'eq = f ≫ singleton _ := by
      apply Pow_unique
      dsimp only [Powerizes, Topos.singleton]
      rw [prod.map_id_comp, assoc, ←(Pow_powerizes B (Predicate.eq B))]
    have shuffle_h_around : (prod.associator B A X).inv ≫ (prod.map (prod.map (𝟙 _) (𝟙 _)) h) = prod.map (𝟙 _) (prod.map (𝟙 _) h) ≫ (prod.associator _ _ _).inv := by simp
    have transpose₂ : P_transpose id_f'eq = (prod.map (𝟙 _) h) ≫ v := by
      apply Pow_unique
      dsimp only [Powerizes]
      rw [h_condition₂, ←assoc, shuffle_h_around, prod.map_id_comp, assoc _ _ (in_ B), ←v_condition, assoc]
    have eqn₁ : f ≫ singleton _ = (prod.map (𝟙 _) h) ≫ v := transpose₁.symm.trans transpose₂
    -- now compose by the `isSingleton B` predicate.
    have eqn₂ : f ≫ singleton _ ≫ Predicate.isSingleton _ = (prod.map (𝟙 _) h) ≫ v ≫ Predicate.isSingleton _ := by
      rw [←assoc, ←assoc, eqn₁]
    rw [←eqn₂]

    -- from here, the argument is mostly definition unpacking.
    apply Pow_unique
    dsimp only [Name, Predicate.true_, Powerizes, Predicate.isSingleton]
    have f_terminal : f ≫ terminal.from B = terminal.from _ := Unique.eq_default _
    have rightUnitor_terminal : (prod.rightUnitor A).hom ≫ terminal.from A = terminal.from _ := Unique.eq_default _
    have A_X_terminal : prod.map (𝟙 A) (terminal.from X) ≫ terminal.from (A ⨯ ⊤_ C) = terminal.from _ := Unique.eq_default _
    have obv : terminal.from (A ⨯ ⊤_ C) ≫ t C = prod.map (𝟙 A) (P_transpose (terminal.from (A ⨯ ⊤_ C) ≫ t C)) ≫ in_ A := Pow_powerizes _ _
    rw [(Classifies (singleton _)).comm, ←assoc, f_terminal, ←assoc, rightUnitor_terminal, prod.map_id_comp, assoc, ←obv, ←assoc, A_X_terminal]


def Exp_map {A B X : C} (f : A ⨯ X ⟶ B) : X ⟶ Exp A B :=
  pullback.lift (h f) (terminal.from X) (ExpMapSquareComm f)


theorem Exp_Exponentiates {A B X : C} (f : A ⨯ X ⟶ B) : Exponentiates (eval A B) f (Exp_map f) := by
  dsimp only [Exponentiates]


  sorry


instance Exp_isExponential (A B : C) : IsExponentialObject (eval A B) where
  exp := fun f ↦ Exp_map f
  exponentiates := Exp_Exponentiates
  unique' := fun {X} (f : A ⨯ X ⟶ B) {exp' : X ⟶ Exp A B} ↦ by {
    intro h
    rw [Exponentiates] at h
    #check (cancel_mono (singleton B)).mpr
    have h_singleton := (cancel_mono (singleton _)).mpr h
    -- rw [pullback.lift_fst] at h_singleton

    sorry
  }


def InternalComposition {X Y Z : C} : (Exp X Y) ⨯ (Exp Y Z) ⟶ Exp X Z :=
  Exp_map ((prod.associator X (Exp X Y) (Exp Y Z)).inv ≫ (prod.map (eval X Y) (𝟙 _)) ≫ eval Y Z)

-- ## TODO
-- exhibit `CartesianClosed C` for a topos `C`.

def ExpHom {X Y : C} (A : C) (f : X ⟶ Y) : Exp A Y ⟶ Exp A X := sorry

def ExpFunctor (A : C) : Cᵒᵖ ⥤ C where
  obj := fun ⟨B⟩ ↦ Exp A B
  map := fun {X Y} ⟨f⟩ ↦ ExpHom A f
  map_id := sorry
  map_comp := sorry


instance CartesianClosed : CartesianClosed C := by
  apply CartesianClosed.mk
  intro B

  sorry


end
end Topos
end CategoryTheory
