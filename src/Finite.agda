module Finite where

open import Data.Empty
open import Data.List as List hiding (filter)
open import Data.List.Properties as ListProps
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.List.Relation.Subset.Propositional
open import Data.Product as Σ
open import Data.Sum as ⊎
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit as ⊤
open import Function
open import Function.LeftInverse as ↞ using (LeftInverse; _↞_)
open import Function.Equality as Π using (_⟨$⟩_; cong)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; refl; subst; isPropositional)
open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Nullary.Negation

fromWitness∘toWitness≗id : ∀ {ℓ} {A : Set ℓ} {A? : Dec A} → fromWitness {Q = A?} ∘ toWitness ≗ id
fromWitness∘toWitness≗id {A? = A?} with A?
… | yes a = λ where tt → refl
… | no ¬a = λ ()

FiniteRec : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} → (A → List A → Set ℓ₂) → Set ℓ₃ → Set _
FiniteRec P B = ∀ xs ys → (∀ a → (a ∈ xs × P a xs) ⊎ (a ∈ ys)) → B

record IsFinite {ℓ₁} (A : Set ℓ₁) : Set ℓ₁ where
  constructor finite
  field
    elements : List A
    membership : ∀ a → a ∈ elements

  size = length elements
  elementsVec = Vec.fromList elements

  finite-⊆ : ∀ {xs} → xs ⊆ elements
  finite-⊆ {x = x} _ = membership x

  finiteRec : ∀ {ℓ₂ ℓ₃} {B : Set ℓ₂} {P : A → List A → Set ℓ₃} → FiniteRec P B → B
  finiteRec rec = rec [] elements (inj₂ ∘ membership)

  dec : Dec A
  dec with elements | membership
  dec | [] | _∈[] = no λ a → case a ∈[] of λ ()
  dec | a ∷ as | _ = yes a

  module _ {ℓ₂} {P : A → Set ℓ₂} (P? : ∀ a → Dec (P a)) where
    ∃? : Dec (∃ P)
    ∃? = finiteRec go
      where
        go : FiniteRec (λ a _ → ¬ P a) _
        go xs [] elem = no λ where
          (a , pa) → case elem a of λ where
            (inj₁ (_ , ¬pa)) → ¬pa pa
            (inj₂ ())
        go xs (y ∷ ys) elem = case P? y of λ where
          (yes py) → yes (-, py)
          (no ¬py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , ¬pa)) → inj₁ (there a∈xs , ¬pa)
              (inj₂ (here refl)) → inj₁ (here refl , ¬py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys

    ∀? : Dec (∀ x → P x)
    ∀? = finiteRec go
      where
        go : FiniteRec (λ a _ → P a) _
        go xs [] elem = yes λ a → case elem a of λ where
          (inj₁ (_ , pa)) → pa
          (inj₂ ())
        go xs (y ∷ ys) elem = case P? y of λ where
          (no ¬py) → no λ py → ¬py (py _)
          (yes py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , pa)) → inj₁ (there a∈xs , pa)
              (inj₂ (here refl)) → inj₁ (here refl , py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys

    filter-∃ : List A → List (∃ P)
    filter-∃ [] = []
    filter-∃ (a ∷ as) =
      case P? a of λ where
        (yes pa) → (-, pa) ∷ filter-∃ as
        (no ¬pa) → filter-∃ as

    filter-∃-∈ : ∀ {a as} → a ∈ as → (pa : True (P? a)) → (a , toWitness pa) ∈ filter-∃ as
    filter-∃-∈ {as = a ∷ as} (here refl) pa with P? a
    filter-∃-∈ (here refl) pa | yes pa′ = here refl
    filter-∃-∈ (here refl) () | no ¬pa
    filter-∃-∈ {as = a ∷ as} (there e) pa with P? a
    filter-∃-∈ (there e) pa | yes pa′ = there (filter-∃-∈ e pa)
    filter-∃-∈ (there e) pa | no ¬pa = filter-∃-∈ e pa

    filter-∃-prop : (∀ {x} → isPropositional (P x)) → IsFinite (∃ P)
    filter-∃-prop prop = record
      { elements = filter-∃ elements
      ; membership = λ where
          (a , pa) →
            subst (λ z → (a , z) ∈ filter-∃ elements)
              (prop _ pa)
              (filter-∃-∈ (membership a) (fromWitness pa)) 
      }

    filter-∃-True : List A → List (∃ (True ∘ P?))
    filter-∃-True = List.map (Σ.map₂ fromWitness) ∘ filter-∃

    filter-∃-True-∈ : ∀ {a as} → a ∈ as → (pa : True (P? a)) → (a , pa) ∈ filter-∃-True as
    filter-∃-True-∈ {a} e pa =
      subst
        (λ pa′ → (a , pa′) ∈ _)
        (fromWitness∘toWitness≗id _)
        (∈-map⁺ _ (filter-∃-∈ e pa))

    filter : IsFinite (∃ (True ∘ P?))
    filter = record
      { elements = filter-∃-True elements
      ; membership = λ where (a , pa) → filter-∃-True-∈ (membership a) pa
      }

  module Ordered {ℓ₂ ℓ₃} {_≈_ : A → A → Set ℓ₂} {_<_ : A → A → Set ℓ₃}
    (<-po : IsDecStrictPartialOrder _≈_ _<_)
    where
    open IsDecStrictPartialOrder <-po

    _≮_ : A → A → Set _
    a ≮ b = ¬ (a < b)

    maxOf : A → ∀ as → ∃ λ a → ∀ {x} → x ∈ as → a ≮ x
    maxOf p [] = p , λ ()
    maxOf p (a ∷ as) =
      let x , f = maxOf p as in
        case (a <? x) ,′ (x <? a) of λ where
          (yes a<x , _) → x , λ {y} y∈a∷as x<y →
            case y∈a∷as of λ where
              (here refl) → asymmetric x<y a<x
              (there y∈as) → f y∈as x<y
          (_ , yes x<a) → a , λ {y} y∈a∷as a<y →
            case y∈a∷as of λ where
              (here refl) → irrefl Eq.refl a<y
              (there y∈as) → f y∈as (trans x<a a<y)
          (no a≮x , no x≮a) → x , λ {y} y∈a∷as x<y →
            case y∈a∷as of λ where
              (here refl) → x≮a x<y
              (there y∈as) → f y∈as x<y

    max : (¬ A) ⊎ (∃ λ a → ∀ x → a ≮ x)
    max =
      case dec of λ where
        (yes a) → let x , m = maxOf a elements in inj₂ (x , (m ∘ membership))
        (no ¬a) → inj₁ ¬a

    pointedMax : A → ∃ λ a → ∀ x → a ≮ x
    pointedMax x =
      case max of λ where
        (inj₁ ¬a) → contradiction x ¬a
        (inj₂ a) → a

open IsFinite

via-left-inverse : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A ↞ B) → IsFinite B → IsFinite A
via-left-inverse f finB = record
  { elements = List.map (from ⟨$⟩_) (elements finB)
  ; membership = λ a → subst (_∈ _) (left-inverse-of a) (∈-map⁺ _ (membership finB (to ⟨$⟩ a)))
  }
  where open LeftInverse f
