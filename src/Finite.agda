module Finite where

open import Data.Bool as Bool
open import Data.Empty as ⊥
open import Data.List as List
open import Data.List.Properties
open import Data.List.All as All
open import Data.List.Any as Any
open import Data.List.Any.Properties
open import Data.List.Any.Membership.Propositional as ∈
open import Data.List.Any.Membership.Propositional.Properties hiding (finite)
open import Data.Nat hiding (_⊔_)
open import Data.Product as ×
open import Data.Sum as ⊎
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit as ⊤
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; refl; subst)
open import Relation.Nullary
open import Relation.Nullary.Decidable

FiniteRec : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} → (A → List A → Set ℓ₂) → Set ℓ₃ → Set _
FiniteRec P B = ∀ xs ys → (∀ a → (a ∈ xs × P a xs) ⊎ (a ∈ ys)) → B

record IsFinite {ℓ₁} (A : Set ℓ₁) : Set ℓ₁ where
  constructor finite
  field
    elements : List A
    membership : ∀ a → a ∈ elements

  size = length elements
  elementsVec = Vec.fromList elements

  finite-⊆ : ∀ {x xs} → x ∈ xs → x ∈ elements
  finite-⊆ {x = x} _ = membership x

  finiteRec : ∀ {ℓ₂ ℓ₃} {B : Set ℓ₂} {P : A → List A → Set ℓ₃} → FiniteRec P B → B
  finiteRec rec = rec [] elements (inj₂ ∘ membership)

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
          (yes py) → yes (, py)
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

open IsFinite

finiteDec : ∀ {ℓ} {A : Set ℓ} → IsFinite A → Dec A
finiteDec (finite [] _∈[]) = no λ x → case x ∈[] of λ ()
finiteDec (finite (x ∷ _) _) = yes x

filter-∃ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  (P? : ∀ a → Dec (P a)) → List A → List (∃ P)
filter-∃ P? [] = []
filter-∃ P? (a ∷ as) =
  case P? a of λ where
    (yes pa) → (, pa) ∷ filter-∃ P? as
    (no ¬pa) → filter-∃ P? as

filter-∃-True : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  (P? : ∀ a → Dec (P a)) → List A → List (∃ λ a → True (P? a))
filter-∃-True P? as = List.map (×.map id fromWitness) (filter-∃ P? as)

∃-witness : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {a}
  (P? : ∀ a → Dec (P a)) → True (P? a) → ∃ λ pa → P? a ≡ yes pa
∃-witness {a = a} P? pa with P? a
∃-witness {a = a} P? pa | yes pa′ = pa′ , refl
∃-witness {a = a} P? () | no ¬pa

filter-∃-∈ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  (P? : ∀ a → Dec (P a)) (as : List A) →
  ∀ {a} → a ∈ as → (pa : True (P? a)) → (a , toWitness pa) ∈ filter-∃ P? as
filter-∃-∈ P? [] () pa
filter-∃-∈ P? (a ∷ as) (here refl) pa with P? a
filter-∃-∈ P? (a ∷ as) (here refl) pa | yes pa′ = here refl
filter-∃-∈ P? (a ∷ as) (here refl) () | no ¬pa
filter-∃-∈ P? (a ∷ as) (there e) pa with P? a
filter-∃-∈ P? (a ∷ as) (there e) pa | yes pa′ = there (filter-∃-∈ P? as e pa)
filter-∃-∈ P? (a ∷ as) (there e) pa | no ¬pa = filter-∃-∈ P? as e pa

fromWitness∘toWitness≗id : ∀ {ℓ} {A : Set ℓ} {A? : Dec A} →
  fromWitness {Q = A?} ∘ toWitness ≗ id
fromWitness∘toWitness≗id {A? = A?} with A?
… | yes a = λ where tt → refl
… | no ¬a = λ ()

filter-∃-True-∈ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  (P? : ∀ a → Dec (P a)) (as : List A) →
  ∀ {a} → a ∈ as → (pa : True (P? a)) → (a , pa) ∈ filter-∃-True P? as
filter-∃-True-∈ P? as {a} e pa =
  subst
    (λ pa′ → (a , pa′) ∈ _)
    (fromWitness∘toWitness≗id _)
    (∈-map⁺ (filter-∃-∈ P? as e pa))

finiteFilter : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  (P? : ∀ a → Dec (P a)) → IsFinite A → IsFinite (∃ λ a → True (P? a))
elements (finiteFilter P? (finite xs _∈xs)) = filter-∃-True P? xs
membership (finiteFilter P? (finite xs _∈xs)) (a , pa) = filter-∃-True-∈ P? xs (a ∈xs) pa

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {_≈_ : Rel A ℓ₂} {_<_ : Rel A ℓ₃}
  (≤-po : IsDecStrictPartialOrder _≈_ _<_) where
  open IsDecStrictPartialOrder ≤-po renaming (_≟_ to _≈?_)

  maximum : A → ∀ as → ∃ λ a → ∀ {x} → x ∈ as → ¬ a < x
  maximum p [] = p , λ ()
  maximum p (a ∷ as) =
    let x , f = maximum p as in
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

  finiteMax : IsFinite A → (¬ A) ⊎ (∃ λ a → ∀ x → ¬ a < x)
  finiteMax af@(finite as _∈as) =
    case finiteDec af of λ where
      (yes a) →
        let x , f = maximum a as in
          inj₂ (x , (f ∘ _∈as))
      (no ¬a) → inj₁ ¬a

  finitePointedMax : IsFinite A → A → ∃ λ a → ∀ x → ¬ a < x
  finitePointedMax af a =
    case finiteMax af of λ where
      (inj₁ ¬a) → ⊥-elim (¬a a)
      (inj₂ m) → m
