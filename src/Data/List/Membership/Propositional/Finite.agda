module Data.List.Membership.Propositional.Finite where

open import Function
open import Data.List as List
open import Data.List.Any as Any
open import Data.List.Membership.Propositional as ∈
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.Product as ×

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.Properties

open import Finite as Finite

module _ {a} {A : Set a} where
  instance
    ∈-IsFinite : ∀ (xs : List A) → IsFinite (∃ (_∈ xs))
    ∈-IsFinite [] = finite [] λ ()
    ∈-IsFinite (x ∷ xs) =
      let finite es _∈es = ∈-IsFinite xs
      in finite ((-, here refl) ∷ List.map (×.map _ there) es) λ where
                (_ , here refl) → here refl
                (_ , there i) → there (∈-map⁺ _ ((-, i) ∈es))


module _ {a p} {A : Set a} {P : Pred A p} {xs} (P? : Decidable P) where
  open import Function.LeftInverse using (leftInverse)

  filterWithin : IsFinite (∃ (_∈ xs)) → IsFinite (∃ ((_∈ xs) ∩ (True ∘ P?)))
  filterWithin fin = let open IsFinite fin in
    via-left-inverse
      (leftInverse
        (λ where (a , p , q) → (a , p) , q)
        (λ where ((a , p) , q) → a , (p , q))
        λ x → refl
      )
      (IsFinite.filter fin (P? ∘ proj₁))
