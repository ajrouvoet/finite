module Data.Maybe.Finite where

open import Data.List as List
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.List.Any.Membership.Propositional.Properties
open import Data.Maybe
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality

instance
  Maybe-IsFinite : ∀ {a} {A : Set a} → IsFinite A → IsFinite (Maybe A)
  Maybe-IsFinite (finite es _∈es) =
    record { membership = maybe (there ∘ ∈-map⁺ ∘ _∈es) (here refl) }
