module Data.Fin.Finite where

open import Data.Fin
open import Data.List
open import Data.Vec
open import Data.Vec.Properties
open import Finite
open import Function

instance
  Fin-IsFinite : ∀ {n} → IsFinite (Fin n)
  Fin-IsFinite = finite _ (∈⇒List-∈ ∘ ∈-allFin)
