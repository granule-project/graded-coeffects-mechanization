module Instances where

open import Semiring
open import Data.Unit
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality


singleton : Semiring
singleton = record
              { grade = ⊤
              ; 1R = tt
              ; 0R = tt
              ; _+R_ = λ x x₁ → tt
              ; _*R_ = λ x x₁ → tt
              ; _≤_ = λ x x₁ → ⊤
              ; _≤d_ = λ r s → yes tt
              ; leftUnit+ = refl
              ; rightUnit+ = refl
              ; comm+ = refl
              ; leftUnit* = refl
              ; rightUnit* = refl
              ; leftAbsorb = refl
              ; rightAbsorb = refl
              ; assoc* = refl
              ; assoc+ = refl
              ; distrib1 = refl
              ; distrib2 = refl
              ; monotone* = λ x x₁ → tt
              ; monotone+ = λ x x₁ → tt
              ; reflexive≤ = tt
              ; transitive≤ = λ x x₁ → tt
              }

singletonNI : NonInterferingSemiring {{singleton}}
singletonNI = record
                { oneIsBottom = tt
                ; zeroIsTop = tt
                ; antisymmetry = λ x x₁ → refl
                ; idem* = refl }
