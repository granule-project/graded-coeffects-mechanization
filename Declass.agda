module Declass where

open import Semiring
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality

data Declass : Set where
  Fin   : ℕ -> Declass
  Omega : Declass

data _<<_ : Declass -> Declass -> Set where
     OmegaBot : (d : Declass) -> Omega << d
     Lt       : (n m : ℕ) -> n ≤ m -> Fin m << Fin n

meet : Declass -> Declass -> Declass
meet Omega _ = Omega
meet _ Omega = Omega
meet (Fin n) (Fin m) = Fin (n ⊔ m)

-- Int % n -> Int
-- Int % m -> Int

-- Int % n -> Int

times : Declass -> Declass -> Declass
times Omega x = x
times x Omega = x
times (Fin n) (Fin m) = Fin (n ⊓ m)

declassS : Semiring
declassS = record
             { grade = Declass
             ; 1R = Omega
             ; 0R = Fin 0
             ; _+R_ = meet
             ; _*R_ = times
             ; _≤_ = _<<_
             ; _≤d_ = {!!}
             ; leftUnit+ = {!!}
             ; rightUnit+ = {!!}
             ; comm+ = {!!}
             ; leftUnit* = {!!}
             ; rightUnit* = {!!}
             ; leftAbsorb = {!!}
             ; rightAbsorb = {!!}
             ; assoc* = {!!}
             ; assoc+ = {!!}
             ; distrib1 = {!!}
             ; distrib2 = {!!}
             ; monotone* = {!!}
             ; monotone+ = {!!}
             ; reflexive≤ = {!!}
             ; transitive≤ = {!!}
             }

zeroTop : {d : Declass} -> d << Fin 0
zeroTop {Fin x} = Lt zero x z≤n
zeroTop {Omega} = OmegaBot (Fin zero)

asym : {d d' : Declass} -> d << d' -> d' << d -> d ≡ d'
asym (OmegaBot .Omega) (OmegaBot .Omega) = refl
asym (Lt .zero .zero z≤n) (Lt .zero .zero z≤n) = refl
asym (Lt .(suc _) .(suc _) (s≤s x)) (Lt .(suc _) .(suc _) (s≤s x₁))
  rewrite asym (Lt _ _ x) (Lt _ _ x₁) = {!!}

laxidem : {d : Declass} -> times d d << d
laxidem {Fin x} rewrite m≤n⇒m⊓n≡m {x} {x} (≤-reflexive refl) = Lt x x (≤-reflexive refl)
laxidem {Omega} = OmegaBot Omega

declassSI : NonInterferingSemiring {{declassS}}
declassSI = record
              { oneIsBottom = \{d} -> OmegaBot d
              ; zeroIsTop = zeroTop
              ; antisymmetry = asym
              ; idem*lax = laxidem
              }
