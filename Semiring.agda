module Semiring where

open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)

boolToSet : Bool -> Set
boolToSet false = ⊥
boolToSet true = ⊤

record Semiring : Set₁ where
  field
    carrier : Set
    1r      : carrier
    0r      : carrier
    _+R_    : carrier -> carrier -> carrier
    _*R_    : carrier -> carrier -> carrier
    _≤_     : carrier -> carrier -> Bool

    leftUnit+   : {r : carrier} -> 0r +R r ≡ r
    rightUnit+  : {r : carrier} -> r +R 0r ≡ r
    comm+       : {r s : carrier} -> r +R s ≡ s +R r

    leftUnit*    : {r : carrier} -> 1r *R r ≡ r
    rightUnit*   : {r : carrier} -> r *R r ≡ r
    leftAbsorb   : {r : carrier} -> r *R 0r ≡ 0r
    rightAbsorb  : {r : carrier} -> 0r *R r ≡ 0r

--    assoc*     : {r s t : carrier} -

    infFlow : {r s adv : carrier} -> boolToSet ((r *R s) ≤ adv) -> boolToSet (s ≤ adv)

open Semiring

data Level : Set where
  Public  : Level
  Private : Level
  Dunno   : Level
  Unused  : Level

levelSemiring : Semiring
carrier levelSemiring = Level
1r levelSemiring      = Private
0r levelSemiring      = Unused

-- central line and its transitivity
_≤_ levelSemiring Unused Public  = true
_≤_ levelSemiring Public Private = true
_≤_ levelSemiring Unused Private = true
-- dunno branch
_≤_ levelSemiring Unused Dunno   = true
_≤_ levelSemiring Private Dunno  = true
-- reflexive cases
_≤_ levelSemiring Dunno Dunno      = true
_≤_ levelSemiring Private Private  = true
_≤_ levelSemiring Public Public    = true
_≤_ levelSemiring Unused Unused    = true

_≤_ levelSemiring _ _            = false

-- unit property
_+R_ levelSemiring Unused x = x
_+R_ levelSemiring x Unused = x
-- otherwise dunno acts like another unit
_+R_ levelSemiring Dunno x = x
_+R_ levelSemiring x Dunno = x
-- otherwise join
_+R_ levelSemiring Private Private = Private
_+R_ levelSemiring Public  Public  = Public
_+R_ levelSemiring Private Public  = Public
_+R_ levelSemiring Public Private  = Public

-- absorbing
_*R_ levelSemiring Unused x = Unused
_*R_ levelSemiring x Unused = Unused
-- dunno behaviour
_*R_ levelSemiring Private Dunno = Dunno
_*R_ levelSemiring Dunno Private = Dunno
_*R_ levelSemiring x Dunno = x
_*R_ levelSemiring Dunno x = x
-- otherwise join
_*R_ levelSemiring Private Private = Private
_*R_ levelSemiring Public  Public  = Public
_*R_ levelSemiring Private Public  = Public
_*R_ levelSemiring Public Private  = Public

leftUnit+ levelSemiring {Public}  = refl
leftUnit+ levelSemiring {Private} = refl
leftUnit+ levelSemiring {Dunno}   = refl
leftUnit+ levelSemiring {Unused}  = refl

rightUnit+ levelSemiring {Public}  = refl
rightUnit+ levelSemiring {Private} = refl
rightUnit+ levelSemiring {Dunno}   = refl
rightUnit+ levelSemiring {Unused}  = refl

comm+ levelSemiring {Public} {Public} = refl
comm+ levelSemiring {Public} {Private} = refl
comm+ levelSemiring {Public} {Dunno} = refl
comm+ levelSemiring {Public} {Unused} = refl
comm+ levelSemiring {Private} {Public} = refl
comm+ levelSemiring {Private} {Private} = refl
comm+ levelSemiring {Private} {Dunno} = refl
comm+ levelSemiring {Private} {Unused} = refl
comm+ levelSemiring {Dunno} {Public} = refl
comm+ levelSemiring {Dunno} {Private} = refl
comm+ levelSemiring {Dunno} {Dunno} = refl
comm+ levelSemiring {Dunno} {Unused} = refl
comm+ levelSemiring {Unused} {Public} = refl
comm+ levelSemiring {Unused} {Private} = refl
comm+ levelSemiring {Unused} {Dunno} = refl
comm+ levelSemiring {Unused} {Unused} = refl

leftAbsorb levelSemiring {Public} = refl
leftAbsorb levelSemiring {Private} = refl
leftAbsorb levelSemiring {Dunno} = refl
leftAbsorb levelSemiring {Unused} = refl

rightAbsorb levelSemiring {Public} = refl
rightAbsorb levelSemiring {Private} = refl
rightAbsorb levelSemiring {Dunno} = refl
rightAbsorb levelSemiring {Unused} = refl

leftUnit* levelSemiring {Public}   = refl
leftUnit* levelSemiring {Private}  = refl
leftUnit* levelSemiring {Dunno}    = refl
leftUnit* levelSemiring {Unused}   = refl

rightUnit* levelSemiring {Public}  = refl
rightUnit* levelSemiring {Private} = refl
rightUnit* levelSemiring {Dunno}   = refl
rightUnit* levelSemiring {Unused}  = refl

infFlow levelSemiring {Public} {Public} {Public} prop = tt
infFlow levelSemiring {Public} {Public} {Private} prop = tt
infFlow levelSemiring {Public} {Public} {Dunno} prop = {!!}
infFlow levelSemiring {Public} {Public} {Unused} prop = {!!}
infFlow levelSemiring {Public} {Private} {Public} prop = {!!}
infFlow levelSemiring {Public} {Private} {Private} prop = tt
infFlow levelSemiring {Public} {Private} {Dunno} prop = tt
infFlow levelSemiring {Public} {Private} {Unused} prop = {!!}
infFlow levelSemiring {Public} {Dunno} {Public} prop = {!!}
infFlow levelSemiring {Public} {Dunno} {Private} prop = {!!}
infFlow levelSemiring {Public} {Dunno} {Dunno} prop = tt
infFlow levelSemiring {Public} {Dunno} {Unused} prop = {!!}
infFlow levelSemiring {Public} {Unused} {Public} prop = tt
infFlow levelSemiring {Public} {Unused} {Private} prop = tt
infFlow levelSemiring {Public} {Unused} {Dunno} prop = tt
infFlow levelSemiring {Public} {Unused} {Unused} prop = tt
infFlow levelSemiring {Private} {Public} {Public} prop = tt
infFlow levelSemiring {Private} {Public} {Private} prop = tt
infFlow levelSemiring {Private} {Public} {Dunno} prop = {!!}
infFlow levelSemiring {Private} {Public} {Unused} prop = {!!}
infFlow levelSemiring {Private} {Private} {Public} prop = {!!}
infFlow levelSemiring {Private} {Private} {Private} prop = tt
infFlow levelSemiring {Private} {Private} {Dunno} prop = tt
infFlow levelSemiring {Private} {Private} {Unused} prop = {!!}
infFlow levelSemiring {Private} {Dunno} {Public} prop = {!!}
infFlow levelSemiring {Private} {Dunno} {Private} prop = {!!}
infFlow levelSemiring {Private} {Dunno} {Dunno} prop = tt
infFlow levelSemiring {Private} {Dunno} {Unused} prop = {!!}
infFlow levelSemiring {Private} {Unused} {Public} prop = tt
infFlow levelSemiring {Private} {Unused} {Private} prop = tt
infFlow levelSemiring {Private} {Unused} {Dunno} prop = tt
infFlow levelSemiring {Private} {Unused} {Unused} prop = tt
infFlow levelSemiring {Dunno} {Public} {Public} prop = tt
infFlow levelSemiring {Dunno} {Public} {Private} prop = tt
infFlow levelSemiring {Dunno} {Public} {Dunno} prop = {!!}
infFlow levelSemiring {Dunno} {Public} {Unused} prop = {!!}
infFlow levelSemiring {Dunno} {Private} {Public} prop = {!!}
infFlow levelSemiring {Dunno} {Private} {Private} prop = tt
infFlow levelSemiring {Dunno} {Private} {Dunno} prop = tt
infFlow levelSemiring {Dunno} {Private} {Unused} prop = {!!}
infFlow levelSemiring {Dunno} {Dunno} {Public} prop = {!!}
infFlow levelSemiring {Dunno} {Dunno} {Private} prop = {!!}
infFlow levelSemiring {Dunno} {Dunno} {Dunno} prop = tt
infFlow levelSemiring {Dunno} {Dunno} {Unused} prop = {!!}
infFlow levelSemiring {Dunno} {Unused} {Public} prop = tt
infFlow levelSemiring {Dunno} {Unused} {Private} prop = tt
infFlow levelSemiring {Dunno} {Unused} {Dunno} prop = tt
infFlow levelSemiring {Dunno} {Unused} {Unused} prop = tt
infFlow levelSemiring {Unused} {Public} {Public} prop = tt
infFlow levelSemiring {Unused} {Public} {Private} prop = tt
infFlow levelSemiring {Unused} {Public} {Dunno} prop = {!!}
infFlow levelSemiring {Unused} {Public} {Unused} prop = {!!}
infFlow levelSemiring {Unused} {Private} {Public} prop = {!!}
infFlow levelSemiring {Unused} {Private} {Private} prop = tt
infFlow levelSemiring {Unused} {Private} {Dunno} prop = tt
infFlow levelSemiring {Unused} {Private} {Unused} prop = {!!}
infFlow levelSemiring {Unused} {Dunno} {Public} prop = {!!}
infFlow levelSemiring {Unused} {Dunno} {Private} prop = {!!}
infFlow levelSemiring {Unused} {Dunno} {Dunno} prop = tt
infFlow levelSemiring {Unused} {Dunno} {Unused} prop = {!!}
infFlow levelSemiring {Unused} {Unused} {Public} prop = tt
infFlow levelSemiring {Unused} {Unused} {Private} prop = tt
infFlow levelSemiring {Unused} {Unused} {Dunno} prop = tt
infFlow levelSemiring {Unused} {Unused} {Unused} prop = tt
