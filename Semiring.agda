{-# OPTIONS --allow-unsolved-metas #-}

module Semiring where

open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Nullary.Decidable

record Semiring : Set₁ where
  field
    grade : Set
    1R      : grade
    0R      : grade
    _+R_    : grade -> grade -> grade
    _*R_    : grade -> grade -> grade
    _≤_     : grade -> grade -> Set

    _≤d_  : (r : grade) -> (s : grade) -> Dec (r ≤ s)

    leftUnit+   : {r : grade} -> 0R +R r ≡ r
    rightUnit+  : {r : grade} -> r +R 0R ≡ r
    comm+       : {r s : grade} -> r +R s ≡ s +R r

    leftUnit*    : {r : grade} -> 1R *R r ≡ r
    rightUnit*   : {r : grade} -> r *R 1R ≡ r
    leftAbsorb   : {r : grade} -> 0R *R r ≡ 0R
    rightAbsorb  : {r : grade} -> r *R 0R ≡ 0R

    assoc*     : {r s t : grade} -> (r *R s) *R t ≡ r *R (s *R t)
    assoc+     : {r s t : grade} -> (r +R s) +R t ≡ r +R (s +R t)

    distrib1    : {r s t : grade} -> r *R (s +R t) ≡ (r *R s) +R (r *R t)
    distrib2    : {r s t : grade} -> (r +R s) *R t ≡ (r *R t) +R (s *R t)

    monotone*  : {r1 r2 s1 s2 : grade} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 *R s1) ≤ (r2 *R s2)
    monotone+  : {r1 r2 s1 s2 : grade} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 +R s1) ≤ (r2 +R s2)

    reflexive≤ : {r : grade} -> r ≤ r
    transitive≤ : {r s t : grade} -> r ≤ s -> s ≤ t -> r ≤ t

open Semiring

record NonInterferingSemiring (R : Semiring) : Set₁ where
  field
    -- in classical logic this is the same as:   r1 ≤ s  →  r1 + r2 ≤ s
    plusMonoInv : {r1 r2 s : grade R} -> ¬ (_≤_ R (_+R_ R r1 r2) s) -> ¬ (_≤_ R r1 s)

    propertyConditionalNI : {r1 r2 r adv : grade R}
                     -> ¬ (_≤_ R (_+R_ R (_*R_ R r r1) r2) adv)
                     ->   (_≤_ R r (1R R))
                     -> ¬ (_≤_ R r1 adv)
    propertyConditionalNI2 : {r1 r2 r adv : grade R}
                     -> ¬ (_≤_ R (_+R_ R (_*R_ R r r1) r2) adv)
                     ->   (_≤_ R r (1R R))
                     -> ¬ (_≤_ R r2 adv)

    propInvTimesMonoAsym : {r s adv : grade R}
                       -> ¬ (_≤_ R (_*R_ R r s) adv)
                       ->   (_≤_ R r adv)
                       -> ¬ (_≤_ R s adv)

open NonInterferingSemiring

-- # Some derived properties
plusMonoInv' : {R : Semiring} {R' : NonInterferingSemiring R}
                -> {r1 r2 s : grade R}
                -> ¬ (_≤_ R (_+R_ R r1 r2)  s) -> ¬ (_≤_ R r2 s)
plusMonoInv' {R} {R'} {r1} {r2} {s} pre =
  plusMonoInv R' {r2} {r1} {s} (\x -> pre (subst (\h -> _≤_ R h s) (comm+ R {r2} {r1}) x))

-- # Level semiring definition

-- Level elements
data Level : Set where
  Public  : Level
  Private : Level
  Dunno   : Level
  Unused  : Level

-- constructive representation of the ordering
data Order : Level -> Level -> Set where
  -- central 'line' and its transitivity
  0Pub    : Order Unused Public
  0Priv   : Order Unused Private
  PrivPub : Order Private Public
  -- dunno branch
  0Dunno  : Order Unused Dunno
  PrivDunno : Order Private Dunno
  DunnoPub  : Order Dunno Public
  -- reflexive cases
  Refl : (l : Level) -> Order l l

-- reify the indexed type ordering
reified : (l : Level) -> (j : Level) -> Dec (Order j l)
reified Public Public   = yes (Refl Public)
reified Public Private  = yes PrivPub
reified Public Dunno    = yes DunnoPub
reified Public Unused   = yes 0Pub
reified Private Public  = no (λ ())
reified Private Private = yes (Refl Private)
reified Private Dunno   = no (λ ())
reified Private Unused  = yes 0Priv
reified Dunno Public    = no (λ ())
reified Dunno Private   = yes PrivDunno
reified Dunno Dunno     = yes (Refl Dunno)
reified Dunno Unused    = yes 0Dunno
reified Unused Public   = no (λ ())
reified Unused Private  = no (λ ())
reified Unused Dunno    = no (λ ())
reified Unused Unused   = yes (Refl Unused)

