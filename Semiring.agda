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
    oneIsBottom : {r : grade R} -> _≤_ R (1R R) r

    -- in classical logic this is the same as:   r1 ≤ s  →  r1 + r2 ≤ s
    antisymmetry : {r s : grade R} -> _≤_ R r s -> _≤_ R s r -> r ≡ s

    plusMono : {r1 r2 s : grade R} -> (_≤_ R r1 s) -> (_≤_ R (_+R_ R r1 r2) s)

    propertyConditionalNI : {r1 r2 r adv : grade R}
                     -> ¬ (_≤_ R (_+R_ R (_*R_ R r r1) r2) adv)
                     ->   (_≤_ R r (1R R))
                     -> ¬ (_≤_ R r1 adv)
    propertyConditionalNI2 : {r1 r2 r adv : grade R}
                     -> ¬ (_≤_ R (_+R_ R (_*R_ R r r1) r2) adv)
                     ->   (_≤_ R r (1R R))
                     -> ¬ (_≤_ R r2 adv)

    -- this is derivable from monotone* and if * is idempotent (which it is for us)
    -- or we could take this as the contrpositive which might look more sane:
    -- (_≤_ R r adv) -> (_≤_ R s adv) -> (_≤_ R (_*R_ R r s) adv)
    propInvTimesMonoAsym : {r s adv : grade R}
                       -> ¬ (_≤_ R (_*R_ R r s) adv)
                       ->   (_≤_ R r adv)
                       -> ¬ (_≤_ R s adv)

open NonInterferingSemiring

plusMonoInv : {R : Semiring} {R' : NonInterferingSemiring R}
              {r1 r2 s : grade R} -> ¬ (_≤_ R (_+R_ R r1 r2) s) -> ¬ (_≤_ R r1 s)
plusMonoInv {R} {R'} {r1} {r2} {s} pre pre0 =
  pre (plusMono R' {r1} {r2} {s} pre0)

-- # Some derived properties
plusMonoInv' : {R : Semiring} {R' : NonInterferingSemiring R}
                -> {r1 r2 s : grade R}
                -> ¬ (_≤_ R (_+R_ R r1 r2)  s) -> ¬ (_≤_ R r2 s)
plusMonoInv' {R} {R'} {r1} {r2} {s} pre =
  plusMonoInv {R} {R'} {r2} {r1} {s} (\x -> pre (subst (\h -> _≤_ R h s) (comm+ R {r2} {r1}) x))

record InformationFlowSemiring (R : Semiring) : Set₁ where
  field
    default : grade R
    _#_     : grade R -> grade R -> grade R

    -- this is a possibility for type preservation from a few of my sketches
    --substProp : {r : grade R} -> _+R_ R (1R R) r ≡ (1R R) # r
  
    unit#   : {r : grade R}     -> default # r  ≡ r
    comm#   : {r s : grade R}   -> r # s        ≡ s # r
    assoc#  : {r s t : grade R} -> (r # s) # t  ≡ r # (s # t)
    idem#   : {r : grade R}     -> r # r        ≡ r

    -- distributivity rules with other operators?
    -- substitution theorem will tell us if we need these
  
open InformationFlowSemiring
