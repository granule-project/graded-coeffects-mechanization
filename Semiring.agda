{-# OPTIONS --allow-unsolved-metas #-}

module Semiring where

open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Nullary.Decidable
open import Data.Maybe
open import Data.Maybe.Properties

record Semiring : Set₁ where
  field
    grade : Set
    1R      : grade
    0R      : grade
    _+R_    : grade -> grade -> grade
    _*R_    : grade -> grade -> grade
    _≤_     : grade -> grade -> Set

    -- Decideable ordering and equality
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

partialJoin : {{ R : Semiring }} -> grade R -> grade R -> Maybe (grade R)
partialJoin {{R}} r s with _≤d_ R r s | _≤d_ R s r
... | yes _ | _     = just s
... | no  _ | yes _ = just r
... | no _  | no  _ = nothing

partialJoinMono : {{ R : Semiring }} {r1 r2 : grade R} {s1 s2 : grade R} {r r' : grade R}
                -> _≤_ R r1 r2
                -> _≤_ R s1 s2
                -> just r ≡ partialJoin r1 s1
                -> just r' ≡ partialJoin r2 s2
                -> _≤_ R r r'
partialJoinMono {{R}} {r1} {r2} {s1} {s2} {r} {r'} pre1 pre2 eq1 eq2
  with _≤d_ R r1 s1 | _≤d_ R s1 r1 | _≤d_ R r2 s2 | _≤d_ R s2 r2
... | yes p1 | yes p2 | yes p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = pre2
... | yes p1 | yes p2 | yes p3 | no ¬p4 rewrite just-injective eq1 | just-injective eq2 = pre2
... | yes p1 | yes p2 | no ¬p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = transitive≤ R p2 pre1
... | yes p1 | no ¬p2 | yes p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = pre2
... | yes p1 | no ¬p2 | yes p3 | no ¬p4 rewrite just-injective eq1 | just-injective eq2 = pre2
... | yes p1 | no ¬p2 | no ¬p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = transitive≤ R pre2 p4
... | no ¬p1 | yes p2 | yes p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = transitive≤ R pre1 p3
... | no ¬p1 | yes p2 | yes p3 | no ¬p4 rewrite just-injective eq1 | just-injective eq2 = transitive≤ R pre1 p3
... | no ¬p1 | yes p2 | no ¬p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = pre1

partialJoinIdem : {{ R : Semiring }} {r : grade R}
                -> just r ≡ partialJoin r r
partialJoinIdem {{R}} {r} with _≤d_ R r r
... | yes p = refl
... | no ¬p = ⊥-elim (¬p (reflexive≤ R {r}))

urhu : {{ R : Semiring }} {r1 r2 adv r : grade R}
     -> _≤_ R r1 adv
     -> ¬ (_≤_ R r2 adv)
     -> just r ≡ partialJoin r1 r2
     -> _≤_ R r adv
urhu {{R}} {r1} {r2} {adv} {r} pre1 npre2 eq with _≤d_ R r1 r2 | _≤d_ R r2 r1
... | a1 | a2 = {!!}

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


joinMonoInv1 : {{ R : Semiring }} {{ R' : NonInterferingSemiring R }}
               {r1 r2 adv r' : grade R}
     -> just r' ≡ partialJoin {{R}} r1 r2
     -> _≤_ R r'  adv
     -> _≤_ R r2 adv
joinMonoInv1 {{R}} {r1} {r2} {adv} {r'} ev pre with _≤d_ R r1 r2 | _≤d_ R r2 r1
... | yes eq | yes eq' rewrite sym (just-injective ev) = pre
... | yes p1 | no ¬p2 rewrite sym (just-injective ev) = pre
... | no ¬p1 | yes p2 = transitive≤ R (subst (\h -> _≤_ R r2 h) (sym (just-injective ev)) p2) pre
joinMonoInv1 {{R}} {r1} {r2} {adv} {r'} () pre | no ¬p1 | no ¬p2

joinMonoInv2 : {{ R : Semiring }} {{ R' : NonInterferingSemiring R }}
               {r1 r2 adv r' : grade R}
     -> just r' ≡ partialJoin {{R}} r1 r2
     -> _≤_ R r'  adv
     -> _≤_ R r1 adv
joinMonoInv2 {{R}} {{R'}} {r1} {r2} {adv} {r'} ev pre with _≤d_ R r1 r2 | _≤d_ R r2 r1
... | yes eq | yes eq' rewrite sym (trans (just-injective ev) (antisymmetry R' eq' eq)) = pre
... | yes p1 | no ¬p2 = transitive≤ R (subst (\h -> _≤_ R r1 h) (sym (just-injective ev)) p1) pre
... | no ¬p1 | yes p2 rewrite sym (just-injective ev) = pre
joinMonoInv2 {{R}} {{R'}} {r1} {r2} {adv} {r'} () pre | no ¬p1 | no ¬p2


-- # Some derived properties

plusMonoInv : {R : Semiring} {R' : NonInterferingSemiring R}
              {r1 r2 s : grade R} -> ¬ (_≤_ R (_+R_ R r1 r2) s) -> ¬ (_≤_ R r1 s)
plusMonoInv {R} {R'} {r1} {r2} {s} pre pre0 =
  pre (plusMono R' {r1} {r2} {s} pre0)

plusMonoInv' : {R : Semiring} {R' : NonInterferingSemiring R}
                -> {r1 r2 s : grade R}
                -> ¬ (_≤_ R (_+R_ R r1 r2)  s) -> ¬ (_≤_ R r2 s)
plusMonoInv' {R} {R'} {r1} {r2} {s} pre =
  plusMonoInv {R} {R'} {r2} {r1} {s} (\x -> pre (subst (\h -> _≤_ R h s) (comm+ R {r2} {r1}) x))

-- Derived alternate characterisation of antisymmetry
antisymmetryAlt : {R : Semiring} {R' : NonInterferingSemiring R} {r s : grade R} -> _≤_ R r s -> r ≢ s -> ¬ (_≤_ R s r)
antisymmetryAlt {R} {R'} {r} {s} pre1 pre2 pre3 = ⊥-elim (pre2 (antisymmetry R' {r} {s} pre1 pre3))

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

    -- definitely holds for Level and seems needed for the proof.
    absorb# : {r : grade R} -> r # (1R R) ≡ (1R R)

    idem* : {r : grade R} -> _*R_ R r r ≡ r

    -- distributivity rules with other operators?
    -- substitution theorem will tell us if we need these

--    leftAbsorbSub   : {r : grade} -> 0R *R r ≡ 0R
--    rightAbsorbSub  : {r : grade} -> r *R 0R ≡ 0R



open InformationFlowSemiring
