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

    leftUnit*    : {r : grade} -> (1R *R r) ≤ r
    rightUnit*   : {r : grade} -> (r *R 1R) ≤ r
    leftAbsorb   : {r : grade} -> (0R *R r) ≤ 0R
    rightAbsorb  : {r : grade} -> (r *R 0R) ≤ 0R

    assoc*     : {r s t : grade} -> (r *R s) *R t ≡ r *R (s *R t)
    assoc+     : {r s t : grade} -> (r +R s) +R t ≡ r +R (s +R t)

    distrib1    : {r s t : grade} -> (r *R (s +R t)) ≤ ((r *R s) +R (r *R t))
    distrib2    : {r s t : grade} -> ((r +R s) *R t) ≤ ((r *R t) +R (s *R t))

    monotone*  : {r1 r2 s1 s2 : grade} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 *R s1) ≤ (r2 *R s2)
    monotone+  : {r1 r2 s1 s2 : grade} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 +R s1) ≤ (r2 +R s2)

    reflexive≤ : {r : grade} -> r ≤ r
    transitive≤ : {r s t : grade} -> r ≤ s -> s ≤ t -> r ≤ t

open Semiring

{- May not need this anymore
partialJoin : {{ R : Semiring }} -> grade R -> grade R -> Maybe (grade R)
partialJoin {{R}} r s with _≤d_ R r s | _≤d_ R s r
... | yes _ | _     = just s
... | no  _ | yes _ = just r
,... | no _  | no  _ = nothing

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
-}

record NonInterferingSemiring (R : Semiring) : Set₁ where
  field
    oneIsBottom : {r : grade R} -> _≤_ R (1R R) r
    zeroIsTop   : {r : grade R} -> _≤_ R r (0R R)

    antisymmetry : {r s : grade R} -> _≤_ R r s -> _≤_ R s r -> r ≡ s

    idem* : {r : grade R} -> _*R_ R r r ≡ r

open NonInterferingSemiring

-- # Some derived properties

decreasing+ : {{ R : Semiring }} {{ R' : NonInterferingSemiring R }} {r1 r2 s : grade R} -> (_≤_ R r1 s) -> (_≤_ R (_+R_ R r1 r2) s)
decreasing+ {{R}} {{R'}} {r1} {r2} {s} pre =
  subst (\h -> (_≤_ R (_+R_ R r1 r2) h)) (rightUnit+ R) (monotone+ R pre (zeroIsTop R'))

propInvTimesMonoAsymN : {{ R : Semiring }} {{ R' : NonInterferingSemiring R }}
                       {r s adv : grade R}
                     -> ¬ (_≤_ R (_*R_ R r s) adv)
                     ->   (_≤_ R r adv)
                     -> ¬ (_≤_ R s adv)
propInvTimesMonoAsymN {{R}} {{R'}} {r} {s} {adv} ngoal pre1 pre2 =
  ngoal
    (subst (\h -> (_≤_ R (_*R_ R r s) h)) (idem* R') (monotone* R pre1 pre2))


decreasing+Inv : {R : Semiring} {R' : NonInterferingSemiring R}
              {r1 r2 s : grade R} -> ¬ (_≤_ R (_+R_ R r1 r2) s) -> ¬ (_≤_ R r1 s)
decreasing+Inv {R} {R'} {r1} {r2} {s} pre pre0 =
  pre (decreasing+ {{R}} {{R'}} {r1} {r2} {s} pre0)

decreasing+Inv' : {R : Semiring} {R' : NonInterferingSemiring R}
                -> {r1 r2 s : grade R}
                -> ¬ (_≤_ R (_+R_ R r1 r2)  s) -> ¬ (_≤_ R r2 s)
decreasing+Inv' {R} {R'} {r1} {r2} {s} pre =
  decreasing+Inv {R} {R'} {r2} {r1} {s} (\x -> pre (subst (\h -> _≤_ R h s) (comm+ R {r2} {r1}) x))

-- Derived alternate characterisation of antisymmetry
antisymmetryAlt : {R : Semiring} {R' : NonInterferingSemiring R} {r s : grade R} -> _≤_ R r s -> r ≢ s -> ¬ (_≤_ R s r)
antisymmetryAlt {R} {R'} {r} {s} pre1 pre2 pre3 = ⊥-elim (pre2 (antisymmetry R' {r} {s} pre1 pre3))

record InformationFlowSemiring (R : Semiring) : Set₁ where
  field
    default : grade R
    _#_     : grade R -> grade R -> grade R

    -- this is a possibility for type preservation from a few of my sketches
    --substProp : {r : grade R} -> _+R_ R (1R R) r ≡ (1R R) # r

    comm#   : {r s : grade R}   -> r # s        ≡ s # r
    assoc#  : {r s t : grade R} -> (r # s) # t  ≡ r # (s # t)
    idem#   : {r : grade R}     -> r # r        ≡ r

    oneIsKey : {r : grade R}    ->  (1R R) # r  ≡ 1R R

    idem* : {r : grade R} -> _*R_ R r r ≡ r
    zeroIsTop : {r : grade R} -> _≤_ R r (0R R)

    timesLeft : {r1 r2 s : grade R} -> (_≤_ R r1 s) -> (_≤_ R (_*R_ R r1 r2) s)
    -- distributivity rules with other operators?
    -- substitution theorem will tell us if we need these


    com* : {r s : grade R} -> _*R_ R r s ≡ _*R_ R s r

    -- 0 * r <= r
    -- r * 0 <= r
    leftAbsorbSub   : {r : grade R} -> _≤_ R (_*R_ R (0R R) r) (0R R)
    rightAbsorbSub  : {r : grade R} -> _≤_ R (_*R_ R r (0R R)) (0R R)

open InformationFlowSemiring

timesLeftSym : {{R : Semiring}} {{R' : InformationFlowSemiring R}}
             -> {r1 r2 s : grade R}
             -> (_≤_ R r1 s) -> (_≤_ R (_*R_ R r2 r1) s)
timesLeftSym {{R}} {{R'}} {r1} {r2} {s} pre = subst (\h -> _≤_ R h s) (com* R') (timesLeft R' pre)

-- # Some more derived properties
decreasing+NF : {{ R : Semiring }} {{ R' : InformationFlowSemiring R }} {r1 r2 s : grade R} -> (_≤_ R r1 s) -> (_≤_ R (_+R_ R r1 r2) s)
decreasing+NF {{R}} {{R'}} {r1} {r2} {s} pre =
  subst (\h -> (_≤_ R (_+R_ R r1 r2) h)) (rightUnit+ R) (monotone+ R pre (zeroIsTop R'))

decreasing+NFSym : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {r1 r2 s : grade R} -> (_≤_ R r2 s) -> (_≤_ R (_+R_ R r1 r2) s)
decreasing+NFSym {{R}} {{R'}} {r1} {r2} {s} pre rewrite comm+ R {r1} {r2} = decreasing+NF pre

propInvTimesMonoAsym : {{ R : Semiring }} {{ R' : InformationFlowSemiring R }}
                       {r s adv : grade R}
                     -> ¬ (_≤_ R (_*R_ R r s) adv)
                     ->   (_≤_ R r adv)
                     -> ¬ (_≤_ R s adv)
propInvTimesMonoAsym {{R}} {{R'}} {r} {s} {adv} ngoal pre1 pre2 =
  ngoal
    (subst (\h -> (_≤_ R (_*R_ R r s) h)) (idem* R') (monotone* R pre1 pre2))
