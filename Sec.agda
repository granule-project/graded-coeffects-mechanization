{-# OPTIONS --allow-unsolved-metas #-}

module Sec where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary
open import Data.Empty
open import Semiring

data Sec : Set where
  Hi : Sec
  Lo  : Sec

_+R_ : Sec -> Sec -> Sec
Lo +R _  = Lo
_ +R Lo  = Lo
Hi +R Hi = Hi

_*R_ : Sec -> Sec -> Sec
Hi *R _ = Hi
_ *R Hi = Hi
Lo *R Lo = Lo

1r : Sec
1r = Lo

0r : Sec
0r = Hi

leftUnit : {r : Sec} -> 1r *R r ≡ r
leftUnit {Hi} = refl
leftUnit {Lo} = refl

rightUnit : {r : Sec} -> r *R 1r ≡ r
rightUnit {Hi} = refl
rightUnit {Lo} = refl

assoc : {r s t : Sec} -> r *R (s *R t) ≡ (r *R s) *R t
assoc {Hi} {Hi} {Hi} = refl
assoc {Hi} {Hi} {Lo} = refl
assoc {Hi} {Lo} {Hi} = refl
assoc {Hi} {Lo} {Lo} = refl
assoc {Lo} {Hi} {Hi} = refl
assoc {Lo} {Hi} {Lo} = refl
assoc {Lo} {Lo} {Hi} = refl
assoc {Lo} {Lo} {Lo} = refl

-- not part of the Semiring but useful for simplifying
-- other proofs
comm* : {r s : Sec} -> r *R s ≡ s *R r
comm* {Hi} {Hi} = refl
comm* {Hi} {Lo} = refl
comm* {Lo} {Hi} = refl
comm* {Lo} {Lo} = refl

rightAbsorb : {r : Sec} -> r *R 0r ≡ 0r
rightAbsorb {Hi} = refl
rightAbsorb {Lo} = refl

leftAbsorb : {r : Sec} -> 0r *R r ≡ 0r
leftAbsorb {r} = trans (comm* {0r} {r}) (rightAbsorb {r})

leftUnit+ : {r : Sec} -> 0r +R r ≡ r
leftUnit+ {Hi} = refl
leftUnit+ {Lo} = refl

rightUnit+ : {r : Sec} -> r +R 0r ≡ r
rightUnit+ {Hi} = refl
rightUnit+ {Lo} = refl

assoc+ : {r s t : Sec} -> r +R (s +R t) ≡ (r +R s) +R t
assoc+ {Hi} {Hi} {Hi} = refl
assoc+ {Hi} {Hi} {Lo} = refl
assoc+ {Hi} {Lo} {Hi} = refl
assoc+ {Hi} {Lo} {Lo} = refl
assoc+ {Lo} {Hi} {Hi} = refl
assoc+ {Lo} {Hi} {Lo} = refl
assoc+ {Lo} {Lo} {Hi} = refl
assoc+ {Lo} {Lo} {Lo} = refl

comm+ : {r s : Sec} -> r +R s ≡ s +R r
comm+ {Hi} {Hi} = refl
comm+ {Hi} {Lo} = refl
comm+ {Lo} {Hi} = refl
comm+ {Lo} {Lo} = refl

distrib1 : {r s t : Sec} -> r *R (s +R t) ≡ (r *R s) +R (r *R t)
distrib1 {r} {s} {t} = {!!}

distrib2 : {r s t : Sec} -> (r +R s) *R t ≡ (r *R t) +R (s *R t)
distrib2 {r} {s} {t} =
 let z = trans (comm* {r +R s} {t}) (distrib1 {t} {r} {s})
     k = cong₂ (\h1 h2 -> h1 +R h2) (comm* {r} {t}) (comm* {s} {t})
 in trans z (sym k)

data SecOrder : Sec -> Sec -> Set where
  ReflLo : SecOrder Lo Lo
  ReflHi : SecOrder Hi Hi
  LoHi   : SecOrder Lo Hi

_≤_ : Sec -> Sec -> Set
_≤_ = SecOrder

monotone* : {r1 r2 s1 s2 : Sec} -> SecOrder r1 r2 -> SecOrder s1 s2 -> SecOrder (r1 *R s1) (r2 *R s2)
monotone* = {!!}

monotone+ : {r1 r2 s1 s2 : Sec} -> SecOrder r1 r2 -> SecOrder s1 s2 -> SecOrder (r1 +R s1) (r2 +R s2)
monotone+ = {!!}

reflexive≤ : {r : Sec} -> SecOrder r r
reflexive≤ {Hi} = ReflHi
reflexive≤ {Lo} = ReflLo

transitive≤ : {r s t : Sec} -> SecOrder r s -> SecOrder s t -> SecOrder r t
transitive≤ {r} {s} {t} = {!!}

secSemiring : Semiring
secSemiring = record
                { grade = Sec
                ; 1R = 1r
                ; 0R = 0r
                ; _+R_ = _+R_
                ; _*R_ = _*R_
                ; _≤_ = SecOrder
                ; leftUnit+ = leftUnit+
                ; rightUnit+ = rightUnit+
                ; comm+ = comm+
                ; leftUnit* = leftUnit
                ; rightUnit* = rightUnit
                ; leftAbsorb = \{r} -> leftAbsorb {r}
                ; rightAbsorb = rightAbsorb
                ; assoc* = sym assoc
                ; assoc+ = sym assoc+
                ; distrib1 = distrib1
                ; distrib2 = distrib2
                ; monotone* = monotone*
                ; monotone+ = monotone+
                ; reflexive≤ = reflexive≤
                ; transitive≤ = transitive≤
                }

plusMonoInv : {r1 r2 adv : Sec} -> ¬ (SecOrder (r1 +R r2) adv) -> ¬ (SecOrder r1 adv)
plusMonoInv {Hi} {Hi} {Hi} pre p = pre p
plusMonoInv {Hi} {Hi} {Lo} pre p = pre p
plusMonoInv {Hi} {Lo} {Hi} pre p = pre LoHi
plusMonoInv {Hi} {Lo} {Lo} pre p = pre ReflLo
plusMonoInv {Lo} {Hi} {Hi} pre p = pre LoHi
plusMonoInv {Lo} {Hi} {Lo} pre p = pre ReflLo
plusMonoInv {Lo} {Lo} {Hi} pre p = pre LoHi
plusMonoInv {Lo} {Lo} {Lo} pre p = pre ReflLo

propertyConditionalNI : {r1 r2 r adv : Sec}
                     -> ¬ (SecOrder ((r *R r1) +R r2) adv)
                     ->   (SecOrder r  1r)
                     -> ¬ (SecOrder r1 adv)
propertyConditionalNI {Hi} {Hi} {Lo} {Hi} pre1 pre2 = pre1
propertyConditionalNI {Hi} {Hi} {Lo} {Lo} pre1 pre2 = pre1
propertyConditionalNI {Hi} {Lo} {Lo} {Hi} pre1 pre2 = ⊥-elim (pre1 LoHi)
propertyConditionalNI {Hi} {Lo} {Lo} {Lo} pre1 pre2 = ⊥-elim (pre1 ReflLo)
propertyConditionalNI {Lo} {Hi} {Lo} {Hi} pre1 pre2 = pre1
propertyConditionalNI {Lo} {Hi} {Lo} {Lo} pre1 pre2 = pre1
propertyConditionalNI {Lo} {Lo} {Lo} {Hi} pre1 pre2 = pre1
propertyConditionalNI {Lo} {Lo} {Lo} {Lo} pre1 pre2 = pre1

propertyConditionalNI2 : {r1 r2 r adv : Sec}
                     -> ¬ (SecOrder ((r *R r1) +R r2) adv)
                     ->   (SecOrder r 1r)
                     -> ¬ (SecOrder r2 adv)
propertyConditionalNI2 {Hi} {Hi} {Lo} {Hi} pre1 pre2 = pre1
propertyConditionalNI2 {Hi} {Hi} {Lo} {Lo} pre1 pre2 = pre1
propertyConditionalNI2 {Hi} {Lo} {Lo} {Hi} pre1 pre2 = pre1
propertyConditionalNI2 {Hi} {Lo} {Lo} {Lo} pre1 pre2 = pre1
propertyConditionalNI2 {Lo} {Hi} {Lo} {Hi} pre1 pre2 = ⊥-elim (pre1 LoHi)
propertyConditionalNI2 {Lo} {Hi} {Lo} {Lo} pre1 pre2 = ⊥-elim (pre1 ReflLo)
propertyConditionalNI2 {Lo} {Lo} {Lo} {Hi} pre1 pre2 = pre1
propertyConditionalNI2 {Lo} {Lo} {Lo} {Lo} pre1 pre2 = pre1

propInvTimesMonoAsym : {r s adv : Sec}
                    -> ¬ ((r *R s) ≤ adv)
                    ->   (r ≤ adv)
                    -> ¬ (s ≤ adv)
propInvTimesMonoAsym {Hi} {Hi} {Hi} pre1 pre2 = pre1
propInvTimesMonoAsym {Hi} {Lo} {Hi} pre1 pre2 = ⊥-elim (pre1 ReflHi)
propInvTimesMonoAsym {Lo} {Hi} {Hi} pre1 pre2 = ⊥-elim (pre1 ReflHi)
propInvTimesMonoAsym {Lo} {Hi} {Lo} pre1 pre2 = pre1
propInvTimesMonoAsym {Lo} {Lo} {Hi} pre1 pre2 = pre1
propInvTimesMonoAsym {Lo} {Lo} {Lo} pre1 pre2 = pre1


secSemiringNI : NonInterferingSemiring secSemiring
secSemiringNI = record
                  { plusMonoInv            = plusMonoInv
                  ; propertyConditionalNI  = propertyConditionalNI
                  ; propertyConditionalNI2 = propertyConditionalNI2
                  ; propInvTimesMonoAsym   = propInvTimesMonoAsym
                  }
