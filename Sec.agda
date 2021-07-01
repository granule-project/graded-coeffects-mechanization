{-# OPTIONS --allow-unsolved-metas #-}

module Sec where

open import Relation.Binary.PropositionalEquality
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
                { carrier = Sec
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
