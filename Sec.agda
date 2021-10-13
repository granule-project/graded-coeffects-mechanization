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
distrib1 {Hi} {Hi} {Hi} = refl
distrib1 {Hi} {Hi} {Lo} = refl
distrib1 {Hi} {Lo} {Hi} = refl
distrib1 {Hi} {Lo} {Lo} = refl
distrib1 {Lo} {Hi} {Hi} = refl
distrib1 {Lo} {Hi} {Lo} = refl
distrib1 {Lo} {Lo} {Hi} = refl
distrib1 {Lo} {Lo} {Lo} = refl

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

orderReified : (r : Sec) -> (s : Sec) -> Dec (SecOrder r s)
orderReified Hi Hi = yes ReflHi
orderReified Hi Lo = no (λ ())
orderReified Lo Hi = yes LoHi
orderReified Lo Lo = yes ReflLo

monotone* : {r1 r2 s1 s2 : Sec} -> SecOrder r1 r2 -> SecOrder s1 s2 -> SecOrder (r1 *R s1) (r2 *R s2)
monotone* ReflLo ReflLo = ReflLo
monotone* ReflLo ReflHi = ReflHi
monotone* ReflLo LoHi = LoHi
monotone* ReflHi ReflLo = ReflHi
monotone* ReflHi ReflHi = ReflHi
monotone* ReflHi LoHi = ReflHi
monotone* LoHi ReflLo = LoHi
monotone* LoHi ReflHi = ReflHi
monotone* LoHi LoHi = LoHi

monotone+ : {r1 r2 s1 s2 : Sec} -> SecOrder r1 r2 -> SecOrder s1 s2 -> SecOrder (r1 +R s1) (r2 +R s2)
monotone+ {.Lo} {.Lo} {.Lo} {.Lo} ReflLo ReflLo = ReflLo
monotone+ {.Lo} {.Lo} {.Hi} {.Hi} ReflLo ReflHi = ReflLo
monotone+ {.Lo} {.Lo} {.Lo} {.Hi} ReflLo LoHi   = ReflLo
monotone+ {.Hi} {.Hi} {s1} {s2} ReflHi pre2 rewrite leftUnit+ {s1} | leftUnit+ {s2} = pre2
monotone+ {.Lo} {.Hi} {.Lo} {.Lo} LoHi ReflLo   = ReflLo
monotone+ {.Lo} {.Hi} {.Hi} {.Hi} LoHi ReflHi   = LoHi
monotone+ {.Lo} {.Hi} {.Lo} {.Hi} LoHi LoHi     = LoHi

reflexive≤ : {r : Sec} -> SecOrder r r
reflexive≤ {Hi} = ReflHi
reflexive≤ {Lo} = ReflLo

transitive≤ : {r s t : Sec} -> SecOrder r s -> SecOrder s t -> SecOrder r t
transitive≤ {.Lo} {.Lo} {t} ReflLo pre2 = pre2
transitive≤ {.Hi} {.Hi} {t} ReflHi pre2 = pre2
transitive≤ {.Lo} {.Hi} {.Hi} LoHi ReflHi = LoHi

instance
  secSemiring : Semiring
  secSemiring = record
                { grade = Sec
                ; 1R = 1r
                ; 0R = 0r
                ; _+R_ = _+R_
                ; _*R_ = _*R_
                ; _≤_ = SecOrder
                ; _≤d_ = orderReified
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

decreasing+ : {r1 r2 adv : Sec} -> (SecOrder r1 adv) -> (SecOrder (r1 +R r2) adv)
decreasing+ {Hi} {Hi} {Hi} ReflHi = ReflHi
decreasing+ {Hi} {Hi} {Lo} ()
decreasing+ {Hi} {Lo} {Hi} ReflHi = LoHi
decreasing+ {Hi} {Lo} {Lo} ()
decreasing+ {Lo} {Hi} {Hi} LoHi   = LoHi
decreasing+ {Lo} {Hi} {Lo} ReflLo = ReflLo
decreasing+ {Lo} {Lo} {Hi} LoHi   = LoHi
decreasing+ {Lo} {Lo} {Lo} ReflLo = ReflLo

propTimesIdem : {r : Sec} -> (r *R r) ≡ r
propTimesIdem {Hi} = refl
propTimesIdem {Lo} = refl

antisym : {r s : Sec} -> (r ≤ s) -> (s ≤ r) -> r ≡ s
antisym {Hi} {Hi} pre1 pre2 = refl
antisym {Hi} {Lo} () pre2
antisym {Lo} {Hi} LoHi ()
antisym {Lo} {Lo} pre1 pre2 = refl

oneIsBot : {r : Sec} -> 1r ≤ r
oneIsBot {Hi} = LoHi
oneIsBot {Lo} = ReflLo

secSemiringNI : NonInterferingSemiring secSemiring
secSemiringNI = record
                  { oneIsBottom            = oneIsBot
                  ; antisymmetry           = antisym
                  ; decreasing+               = decreasing+
                  ; idem*   = propTimesIdem
                  }
