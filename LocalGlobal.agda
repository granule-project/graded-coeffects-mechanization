module LocalGlobal where

open import Semiring
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Agda.Builtin.Bool

data Locality : Set where
  Unused : Locality -- 0
  Local  : Locality -- 1, i.e., we can do `a [Local] -> a`
  Global : Locality
  Arb    : Locality

data Ordering : Locality -> Locality -> Set where

  ArbToLocal    : Ordering Arb    Local -- Arb < Local
  ArbToGlobal   : Ordering Arb    Global -- Arb < Global
  GlobalToLocal : Ordering Global Local -- Global < Local

 -- Discussion: (maybe Local < Unused ?)
 -- JP: order for Unused<->Arb? 

{-

x : Local A  |- t : B
-----------------------
x : Global A |- t : B

BUT NOT

x : Global A  /|- t : B
-----------------------
x : Local A /|- t : B

-}

  ReflL         : Ordering Local  Local
  ReflG         : Ordering Global Global
  Refl0         : Ordering Unused Unused
  ReflA         : Ordering Arb    Arb

_+l_ : Locality -> Locality -> Locality
Unused +l y      = y
y      +l Unused = y
Local  +l Local  = Local
Arb    +l y      = Arb
y      +l Arb    = Arb
x      +l Global = Global
Global +l y      = Global

_*l_ : Locality -> Locality -> Locality
Unused *l y      = Unused
y      *l Unused = Unused
Local  *l Local  = Local
Arb    *l x      = Arb
x      *l Arb    = Arb
x      *l Global = Global
Global *l y      = Global


{-
x : Local |- t : A
--------------------------------------
x : Global |- [Global] t : A [Global]

-}


-- f : (Handle -> a [Global])
-------------------------------
-- withFile s f : a [Global]



--        e : a [Global]
---------------------------------------------
-- region e : a [Global]


-- e1 : a [Local]
-- e2 : b [Local]
-------------------
--- <e1, e2> : (a, b) [Local]

localGlobal : Semiring
localGlobal =
  record
    { grade = Locality
    ; 1R = Local  -- i.e., we can go a [Local] -> a
    ; 0R = Unused
    ; _+R_ = _+l_
    ; _*R_ = _*l_
    ; _≤_ = Ordering
    ; _≤d_ = dec<=
    ; leftUnit+ = refl
    ; rightUnit+ = right+
    ; comm+ = \{r} {s} -> commPlus {r} {s}
    ; leftUnit* = leftUnit*
    ; rightUnit* = rightUnit*
    ; leftAbsorb = refl
    ; rightAbsorb = rightabsorb
    ; assoc* = assoc*
    ; assoc+ = \{r} {s} {t} -> assocPlus {r} {s} {t}
    ; distrib1 = distrib1
    ; distrib2 = \{r} {s} {t} -> distrib2prop {r} {s} {t}
    ; monotone* = mon*
    ; monotone+ = mon+
    ; reflexive≤ = reflexive
    ; transitive≤ = transt
    }
  where
    reflexive : {r : Locality} → Ordering r r
    reflexive {Local} = ReflL
    reflexive {Global} = ReflG
    reflexive {Unused} = Refl0
    reflexive {Arb} = ReflA

    transt : {r s t : Locality} →
      Ordering r s → Ordering s t → Ordering r t
    transt {.Global} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    transt {.Arb} {.Local} {.Local} ArbToLocal ReflL = ArbToLocal
    transt {.Arb} {.Global} {.Local} ArbToGlobal GlobalToLocal = ArbToLocal
    transt {.Arb} {.Global} {.Global} ArbToGlobal ReflG = ArbToGlobal
    transt {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    transt {.Global} {.Global} {.Local} ReflG GlobalToLocal = GlobalToLocal
    transt {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    transt {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0
    transt {.Arb} {.Arb} {.Local} ReflA ArbToLocal = ArbToLocal
    transt {.Arb} {.Arb} {.Global} ReflA ArbToGlobal = ArbToGlobal
    transt {.Arb} {.Arb} {.Arb} ReflA ReflA = ReflA

    dec<= :  (r s : Locality) → Dec (Ordering r s)
    dec<= Local Local = yes ReflL
    dec<= Local Global = no (λ ())
    dec<= Local Arb = no (\ ())
    dec<= Local Unused = no (\ ())
    dec<= Global Local = yes GlobalToLocal
    dec<= Global Global = yes ReflG
    dec<= Global Arb = no (\ ())
    dec<= Global Unused = no (\())
    dec<= Arb Local = yes ArbToLocal
    dec<= Arb Global = yes ArbToGlobal
    dec<= Arb Arb = yes ReflA
    dec<= Arb Unused = no (\ ())
    dec<= Unused Local = no (\ ())
    dec<= Unused Global = no (\())
    dec<= Unused Arb = no (\ ())
    dec<= Unused Unused = yes Refl0


    right+ : {x : Locality} -> (x +l Unused) ≡ x
    right+ {Local} = refl
    right+ {Global} = refl
    right+ {Unused} = refl
    right+ {Arb} = refl

    commPlus : {x y : Locality} -> (x +l y) ≡ (y +l x)
    commPlus {Local} {Local} = refl
    commPlus {Local} {Global} = refl
    commPlus {Local} {Unused} = refl
    commPlus {Local} {Arb} = refl
    commPlus {Global} {Local} = refl
    commPlus {Global} {Global} = refl
    commPlus {Global} {Unused} = refl
    commPlus {Global} {Arb} = refl
    commPlus {Unused} {Local} = refl
    commPlus {Unused} {Global} = refl
    commPlus {Unused} {Unused} = refl
    commPlus {Unused} {Arb} = refl
    commPlus {Arb} {Local} = refl
    commPlus {Arb} {Global} = refl
    commPlus {Arb} {Unused} = refl
    commPlus {Arb} {Arb} = refl

    leftUnit* : {x : Locality} ->  (Local *l x) ≡ x
    leftUnit* {Local} = refl
    leftUnit* {Global} = refl
    leftUnit* {Unused} = refl
    leftUnit* {Arb}    = refl

    rightUnit* : {x : Locality} ->  (x *l Local) ≡ x
    rightUnit* {Local} = refl
    rightUnit* {Global} = refl
    rightUnit* {Unused} = refl
    rightUnit* {Arb} = refl

    rightabsorb : {x : Locality} → (x *l Unused) ≡ Unused
    rightabsorb {Local} = refl
    rightabsorb {Global} = refl
    rightabsorb {Unused} = refl
    rightabsorb {Arb} = refl

    mon* : {r1 r2 s1 s2 : Locality} →
      Ordering r1 r2 → Ordering s1 s2 → Ordering (r1 *l s1) (r2 *l s2)
    mon* {.Global} {.Local} {.Global} {.Local} GlobalToLocal GlobalToLocal = GlobalToLocal
    mon* {.Global} {.Local} {.Arb} {.Local} GlobalToLocal ArbToLocal = ArbToLocal
    mon* {.Global} {.Local} {.Arb} {.Global} GlobalToLocal ArbToGlobal = ArbToGlobal
    mon* {.Global} {.Local} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    mon* {.Global} {.Local} {.Global} {.Global} GlobalToLocal ReflG = ReflG
    mon* {.Global} {.Local} {.Unused} {.Unused} GlobalToLocal Refl0 = Refl0
    mon* {.Global} {.Local} {.Arb} {.Arb} GlobalToLocal ReflA = ReflA
    mon* {.Arb} {.Local} {.Global} {.Local} ArbToLocal GlobalToLocal = ArbToLocal
    mon* {.Arb} {.Local} {.Arb} {.Local} ArbToLocal ArbToLocal = ArbToLocal
    mon* {.Arb} {.Local} {.Arb} {.Global} ArbToLocal ArbToGlobal = ArbToGlobal
    mon* {.Arb} {.Local} {.Local} {.Local} ArbToLocal ReflL = ArbToLocal
    mon* {.Arb} {.Local} {.Global} {.Global} ArbToLocal ReflG = ArbToGlobal
    mon* {.Arb} {.Local} {.Unused} {.Unused} ArbToLocal Refl0 = Refl0
    mon* {.Arb} {.Local} {.Arb} {.Arb} ArbToLocal ReflA = ReflA
    mon* {.Arb} {.Global} {.Global} {.Local} ArbToGlobal GlobalToLocal = ArbToGlobal
    mon* {.Arb} {.Global} {.Arb} {.Local} ArbToGlobal ArbToLocal = ArbToGlobal
    mon* {.Arb} {.Global} {.Arb} {.Global} ArbToGlobal ArbToGlobal = ArbToGlobal
    mon* {.Arb} {.Global} {.Local} {.Local} ArbToGlobal ReflL = ArbToGlobal
    mon* {.Arb} {.Global} {.Global} {.Global} ArbToGlobal ReflG = ArbToGlobal
    mon* {.Arb} {.Global} {.Unused} {.Unused} ArbToGlobal Refl0 = Refl0
    mon* {.Arb} {.Global} {.Arb} {.Arb} ArbToGlobal ReflA = ReflA
    mon* {.Local} {.Local} {.Global} {.Local} ReflL GlobalToLocal = GlobalToLocal
    mon* {.Local} {.Local} {.Arb} {.Local} ReflL ArbToLocal = ArbToLocal
    mon* {.Local} {.Local} {.Arb} {.Global} ReflL ArbToGlobal = ArbToGlobal
    mon* {.Local} {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    mon* {.Local} {.Local} {.Global} {.Global} ReflL ReflG = ReflG
    mon* {.Local} {.Local} {.Unused} {.Unused} ReflL Refl0 = Refl0
    mon* {.Local} {.Local} {.Arb} {.Arb} ReflL ReflA = ReflA
    mon* {.Global} {.Global} {.Global} {.Local} ReflG GlobalToLocal = ReflG
    mon* {.Global} {.Global} {.Arb} {.Local} ReflG ArbToLocal = ArbToGlobal
    mon* {.Global} {.Global} {.Arb} {.Global} ReflG ArbToGlobal = ArbToGlobal
    mon* {.Global} {.Global} {.Local} {.Local} ReflG ReflL = ReflG
    mon* {.Global} {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    mon* {.Global} {.Global} {.Unused} {.Unused} ReflG Refl0 = Refl0
    mon* {.Global} {.Global} {.Arb} {.Arb} ReflG ReflA = ReflA
    mon* {.Unused} {.Unused} {.Global} {.Local} Refl0 GlobalToLocal = Refl0
    mon* {.Unused} {.Unused} {.Arb} {.Local} Refl0 ArbToLocal = Refl0
    mon* {.Unused} {.Unused} {.Arb} {.Global} Refl0 ArbToGlobal = Refl0
    mon* {.Unused} {.Unused} {.Local} {.Local} Refl0 ReflL = Refl0
    mon* {.Unused} {.Unused} {.Global} {.Global} Refl0 ReflG = Refl0
    mon* {.Unused} {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0
    mon* {.Unused} {.Unused} {.Arb} {.Arb} Refl0 ReflA = Refl0
    mon* {.Arb} {.Arb} {.Global} {.Local} ReflA GlobalToLocal = ReflA
    mon* {.Arb} {.Arb} {.Arb} {.Local} ReflA ArbToLocal = ReflA
    mon* {.Arb} {.Arb} {.Arb} {.Global} ReflA ArbToGlobal = ReflA
    mon* {.Arb} {.Arb} {.Local} {.Local} ReflA ReflL = ReflA
    mon* {.Arb} {.Arb} {.Global} {.Global} ReflA ReflG = ReflA
    mon* {.Arb} {.Arb} {.Unused} {.Unused} ReflA Refl0 = Refl0
    mon* {.Arb} {.Arb} {.Arb} {.Arb} ReflA ReflA = ReflA

    mon+ : {r1 r2 s1 s2 : Locality} →
      Ordering r1 r2 → Ordering s1 s2 → Ordering (r1 +l s1) (r2 +l s2)
    mon+ {.Global} {.Local} {.Global} {.Local} GlobalToLocal GlobalToLocal = GlobalToLocal
    mon+ {.Global} {.Local} {.Arb} {.Local} GlobalToLocal ArbToLocal = ArbToLocal
    mon+ {.Global} {.Local} {.Arb} {.Global} GlobalToLocal ArbToGlobal = ArbToGlobal
    mon+ {.Global} {.Local} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    mon+ {.Global} {.Local} {.Global} {.Global} GlobalToLocal ReflG = ReflG
    mon+ {.Global} {.Local} {.Unused} {.Unused} GlobalToLocal Refl0 = GlobalToLocal
    mon+ {.Global} {.Local} {.Arb} {.Arb} GlobalToLocal ReflA = ReflA
    mon+ {.Arb} {.Local} {.Global} {.Local} ArbToLocal GlobalToLocal = ArbToLocal
    mon+ {.Arb} {.Local} {.Arb} {.Local} ArbToLocal ArbToLocal = ArbToLocal
    mon+ {.Arb} {.Local} {.Arb} {.Global} ArbToLocal ArbToGlobal = ArbToGlobal
    mon+ {.Arb} {.Local} {.Local} {.Local} ArbToLocal ReflL = ArbToLocal
    mon+ {.Arb} {.Local} {.Global} {.Global} ArbToLocal ReflG = ArbToGlobal
    mon+ {.Arb} {.Local} {.Unused} {.Unused} ArbToLocal Refl0 = ArbToLocal
    mon+ {.Arb} {.Local} {.Arb} {.Arb} ArbToLocal ReflA = ReflA
    mon+ {.Arb} {.Global} {.Global} {.Local} ArbToGlobal GlobalToLocal = ArbToGlobal
    mon+ {.Arb} {.Global} {.Arb} {.Local} ArbToGlobal ArbToLocal = ArbToGlobal
    mon+ {.Arb} {.Global} {.Arb} {.Global} ArbToGlobal ArbToGlobal = ArbToGlobal
    mon+ {.Arb} {.Global} {.Local} {.Local} ArbToGlobal ReflL = ArbToGlobal
    mon+ {.Arb} {.Global} {.Global} {.Global} ArbToGlobal ReflG = ArbToGlobal
    mon+ {.Arb} {.Global} {.Unused} {.Unused} ArbToGlobal Refl0 = ArbToGlobal
    mon+ {.Arb} {.Global} {.Arb} {.Arb} ArbToGlobal ReflA = ReflA
    mon+ {.Local} {.Local} {.Global} {.Local} ReflL GlobalToLocal = GlobalToLocal
    mon+ {.Local} {.Local} {.Arb} {.Local} ReflL ArbToLocal = ArbToLocal
    mon+ {.Local} {.Local} {.Arb} {.Global} ReflL ArbToGlobal = ArbToGlobal
    mon+ {.Local} {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    mon+ {.Local} {.Local} {.Global} {.Global} ReflL ReflG = ReflG
    mon+ {.Local} {.Local} {.Unused} {.Unused} ReflL Refl0 = ReflL
    mon+ {.Local} {.Local} {.Arb} {.Arb} ReflL ReflA = ReflA
    mon+ {.Global} {.Global} {.Global} {.Local} ReflG GlobalToLocal = ReflG
    mon+ {.Global} {.Global} {.Arb} {.Local} ReflG ArbToLocal = ArbToGlobal
    mon+ {.Global} {.Global} {.Arb} {.Global} ReflG ArbToGlobal = ArbToGlobal
    mon+ {.Global} {.Global} {.Local} {.Local} ReflG ReflL = ReflG
    mon+ {.Global} {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    mon+ {.Global} {.Global} {.Unused} {.Unused} ReflG Refl0 = ReflG
    mon+ {.Global} {.Global} {.Arb} {.Arb} ReflG ReflA = ReflA
    mon+ {.Unused} {.Unused} {.Global} {.Local} Refl0 GlobalToLocal = GlobalToLocal
    mon+ {.Unused} {.Unused} {.Arb} {.Local} Refl0 ArbToLocal = ArbToLocal
    mon+ {.Unused} {.Unused} {.Arb} {.Global} Refl0 ArbToGlobal = ArbToGlobal
    mon+ {.Unused} {.Unused} {.Local} {.Local} Refl0 ReflL = ReflL
    mon+ {.Unused} {.Unused} {.Global} {.Global} Refl0 ReflG = ReflG
    mon+ {.Unused} {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0
    mon+ {.Unused} {.Unused} {.Arb} {.Arb} Refl0 ReflA = ReflA
    mon+ {.Arb} {.Arb} {.Global} {.Local} ReflA GlobalToLocal = ReflA
    mon+ {.Arb} {.Arb} {.Arb} {.Local} ReflA ArbToLocal = ReflA
    mon+ {.Arb} {.Arb} {.Arb} {.Global} ReflA ArbToGlobal = ReflA
    mon+ {.Arb} {.Arb} {.Local} {.Local} ReflA ReflL = ReflA
    mon+ {.Arb} {.Arb} {.Global} {.Global} ReflA ReflG = ReflA
    mon+ {.Arb} {.Arb} {.Unused} {.Unused} ReflA Refl0 = ReflA
    mon+ {.Arb} {.Arb} {.Arb} {.Arb} ReflA ReflA = ReflA

    assoc* : {r s t : Locality} → ((r *l s) *l t) ≡ (r *l (s *l t))
    assoc* {Local} {Local} {Local} = refl
    assoc* {Local} {Local} {Global} = refl
    assoc* {Local} {Local} {Arb} = refl
    assoc* {Local} {Local} {Unused} = refl
    assoc* {Local} {Global} {Local} = refl
    assoc* {Local} {Global} {Global} = refl
    assoc* {Local} {Global} {Arb} = refl
    assoc* {Local} {Global} {Unused} = refl
    assoc* {Local} {Arb} {Local} = refl
    assoc* {Local} {Arb} {Global} = refl
    assoc* {Local} {Arb} {Arb} = refl
    assoc* {Local} {Arb} {Unused} = refl
    assoc* {Local} {Unused} {t} = refl
    assoc* {Global} {Local} {Local} = refl
    assoc* {Global} {Local} {Global} = refl
    assoc* {Global} {Local} {Arb} = refl
    assoc* {Global} {Local} {Unused} = refl
    assoc* {Global} {Global} {Local} = refl
    assoc* {Global} {Global} {Global} = refl
    assoc* {Global} {Global} {Arb} = refl
    assoc* {Global} {Global} {Unused} = refl
    assoc* {Global} {Arb} {Local} = refl
    assoc* {Global} {Arb} {Global} = refl
    assoc* {Global} {Arb} {Arb} = refl
    assoc* {Global} {Arb} {Unused} = refl
    assoc* {Global} {Unused} {t} = refl
    assoc* {Arb} {Local} {Local} = refl
    assoc* {Arb} {Local} {Global} = refl
    assoc* {Arb} {Local} {Arb} = refl
    assoc* {Arb} {Local} {Unused} = refl
    assoc* {Arb} {Global} {Local} = refl
    assoc* {Arb} {Global} {Global} = refl
    assoc* {Arb} {Global} {Arb} = refl
    assoc* {Arb} {Global} {Unused} = refl
    assoc* {Arb} {Arb} {Local} = refl
    assoc* {Arb} {Arb} {Global} = refl
    assoc* {Arb} {Arb} {Arb} = refl
    assoc* {Arb} {Arb} {Unused} = refl
    assoc* {Arb} {Unused} {t} = refl
    assoc* {Unused} {s} {t} = refl

    distrib1 : {r s t : Locality} → (r *l (s +l t)) ≡ ((r *l s) +l (r *l t))
    distrib1 {Local} {s} {t} rewrite leftUnit* {s +l t} | leftUnit* {s} | leftUnit* {t} = refl
    distrib1 {Global} {Local} {Local} = refl
    distrib1 {Global} {Local} {Global} = refl
    distrib1 {Global} {Local} {Arb} = refl
    distrib1 {Global} {Local} {Unused} = refl
    distrib1 {Global} {Global} {Local} = refl
    distrib1 {Global} {Global} {Global} = refl
    distrib1 {Global} {Global} {Arb} = refl
    distrib1 {Global} {Global} {Unused} = refl
    distrib1 {Global} {Arb} {Local} = refl
    distrib1 {Global} {Arb} {Global} = refl
    distrib1 {Global} {Arb} {Arb} = refl
    distrib1 {Global} {Arb} {Unused} = refl
    distrib1 {Global} {Unused} {Local} = refl
    distrib1 {Global} {Unused} {Global} = refl
    distrib1 {Global} {Unused} {Arb} = refl
    distrib1 {Global} {Unused} {Unused} = refl
    distrib1 {Arb} {Local} {Local} = refl
    distrib1 {Arb} {Local} {Global} = refl
    distrib1 {Arb} {Local} {Arb} = refl
    distrib1 {Arb} {Local} {Unused} = refl
    distrib1 {Arb} {Global} {Local} = refl
    distrib1 {Arb} {Global} {Global} = refl
    distrib1 {Arb} {Global} {Arb} = refl
    distrib1 {Arb} {Global} {Unused} = refl
    distrib1 {Arb} {Arb} {Local} = refl
    distrib1 {Arb} {Arb} {Global} = refl
    distrib1 {Arb} {Arb} {Arb} = refl
    distrib1 {Arb} {Arb} {Unused} = refl
    distrib1 {Arb} {Unused} {Local} = refl
    distrib1 {Arb} {Unused} {Global} = refl
    distrib1 {Arb} {Unused} {Arb} = refl
    distrib1 {Arb} {Unused} {Unused} = refl
    distrib1 {Unused} {s} {t} = refl

    -- used by distrib2
    comm* : {x y : Locality} -> x *l y ≡ y *l x
    comm* {Local} {Local} = refl
    comm* {Local} {Global} = refl
    comm* {Local} {Arb} = refl
    comm* {Local} {Unused} = refl
    comm* {Global} {Local} = refl
    comm* {Global} {Global} = refl
    comm* {Global} {Arb} = refl
    comm* {Global} {Unused} = refl
    comm* {Arb} {Local} = refl
    comm* {Arb} {Global} = refl
    comm* {Arb} {Arb} = refl
    comm* {Arb} {Unused} = refl
    comm* {Unused} {Local} = refl
    comm* {Unused} {Global} = refl
    comm* {Unused} {Arb} = refl
    comm* {Unused} {Unused} = refl

    distrib2prop : {r s t : Locality} → ((r +l s) *l t) ≡ ((r *l t) +l (s *l t))
    distrib2prop {r} {s} {t} rewrite comm* {r +l s} {t} | comm* {r} {t} | comm* {s} {t} = distrib1

    assocPlus : {r s t : Locality} → ((r +l s) +l t) ≡ (r +l (s +l t))
    assocPlus {Local} {Local} {Local} = refl
    assocPlus {Local} {Local} {Global} = refl
    assocPlus {Local} {Local} {Arb} = refl
    assocPlus {Local} {Local} {Unused} = refl
    assocPlus {Local} {Global} {Local} = refl
    assocPlus {Local} {Global} {Global} = refl
    assocPlus {Local} {Global} {Arb} = refl
    assocPlus {Local} {Global} {Unused} = refl
    assocPlus {Local} {Arb} {Local} = refl
    assocPlus {Local} {Arb} {Global} = refl
    assocPlus {Local} {Arb} {Arb} = refl
    assocPlus {Local} {Arb} {Unused} = refl
    assocPlus {Local} {Unused} {t} = refl
    assocPlus {Global} {Local} {Local} = refl
    assocPlus {Global} {Local} {Global} = refl
    assocPlus {Global} {Local} {Arb} = refl
    assocPlus {Global} {Local} {Unused} = refl
    assocPlus {Global} {Global} {Local} = refl
    assocPlus {Global} {Global} {Global} = refl
    assocPlus {Global} {Global} {Arb} = refl
    assocPlus {Global} {Global} {Unused} = refl
    assocPlus {Global} {Arb} {Local} = refl
    assocPlus {Global} {Arb} {Global} = refl
    assocPlus {Global} {Arb} {Arb} = refl
    assocPlus {Global} {Arb} {Unused} = refl
    assocPlus {Global} {Unused} {t} = refl
    assocPlus {Arb} {Local} {Local} = refl
    assocPlus {Arb} {Local} {Global} = refl
    assocPlus {Arb} {Local} {Arb} = refl
    assocPlus {Arb} {Local} {Unused} = refl
    assocPlus {Arb} {Global} {Local} = refl
    assocPlus {Arb} {Global} {Global} = refl
    assocPlus {Arb} {Global} {Arb} = refl
    assocPlus {Arb} {Global} {Unused} = refl
    assocPlus {Arb} {Arb} {Local} = refl
    assocPlus {Arb} {Arb} {Global} = refl
    assocPlus {Arb} {Arb} {Arb} = refl
    assocPlus {Arb} {Arb} {Unused} = refl
    assocPlus {Arb} {Unused} {t} = refl
    assocPlus {Unused} {s} {t} = refl
