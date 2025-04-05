module LocalGlobal where

open import Semiring
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Agda.Builtin.Bool

data Locality : Set where
  Unused   : Locality -- 0
  Global   : Locality
  Local    : Locality -- i.e. not Global
  Anywhere : Locality -- 1 i.e. default

data Ordering : Locality -> Locality -> Set where
  GlobalToLocal    : Ordering Global   Local    -- Global   < Local
  AnywhereToLocal  : Ordering Anywhere Local    -- Anywhere < Local
  GlobalToAnywhere : Ordering Global   Anywhere -- Global   < Anywhere


{-

x : Local A  |- t : B
-----------------------
x : Global A |- t : B

BUT NOT

x : Global A  /|- t : B
-----------------------
x : Local A /|- t : B

-}

  Refl0            : Ordering Unused   Unused
  ReflG            : Ordering Global   Global
  ReflL            : Ordering Local    Local
  ReflA            : Ordering Anywhere Anywhere

_+l_ : Locality -> Locality -> Locality
Unused   +l x        = x
x        +l Unused   = x
Global   +l x        = Global
x        +l Global   = Global
Local    +l x        = Local
x        +l Local    = Local
Anywhere +l Anywhere = Anywhere

_*l_ : Locality -> Locality -> Locality
Unused   *l x        = Unused
x        *l Unused   = Unused
Global   *l x        = Global
x        *l Global   = Global
Local    *l x        = Local
x        *l Local    = Local
Anywhere *l Anywhere = Anywhere


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
    ; 1R = Anywhere
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
    reflexive : {r : Locality} -> Ordering r r
    reflexive {Unused} = Refl0
    reflexive {Global} = ReflG
    reflexive {Local} = ReflL
    reflexive {Anywhere} = ReflA

    transt : {r s t : Locality} ->
      Ordering r s -> Ordering s t -> Ordering r t
    transt {.Global} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    transt {.Anywhere} {.Local} {.Local} AnywhereToLocal ReflL = AnywhereToLocal
    transt {.Global} {.Anywhere} {.Local} GlobalToAnywhere AnywhereToLocal = GlobalToLocal
    transt {.Global} {.Anywhere} {.Anywhere} GlobalToAnywhere ReflA = GlobalToAnywhere
    transt {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0
    transt {.Global} {.Global} {.Local} ReflG GlobalToLocal = GlobalToLocal
    transt {.Global} {.Global} {.Anywhere} ReflG GlobalToAnywhere = GlobalToAnywhere
    transt {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    transt {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    transt {.Anywhere} {.Anywhere} {.Local} ReflA AnywhereToLocal = AnywhereToLocal
    transt {.Anywhere} {.Anywhere} {.Anywhere} ReflA ReflA = ReflA

    dec<= :  (r s : Locality) -> Dec (Ordering r s)
    dec<= Unused Unused = yes Refl0
    dec<= Unused Global = no (λ ())
    dec<= Unused Local = no (λ ())
    dec<= Unused Anywhere = no (λ ())
    dec<= Global Unused = no (λ ())
    dec<= Global Global = yes ReflG
    dec<= Global Local = yes GlobalToLocal
    dec<= Global Anywhere = yes GlobalToAnywhere
    dec<= Local Unused = no (λ ())
    dec<= Local Global = no (λ ())
    dec<= Local Local = yes ReflL
    dec<= Local Anywhere = no (λ ())
    dec<= Anywhere Unused = no (λ ())
    dec<= Anywhere Global = no (λ ())
    dec<= Anywhere Local = yes AnywhereToLocal
    dec<= Anywhere Anywhere = yes ReflA

    right+ : {x : Locality} -> (x +l Unused) ≡ x
    right+ {Unused} = refl
    right+ {Global} = refl
    right+ {Local} = refl
    right+ {Anywhere} = refl

    commPlus : {x y : Locality} -> (x +l y) ≡ (y +l x)
    commPlus {Unused} {Unused} = refl
    commPlus {Unused} {Global} = refl
    commPlus {Unused} {Local} = refl
    commPlus {Unused} {Anywhere} = refl
    commPlus {Global} {Unused} = refl
    commPlus {Global} {Global} = refl
    commPlus {Global} {Local} = refl
    commPlus {Global} {Anywhere} = refl
    commPlus {Local} {Unused} = refl
    commPlus {Local} {Global} = refl
    commPlus {Local} {Local} = refl
    commPlus {Local} {Anywhere} = refl
    commPlus {Anywhere} {Unused} = refl
    commPlus {Anywhere} {Global} = refl
    commPlus {Anywhere} {Local} = refl
    commPlus {Anywhere} {Anywhere} = refl

    leftUnit* : {x : Locality} -> (Anywhere *l x) ≡ x
    leftUnit* {Unused} = refl
    leftUnit* {Global} = refl
    leftUnit* {Local} = refl
    leftUnit* {Anywhere} = refl

    rightUnit* : {x : Locality} -> (x *l Anywhere) ≡ x
    rightUnit* {Unused} = refl
    rightUnit* {Global} = refl
    rightUnit* {Local} = refl
    rightUnit* {Anywhere} = refl

    rightabsorb : {x : Locality} -> (x *l Unused) ≡ Unused
    rightabsorb {Unused} = refl
    rightabsorb {Global} = refl
    rightabsorb {Local} = refl
    rightabsorb {Anywhere} = refl

    mon* : {r1 r2 s1 s2 : Locality} ->
      Ordering r1 r2 -> Ordering s1 s2 -> Ordering (r1 *l s1) (r2 *l s2)
    mon* {.Global} {.Local} {.Global} {.Local} GlobalToLocal GlobalToLocal = GlobalToLocal
    mon* {.Global} {.Local} {.Anywhere} {.Local} GlobalToLocal AnywhereToLocal = GlobalToLocal
    mon* {.Global} {.Local} {.Global} {.Anywhere} GlobalToLocal GlobalToAnywhere = GlobalToLocal
    mon* {.Global} {.Local} {.Unused} {.Unused} GlobalToLocal Refl0 = Refl0
    mon* {.Global} {.Local} {.Global} {.Global} GlobalToLocal ReflG = ReflG
    mon* {.Global} {.Local} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    mon* {.Global} {.Local} {.Anywhere} {.Anywhere} GlobalToLocal ReflA = GlobalToLocal
    mon* {.Anywhere} {.Local} {.Global} {.Local} AnywhereToLocal GlobalToLocal = GlobalToLocal
    mon* {.Anywhere} {.Local} {.Anywhere} {.Local} AnywhereToLocal AnywhereToLocal = AnywhereToLocal
    mon* {.Anywhere} {.Local} {.Global} {.Anywhere} AnywhereToLocal GlobalToAnywhere = GlobalToLocal
    mon* {.Anywhere} {.Local} {.Unused} {.Unused} AnywhereToLocal Refl0 = Refl0
    mon* {.Anywhere} {.Local} {.Global} {.Global} AnywhereToLocal ReflG = ReflG
    mon* {.Anywhere} {.Local} {.Local} {.Local} AnywhereToLocal ReflL = ReflL
    mon* {.Anywhere} {.Local} {.Anywhere} {.Anywhere} AnywhereToLocal ReflA = AnywhereToLocal
    mon* {.Global} {.Anywhere} {.Global} {.Local} GlobalToAnywhere GlobalToLocal = GlobalToLocal
    mon* {.Global} {.Anywhere} {.Anywhere} {.Local} GlobalToAnywhere AnywhereToLocal = GlobalToLocal
    mon* {.Global} {.Anywhere} {.Global} {.Anywhere} GlobalToAnywhere GlobalToAnywhere = GlobalToAnywhere
    mon* {.Global} {.Anywhere} {.Unused} {.Unused} GlobalToAnywhere Refl0 = Refl0
    mon* {.Global} {.Anywhere} {.Global} {.Global} GlobalToAnywhere ReflG = ReflG
    mon* {.Global} {.Anywhere} {.Local} {.Local} GlobalToAnywhere ReflL = GlobalToLocal
    mon* {.Global} {.Anywhere} {.Anywhere} {.Anywhere} GlobalToAnywhere ReflA = GlobalToAnywhere
    mon* {.Unused} {.Unused} {.Global} {.Local} Refl0 GlobalToLocal = Refl0
    mon* {.Unused} {.Unused} {.Anywhere} {.Local} Refl0 AnywhereToLocal = Refl0
    mon* {.Unused} {.Unused} {.Global} {.Anywhere} Refl0 GlobalToAnywhere = Refl0
    mon* {.Unused} {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0
    mon* {.Unused} {.Unused} {.Global} {.Global} Refl0 ReflG = Refl0
    mon* {.Unused} {.Unused} {.Local} {.Local} Refl0 ReflL = Refl0
    mon* {.Unused} {.Unused} {.Anywhere} {.Anywhere} Refl0 ReflA = Refl0
    mon* {.Global} {.Global} {.Global} {.Local} ReflG GlobalToLocal = ReflG
    mon* {.Global} {.Global} {.Anywhere} {.Local} ReflG AnywhereToLocal = ReflG
    mon* {.Global} {.Global} {.Global} {.Anywhere} ReflG GlobalToAnywhere = ReflG
    mon* {.Global} {.Global} {.Unused} {.Unused} ReflG Refl0 = Refl0
    mon* {.Global} {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    mon* {.Global} {.Global} {.Local} {.Local} ReflG ReflL = ReflG
    mon* {.Global} {.Global} {.Anywhere} {.Anywhere} ReflG ReflA = ReflG
    mon* {.Local} {.Local} {.Global} {.Local} ReflL GlobalToLocal = GlobalToLocal
    mon* {.Local} {.Local} {.Anywhere} {.Local} ReflL AnywhereToLocal = ReflL
    mon* {.Local} {.Local} {.Global} {.Anywhere} ReflL GlobalToAnywhere = GlobalToLocal
    mon* {.Local} {.Local} {.Unused} {.Unused} ReflL Refl0 = Refl0
    mon* {.Local} {.Local} {.Global} {.Global} ReflL ReflG = ReflG
    mon* {.Local} {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    mon* {.Local} {.Local} {.Anywhere} {.Anywhere} ReflL ReflA = ReflL
    mon* {.Anywhere} {.Anywhere} {.Global} {.Local} ReflA GlobalToLocal = GlobalToLocal
    mon* {.Anywhere} {.Anywhere} {.Anywhere} {.Local} ReflA AnywhereToLocal = AnywhereToLocal
    mon* {.Anywhere} {.Anywhere} {.Global} {.Anywhere} ReflA GlobalToAnywhere = GlobalToAnywhere
    mon* {.Anywhere} {.Anywhere} {.Unused} {.Unused} ReflA Refl0 = Refl0
    mon* {.Anywhere} {.Anywhere} {.Global} {.Global} ReflA ReflG = ReflG
    mon* {.Anywhere} {.Anywhere} {.Local} {.Local} ReflA ReflL = ReflL
    mon* {.Anywhere} {.Anywhere} {.Anywhere} {.Anywhere} ReflA ReflA = ReflA

    mon+ : {r1 r2 s1 s2 : Locality} ->
      Ordering r1 r2 -> Ordering s1 s2 -> Ordering (r1 +l s1) (r2 +l s2)
    mon+ {.Global} {.Local} {.Global} {.Local} GlobalToLocal GlobalToLocal = GlobalToLocal
    mon+ {.Global} {.Local} {.Anywhere} {.Local} GlobalToLocal AnywhereToLocal = GlobalToLocal
    mon+ {.Global} {.Local} {.Global} {.Anywhere} GlobalToLocal GlobalToAnywhere = GlobalToLocal
    mon+ {.Global} {.Local} {.Unused} {.Unused} GlobalToLocal Refl0 = GlobalToLocal
    mon+ {.Global} {.Local} {.Global} {.Global} GlobalToLocal ReflG = ReflG
    mon+ {.Global} {.Local} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    mon+ {.Global} {.Local} {.Anywhere} {.Anywhere} GlobalToLocal ReflA = GlobalToLocal
    mon+ {.Anywhere} {.Local} {.Global} {.Local} AnywhereToLocal GlobalToLocal = GlobalToLocal
    mon+ {.Anywhere} {.Local} {.Anywhere} {.Local} AnywhereToLocal AnywhereToLocal = AnywhereToLocal
    mon+ {.Anywhere} {.Local} {.Global} {.Anywhere} AnywhereToLocal GlobalToAnywhere = GlobalToLocal
    mon+ {.Anywhere} {.Local} {.Unused} {.Unused} AnywhereToLocal Refl0 = AnywhereToLocal
    mon+ {.Anywhere} {.Local} {.Global} {.Global} AnywhereToLocal ReflG = ReflG
    mon+ {.Anywhere} {.Local} {.Local} {.Local} AnywhereToLocal ReflL = ReflL
    mon+ {.Anywhere} {.Local} {.Anywhere} {.Anywhere} AnywhereToLocal ReflA = AnywhereToLocal
    mon+ {.Global} {.Anywhere} {.Global} {.Local} GlobalToAnywhere GlobalToLocal = GlobalToLocal
    mon+ {.Global} {.Anywhere} {.Anywhere} {.Local} GlobalToAnywhere AnywhereToLocal = GlobalToLocal
    mon+ {.Global} {.Anywhere} {.Global} {.Anywhere} GlobalToAnywhere GlobalToAnywhere = GlobalToAnywhere
    mon+ {.Global} {.Anywhere} {.Unused} {.Unused} GlobalToAnywhere Refl0 = GlobalToAnywhere
    mon+ {.Global} {.Anywhere} {.Global} {.Global} GlobalToAnywhere ReflG = ReflG
    mon+ {.Global} {.Anywhere} {.Local} {.Local} GlobalToAnywhere ReflL = GlobalToLocal
    mon+ {.Global} {.Anywhere} {.Anywhere} {.Anywhere} GlobalToAnywhere ReflA = GlobalToAnywhere
    mon+ {.Unused} {.Unused} {.Global} {.Local} Refl0 GlobalToLocal = GlobalToLocal
    mon+ {.Unused} {.Unused} {.Anywhere} {.Local} Refl0 AnywhereToLocal = AnywhereToLocal
    mon+ {.Unused} {.Unused} {.Global} {.Anywhere} Refl0 GlobalToAnywhere = GlobalToAnywhere
    mon+ {.Unused} {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0
    mon+ {.Unused} {.Unused} {.Global} {.Global} Refl0 ReflG = ReflG
    mon+ {.Unused} {.Unused} {.Local} {.Local} Refl0 ReflL = ReflL
    mon+ {.Unused} {.Unused} {.Anywhere} {.Anywhere} Refl0 ReflA = ReflA
    mon+ {.Global} {.Global} {.Global} {.Local} ReflG GlobalToLocal = ReflG
    mon+ {.Global} {.Global} {.Anywhere} {.Local} ReflG AnywhereToLocal = ReflG
    mon+ {.Global} {.Global} {.Global} {.Anywhere} ReflG GlobalToAnywhere = ReflG
    mon+ {.Global} {.Global} {.Unused} {.Unused} ReflG Refl0 = ReflG
    mon+ {.Global} {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    mon+ {.Global} {.Global} {.Local} {.Local} ReflG ReflL = ReflG
    mon+ {.Global} {.Global} {.Anywhere} {.Anywhere} ReflG ReflA = ReflG
    mon+ {.Local} {.Local} {.Global} {.Local} ReflL GlobalToLocal = GlobalToLocal
    mon+ {.Local} {.Local} {.Anywhere} {.Local} ReflL AnywhereToLocal = ReflL
    mon+ {.Local} {.Local} {.Global} {.Anywhere} ReflL GlobalToAnywhere = GlobalToLocal
    mon+ {.Local} {.Local} {.Unused} {.Unused} ReflL Refl0 = ReflL
    mon+ {.Local} {.Local} {.Global} {.Global} ReflL ReflG = ReflG
    mon+ {.Local} {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    mon+ {.Local} {.Local} {.Anywhere} {.Anywhere} ReflL ReflA = ReflL
    mon+ {.Anywhere} {.Anywhere} {.Global} {.Local} ReflA GlobalToLocal = GlobalToLocal
    mon+ {.Anywhere} {.Anywhere} {.Anywhere} {.Local} ReflA AnywhereToLocal = AnywhereToLocal
    mon+ {.Anywhere} {.Anywhere} {.Global} {.Anywhere} ReflA GlobalToAnywhere = GlobalToAnywhere
    mon+ {.Anywhere} {.Anywhere} {.Unused} {.Unused} ReflA Refl0 = ReflA
    mon+ {.Anywhere} {.Anywhere} {.Global} {.Global} ReflA ReflG = ReflG
    mon+ {.Anywhere} {.Anywhere} {.Local} {.Local} ReflA ReflL = ReflL
    mon+ {.Anywhere} {.Anywhere} {.Anywhere} {.Anywhere} ReflA ReflA = ReflA

    assoc* : {r s t : Locality} -> ((r *l s) *l t) ≡ (r *l (s *l t))
    assoc* {Unused} {Unused} {Unused} = refl
    assoc* {Unused} {Unused} {Global} = refl
    assoc* {Unused} {Unused} {Local} = refl
    assoc* {Unused} {Unused} {Anywhere} = refl
    assoc* {Unused} {Global} {Unused} = refl
    assoc* {Unused} {Global} {Global} = refl
    assoc* {Unused} {Global} {Local} = refl
    assoc* {Unused} {Global} {Anywhere} = refl
    assoc* {Unused} {Local} {Unused} = refl
    assoc* {Unused} {Local} {Global} = refl
    assoc* {Unused} {Local} {Local} = refl
    assoc* {Unused} {Local} {Anywhere} = refl
    assoc* {Unused} {Anywhere} {Unused} = refl
    assoc* {Unused} {Anywhere} {Global} = refl
    assoc* {Unused} {Anywhere} {Local} = refl
    assoc* {Unused} {Anywhere} {Anywhere} = refl
    assoc* {Global} {Unused} {Unused} = refl
    assoc* {Global} {Unused} {Global} = refl
    assoc* {Global} {Unused} {Local} = refl
    assoc* {Global} {Unused} {Anywhere} = refl
    assoc* {Global} {Global} {Unused} = refl
    assoc* {Global} {Global} {Global} = refl
    assoc* {Global} {Global} {Local} = refl
    assoc* {Global} {Global} {Anywhere} = refl
    assoc* {Global} {Local} {Unused} = refl
    assoc* {Global} {Local} {Global} = refl
    assoc* {Global} {Local} {Local} = refl
    assoc* {Global} {Local} {Anywhere} = refl
    assoc* {Global} {Anywhere} {Unused} = refl
    assoc* {Global} {Anywhere} {Global} = refl
    assoc* {Global} {Anywhere} {Local} = refl
    assoc* {Global} {Anywhere} {Anywhere} = refl
    assoc* {Local} {Unused} {Unused} = refl
    assoc* {Local} {Unused} {Global} = refl
    assoc* {Local} {Unused} {Local} = refl
    assoc* {Local} {Unused} {Anywhere} = refl
    assoc* {Local} {Global} {Unused} = refl
    assoc* {Local} {Global} {Global} = refl
    assoc* {Local} {Global} {Local} = refl
    assoc* {Local} {Global} {Anywhere} = refl
    assoc* {Local} {Local} {Unused} = refl
    assoc* {Local} {Local} {Global} = refl
    assoc* {Local} {Local} {Local} = refl
    assoc* {Local} {Local} {Anywhere} = refl
    assoc* {Local} {Anywhere} {Unused} = refl
    assoc* {Local} {Anywhere} {Global} = refl
    assoc* {Local} {Anywhere} {Local} = refl
    assoc* {Local} {Anywhere} {Anywhere} = refl
    assoc* {Anywhere} {Unused} {Unused} = refl
    assoc* {Anywhere} {Unused} {Global} = refl
    assoc* {Anywhere} {Unused} {Local} = refl
    assoc* {Anywhere} {Unused} {Anywhere} = refl
    assoc* {Anywhere} {Global} {Unused} = refl
    assoc* {Anywhere} {Global} {Global} = refl
    assoc* {Anywhere} {Global} {Local} = refl
    assoc* {Anywhere} {Global} {Anywhere} = refl
    assoc* {Anywhere} {Local} {Unused} = refl
    assoc* {Anywhere} {Local} {Global} = refl
    assoc* {Anywhere} {Local} {Local} = refl
    assoc* {Anywhere} {Local} {Anywhere} = refl
    assoc* {Anywhere} {Anywhere} {Unused} = refl
    assoc* {Anywhere} {Anywhere} {Global} = refl
    assoc* {Anywhere} {Anywhere} {Local} = refl
    assoc* {Anywhere} {Anywhere} {Anywhere} = refl

    distrib1 : {r s t : Locality} -> (r *l (s +l t)) ≡ ((r *l s) +l (r *l t))
    distrib1 {Unused} {s} {t} = refl
    distrib1 {Global} {Unused} {Unused} = refl
    distrib1 {Global} {Unused} {Global} = refl
    distrib1 {Global} {Unused} {Local} = refl
    distrib1 {Global} {Unused} {Anywhere} = refl
    distrib1 {Global} {Global} {Unused} = refl
    distrib1 {Global} {Global} {Global} = refl
    distrib1 {Global} {Global} {Local} = refl
    distrib1 {Global} {Global} {Anywhere} = refl
    distrib1 {Global} {Local} {Unused} = refl
    distrib1 {Global} {Local} {Global} = refl
    distrib1 {Global} {Local} {Local} = refl
    distrib1 {Global} {Local} {Anywhere} = refl
    distrib1 {Global} {Anywhere} {Unused} = refl
    distrib1 {Global} {Anywhere} {Global} = refl
    distrib1 {Global} {Anywhere} {Local} = refl
    distrib1 {Global} {Anywhere} {Anywhere} = refl
    distrib1 {Local} {Unused} {Unused} = refl
    distrib1 {Local} {Unused} {Global} = refl
    distrib1 {Local} {Unused} {Local} = refl
    distrib1 {Local} {Unused} {Anywhere} = refl
    distrib1 {Local} {Global} {Unused} = refl
    distrib1 {Local} {Global} {Global} = refl
    distrib1 {Local} {Global} {Local} = refl
    distrib1 {Local} {Global} {Anywhere} = refl
    distrib1 {Local} {Local} {Unused} = refl
    distrib1 {Local} {Local} {Global} = refl
    distrib1 {Local} {Local} {Local} = refl
    distrib1 {Local} {Local} {Anywhere} = refl
    distrib1 {Local} {Anywhere} {Unused} = refl
    distrib1 {Local} {Anywhere} {Global} = refl
    distrib1 {Local} {Anywhere} {Local} = refl
    distrib1 {Local} {Anywhere} {Anywhere} = refl
    distrib1 {Anywhere} {s} {t} rewrite leftUnit* {s +l t} | leftUnit* {s} | leftUnit* {t} = refl

    comm* : {x y : Locality} -> x *l y ≡ y *l x
    comm* {Unused} {Unused} = refl
    comm* {Unused} {Global} = refl
    comm* {Unused} {Local} = refl
    comm* {Unused} {Anywhere} = refl
    comm* {Global} {Unused} = refl
    comm* {Global} {Global} = refl
    comm* {Global} {Local} = refl
    comm* {Global} {Anywhere} = refl
    comm* {Local} {Unused} = refl
    comm* {Local} {Global} = refl
    comm* {Local} {Local} = refl
    comm* {Local} {Anywhere} = refl
    comm* {Anywhere} {Unused} = refl
    comm* {Anywhere} {Global} = refl
    comm* {Anywhere} {Local} = refl
    comm* {Anywhere} {Anywhere} = refl

    distrib2prop : {r s t : Locality} -> ((r +l s) *l t) ≡ ((r *l t) +l (s *l t))
    distrib2prop {r} {s} {t} rewrite comm* {r +l s} {t} | comm* {r} {t} | comm* {s} {t} = distrib1

    assocPlus : {r s t : Locality} -> ((r +l s) +l t) ≡ (r +l (s +l t))
    assocPlus {Unused} {Unused} {Unused} = refl
    assocPlus {Unused} {Unused} {Global} = refl
    assocPlus {Unused} {Unused} {Local} = refl
    assocPlus {Unused} {Unused} {Anywhere} = refl
    assocPlus {Unused} {Global} {Unused} = refl
    assocPlus {Unused} {Global} {Global} = refl
    assocPlus {Unused} {Global} {Local} = refl
    assocPlus {Unused} {Global} {Anywhere} = refl
    assocPlus {Unused} {Local} {Unused} = refl
    assocPlus {Unused} {Local} {Global} = refl
    assocPlus {Unused} {Local} {Local} = refl
    assocPlus {Unused} {Local} {Anywhere} = refl
    assocPlus {Unused} {Anywhere} {Unused} = refl
    assocPlus {Unused} {Anywhere} {Global} = refl
    assocPlus {Unused} {Anywhere} {Local} = refl
    assocPlus {Unused} {Anywhere} {Anywhere} = refl
    assocPlus {Global} {Unused} {Unused} = refl
    assocPlus {Global} {Unused} {Global} = refl
    assocPlus {Global} {Unused} {Local} = refl
    assocPlus {Global} {Unused} {Anywhere} = refl
    assocPlus {Global} {Global} {Unused} = refl
    assocPlus {Global} {Global} {Global} = refl
    assocPlus {Global} {Global} {Local} = refl
    assocPlus {Global} {Global} {Anywhere} = refl
    assocPlus {Global} {Local} {Unused} = refl
    assocPlus {Global} {Local} {Global} = refl
    assocPlus {Global} {Local} {Local} = refl
    assocPlus {Global} {Local} {Anywhere} = refl
    assocPlus {Global} {Anywhere} {Unused} = refl
    assocPlus {Global} {Anywhere} {Global} = refl
    assocPlus {Global} {Anywhere} {Local} = refl
    assocPlus {Global} {Anywhere} {Anywhere} = refl
    assocPlus {Local} {Unused} {Unused} = refl
    assocPlus {Local} {Unused} {Global} = refl
    assocPlus {Local} {Unused} {Local} = refl
    assocPlus {Local} {Unused} {Anywhere} = refl
    assocPlus {Local} {Global} {Unused} = refl
    assocPlus {Local} {Global} {Global} = refl
    assocPlus {Local} {Global} {Local} = refl
    assocPlus {Local} {Global} {Anywhere} = refl
    assocPlus {Local} {Local} {Unused} = refl
    assocPlus {Local} {Local} {Global} = refl
    assocPlus {Local} {Local} {Local} = refl
    assocPlus {Local} {Local} {Anywhere} = refl
    assocPlus {Local} {Anywhere} {Unused} = refl
    assocPlus {Local} {Anywhere} {Global} = refl
    assocPlus {Local} {Anywhere} {Local} = refl
    assocPlus {Local} {Anywhere} {Anywhere} = refl
    assocPlus {Anywhere} {Unused} {Unused} = refl
    assocPlus {Anywhere} {Unused} {Global} = refl
    assocPlus {Anywhere} {Unused} {Local} = refl
    assocPlus {Anywhere} {Unused} {Anywhere} = refl
    assocPlus {Anywhere} {Global} {Unused} = refl
    assocPlus {Anywhere} {Global} {Global} = refl
    assocPlus {Anywhere} {Global} {Local} = refl
    assocPlus {Anywhere} {Global} {Anywhere} = refl
    assocPlus {Anywhere} {Local} {Unused} = refl
    assocPlus {Anywhere} {Local} {Global} = refl
    assocPlus {Anywhere} {Local} {Local} = refl
    assocPlus {Anywhere} {Local} {Anywhere} = refl
    assocPlus {Anywhere} {Anywhere} {Unused} = refl
    assocPlus {Anywhere} {Anywhere} {Global} = refl
    assocPlus {Anywhere} {Anywhere} {Local} = refl
    assocPlus {Anywhere} {Anywhere} {Anywhere} = refl
