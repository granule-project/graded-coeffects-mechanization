{-# OPTIONS --allow-unsolved-metas #-}

module BinaryFundamentalTheorem where

open import GrCore
open import Data.Unit hiding (_≤_; _≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool hiding (_≤_; _≟_)
open import Data.List hiding (_++_)
open import Data.Nat hiding (_≤_)
open import Function
open import Data.Maybe
open import Relation.Nullary
open import Data.Sum

open import Semiring

open import OperationalModel
open import RelationalModel
open import UnaryFundamentalTheorem

-------------------------------
-- Binary fundamental theorem

-------------------------

propInvdecreasing+1 : {{R : Semiring}} {{R' : NonInterferingSemiring {{R}}}}
                -> {r1 r2 r adv : grade}
                -> ¬((r1 +R (r *R r2)) ≤ adv)
                -> ¬(r1 ≤ adv)
propInvdecreasing+1 {{R}} {{R'}} {r1} {r2} {r} {adv} pre = decreasing+Inv {r1} {r *R r2} {adv} pre

propInvdecreasing+2 : {{R : Semiring}} {{R' : NonInterferingSemiring {{R}}}}
                -> {r1 r2 r adv : grade}
                -> ¬((r1 +R (r *R r2)) ≤ adv)
                -> ¬((r *R r2) ≤ adv)
propInvdecreasing+2 {{R}} {{R'}} {r1} {r2} {r} {adv} pre = decreasing+Inv' {r1} {r *R r2} {adv} pre

-- TODO: remove terminating
{-# TERMINATING #-}
biFundamentalTheorem : {{R : Semiring}} {{R' : NonInterferingSemiring {{R}}}} {sz : ℕ}
          {Γ : Context sz} {e : Term} {τ : Type}

        -> Γ ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ ⟧Γ adv γ1 γ2
        -> ⟦ τ ⟧e adv (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheorem {{R}} {{R'}} {_} {Γ} {Var .(Γlength Γ1)} {τ} (var {_} {_} {.τ} {.Γ} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos with Γ1 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | (argInterp , _) = conc

  where
    conc : ⟦ τ ⟧v adv v1 v2
    -- due to the typing of the variable rule, the promotion here for values going into
    -- the input is at grade 1
    -- then either we have:
    --    * 1 <= adv i.e., adversary is allowed to see this
    --    * e.g., Pub <= Priv  (adversary is Private) or Pub <= Pub (advesary is Public)
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner = inner v1 v2 (isSimultaneous' {v1} {a1} {γ1'} v1redux) (isSimultaneous' {v2} {a2} {γ2'} v2redux)
        --    * ¬ (1 <= adv) i.e.., adversary cannot see this.
        -- however, since ∀ r . 1 <= r (e.g., for Sec) then this is cannot be the case.
    ... | boxInterpBiunobs eq .a1 .a2 inner = ⊥-elim (eq (oneIsBottom {adv}))

-- generalises the above for any variable
... | Ext G1' a | a1 ∷ γ1' | a2 ∷ γ2' | (argInterp , restInterp) =
   {!!}


biFundamentalTheorem {{R}} {{R'}} {sz} {Γ} {App t1 t2} {.B} (app {s} {Γ} {Γ1} {Γ2} {r} {A} {B} typ1 typ2 {pos}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos =
   let
    -- Reducability of `App t1 t2` implies that there exists a value `Abs var1 bod1` which can be obtained by
    -- reducing `t1` underneath context `γ1` and `Abs var2 bod2` underneath context `γ2`
    ((var1 , bod1) , (fun1redux , bodTy1)) = reduxTheoremAppTy {multisubst' 0 γ1 t1} {multisubst' 0 γ1 t2} {v1} {0} {Empty} {A} {B} (subst (\r -> multiRedux r ≡ v1) (substPresApp {0} {γ1} {t1} {t2}) v1redux) (multiSubstTy {sz} {Γ1} {t1} {FunTy A r B} {γ1} typ1)
    ((var2 , bod2) , (fun2redux , bodTy2)) = reduxTheoremAppTy {multisubst' 0 γ2 t1} {multisubst' 0 γ2 t2} {v2} {0} {Empty} {A} {B} (subst (\r -> multiRedux r ≡ v2) (substPresApp {0} {γ2} {t1} {t2}) v2redux) (multiSubstTy {sz} {Γ1} {t1} {FunTy A r B} {γ2} typ1)
    fun1 = Abs var1 bod1
    fun2 = Abs var2 bod2

   -- Apply binary fundmanetal lemma inductively on left-hand side (t1)
    ih1 = biFundamentalTheorem {sz} {Γ1} {t1} {FunTy A r B} typ1 adv (splitContext1 contextInterp)
    -- This provides the values obtained by the first premise
    ih1applied = ih1  fun1 fun2 fun1redux fun2redux

    -- Join up the reductions
    -- multiRedux (App (multisubst' 0 γ1 t1) (multisubst' 0 γ1 t2)) ≡ v1
    aeq1 = trans (cong multiRedux (sym (substPresApp {0} {γ1} {t1} {t2}))) v1redux
    -- multiRedux (App (Abs var1 bod1) (multisubst' 0 γ1 t2)) ≡ v1
    aeq2 = trans (sym (multReduxCongruence {multisubst' zero γ1 t1} {Abs var1 bod1} {\t1' -> App t1' (multisubst' 0 γ1 t2)} fun1redux)) aeq1
    --
    v1reduxerFull = trans (sym (betaVariant1 {bod1} {multisubst' 0 γ1 t2} {var1})) aeq2

    -- multiRedux (App (multisubst' 0 γ2 t1) (multisubst' 0 γ2 t2)) ≡ v2
    beq1 = trans (cong multiRedux (sym (substPresApp {0} {γ2} {t1} {t2}))) v2redux
    -- multiRedux (App (Abs var1 bod2) (multisubst' 0 γ2 t2)) ≡ v2
    beq2 = trans (sym (multReduxCongruence {multisubst' zero γ2 t1} {Abs var2 bod2} {\t1' -> App t1' (multisubst' 0 γ2 t2)} fun2redux)) beq1
    --
    v2reduxerFull = trans (sym (betaVariant1 {bod2} {multisubst' 0 γ2 t2} {var2})) beq2

   in
     extract ih1applied (multisubst' zero γ1 t2) (multisubst' zero γ2 t2) argument v1 v2 v1reduxerFull v2reduxerFull
  where
    extract : {x y : ℕ} {e1 e2 : Term} -> ⟦ FunTy A r B ⟧v adv (Abs x e1) (Abs y e2)
           -> (forall (v1 : Term) (v2 : Term)
                 -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2)
                 -> ⟦ B ⟧e adv (syntacticSubst v1 x e1) (syntacticSubst v2 y e2))
    extract {x} {y} {e1} {e2} pre with pre
    ... | funInterpBi .e1 .e2 inner _ _ = inner

    -- pull out to its own thing to resue
    splitContext1 : {sz : ℕ} {γ1 γ2 : List Term} {Γ1 Γ2 : Context sz} -> ⟦ Γ1 ++ (r · Γ2) ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
    splitContext1 = binaryPlusElimLeftΓ binaryPlusElimLeftBox

    splitContext2 : {sz : ℕ} {γ1 γ2 : List Term} {Γ1 Γ2 : Context sz} -> ⟦ Γ1 ++ (r · Γ2) ⟧Γ adv γ1 γ2 -> ⟦ r · Γ2 ⟧Γ adv γ1 γ2
    splitContext2 = binaryPlusElimRightΓ binaryPlusElimRightBox

    argument : ⟦ Box r A ⟧e adv (Promote (multisubst γ1 t2)) (Promote (multisubst γ2 t2))
    argument =
      let ih2 = biFundamentalTheorem {sz} {r · Γ2} {Promote t2} {Box r A} (pr {Γ' = r · Γ2} {r} typ2 {refl}) {γ1} {γ2} adv (splitContext2 contextInterp)
      in subst₂ (\h1 h2 -> ⟦ Box r A ⟧e adv h1 h2) (substPresProm {0} {γ1} {t2}) (substPresProm {0} {γ2} {t2}) ih2

-- # ABS
biFundamentalTheorem {sz} {Γ'} {Abs .(Γlength Γ1 + 1) t} {FunTy A r B} (abs {s1} {s2} {Γ} {Γ1} {Γ2} {Γ'} pos typ {rel}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ FunTy A r B ⟧v adv h1 h2) (thm γ1 v1 v1redux) (thm γ2 v2 v2redux) (funInterpBi {adv} {A} {B} {r} {Γlength Γ1 + 1} {Γlength Γ1 + 1} (multisubst γ1 t) ((multisubst γ2 t)) body ubody1 ubody2)
  where
    body : (forall (v1' : Term) (v2' : Term)
         -> ⟦ Box r A ⟧e adv (Promote v1') (Promote v2')
         -> ⟦ B ⟧e adv (syntacticSubst v1' (Γlength Γ1 + 1) (multisubst γ1 t)) (syntacticSubst v2' (Γlength Γ1 + 1) (multisubst γ2 t)))
    body v1' v2' arg rewrite pos | rel | (substitutionResult {s1} {v1'} {γ1} {t} {Γ1}) | (substitutionResult {s1} {v2'} {γ2} {t} {Γ1}) =
      biFundamentalTheorem {suc (s1 + s2)} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typ {v1' ∷ γ1} {v2' ∷ γ2} adv (arg , contextInterp)

    ubody1 : (v : Term) →
      [ Box r A ]e (Promote v) →
      [ B ]e (syntacticSubst v (Γlength Γ1 + 1) (multisubst γ1 t))
    ubody1 v arg rewrite pos | rel | substitutionResult {s1} {v} {γ1} {t} {Γ1} = utheorem {suc (s1 + s2)} {v ∷ γ1} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typ (arg , proj₁ (binaryImpliesUnaryG contextInterp))

    ubody2 : (v : Term) →
      [ Box r A ]e (Promote v) →
      [ B ]e (syntacticSubst v (Γlength Γ1 + 1) (multisubst γ2 t))
    ubody2 v arg rewrite pos | rel | substitutionResult {s1} {v} {γ2} {t} {Γ1} = utheorem {suc (s1 + s2)} {v ∷ γ2} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typ (arg , proj₂ (binaryImpliesUnaryG contextInterp))

    thm : (γ : List Term) -> (v : Term)
        -> multiRedux (multisubst γ (Abs (Γlength Γ1 + 1) t)) ≡ v -> Abs (Γlength Γ1 + 1) (multisubst γ t) ≡ v
    thm γ v redux =
     let
       qr = cong multiRedux (substPresAbs {0} {γ} {Γlength Γ1 + 1} {t})
       qr' = trans qr (valuesDontReduce {Abs (Γlength Γ1 + 1) (multisubst γ t)} (absValue {Γlength Γ1 + 1} (multisubst γ t)))
     in sym (trans (sym redux) qr')

-- # PROMOTION
biFundamentalTheorem {sz} {Γ'} {Promote t} {Box r A} (pr {s} {Γ} {Γ'} typ {prf}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux with r ≤d adv
... | no eq rewrite prf =
  let
    (uinterp1 , uinterp2) = underBox {sz} {γ1} {γ2} {Γ} contextInterp
    ih1 = utheorem {s} {γ1} {Γ} {t} {A} typ uinterp1
    ih2 = utheorem {s} {γ2} {Γ} {t} {A} typ uinterp2
  in
   subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2)
     (reduxAndSubstCombinedProm {v1} {t} {γ1} v1redux)
     (reduxAndSubstCombinedProm {v2} {t} {γ2} v2redux)
     (boxInterpBiunobs eq (multisubst γ1 t) (multisubst γ2 t) (ih1 , ih2))
  where

    binaryToUnaryVal : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ([ Box s A ]v (Promote v1)) × ([ Box s A ]v (Promote v2))
    binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpBiobs eq' .v1 .v2 ainterp) =
      let (a , b) = binaryImpliesUnary {A} {v1} {v2} {adv} ainterp in (boxInterpV v1 a , boxInterpV v2 b)

    binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 (left , right)) = (boxInterpV v1 left) , (boxInterpV v2 right)

    binaryToUnaryExp : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ([ Box s A ]e (Promote v1)) × ([ Box s A ]e (Promote v2))
    binaryToUnaryExp {s} {v1} {v2} {A} arg1 = (left , right)
      where
        left : [ Box s A ]e (Promote v1)
        left v0 redux rewrite trans (sym redux) (reduxProm {v1}) with binaryToUnaryVal {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
        ... | (left' , right') = left'

        right : [ Box s A ]e (Promote v2)
        right v0 redux rewrite trans (sym redux) (reduxProm {v2}) with binaryToUnaryVal {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
        ... | (left' , right') = right'

    underBox : {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> [ Γ ]Γ γ1 × [ Γ ]Γ γ2
    underBox {_} {_} {_} {Empty} g = (tt , tt)
    underBox {_} {[]} {[]} {Ext Γ (Grad A r)} ()
    underBox {_} {[]} {x ∷ γ2} {Ext Γ (Grad A r)} ()
    underBox {_} {x ∷ γ1} {[]} {Ext Γ (Grad A r)} ()
    underBox {suc sz} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A r')} (arg , g) =
     let
      (left , right) = underBox {sz} {γ1} {γ2} {Γ} g
      (l , r) = binaryToUnaryExp arg
     in
       (l , left) , (r , right)

--------------------------------------------------------
... | yes eq rewrite prf =
  let
    ih = biFundamentalTheorem {sz} {Γ} {t} {A} typ {γ1} {γ2} adv (underBox {sz} {γ1} {γ2} contextInterp)
  in
    subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2) (thm {v1} {γ1} v1redux) (thm {v2} {γ2} v2redux) (boxInterpBiobs eq (multisubst γ1 t) (multisubst γ2 t) ih)

  where

    convertVal : {s : grade} {v1 : Term} {v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧v adv (Promote v1) (Promote v2)
    convertVal {s} {v1} {v2} {A} (boxInterpBiobs prop .v1 .v2 interp) with s ≤d adv
    ... | yes eq = boxInterpBiobs eq v1 v2 interp
    ... | no eq  = boxInterpBiunobs eq v1 v2 (binaryImpliesUnary {A} {v1} {v2} interp)

    convertVal {s} {v1} {v2} {A} (boxInterpBiunobs x .v1 .v2 interp) = boxInterpBiunobs (propInvTimesMonoAsymN x eq) v1 v2 interp

    underBox : {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ ⟧Γ adv γ1 γ2
    underBox = binaryTimesElimRightΓ convertVal

    thm : {v : Term} {γ : List Term} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
    thm {v} {γ} redux =
       let qr = cong multiRedux (substPresProm {0} {γ} {t})
           qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')

biFundamentalTheorem {_} {_} {.unit} {.Unit} unitConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ Unit ⟧v adv h1 h2) thm1 thm2 (unitInterpBi {adv})
    where
      thm1 : unit ≡ v1
      thm1 = trans (sym (cong multiRedux (substPresUnit {γ1} {0}))) v1redux

      thm2 : unit ≡ v2
      thm2 = trans (sym (cong multiRedux (substPresUnit {γ2} {0}))) v2redux


biFundamentalTheorem {_} {_} {.vtrue} {.BoolTy} trueConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ BoolTy ⟧v adv h1 h2) thm1 thm2 boolInterpTrueBi
   where
    thm1 : vtrue ≡ v1
    thm1 = trans (sym (cong multiRedux (substPresTrue {γ1} {0}))) v1redux

    thm2 : vtrue ≡ v2
    thm2 = trans (sym (cong multiRedux (substPresTrue {γ2} {0}))) v2redux

biFundamentalTheorem {_} {_} {.vfalse} {.BoolTy} falseConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ BoolTy ⟧v adv h1 h2) thm1 thm2 boolInterpFalseBi
   where
    thm1 : vfalse ≡ v1
    thm1 = trans (sym (cong multiRedux (substPresFalse {γ1} {0}))) v1redux

    thm2 : vfalse ≡ v2
    thm2 = trans (sym (cong multiRedux (substPresFalse {γ2} {0}))) v2redux

biFundamentalTheorem {sz} {Γ} {If tg t1 t2} {B} (if {s} {Γ} {Γ1} {Γ2} {.B} {.tg} {.t1} {.t2} {r} {used} typG typ1 typ2 {res})
  {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite sym res =
     caseBody
  where

       v1redux' : multiRedux (If (multisubst γ1 tg) (multisubst γ1 t1) (multisubst γ1 t2))  ≡ v1
       v1redux' = (trans (cong multiRedux (sym (substPresIf {0} {γ1} {tg} {t1} {t2}))) v1redux)

       v2redux' : multiRedux (If (multisubst γ2 tg) (multisubst γ2 t1) (multisubst γ2 t2))  ≡ v2
       v2redux' = (trans (cong multiRedux (sym (substPresIf {0} {γ2} {tg} {t1} {t2}))) v2redux)

       boolDisc : true ≡ false -> ⊥
       boolDisc ()

       convertHyp : {x y : Term} {r1 r2 : grade} {A : Type}
                  -> ⟦ Box ((r *R r1) +R r2) A ⟧e adv (Promote x) (Promote y) -> ⟦ Box r1 A ⟧e adv (Promote x) (Promote y)
       convertHyp {x} {y} {r1} {r2} {A} pre v0 v1 v0redux v1redux with pre v0 v1 v0redux v1redux | r1 ≤d adv
       ... | boxInterpBiobs   eq' t1 t2 inner | yes eq  = boxInterpBiobs eq t1 t2 inner
       ... | boxInterpBiobs   eq' t1 t2 inner | no eq   = boxInterpBiunobs eq t1 t2 (binaryImpliesUnary {A} {t1} {t2} {adv} inner)
       ... | boxInterpBiunobs eq' t1 t2 inner | yes eq  = ⊥-elim ((propertyConditionalNI eq' used) eq)
         where
           propertyConditionalNI : {r1 r2 r adv : grade}
                     -> ¬ (((r *R r1) +R r2) ≤ adv)
                     ->   (r ≤ 1R)
                     -> ¬ (r1 ≤ adv)
           propertyConditionalNI {r1} {r2} {r} {adv} npre pre1 pre2 =
                           npre (decreasing+ (transitive≤ (monotone* pre1 pre2) (≡-to-≤ (leftUnit* {adv}))))
       ... | boxInterpBiunobs eq' t1 t2 inner | no eq   = boxInterpBiunobs eq t1 t2 inner

       convert : {sz : ℕ} {Γ1 Γ2 : Context sz} {γ1 γ2 : List Term} -> ⟦ (r · Γ1) ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
       convert {.0} {Empty} {Empty} {[]} {[]} g = tt
       convert {suc sz} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {x1 ∷ γ1} {x2 ∷ γ2} (hd , tl) =
          convertHyp hd , convert {sz} {Γ1} {Γ2} {γ1} {γ2} tl

       convert2 : {sz : ℕ} {Γ1 Γ2 : Context sz} {γ1 γ2 : List Term} -> ⟦ (r · Γ1) ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ2 ⟧Γ adv γ1 γ2
       convert2 = binaryPlusElimRightΓ binaryPlusElimRightBox

       -- induct on boolean to determine which (pairs of) values are valid
       ih : ⟦ BoolTy ⟧e adv (multisubst γ1 tg) (multisubst γ2 tg)
       ih = biFundamentalTheorem {sz} {Γ1} {tg} {BoolTy} typG {γ1} {γ2} adv (convert contextInterp)

      -- induct on the case bodies depending on what values appear
       caseBody : ⟦ B ⟧v adv v1 v2
       caseBody with reduxTheoremBool {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux'
                    | reduxTheoremBool {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux'
       caseBody | inj₁ trueEv1 | inj₁ trueEv2 =
         biFundamentalTheorem {sz} {Γ2} {t1} {B} typ1 {γ1} {γ2} adv (convert2 contextInterp) v1 v2
           (sym (reduxTheoremBool1 {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux' trueEv1))
             (sym (reduxTheoremBool1 {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux' trueEv2))
       caseBody | inj₁ trueEv1  | inj₂ falseEv2 with ih vtrue vfalse trueEv1 falseEv2
       ... | ()
       caseBody | inj₂ falseEv1 | inj₁ trueEv2  with ih vfalse vtrue falseEv1 trueEv2
       ... | ()
       caseBody | inj₂ falseEv1 | inj₂ falseEv2 =
         biFundamentalTheorem {sz} {Γ2} {t2} {B} typ2 {γ1} {γ2} adv (convert2 contextInterp) v1 v2
           (sym (reduxTheoremBool2 {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux' falseEv1))
             (sym (reduxTheoremBool2 {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux' falseEv2))

{-
Not needed any more but possible useful elseshere
lem : {{R : Semiring}} {adv : grade}
      {A : Type} {v1 v2 : Term}
   -> Value v1
   -> Value v2
   -> ⟦ A ⟧e adv v1 v2
   -> ⟦ A ⟧v adv v1 v2

lem {adv} {A} {v1} {v2} isvalv1 isvalv2 mem =
  mem v1 v2 (valuesDontReduce {v1} isvalv1) (valuesDontReduce {v2} isvalv2)
-}

boolBinaryValueInterpEquality : {{R : Semiring}} {r : grade} (v1 v2 : Term) -> ⟦ BoolTy ⟧v r v1 v2 -> v1 ≡ v2
boolBinaryValueInterpEquality .vtrue .vtrue boolInterpTrueBi = refl
boolBinaryValueInterpEquality .vfalse .vfalse boolInterpFalseBi = refl

boolBinaryExprInterpEquality : {{R : Semiring}} {r : grade} (v1 v2 : Term)
                              -> ⟦ BoolTy ⟧e r v1 v2
                              -> multiRedux v1 ≡ multiRedux v2
boolBinaryExprInterpEquality t1 t2 prf =
  boolBinaryValueInterpEquality (multiRedux t1) (multiRedux t2) ((prf (multiRedux t1) (multiRedux t2) refl refl))

