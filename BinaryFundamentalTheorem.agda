{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module BinaryFundamentalTheorem where

open import GrCore
open import Data.Unit hiding (_≤_; _≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Bool hiding (_≤_; _≟_)
open import Data.Vec hiding (_++_)
open import Data.Nat hiding (_≤_)
open import Function
open import Data.Maybe hiding (map)
open import Relation.Nullary
open import Data.Sum hiding (map)
open import Data.Fin hiding (_≤_; _+_)

open import Semiring

open import OperationalModel
open import RelationalModel
open import UnaryFundamentalTheorem

open NonInterferingSemiring {{...}}

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
biFundamentalTheorem : {{R : Semiring}} {{R' : NonInterferingSemiring {{R}}}} {s : ℕ}
          {Γ : Context s} {e : Term s} {τ : Type}

        -> Γ ⊢ e ∶ τ
        -> {γ1 : Vec (Term 0) s} {γ2 : Vec (Term 0) s}
        -> (adv : grade)
        -> ⟦ Γ ⟧Γ adv γ1 γ2
        -> ⟦ τ ⟧e adv (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheorem {{R}} {{R'}} {_} {Γ} {Var x} {τ} (var {_} {_} {.τ} {.Γ} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos with Γ2 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | (argInterp , _) = conc

  where
    conc : ⟦ τ ⟧v adv v1 v2
    -- due to the typing of the variable rule, the promotion here for values going into
    -- the input is at grade 1
    -- then either we have:
    --    * 1 <= adv i.e., adversary is allowed to see this
    --    * e.g., Pub <= Priv  (adversary is Private) or Pub <= Pub (advesary is Public)
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner =
       inner v1 v2 (isSimultaneousGen {zero} {_} {zero} {a1} {v1} {γ1'} v1redux)
                   (isSimultaneousGen {zero} {_} {zero} {a2} {v2} {γ2'} v2redux)
        --    * ¬ (1 <= adv) i.e.., adversary cannot see this.
        -- however, since ∀ r . 1 <= r (e.g., for Sec) then this is cannot be the case.
    ... | boxInterpBiunobs eq .a1 .a2 inner = ⊥-elim (eq (oneIsBottom {adv}))

-- generalises the above for any variable
... | Ext G1' a | a1 ∷ γ1' | a2 ∷ γ2' | contextInterp = {!!}

-- # APP

biFundamentalTheorem {{R}} {{R'}} {sz} {Γ} {App t1 t2} {.B} (app {s} {Γ} {Γ1} {Γ2} {r} {A} {B} typ1 typ2 {pos}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos =
   let
    -- Reducability of `App t1 t2` implies that there exists a value `Abs var1 bod1` which can be obtained by
    -- reducing `t1` underneath context `γ1` and `Abs var2 bod2` underneath context `γ2`
    (bod1 , (fun1redux , bodTy1)) =
       reduxTheoremAppTy {_} {multisubst γ1 t1} {multisubst γ1 t2} {v1} {Empty} {A} {B} (subst (\r -> multiRedux r ≡ v1) (substPresApp {_} {_} {γ1} {t1} {t2}) v1redux) (multiSubstTy {sz} {γ1} {Γ1}  {FunTy A r B} {t1} typ1)
    (bod2 , (fun2redux , bodTy2)) =
       reduxTheoremAppTy {_} {multisubst γ2 t1} {multisubst γ2 t2} {v2} {Empty} {A} {B} (subst (\r -> multiRedux r ≡ v2) (substPresApp {_} {_} {γ2} {t1} {t2}) v2redux) (multiSubstTy {sz} {γ2} {Γ1} {FunTy A r B} {t1} typ1)
    fun1 = Abs bod1
    fun2 = Abs bod2

   -- Apply binary fundmanetal lemma inductively on left-hand side (t1)
    ih1 = biFundamentalTheorem {sz} {Γ1} {t1} {FunTy A r B} typ1 adv (splitContext1 contextInterp)
    -- This provides the values obtained by the first premise
    ih1applied = ih1  fun1 fun2 fun1redux fun2redux

    -- Join up the reductions
    -- multiRedux (App (multisubst' 0 γ1 t1) (multisubst' 0 γ1 t2)) ≡ v1
    aeq1 = trans (cong multiRedux (sym (substPresApp {_} {_} {γ1} {t1} {t2}))) v1redux
    -- multiRedux (App (Abs var1 bod1) (multisubst' 0 γ1 t2)) ≡ v1
    aeq2 = trans (sym (multReduxCongruence {_} {multisubst γ1 t1} {Abs bod1} {\t1' -> App t1' (multisubst γ1 t2)} fun1redux)) aeq1
    --
    v1reduxerFull = trans (sym (betaUnderMultiRedux {_} {bod1} {multisubst γ1 t2})) aeq2

    -- multiRedux (App (multisubst' 0 γ2 t1) (multisubst' 0 γ2 t2)) ≡ v2
    beq1 = trans (cong multiRedux (sym (substPresApp {_} {_} {γ2} {t1} {t2}))) v2redux
    -- multiRedux (App (Abs var1 bod2) (multisubst' 0 γ2 t2)) ≡ v2
    beq2 = trans (sym (multReduxCongruence {_} {multisubst γ2 t1} {Abs bod2} {\t1' -> App t1' (multisubst γ2 t2)} fun2redux)) beq1
    --
    v2reduxerFull = trans (betaUnderMultiRedux {zero} {bod2} {multisubst γ2 t2}) beq2

   in
     extract ih1applied (multisubst γ1 t2) (multisubst γ2 t2) argument v1 v2 v1reduxerFull v2reduxerFull
  where
    extract : {s : ℕ} {e1 e2 : Term (suc s)} -> ⟦ FunTy A r B ⟧v adv (Abs e1) (Abs e2)
           -> (forall (v1 : Term s) (v2 : Term s)
                 -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2)
                 -> ⟦ B ⟧e adv (syntacticSubst v1 zero e1) (syntacticSubst v2 zero e2))
    extract {s} {e1} {e2} pre with pre
    ... | funInterpBi .e1 .e2 inner _ _ = inner

    -- pull out to its own thing to resue
    splitContext1 : {sz : ℕ} {γ1 γ2 : Vec (Term 0) sz} {Γ1 Γ2 : Context sz} -> ⟦ Γ1 ++ (r · Γ2) ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
    splitContext1 = binaryPlusElimLeftΓ binaryPlusElimLeftBox

    splitContext2 : {sz : ℕ} {γ1 γ2 : Vec (Term 0) sz} {Γ1 Γ2 : Context sz} -> ⟦ Γ1 ++ (r · Γ2) ⟧Γ adv γ1 γ2 -> ⟦ r · Γ2 ⟧Γ adv γ1 γ2
    splitContext2 = binaryPlusElimRightΓ binaryPlusElimRightBox

    argument : ⟦ Box r A ⟧e adv (Promote (multisubst γ1 t2)) (Promote (multisubst γ2 t2))
    argument =
      let ih2 = biFundamentalTheorem {sz} {r · Γ2} {Promote t2} {Box r A} (pr {Γ' = r · Γ2} {r} typ2 {refl}) {γ1} {γ2} adv (splitContext2 contextInterp)
      in subst₂ (\h1 h2 -> ⟦ Box r A ⟧e adv h1 h2) (substPresProm {_} {_} {γ1} {t2}) (substPresProm {_} {_} {γ2} {t2}) ih2

-- # ABS
biFundamentalTheorem {sz} {Γ'} {Abs t} {FunTy A r B} (abs {s1} {s2} {Γ} {Γ1} {Γ2} {Γ'} pos typ {rel}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ FunTy A r B ⟧v adv h1 h2) (thm γ1 v1 v1redux) (thm γ2 v2 v2redux) (funInterpBi {_} {adv} {A} {B} {r} {Γlength Γ1 + 1} {Γlength Γ1 + 1} (multisubst' (map raiseTerm γ1) t) ((multisubst' (map raiseTerm γ2) t)) body ubody1 ubody2)
  where
    body : forall (v1' : Term 0) (v2' : Term 0)
         -> ⟦ Box r A ⟧e adv (Promote v1') (Promote v2')
         -> ⟦ B ⟧e adv (syntacticSubst v1' zero (multisubst' (map raiseTerm γ1) t)) (syntacticSubst v2' zero (multisubst' (map raiseTerm γ2) t))
    body  v1' v2' arg rewrite pos | rel
           | multiSubstComm {s1 + s2} {zero} {γ1} {v1'} {t}
           | multiSubstComm {s1 + s2} {zero} {γ2} {v2'} {t} =
      biFundamentalTheorem {suc (s1 + s2)} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} (exchange typ) {v1' ∷ γ1} {v2' ∷ γ2} adv ((arg , contextInterp))

    ubody1 : (v : Term 0) →
      [ Box r A ]e (Promote v) →
      [ B ]e (syntacticSubst v zero (multisubst' (map raiseTerm γ1) t))
    ubody1 v arg rewrite pos | rel | multiSubstComm {s1 + s2} {zero} {γ1} {v} {t} =
       utheorem {suc (s1 + s2)} {v ∷ γ1} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} (exchange typ) (arg , proj₁ (binaryImpliesUnaryG contextInterp))

    ubody2 : (v : Term 0) →
      [ Box r A ]e (Promote v) →
      [ B ]e (syntacticSubst v zero (multisubst' (map raiseTerm γ2) t))
    ubody2 v arg rewrite pos | rel | multiSubstComm {s1 + s2} {zero} {γ2} {v} {t} =
       utheorem {suc (s1 + s2)} {v ∷ γ2} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} (exchange typ) (arg , proj₂ (binaryImpliesUnaryG contextInterp))

    thm : (γ : Vec (Term 0) sz) -> (v : Term 0)
        -> multiRedux (multisubst γ (Abs t)) ≡ v -> Abs (multisubst' (map raiseTerm γ) t) ≡ v
    thm γ v redux =
     let
       qr = cong multiRedux (substPresAbs {_} {_} {γ} {t})
       qr' = trans qr ((valuesDontReduce {_} {Abs (multisubst' (map raiseTerm γ) t)} (absValue {0} (multisubst' (map raiseTerm γ) t))))
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
     (reduxAndSubstCombinedProm {_} {_} {γ1} {v1} {t} v1redux)
     (reduxAndSubstCombinedProm {_} {_} {γ2} {v2} {t} v2redux)
     (boxInterpBiunobs eq (multisubst γ1 t) (multisubst γ2 t) (ih1 , ih2))
  where

    binaryToUnaryVal : {sz : ℕ} {s : grade} {v1 v2 : Term sz} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ([ Box s A ]v (Promote v1)) × ([ Box s A ]v (Promote v2))
    binaryToUnaryVal {sz} {s} {v1} {v2} {A} (boxInterpBiobs eq' .v1 .v2 ainterp) =
      let (a , b) = binaryImpliesUnary {_} {A} {v1} {v2} {adv} ainterp in (boxInterpV v1 a , boxInterpV v2 b)

    binaryToUnaryVal {sz} {s} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 (left , right)) = (boxInterpV v1 left) , (boxInterpV v2 right)

    binaryToUnaryExp : {sz : ℕ} {s : grade} {v1 v2 : Term sz} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ([ Box s A ]e (Promote v1)) × ([ Box s A ]e (Promote v2))
    binaryToUnaryExp {sz} {s} {v1} {v2} {A} arg1 = (left , right)
      where
        left : [ Box s A ]e (Promote v1)
        left v0 redux rewrite trans (sym redux) (reduxProm {_} {v1}) with binaryToUnaryVal {sz} {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
        ... | (left' , right') = left'

        right : [ Box s A ]e (Promote v2)
        right v0 redux rewrite trans (sym redux) (reduxProm {_} {v2}) with binaryToUnaryVal {sz} {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
        ... | (left' , right') = right'

    underBox : {sz : ℕ} {γ1 γ2 : Vec (Term 0) sz} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> [ Γ ]Γ γ1 × [ Γ ]Γ γ2
    underBox {zero} {[]} {[]} {Empty} g = tt , tt
    underBox {suc sz} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A r')} (arg , g) =
     let
      (left , right) = underBox {sz} {γ1} {γ2} {Γ} g
      (l , r) = binaryToUnaryExp {0} {r'} {v1} {v2} arg
     in
       (l , left) , (r , right)

--------------------------------------------------------
... | yes eq rewrite prf =
  let
    ih = biFundamentalTheorem {sz} {Γ} {t} {A} typ {γ1} {γ2} adv (underBox {sz} {γ1} {γ2} contextInterp)
  in
    subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2) (thm {v1} {γ1} v1redux) (thm {v2} {γ2} v2redux) (boxInterpBiobs eq (multisubst γ1 t) (multisubst γ2 t) ih)

  where

    convertVal :  {sz : ℕ} {s : grade} {v1 : Term sz} {v2 : Term sz} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧v adv (Promote v1) (Promote v2)
    convertVal {sz} {s} {v1} {v2} {A} (boxInterpBiobs prop .v1 .v2 interp) with s ≤d adv
    ... | yes eq = boxInterpBiobs eq v1 v2 interp
    ... | no eq  = boxInterpBiunobs eq v1 v2 (binaryImpliesUnary {_} {A} {v1} {v2} interp)

    convertVal {sz} {s} {v1} {v2} {A} (boxInterpBiunobs x .v1 .v2 interp) = boxInterpBiunobs (propInvTimesMonoAsymN x eq) v1 v2 interp

    underBox : {sz : ℕ} {γ1 γ2 : Vec (Term 0) sz} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ ⟧Γ adv γ1 γ2
    underBox = binaryTimesElimRightΓ convertVal

    thm : {v : Term 0} {γ : Vec (Term 0) sz} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
    thm {v} {γ} redux =
       let qr = cong multiRedux (substPresProm {_} {_} {γ} {t})
           qr' = trans qr (valuesDontReduce {zero} {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')

-- # Units
biFundamentalTheorem {_} {_} {.unit} {.Unit} unitConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ Unit ⟧v adv h1 h2) thm1 thm2 (unitInterpBi {_} {adv})
    where
      thm1 : unit ≡ v1
      thm1 = trans (sym (cong multiRedux (substPresUnit {_} {_} {γ1} ))) v1redux

      thm2 : unit ≡ v2
      thm2 = trans (sym (cong multiRedux (substPresUnit {_} {_} {γ2}))) v2redux

-- # Bools
biFundamentalTheorem {_} {_} {.vtrue} {.BoolTy} trueConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ BoolTy ⟧v adv h1 h2) thm1 thm2 boolInterpTrueBi
   where
    thm1 : vtrue ≡ v1
    thm1 = trans (sym (cong multiRedux (substPresTrue {_} {_} {γ1}))) v1redux

    thm2 : vtrue ≡ v2
    thm2 = trans (sym (cong multiRedux (substPresTrue {_} {_} {γ2}))) v2redux

biFundamentalTheorem {_} {_} {.vfalse} {.BoolTy} falseConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ BoolTy ⟧v adv h1 h2) thm1 thm2 boolInterpFalseBi
   where
    thm1 : vfalse ≡ v1
    thm1 = trans (sym (cong multiRedux (substPresFalse {_} {_} {γ1}))) v1redux

    thm2 : vfalse ≡ v2
    thm2 = trans (sym (cong multiRedux (substPresFalse {_} {_} {γ2}))) v2redux

biFundamentalTheorem {sz} {Γ} {If tg t1 t2} {B} (if {s} {Γ} {Γ1} {Γ2} {.B} {.tg} {.t1} {.t2} {r} {used} typG typ1 typ2 {res})
  {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite sym res =
     caseBody
  where

       v1redux' : multiRedux (If (multisubst γ1 tg) (multisubst γ1 t1) (multisubst γ1 t2))  ≡ v1
       v1redux' = (trans (cong multiRedux (sym (substPresIf {_}{_} {γ1} {tg} {t1} {t2}))) v1redux)

       v2redux' : multiRedux (If (multisubst γ2 tg) (multisubst γ2 t1) (multisubst γ2 t2))  ≡ v2
       v2redux' = (trans (cong multiRedux (sym (substPresIf {_}{_} {γ2} {tg} {t1} {t2}))) v2redux)

       boolDisc : true ≡ false -> ⊥
       boolDisc ()

       convertHyp : {x y : Term 0} {r1 r2 : grade} {A : Type}
                  -> ⟦ Box ((r *R r1) +R r2) A ⟧e adv (Promote x) (Promote y) -> ⟦ Box r1 A ⟧e adv (Promote x) (Promote y)
       convertHyp {x} {y} {r1} {r2} {A} pre v0 v1 v0redux v1redux with pre v0 v1 v0redux v1redux | r1 ≤d adv
       ... | boxInterpBiobs   eq' t1 t2 inner | yes eq  = boxInterpBiobs eq t1 t2 inner
       ... | boxInterpBiobs   eq' t1 t2 inner | no eq   = boxInterpBiunobs eq t1 t2 (binaryImpliesUnary {_} {A} {t1} {t2} {adv} inner)
       ... | boxInterpBiunobs eq' t1 t2 inner | yes eq  = ⊥-elim ((propertyConditionalNI eq' used) eq)
         where
           propertyConditionalNI : {r1 r2 r adv : grade}
                     -> ¬ (((r *R r1) +R r2) ≤ adv)
                     ->   (r ≤ 1R)
                     -> ¬ (r1 ≤ adv)
           propertyConditionalNI {r1} {r2} {r} {adv} npre pre1 pre2 =
                           npre (decreasing+ (transitive≤ (monotone* pre1 pre2) (≡-to-≤ (leftUnit* {adv}))))
       ... | boxInterpBiunobs eq' t1 t2 inner | no eq   = boxInterpBiunobs eq t1 t2 inner

       convert : {sz : ℕ} {Γ1 Γ2 : Context sz} {γ1 γ2 : Vec (Term 0) sz} -> ⟦ (r · Γ1) ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
       convert {.0} {Empty} {Empty} {[]} {[]} g = tt
       convert {suc sz} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {x1 ∷ γ1} {x2 ∷ γ2} (hd , tl) =
          convertHyp hd , convert {sz} {Γ1} {Γ2} {γ1} {γ2} tl

       convert2 : {sz : ℕ} {Γ1 Γ2 : Context sz} {γ1 γ2 : Vec (Term 0) sz} -> ⟦ (r · Γ1) ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ2 ⟧Γ adv γ1 γ2
       convert2 = binaryPlusElimRightΓ binaryPlusElimRightBox

       -- induct on boolean to determine which (pairs of) values are valid
       ih : ⟦ BoolTy ⟧e adv (multisubst γ1 tg) (multisubst γ2 tg)
       ih = biFundamentalTheorem {sz} {Γ1} {tg} {BoolTy} typG {γ1} {γ2} adv (convert contextInterp)

      -- induct on the case bodies depending on what values appear
       caseBody : ⟦ B ⟧v adv v1 v2
       caseBody with reduxTheoremBool {_} {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux'
                    | reduxTheoremBool {_} {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux'
       caseBody | inj₁ trueEv1 | inj₁ trueEv2 =
         biFundamentalTheorem {sz} {Γ2} {t1} {B} typ1 {γ1} {γ2} adv (convert2 contextInterp) v1 v2
           (sym (reduxTheoremBool1 {_} {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux' trueEv1))
             (sym (reduxTheoremBool1 {_} {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux' trueEv2))
       caseBody | inj₁ trueEv1  | inj₂ falseEv2 with ih vtrue vfalse trueEv1 falseEv2
       ... | ()
       caseBody | inj₂ falseEv1 | inj₁ trueEv2  with ih vfalse vtrue falseEv1 trueEv2
       ... | ()
       caseBody | inj₂ falseEv1 | inj₂ falseEv2 =
         biFundamentalTheorem {sz} {Γ2} {t2} {B} typ2 {γ1} {γ2} adv (convert2 contextInterp) v1 v2
           (sym (reduxTheoremBool2 {_} {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux' falseEv1))
             (sym (reduxTheoremBool2 {_} {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux' falseEv2))

-- # UNBOX

biFundamentalTheorem {sz} {Γ} {Let t1 t2} {B} (unbox {s} {Γ1} {Γ2} {Γ} {r} {A} {B} t1 t2 typing1 typing2 { prf })
  {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite sym prf =
     let
       -- Reason about the decomposition of a multireduction on a let
       (e0 , e0redux , bodyRedux1) =
         reduxTheoremLet {0} {multisubst γ1 t1} {multisubst' (map raiseTerm γ1) t2} {v1} (trans (sym (cong multiRedux (substPresLet {zero} {sz} {γ1} {t1}))) v1redux)

       (e0' , e0'redux , bodyRedux2) =
         reduxTheoremLet {0} {multisubst γ2 t1} {multisubst' (map raiseTerm γ2) t2} {v2} (trans (sym (cong multiRedux (substPresLet {zero} {sz} {γ2} {t1}))) v2redux)

       -- Induct on the argument
       ihArg = biFundamentalTheorem {sz} {Γ1} {t1} {Box r A} typing1 {γ1} {γ2} adv leftContext (Promote e0) (Promote e0') e0redux e0'redux

       -- Reason about shape of reductions on the body term
       bodyRedux1' = subst (\h -> multiRedux h ≡ v1)
                        (multiSubstComm {sz} {zero} {γ1} {e0}) bodyRedux1
       bodyRedux2' = subst (\h -> multiRedux h ≡ v2)
                        (multiSubstComm {sz} {zero} {γ2} {e0'}) bodyRedux2

       -- Glue argument induction onto body induction
       ihBody = biFundamentalTheorem {suc sz} {Ext Γ2 (Grad A r)} {t2} {B} typing2 {e0 ∷ γ1} {e0' ∷ γ2} adv (lifter ihArg , rightContext) v1 v2 bodyRedux1' bodyRedux2'

   in ihBody

  where
    -- lift a value interpretation to an expression interpretation on a value term
    lifter : {e1 e2 : Term 0} -> ⟦ Box r A ⟧v adv (Promote e1) (Promote e2) -> ⟦ Box r A ⟧e adv (Promote e1) (Promote e2)
    lifter {e1} {e2} vmeaning v3 v4 v3redux v4redux
      rewrite trans (sym (valuesDontReduce {zero} {Promote e1} (promoteValue e1))) v3redux
            | trans (sym (valuesDontReduce {zero} {Promote e2} (promoteValue e2))) v4redux
        = vmeaning

    -- Split context interpretations
    leftContext : ⟦ Γ1 ⟧Γ adv γ1 γ2
    leftContext = binaryPlusElimLeftΓ {sz} {zero} {adv} {γ1} {γ2} {Γ1} {Γ2} binaryPlusElimLeftBox
                   (subst (\h -> ⟦ h ⟧Γ adv γ1 γ2) prf contextInterp)

    rightContext : ⟦ Γ2 ⟧Γ adv γ1 γ2
    rightContext = binaryPlusElimRightΓ {sz} {zero} {adv} {γ1} {γ2} {Γ1} {Γ2} binaryPlusElimRightBox
                   (subst (\h -> ⟦ h ⟧Γ adv γ1 γ2) prf contextInterp)

biFundamentalTheorem {s = sz} {Γ} {.(tuple t1 t2)} {.(ProdTy _ _)}
   (prodIntro {_} {.Γ} {Γ1} {Γ2} {A} {B} {t1} {t2} deriv1 deriv2 {prf}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite sym prf  | sym v1redux | sym v2redux
      | substPresTuple {_} {_} {γ1} {t1} {t2}
      | substPresTuple {_} {_} {γ2} {t1} {t2}
      | reduxTuple {_} {multisubst γ1 t1} {multisubst γ1 t2}
      | reduxTuple {_} {multisubst γ2 t1} {multisubst γ2 t2} =
      let
        ih1 = biFundamentalTheorem {sz} {Γ1} {t1} {A} deriv1 {γ1} {γ2} adv leftContext
        ih2 = biFundamentalTheorem {sz} {Γ2} {t2} {B} deriv2 {γ1} {γ2} adv rightContext
      in prodInterpBi {zero} {adv} {A} {B} (multiRedux (multisubst γ1 t1)) (multiRedux (multisubst γ2 t1)) (multiRedux (multisubst γ1 t2)) (multiRedux (multisubst γ2 t2))
           (ih1 (multiRedux (multisubst γ1 t1)) (multiRedux (multisubst γ2 t1)) refl refl)
           (ih2 (multiRedux (multisubst γ1 t2)) (multiRedux (multisubst γ2 t2)) refl refl)
    where
      -- Split context interpretations
      leftContext : ⟦ Γ1 ⟧Γ adv γ1 γ2
      leftContext = binaryPlusElimLeftΓ {sz} {zero} {adv} {γ1} {γ2} {Γ1} {Γ2} binaryPlusElimLeftBox contextInterp

      rightContext : ⟦ Γ2 ⟧Γ adv γ1 γ2
      rightContext = binaryPlusElimRightΓ {sz} {zero} {adv} {γ1} {γ2} {Γ1} {Γ2} binaryPlusElimRightBox contextInterp

biFundamentalTheorem {s = sz} {Γ} {LetProd t1 t2} {.C} (prodElim {_} {Γ} {Γ1} {Γ2} {t1} {t2} {A} {B} {C} {r} deriv1 deriv2 {prf})
  {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux with r ≤d adv
... | yes r-less-adv rewrite sym prf
   | substPresLetProd {zero} {sz} {γ1} {t1} {t2}
   | substPresLetProd {zero} {sz} {γ2} {t1} {t2} =
    let
      (va , vb , tupleRedux , (vaIsVal , vbIsVal) , restSubst) = reduxTheoremLetProd {zero} {v1} {multisubst γ1 t1} {multisubst'' γ1 t2} v1redux
      (va' , vb' , tupleRedux' , (va'IsVal , vb'IsVal) , restSubst') = reduxTheoremLetProd {zero} {v2} {multisubst γ2 t1} {multisubst'' γ2 t2} v2redux
      ih = biFundamentalTheorem deriv1 adv leftContext' (tuple va vb) (tuple va' vb') tupleRedux tupleRedux'

      -- Reason about shape of reductions on the body term
      bodyRedux1' = subst (\h -> multiRedux h ≡ v1)
                        (multiSubstComm2{sz} {zero} {γ1} {va} {vb}) restSubst
      bodyRedux2' = subst (\h -> multiRedux h ≡ v2)
                        (multiSubstComm2 {sz} {zero} {γ2} {va'} {vb'}) restSubst'

      body = biFundamentalTheorem deriv2 adv (rightContext' va va' vb vb' vaIsVal va'IsVal vbIsVal vb'IsVal ih) v1 v2 bodyRedux1' bodyRedux2'
     in body
   where
      -- Split context interpretations
      leftContext : ⟦ r · Γ1 ⟧Γ adv γ1 γ2
      leftContext = binaryPlusElimLeftΓ {sz} {zero} {adv} {γ1} {γ2} {r · Γ1} {Γ2} binaryPlusElimLeftBox contextInterp


      convertVal :  {sz : ℕ} {s : grade} {v1 : Term sz} {v2 : Term sz} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧v adv (Promote v1) (Promote v2)
      convertVal {sz} {s} {v1} {v2} {A} (boxInterpBiobs prop .v1 .v2 interp) with s ≤d adv
      ... | yes eq = boxInterpBiobs eq v1 v2 interp
      ... | no eq  = boxInterpBiunobs eq v1 v2 (binaryImpliesUnary {_} {A} {v1} {v2} interp)

      convertVal {sz} {s} {v1} {v2} {A} (boxInterpBiunobs x .v1 .v2 interp) with r ≤d adv | s ≤d adv
      ... | yes eq1 | yes eq2 = ⊥-elim (x (subst (\h -> ((r *R s) ≤ h)) (idem* {adv}) (monotone* eq1 eq2)))
      ... | yes eq1 | no eq2 = boxInterpBiunobs eq2 v1 v2 interp
      ... | no eq1  | yes eq2 = ⊥-elim (eq1 r-less-adv)
      ... | no eq1  | no eq2 = boxInterpBiunobs eq2 v1 v2 interp

      leftContext' : ⟦ Γ1 ⟧Γ adv γ1 γ2
      leftContext' = binaryTimesElimRightΓ convertVal (binaryPlusElimLeftΓ {sz} {zero} {adv} {γ1} {γ2} {r · Γ1} {Γ2} binaryPlusElimLeftBox contextInterp)

      rightContext : ⟦ Γ2 ⟧Γ adv γ1 γ2
      rightContext = binaryPlusElimRightΓ {sz} {zero} {adv} {γ1} {γ2} {r · Γ1} {Γ2} binaryPlusElimRightBox contextInterp

      rightContext' : (va va' vb vb' : Term zero)
                   -> Value va
                   -> Value va'
                   -> Value vb
                   -> Value vb'
                   -> ⟦ ProdTy A B ⟧v adv (tuple va vb) (tuple va' vb')
                   -> ⟦ Ext (Ext Γ2 (Grad A r)) (Grad B r) ⟧Γ adv (vb ∷ va ∷ γ1) (vb' ∷ va' ∷ γ2)
      rightContext' va va' vb vb' valva valva' valvb valvb' (prodInterpBi .va .va' .vb .vb' part1 part2) with r ≤d adv
      ... | yes prf = arg2 , arg1 , rightContext
        where
          part1e : ⟦ A ⟧e adv va va'
          part1e va0 va0' va0redux va0'redux
            rewrite sym va0redux | sym va0'redux
                  | valuesDontReduce valva
                  | valuesDontReduce valva'
                 = part1

          arg1 : ⟦ Box r A ⟧e adv (Promote va) (Promote va')
          arg1 va0 va0' va0redux va0'redux rewrite sym va0redux | sym va0'redux = boxInterpBiobs prf va va' part1e

          part2e : ⟦ B ⟧e adv vb vb'
          part2e vb0 vb0' vb0redux vb0'redux
            rewrite sym vb0redux | sym vb0'redux
                  | valuesDontReduce valvb
                  | valuesDontReduce valvb'
                 = part2

          arg2 : ⟦ Box r B ⟧e adv (Promote vb) (Promote vb')
          arg2 vb0 vb0' vb0redux vb0'redux rewrite sym vb0redux | sym vb0'redux = boxInterpBiobs prf vb vb' part2e
      ... | no prf  = arg2 , arg1 , rightContext
        where
          part1e : ⟦ A ⟧e adv va va'
          part1e va0 va0' va0redux va0'redux
            rewrite sym va0redux | sym va0'redux
                  | valuesDontReduce valva
                  | valuesDontReduce valva'
                 = part1

          arg1 : ⟦ Box r A ⟧e adv (Promote va) (Promote va')
          arg1 va0 va0' va0redux va0'redux rewrite sym va0redux | sym va0'redux = boxInterpBiunobs prf va va' (binaryImpliesUnary part1e)

          part2e : ⟦ B ⟧e adv vb vb'
          part2e vb0 vb0' vb0redux vb0'redux
            rewrite sym vb0redux | sym vb0'redux
                  | valuesDontReduce valvb
                  | valuesDontReduce valvb'
                 = part2

          arg2 : ⟦ Box r B ⟧e adv (Promote vb) (Promote vb')
          arg2 vb0 vb0' vb0redux vb0'redux rewrite sym vb0redux | sym vb0'redux = boxInterpBiunobs prf vb vb' (binaryImpliesUnary part2e)

... | no not-r-less-adv rewrite sym prf
   | substPresLetProd {zero} {sz} {γ1} {t1} {t2}
   | substPresLetProd {zero} {sz} {γ2} {t1} {t2} =
 ?
