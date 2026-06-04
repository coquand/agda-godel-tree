{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EncodeClosed -- the missing structural lemma :
--
--   closed_encode : {P : Formula} (d : Deriv P) -> Closed (encode d)
--
-- "every proof code is closed".   Routine induction on  d : every  encode
-- clause emits only  natCode / codeTerm / codeFun1 / codeFun2 / codeFormula
-- ( all closed ) and recursive  encode s.   Discharges the  Closed (encode d)
-- HYPOTHESIS that  T4.ChaitinG1Discharge / ChaitinG1Chain  currently carry,
-- and ( with completeness  thmT_complete_rec ) gives a CLOSED proof code
-- w := encode d  with  thmT w = codeFormula P  -- the surprise-GII Step-2 input.

module T4.EncodeClosed where

open import T4.Base
open import T4.Tags using ( tag_ax ; tag_sb ; tag_mp ; tag_ind )
open import T4.Code using ( codeTerm ; codeFun1 ; codeFun2 ; codeFormula )
open import T4.Encode using ( encode )

open import BRA3.Dispatch using ( Closed ; closed_O ; closed_natCode ; closed_ap2 )

------------------------------------------------------------------------
-- SECTION 0.  Closedness of the code-builders ( complete  Fun1 / Fun2 ).

clPair : {a b : Term} -> Closed a -> Closed b -> Closed (ap2 Pair a b)
clPair {a} {b} ca cb = closed_ap2 Pair a b ca cb

closed_codeFun1 : (f : Fun1) -> Closed (codeFun1 f)
closed_codeFun2 : (g : Fun2) -> Closed (codeFun2 g)

closed_codeFun1 s           = closed_natCode _
closed_codeFun1 o           = closed_natCode _
closed_codeFun1 u           = closed_natCode _
closed_codeFun1 (C g h1 h2) =
  clPair (closed_natCode _)
    (clPair (closed_codeFun2 g) (clPair (closed_codeFun1 h1) (closed_codeFun1 h2)))

closed_codeFun2 v           = closed_natCode _
closed_codeFun2 (R g h1 h2) =
  clPair (closed_natCode _)
    (clPair (closed_codeFun1 g) (clPair (closed_codeFun2 h1) (closed_codeFun2 h2)))

closed_codeTerm : (t : Term) -> Closed (codeTerm t)
closed_codeTerm O           = closed_O
closed_codeTerm (var k)     = clPair (closed_natCode _) (closed_natCode _)
closed_codeTerm (ap1 f t)   =
  clPair (closed_natCode _) (clPair (closed_codeFun1 f) (closed_codeTerm t))
closed_codeTerm (ap2 g a b) =
  clPair (closed_natCode _)
    (clPair (closed_codeFun2 g) (clPair (closed_codeTerm a) (closed_codeTerm b)))

closed_codeFormula : (P : Formula) -> Closed (codeFormula P)
closed_codeFormula (atomic (eqn a b)) =
  clPair (closed_natCode _) (clPair (closed_codeTerm a) (closed_codeTerm b))
closed_codeFormula (neg p)   =
  clPair (closed_natCode _) (closed_codeFormula p)
closed_codeFormula (imp p q) =
  clPair (closed_natCode _) (clPair (closed_codeFormula p) (closed_codeFormula q))

------------------------------------------------------------------------
-- SECTION 1.  Closedness of the  pack / packAx / encode_sb  shapes
-- ( reproduced as closures matching  encode 's reduced output ).

clPk : (k : Nat) {x : Term} -> Closed x -> Closed (ap2 Pair (natCode k) x)
clPk k cx = clPair (closed_natCode k) cx

clPkAx :
  (idx : Nat) {body : Term} -> Closed body ->
  Closed (ap2 Pair (natCode tag_ax) (ap2 Pair (natCode idx) body))
clPkAx idx cb = clPk tag_ax (clPk idx cb)

clSb :
  {k : Nat} {t inner : Term} -> Closed t -> Closed inner ->
  Closed (ap2 Pair (natCode tag_sb)
            (ap2 Pair (ap2 Pair (natCode k) t) inner))
clSb {k} ct cinner = clPk tag_sb (clPair (clPk k ct) cinner)

------------------------------------------------------------------------
-- SECTION 2.  The lemma.

closed_encode : {P : Formula} (d : Deriv P) -> Closed (encode d)
closed_encode ax_succ_nonzero      = clPkAx 0 closed_O
closed_encode (ax_o t)             = clSb (closed_codeTerm t) (clPkAx 1 closed_O)
closed_encode (ax_u t)             = clSb (closed_codeTerm t) (clPkAx 2 closed_O)
closed_encode (ax_v a b)           =
  clSb (closed_codeTerm b)
    (clSb (closed_codeTerm a)
      (clSb (closed_codeTerm (var _)) (clPkAx 3 closed_O)))
closed_encode (ax_eqTrans x y z)   =
  clSb (closed_codeTerm z)
    (clSb (closed_codeTerm y)
      (clSb (closed_codeTerm x)
        (clSb (closed_codeTerm (var _))
          (clSb (closed_codeTerm (var _)) (clPkAx 4 closed_O)))))
closed_encode (ax_eqCong1 f a b)   =
  clSb (closed_codeTerm b)
    (clSb (closed_codeTerm a)
      (clSb (closed_codeTerm (var _)) (clPkAx 5 (closed_codeFun1 f))))
closed_encode (ax_eqCongL g a b c) =
  clSb (closed_codeTerm c)
    (clSb (closed_codeTerm b)
      (clSb (closed_codeTerm a)
        (clSb (closed_codeTerm (var _))
          (clSb (closed_codeTerm (var _)) (clPkAx 6 (closed_codeFun2 g))))))
closed_encode (ax_eqCongR g a b c) =
  clSb (closed_codeTerm c)
    (clSb (closed_codeTerm b)
      (clSb (closed_codeTerm a)
        (clSb (closed_codeTerm (var _))
          (clSb (closed_codeTerm (var _)) (clPkAx 7 (closed_codeFun2 g))))))
closed_encode (ax_C g h1 h2 t)     =
  clSb (closed_codeTerm t) (clPkAx 8 (closed_codeFun1 (C g h1 h2)))
closed_encode (ax_R_base g h1 h2 x) =
  clSb (closed_codeTerm x) (clPkAx 9 (closed_codeFun2 (R g h1 h2)))
closed_encode (ax_R_step g h1 h2 x n) =
  clSb (closed_codeTerm n)
    (clSb (closed_codeTerm x)
      (clSb (closed_codeTerm (var _)) (clPkAx 10 (closed_codeFun2 (R g h1 h2)))))
closed_encode (axK A B)            =
  clPkAx 11 (clPair (closed_codeFormula A) (closed_codeFormula B))
closed_encode (axS A B Cf)         =
  clPkAx 12 (clPair (closed_codeFormula A)
              (clPair (closed_codeFormula B) (closed_codeFormula Cf)))
closed_encode (axNeg A B)          =
  clPkAx 13 (clPair (closed_codeFormula A) (closed_codeFormula B))
closed_encode (mp dPQ dP)          =
  clPk tag_mp (clPair (closed_encode dPQ) (closed_encode dP))
closed_encode (ruleInst k t dP)    =
  clPk tag_sb (clPair (clPair (closed_natCode k) (closed_codeTerm t))
                      (closed_encode dP))
closed_encode (ruleIndNat k dB dS) =
  clPk tag_ind (clPair (closed_encode dB) (closed_encode dS))
