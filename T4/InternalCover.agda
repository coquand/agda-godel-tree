{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.InternalCover -- INTERNAL CORRECTNESS OF  enum  ( the surprise-GII
-- enum-coverage lemma ), proved over a FREE program variable WITHOUT any
-- surjective-pairing law for  pi .
--
-- =====================================================================
-- HEADLINE.
-- =====================================================================
--
--   internalCover :
--     (Cf : Formula) ->
--     ((k : Nat) -> Lt k Bnat ->
--        Deriv (imp (eqF (var 0) (ap1 enum (natCode k))) Cf)) ->
--     Deriv (imp (eqF (ap1 (checkAlphN Lstar_meta) (var 0)) (ap1 s O)) Cf)
--
-- "If  Cf  follows from  p = enum k  for every enumerated index  k , and the
-- free code  p = var 0  passes the depth-L* validity check, then  Cf ."  This
-- is the ELIMINATED form of  T  internally proving
--   checkAlph p  =>  |p| <= L*  =>  ( p = enum 0  \/ ... \/ p = enum (Bnat-1) )
-- i.e.  EnumProg.enum_cover  INTERNALISED ( object-level, over free  p ).
--
-- =====================================================================
-- WHY NO SURJECTIVE PAIRING ( the method, cf. T4.CheckAlphN ).
-- =====================================================================
--
-- The checker  checkAlphN n p = natEqF p (reconF n p)  is its OWN structural
-- witness : its acceptance  = s O  reflects ( natEqF_sound_imp ) into the
-- object equation  p = reconF n p , and the canonical reconstruction
--  reconF n p  carries the cell shape and valid head LITERALLY.   So the
-- coverage induction reads off  p = pi (natCode i) (Snd p)  ( valid tag,
-- shorter valid tail ) directly from the checker's assertion -- never needing
-- the universal  pi (Fst p)(Snd p) = p  ( which is unshipped Cantor
-- surjectivity ).   The bounded depth  n  drives an EXTERNAL induction whose
-- step peels exactly one cell.

open import T4.Base

module T4.InternalCover (Lstar_meta : Nat) where

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.ChurchT117   using ( Fst )
open import BRA3.ChurchT116   using ( Snd )
open import BRA3.SubT.NatEq   using ( natEqF )
open import BRA3.SubT.NatEqRefl using ( natEqF_self_univ )
open import BRA3.PairAlgebra  using ( Pair )
open import BRA3.Dispatch     using ( condFork ; condFork_false )
open import BRA3.RecBRA3AtPairUniv using ( condFork_true_univ )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import BRA3.Logic        using ( prependEqLeft ; appendEqRight )
open import BRA3.ChurchCM     using ( caseElim )
open import BRA3.ChurchDChurchAsSub using ( caseElimUnderOne )
open import BRA3.Contrapositive using ( identP ; compI )
open import BRA3.RuleInst2    using ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right )

open import T4.Thm12.ImpHelpers using
  ( impLift ; impCong1 ; impCongR ; impEqTrans ; impRuleSym )
open import T4.RunProgMono    using ( impEqTrans2 )
open import T4.NatEqReflect   using ( app2 )
open import T4.NatEqSoundImp  using ( natEqF_sound_imp )
open import T4.CheckAlphN

open import T4.SurpriseG2.MetaPigeonhole using ( Lt )
open import T4.EnumProg Lstar_meta using
  ( Sigma ; mkSigma ; fst ; snd ; And ; Or ; inl ; inr
  ; Lst ; lnil ; lcons ; lapp ; llen ; LMem ; lhere ; lthere ; lapp_mem
  ; strsExact ; strsUpTo ; extendAll
  ; extendAll_intro1 ; extendAll_intro2 ; extendAll_intro3
  ; exactSub ; nthD ; memToIndex
  ; enum ; Bnat ; enumAt )

------------------------------------------------------------------------
-- SECTION 1.  Meta-list membership lemmas ( pure  Lst  induction ).

-- A member of  strsUpTo n  lives in  strsExact m  for some  m <= n .
upToExact :
  (n : Nat) (x : Term) -> LMem x (strsUpTo n) ->
  Sigma Nat (\ m -> And (NatLe m n) (LMem x (strsExact m)))
upToExact zero    x mem = mkSigma zero (mkSigma (le-zero zero) mem)
upToExact (suc n) x mem with lapp_mem x (strsExact (suc n)) (strsUpTo n) mem
... | inl mE = mkSigma (suc n) (mkSigma (le-refl (suc n)) mE)
... | inr mU with upToExact n x mU
...   | mkSigma m (mkSigma le me) = mkSigma m (mkSigma (le-suc-right le) me)

-- Re-cons under a valid tag lands in  strsUpTo (suc n) .
consMem1 :
  (n : Nat) (x : Term) -> LMem x (strsUpTo n) ->
  LMem (ap2 pi (natCode 1) x) (strsUpTo (suc n))
consMem1 n x mem with upToExact n x mem
... | mkSigma m (mkSigma le me) =
      exactSub (suc m) (suc n) (le-suc le)
        (ap2 pi (natCode 1) x) (extendAll_intro1 x (strsExact m) me)

consMem2 :
  (n : Nat) (x : Term) -> LMem x (strsUpTo n) ->
  LMem (ap2 pi (natCode 2) x) (strsUpTo (suc n))
consMem2 n x mem with upToExact n x mem
... | mkSigma m (mkSigma le me) =
      exactSub (suc m) (suc n) (le-suc le)
        (ap2 pi (natCode 2) x) (extendAll_intro2 x (strsExact m) me)

consMem3 :
  (n : Nat) (x : Term) -> LMem x (strsUpTo n) ->
  LMem (ap2 pi (natCode 3) x) (strsUpTo (suc n))
consMem3 n x mem with upToExact n x mem
... | mkSigma m (mkSigma le me) =
      exactSub (suc m) (suc n) (le-suc le)
        (ap2 pi (natCode 3) x) (extendAll_intro3 x (strsExact m) me)

-- O  is always a ( length-0 ) member.
memO : (n : Nat) -> LMem O (strsUpTo n)
memO n = exactSub zero n (le-zero n) O (lhere lnil)

------------------------------------------------------------------------
-- SECTION 2.  The condFork case split, threaded under a context  Q .
--   from  p = condFork (Pair A B) g  and the two branch-continuations
--   ( given  p = A , resp.  p = B ),  conclude  Cf .

forkCase :
  (Q : Formula) (p A B g : Term) (Cf : Formula) ->
  Deriv (imp Q (eqF p (ap2 condFork (ap2 Pair A B) g))) ->
  Deriv (imp Q (imp (eqF p A) Cf)) ->
  Deriv (imp Q (imp (eqF p B) Cf)) ->
  Deriv (imp Q Cf)
forkCase Q p A B g Cf q1 kFst kSnd =
  let cf : Term
      cf = ap2 condFork (ap2 Pair A B) g

      -- under  (g = O) :  cf = B .
      sndChain : Deriv (imp (eqF g O) (eqF cf B))
      sndChain =
        impEqTrans {eqF g O} cf (ap2 condFork (ap2 Pair A B) O) B
          (impCongR {eqF g O} condFork g O (ap2 Pair A B) (identP (eqF g O)))
          (impEqTrans {eqF g O} (ap2 condFork (ap2 Pair A B) O) (ap1 Snd (ap2 Pair A B)) B
             (impLift {eqF g O} (condFork_false (ap2 Pair A B)))
             (impLift {eqF g O} (axSnd A B)))

      -- under  (g /= O) :  cf = A .
      gIsSucc : Deriv (imp (neg (eqF g O)) (eqF g (ap1 s (ap1 predecessor g))))
      gIsSucc = impRuleSym (ruleInst 0 g L_sp)

      fstChain : Deriv (imp (neg (eqF g O)) (eqF cf A))
      fstChain =
        impEqTrans {neg (eqF g O)} cf
          (ap2 condFork (ap2 Pair A B) (ap1 s (ap1 predecessor g))) A
          (impCongR {neg (eqF g O)} condFork g (ap1 s (ap1 predecessor g)) (ap2 Pair A B) gIsSucc)
          (impEqTrans {neg (eqF g O)}
             (ap2 condFork (ap2 Pair A B) (ap1 s (ap1 predecessor g)))
             (ap1 Fst (ap2 Pair A B)) A
             (impLift {neg (eqF g O)} (condFork_true_univ (ap2 Pair A B) (ap1 predecessor g)))
             (impLift {neg (eqF g O)} (axFst A B)))

      -- p = B  under  (Q , g = O) ;   p = A  under  (Q , g /= O) .
      pEqB : Deriv (imp Q (imp (eqF g O) (eqF p B)))
      pEqB = impEqTrans2 {Q} {eqF g O} p cf B
               (compI q1 (axK (eqF p cf) (eqF g O)))
               (impLift {Q} sndChain)

      pEqA : Deriv (imp Q (imp (neg (eqF g O)) (eqF p A)))
      pEqA = impEqTrans2 {Q} {neg (eqF g O)} p cf A
               (compI q1 (axK (eqF p cf) (neg (eqF g O))))
               (impLift {Q} fstChain)

      argX : Deriv (imp Q (imp (eqF g O) Cf))
      argX = app2 (compI kSnd (axK (imp (eqF p B) Cf) (eqF g O))) pEqB

      argY : Deriv (imp Q (imp (neg (eqF g O)) Cf))
      argY = app2 (compI kFst (axK (imp (eqF p A) Cf) (neg (eqF g O)))) pEqA
  in caseElimUnderOne {Q} {eqF g O} {neg (eqF g O)} {Cf}
       (impLift {Q} (identP (neg (eqF g O))))
       argX argY

------------------------------------------------------------------------
-- SECTION 3.  The cell branch :  given  p = pi (natCode i) (reconF n (Snd p))
--   ( i.e.  p = cellOf i (reconF n) p ),  apply the IH at  Snd p  and  cases .

cellBranch :
  (n : Nat) (p : Term) (i : Nat) (Cf : Formula) ->
  ( (Cf' : Formula) ->
    ((x : Term) -> LMem x (strsUpTo n) ->
       Deriv (imp (eqF (ap1 Snd p) x) Cf')) ->
    Deriv (imp (eqF (ap1 (checkAlphN n) (ap1 Snd p)) (ap1 s O)) Cf') ) ->
  ((x : Term) -> LMem x (strsUpTo n) ->
     LMem (ap2 pi (natCode i) x) (strsUpTo (suc n))) ->
  ((x : Term) -> LMem x (strsUpTo (suc n)) -> Deriv (imp (eqF p x) Cf)) ->
  Deriv (imp (eqF p (ap1 (cellOf i (reconF n)) p)) Cf)
cellBranch n p i Cf ih consMemI cases =
  let Q : Formula
      Q = eqF p (ap1 (cellOf i (reconF n)) p)

      sp : Term
      sp = ap1 Snd p
      rsp : Term
      rsp = ap1 (reconF n) sp
      cellTm : Term
      cellTm = ap2 pi (natCode i) rsp

      pcell : Deriv (imp Q (eqF p cellTm))
      pcell = impEqTrans {Q} p (ap1 (cellOf i (reconF n)) p) cellTm
                (identP Q)
                (impLift {Q} (cellOf_eq i (reconF n) p))

      pSnd : Deriv (imp Q (eqF sp rsp))
      pSnd = impEqTrans {Q} sp (ap1 Snd cellTm) rsp
               (impCong1 {Q} Snd p cellTm pcell)
               (impLift {Q} (axSnd (natCode i) rsp))

      pchk : Deriv (imp Q (eqF (ap1 (checkAlphN n) sp) (ap1 s O)))
      pchk =
        impEqTrans {Q} (ap1 (checkAlphN n) sp) (ap2 natEqF sp rsp) (ap1 s O)
          (impLift {Q} (checkAlphN_eq n sp))
          (impEqTrans {Q} (ap2 natEqF sp rsp) (ap2 natEqF sp sp) (ap1 s O)
             (impCongR {Q} natEqF rsp sp sp (impRuleSym pSnd))
             (impLift {Q} (natEqF_self_univ sp)))

      pPiSnd : Deriv (imp Q (eqF p (ap2 pi (natCode i) sp)))
      pPiSnd = impEqTrans {Q} p cellTm (ap2 pi (natCode i) sp)
                 pcell
                 (impCongR {Q} pi rsp sp (natCode i) (impRuleSym pSnd))

      cases' :
        (x : Term) -> LMem x (strsUpTo n) ->
        Deriv (imp (eqF sp x) (imp Q Cf))
      cases' x mem =
        let casePx : Deriv (imp (eqF p (ap2 pi (natCode i) x)) Cf)
            casePx = cases (ap2 pi (natCode i) x) (consMemI x mem)

            congTail : Deriv (imp (eqF sp x) (imp Q
                          (eqF (ap2 pi (natCode i) sp) (ap2 pi (natCode i) x))))
            congTail =
              compI (impCongR {eqF sp x} pi sp x (natCode i) (identP (eqF sp x)))
                    (axK (eqF (ap2 pi (natCode i) sp) (ap2 pi (natCode i) x)) Q)

            pEqPiX : Deriv (imp (eqF sp x) (imp Q (eqF p (ap2 pi (natCode i) x))))
            pEqPiX = impEqTrans2 {eqF sp x} {Q} p (ap2 pi (natCode i) sp) (ap2 pi (natCode i) x)
                       (impLift {eqF sp x} pPiSnd)
                       congTail
        in app2 (impLift {eqF sp x} (impLift {Q} casePx)) pEqPiX

      ihApplied : Deriv (imp (eqF (ap1 (checkAlphN n) sp) (ap1 s O)) (imp Q Cf))
      ihApplied = ih (imp Q Cf) cases'

      doubleQ : Deriv (imp Q (imp Q Cf))
      doubleQ = compI pchk ihApplied
  in mp (mp (axS Q Q Cf) doubleQ) (identP Q)

------------------------------------------------------------------------
-- SECTION 4.  The coverage eliminator, by external induction on  n .

coverElimN :
  (n : Nat) (p : Term) (Cf : Formula) ->
  ((x : Term) -> LMem x (strsUpTo n) -> Deriv (imp (eqF p x) Cf)) ->
  Deriv (imp (eqF (ap1 (checkAlphN n) p) (ap1 s O)) Cf)
coverElimN zero p Cf cases =
  let eqE : Deriv (eqF (ap1 (checkAlphN zero) p) (ap2 natEqF p O))
      eqE = ruleTrans (checkAlphN_eq zero p) (congR natEqF p (reconF_zero_eq p))
      toEq : Deriv (imp (eqF (ap1 (checkAlphN zero) p) (ap1 s O)) (eqF p O))
      toEq = compI (prependEqLeft (ap2 natEqF p O) (ap1 (checkAlphN zero) p) (ap1 s O)
                      (ruleSym eqE))
                   (natEqF_sound_imp p O)
  in compI toEq (cases O (lhere lnil))
coverElimN (suc n) p Cf cases =
  let Acc : Formula
      Acc = eqF (ap1 (checkAlphN (suc n)) p) (ap1 s O)

      g1 : Term
      g1 = ap1 (cellOf 1 (reconF n)) p
      c2 : Term
      c2 = ap1 (cell2Fun (reconF n)) p
      h1 : Term
      h1 = ap2 natEqF (ap1 Fst p) (natCode 1)

      recEq : Deriv (imp Acc (eqF p (ap1 (reconF (suc n)) p)))
      recEq = compI (prependEqLeft (ap2 natEqF p (ap1 (reconF (suc n)) p))
                       (ap1 (checkAlphN (suc n)) p) (ap1 s O)
                       (ruleSym (checkAlphN_eq (suc n) p)))
                    (natEqF_sound_imp p (ap1 (reconF (suc n)) p))

      pEqC1 : Deriv (imp Acc (eqF p (ap2 condFork (ap2 Pair g1 c2) h1)))
      pEqC1 = impEqTrans {Acc} p (ap1 (reconF (suc n)) p)
                (ap2 condFork (ap2 Pair g1 c2) h1)
                recEq (impLift {Acc} (reconF_suc_eq n p))

      ----------------------------------------------------------------
      -- level 3 :  p = c3  ( c3 = cell3Fun (reconF n) p ).
      g3 : Term
      g3 = ap1 (cellOf 3 (reconF n)) p
      h3 : Term
      h3 = ap2 natEqF (ap1 Fst p) (natCode 3)

      level3 : Deriv (imp (eqF p (ap1 (cell3Fun (reconF n)) p)) Cf)
      level3 =
        let Q3 : Formula
            Q3 = eqF p (ap1 (cell3Fun (reconF n)) p)
            pEqC3 : Deriv (imp Q3 (eqF p (ap2 condFork (ap2 Pair g3 O) h3)))
            pEqC3 = impEqTrans {Q3} p (ap1 (cell3Fun (reconF n)) p)
                      (ap2 condFork (ap2 Pair g3 O) h3)
                      (identP Q3) (impLift {Q3} (cell3_eq (reconF n) p))
            kFst3 : Deriv (imp Q3 (imp (eqF p g3) Cf))
            kFst3 = impLift {Q3}
                      (cellBranch n p 3 Cf (coverElimN n (ap1 Snd p)) (consMem3 n) cases)
            kSnd3 : Deriv (imp Q3 (imp (eqF p O) Cf))
            kSnd3 = impLift {Q3} (cases O (memO (suc n)))
        in forkCase Q3 p g3 O h3 Cf pEqC3 kFst3 kSnd3

      ----------------------------------------------------------------
      -- level 2 :  p = c2  ( c2 = cell2Fun (reconF n) p ).
      g2 : Term
      g2 = ap1 (cellOf 2 (reconF n)) p
      c3 : Term
      c3 = ap1 (cell3Fun (reconF n)) p
      h2 : Term
      h2 = ap2 natEqF (ap1 Fst p) (natCode 2)

      level2 : Deriv (imp (eqF p (ap1 (cell2Fun (reconF n)) p)) Cf)
      level2 =
        let Q2 : Formula
            Q2 = eqF p (ap1 (cell2Fun (reconF n)) p)
            pEqC2 : Deriv (imp Q2 (eqF p (ap2 condFork (ap2 Pair g2 c3) h2)))
            pEqC2 = impEqTrans {Q2} p (ap1 (cell2Fun (reconF n)) p)
                      (ap2 condFork (ap2 Pair g2 c3) h2)
                      (identP Q2) (impLift {Q2} (cell2_eq (reconF n) p))
            kFst2 : Deriv (imp Q2 (imp (eqF p g2) Cf))
            kFst2 = impLift {Q2}
                      (cellBranch n p 2 Cf (coverElimN n (ap1 Snd p)) (consMem2 n) cases)
            kSnd2 : Deriv (imp Q2 (imp (eqF p c3) Cf))
            kSnd2 = impLift {Q2} level3
        in forkCase Q2 p g2 c3 h2 Cf pEqC2 kFst2 kSnd2

      ----------------------------------------------------------------
      -- level 1 :  p = reconF (suc n) p .
      kFst1 : Deriv (imp Acc (imp (eqF p g1) Cf))
      kFst1 = impLift {Acc}
                (cellBranch n p 1 Cf (coverElimN n (ap1 Snd p)) (consMem1 n) cases)
      kSnd1 : Deriv (imp Acc (imp (eqF p c2) Cf))
      kSnd1 = impLift {Acc} level2
  in forkCase Acc p g1 c2 h1 Cf pEqC1 kFst1 kSnd1

------------------------------------------------------------------------
-- SECTION 5.  Packaging :  members of  progs = strsUpTo Lstar_meta  ARE
-- enumerated slots ( memToIndex + enumAt ).

internalCover :
  (Cf : Formula) ->
  ((k : Nat) -> Lt k Bnat ->
     Deriv (imp (eqF (var zero) (ap1 enum (natCode k))) Cf)) ->
  Deriv (imp (eqF (ap1 (checkAlphN Lstar_meta) (var zero)) (ap1 s O)) Cf)
internalCover Cf cases =
  coverElimN Lstar_meta (var zero) Cf cases0
  where
    cases0 :
      (x : Term) -> LMem x (strsUpTo Lstar_meta) ->
      Deriv (imp (eqF (var zero) x) Cf)
    cases0 x mem with memToIndex (strsUpTo Lstar_meta) x mem
    ... | mkSigma k (mkSigma klt eqkx) =
          let enumEqX : Deriv (eqF (ap1 enum (natCode k)) x)
              enumEqX = eqSubst (\ z -> Deriv (eqF (ap1 enum (natCode k)) z))
                                eqkx (enumAt k klt)
          in compI (appendEqRight (var zero) x (ap1 enum (natCode k)) (ruleSym enumEqX))
                   (cases k klt)
