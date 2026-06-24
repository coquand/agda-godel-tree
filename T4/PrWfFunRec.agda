{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfFunRec -- the OBJECT FUNCODE-VALIDITY predicate  wfFunRec : Fun1 , a
-- binRec fold over a derivation TREE that, at every node carrying funcode(s),
-- checks  funValid (carried fun) = O  (one-level reconstruction, T4.PrFunValid)
-- and recurses on the children:
--
--   wfFunRec O                  = O           (base; O excluded already by wfRed)
--   wfFunRec (derLeaf)          = O
--   wfFunRec (ap1c f d)         = pi (funValid f)              (wfFunRec d)
--   wfFunRec (ap2c g d1 d2)     = pi (funValid g) (pi (wfFunRec d1)(wfFunRec d2))
--   wfFunRec (derO d)           = wfFunRec d
--   wfFunRec (derU d)           = wfFunRec d
--   wfFunRec (derV d1 d2)       = pi (wfFunRec d1)(wfFunRec d2)
--   wfFunRec (derC g h1 h2 d)   = pi (fv3 g h1 h2) (wfFunRec d)
--   wfFunRec (derRb g h1 h2 d)  = pi (fv3 g h1 h2) (wfFunRec d)
--   wfFunRec (derRs g h1 h2 d1 d2) = pi (fv3 g h1 h2) (pi (wfFunRec d1)(wfFunRec d2))
--   wfFunRec (node, tag not 1..8) = O
-- where  fv3 g h1 h2 = pi (funValid g)(pi (funValid h1)(funValid h2)) .
--
-- The redex nodes (derC/derRb/derRs) carry bun3 g h1 h2 and the residual
-- triangle re-uses g,h1,h2 as CONGRUENCE funs, so their (shallow) validity is
-- needed for  wfFunRec (triF p) = O .  Conjoined with the tree-validity  wfRed
-- (base-reject) this gives FULL validity  wfRedFull = pi wfRed wfFunRec .
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrWfFunRec where

open import T4.Base

open import T4.PrDerCode
  using ( derLeaf ; ap1c ; ap2c ; derO ; derU ; derV ; derC ; derRb ; derRs
        ; dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs
        ; filler ; bun3 )
open import T4.PrWfFun using ( wfFun ; isF1 ; isF2 )
open import T4.PrCodeObj using ( cRec ; cComp )

-- DEEP funcode validity wired in as funValid/funValidF (replacing the shallow
-- T4.PrFunValid.funValid that was too weak for compound-fun congruences).
funValid : Term -> Term
funValid x = ap1 wfFun x
funValidF : Fun1
funValidF = wfFun
funValidF_eq : (x : Term) -> Deriv (eqF (ap1 funValidF x) (funValid x))
funValidF_eq x = axRefl (ap1 wfFun x)
open import T4.BinTree using ( binLeaf ; binNode ; binRec ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( foldOf ; test1 ; module NP )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt ; fold_at_O )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )
open import T4.PrDev using ( idxTest_fire ; idxTest_skip )

open import BRA3.Church       using ( pi )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  Index Fun1s, cells, the dispatch cascade and  wfFunRec .

derTagIdx : Fun1
derTagIdx = compose1U Fst nIdx
derBunIdx : Fun1
derBunIdx = compose1U Snd nIdx

bunGidx : Fun1
bunGidx = compose1U Fst derBunIdx
bunSndIdx : Fun1
bunSndIdx = compose1U Snd derBunIdx
bunH1idx : Fun1
bunH1idx = compose1U Fst bunSndIdx
bunH2idx : Fun1
bunH2idx = compose1U Snd bunSndIdx

fvB : Fun1                          -- funValid (the single bundle = Snd label)
fvB = compose1U funValidF derBunIdx
fv3 : Fun1                          -- pi (funValid g)(pi (funValid h1)(funValid h2))
fv3 = C pi (compose1U funValidF bunGidx)
           (C pi (compose1U funValidF bunH1idx) (compose1U funValidF bunH2idx))

unaryCell : Fun1                    -- wfFunRec l
unaryCell = lookupAt lIdx
wfAdCell : Fun1                     -- pi (wfFunRec l)(wfFunRec r)
wfAdCell = C pi (lookupAt lIdx) (lookupAt rIdx)
-- FIX(C): ap1c carries a Fun1 funcode (head in {3,4,5,6}); ap2c a Fun2 (head {7,8}).
arF1cell : Fun1                     -- isF1 funP : head in {3,4,5,6}
arF1cell = C pi (C natEqF bunGidx (constN 7))
             (C pi (C natEqF bunGidx (constN 8)) (C natEqF bunGidx (constN 1)))
arF2cell : Fun1                     -- isF2 funP : head in {7,8}
arF2cell = C pi (C natEqF bunGidx (constN 3))
             (C pi (C natEqF bunGidx (constN 4))
               (C pi (C natEqF bunGidx (constN 5))
                 (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1)))))
ap1cCell : Fun1                     -- pi (isF1 f)(pi (funValid f)(wfFunRec l))
ap1cCell = C pi arF1cell (C pi fvB unaryCell)
ap2cCell : Fun1                     -- pi (isF2 g)(pi (funValid g)(pi (wfFunRec l)(wfFunRec r)))
ap2cCell = C pi arF2cell (C pi fvB wfAdCell)
rcUnaryCell : Fun1                  -- pi (fv3 g h1 h2)(wfFunRec l)  (unused after FIX(C))
rcUnaryCell = C pi fv3 unaryCell
-- FIX(C): derC (tag 6) validates the reconstructed cComp = Pair 6 bundle (arity-aware
-- wfFun gives g Fun2, h1/h2 Fun1 -- exactly what the residual ap2c g(ap1c h1)(ap1c h2) needs).
recCForm : Fun1                     -- Pair (natCode 6) (the bundle) = cComp g h1 h2
recCForm = C Pair (constN 6) derBunIdx
recCwf : Fun1
recCwf = compose1U wfFun recCForm
rcCompC : Fun1                      -- pi (wfFun (cComp g h1 h2))(wfFunRec l)
rcCompC = C pi recCwf unaryCell
-- FIX(B): the derRs (tag 8) cell validates the RECONSTRUCTED R-combinator
-- Pair (natCode 8) bundle = cRec g h1 h2 (deep wfFun, supplying both the shallow
-- reassembly for the src endpoint AND the deep component validities), because the
-- triF residual third arm reuses the bundle wholesale as ap2c (Pair 8 bundle) .
recRForm : Fun1                     -- Pair (natCode 8) (the bundle)
recRForm = C Pair (constN 8) derBunIdx
recRwf : Fun1                       -- wfFun (Pair 8 bundle)
recRwf = compose1U wfFun recRForm
rcCompRb : Fun1                     -- derRb (tag 7): pi (wfFun (cRec g h1 h2))(wfFunRec l)
rcCompRb = C pi recRwf unaryCell
rcBinCell : Fun1                    -- pi (wfFun (cRec g h1 h2))(pi (wfFunRec l)(wfFunRec r))
rcBinCell = C pi recRwf wfAdCell

testTag : Nat -> Fun1
testTag k = C natEqF derTagIdx (constN k)

ff_l8 : Fun1
ff_l8 = C condFork (C pi rcBinCell Z) (testTag 8)
ff_l7 : Fun1
ff_l7 = C condFork (C pi rcCompRb ff_l8) (testTag 7)
ff_l6 : Fun1
ff_l6 = C condFork (C pi rcCompC ff_l7) (testTag 6)
ff_l5 : Fun1
ff_l5 = C condFork (C pi wfAdCell ff_l6) (testTag 5)
ff_l4 : Fun1
ff_l4 = C condFork (C pi unaryCell ff_l5) (testTag 4)
ff_l3 : Fun1
ff_l3 = C condFork (C pi unaryCell ff_l4) (testTag 3)
ff_l2 : Fun1
ff_l2 = C condFork (C pi ap2cCell ff_l3) (testTag 2)
fnCellNode : Fun1
fnCellNode = C condFork (C pi ap1cCell ff_l2) (testTag 1)

wfFunRec : Fun1
wfFunRec = binRec Z Z fnCellNode

------------------------------------------------------------------------
-- SECTION 2.  wfFunRec O = O (base) and the leaf.

wfFunRec_O : Deriv (eqF (ap1 wfFunRec O) O)
wfFunRec_O = ruleTrans (fold_at_O Z (Post (stepOf Z fnCellNode) pi)) (axZ O)
  where open import T4.ParsObj using ( stepOf )

wfFunRec_reflO : Deriv (eqF (ap1 wfFunRec derLeaf) O)
wfFunRec_reflO =
  let open NP Z Z fnCellNode O dgReflO
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (axZ input_pkg)

------------------------------------------------------------------------
-- SECTION 3.  Shared node plumbing.

w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())
wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
wn m k p = decideNatNeq m k p

module Node (lab l r : Term) where
  open NP Z Z fnCellNode (natCode 1) (ap2 Pair lab (ap2 Pair l r)) public
  t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
  t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
  nIdx_eq : Deriv (eqF (ap1 nIdx input_pkg) lab)
  nIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
              (ruleTrans (cong1 Fst np_rc) (axFst lab (ap2 Pair l r)))
  sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) input_pkg) (ap2 Pair l r))
  sndArg_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                (ruleTrans (cong1 Snd np_rc) (axSnd lab (ap2 Pair l r)))
  lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) l)
  lIdx_eq = ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) input_pkg)
              (ruleTrans (cong1 Fst sndArg_eq) (axFst l r))
  rIdx_eq : Deriv (eqF (ap1 rIdx input_pkg) r)
  rIdx_eq = ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) input_pkg)
              (ruleTrans (cong1 Snd sndArg_eq) (axSnd l r))
  leq_lr_P : Deriv (leq (ap2 Pair l r) P_outer)
  leq_lr_P = leq_trans (ap2 Pair l r) (ap2 Pair lab (ap2 Pair l r)) P_outer
               (leq_pi_right lab (ap2 Pair l r)) leq_b_P
  recL : Deriv (eqF (ap1 unaryCell input_pkg) (ap1 wfFunRec l))
  recL = np_lookup_gen lIdx l lIdx_eq
           (leq_trans l (ap2 Pair l r) P_outer (leq_pi_left l r) leq_lr_P)
  recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 wfFunRec r))
  recR = np_lookup_gen rIdx r rIdx_eq
           (leq_trans r (ap2 Pair l r) P_outer (leq_pi_right l r) leq_lr_P)
  tag_eq : (hf : Term) -> Deriv (eqF (ap1 Fst lab) hf) ->
           Deriv (eqF (ap1 derTagIdx input_pkg) hf)
  tag_eq hf eq = ruleTrans (compose1U_eq Fst nIdx input_pkg)
                   (ruleTrans (cong1 Fst nIdx_eq) eq)
  to_cellNode : Deriv (eqF (ap1 wfFunRec (binNode lab l r)) (ap1 fnCellNode input_pkg))
  to_cellNode = collapse_snd t1_O
  -- bundle (= Snd label) value.
  derBun_eq : Deriv (eqF (ap1 derBunIdx input_pkg) (ap1 Snd lab))
  derBun_eq = ruleTrans (compose1U_eq Snd nIdx input_pkg) (cong1 Snd nIdx_eq)
  -- funValid of a single bundle  bnd  given  Snd lab = bnd .
  fvOf : (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
         Deriv (eqF (ap1 fvB input_pkg) (funValid bnd))
  fvOf bnd e =
    ruleTrans (compose1U_eq funValidF derBunIdx input_pkg)
      (ruleTrans (cong1 funValidF derBun_eq)
        (ruleTrans (cong1 funValidF e) (funValidF_eq bnd)))
  -- FIX(C) arity value lemmas: head of the carried fun.
  bunG_at : (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
            Deriv (eqF (ap1 bunGidx input_pkg) (ap1 Fst bnd))
  bunG_at bnd e = ruleTrans (compose1U_eq Fst derBunIdx input_pkg)
                    (cong1 Fst (ruleTrans derBun_eq e))
  nHb : (k : Nat) (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
        Deriv (eqF (ap1 (C natEqF bunGidx (constN k)) input_pkg) (ap2 natEqF (ap1 Fst bnd) (natCode k)))
  nHb k bnd e =
    ruleTrans (ax_C natEqF bunGidx (constN k) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN k) input_pkg) (bunG_at bnd e))
                 (congR natEqF (ap1 Fst bnd) (constN_eq k input_pkg)))
  arF1_of : (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
            Deriv (eqF (ap1 arF1cell input_pkg) (isF1 bnd))
  arF1_of bnd e =
    ruleTrans (ax_C pi (C natEqF bunGidx (constN 7)) (C pi (C natEqF bunGidx (constN 8)) (C natEqF bunGidx (constN 1))) input_pkg)
      (ruleTrans (congL pi (ap1 (C pi (C natEqF bunGidx (constN 8)) (C natEqF bunGidx (constN 1))) input_pkg) (nHb 7 bnd e))
        (congR pi (ap2 natEqF (ap1 Fst bnd) (natCode 7))
          (ruleTrans (ax_C pi (C natEqF bunGidx (constN 8)) (C natEqF bunGidx (constN 1)) input_pkg)
            (ruleTrans (congL pi (ap1 (C natEqF bunGidx (constN 1)) input_pkg) (nHb 8 bnd e))
                       (congR pi (ap2 natEqF (ap1 Fst bnd) (natCode 8)) (nHb 1 bnd e))))))
  arF2_of : (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
            Deriv (eqF (ap1 arF2cell input_pkg) (isF2 bnd))
  arF2_of bnd e =
    ruleTrans (ax_C pi (C natEqF bunGidx (constN 3)) (C pi (C natEqF bunGidx (constN 4)) (C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1))))) input_pkg)
      (ruleTrans (congL pi (ap1 (C pi (C natEqF bunGidx (constN 4)) (C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1))))) input_pkg) (nHb 3 bnd e))
        (congR pi (ap2 natEqF (ap1 Fst bnd) (natCode 3))
          (ruleTrans (ax_C pi (C natEqF bunGidx (constN 4)) (C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1)))) input_pkg)
            (ruleTrans (congL pi (ap1 (C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1)))) input_pkg) (nHb 4 bnd e))
              (congR pi (ap2 natEqF (ap1 Fst bnd) (natCode 4))
                (ruleTrans (ax_C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1))) input_pkg)
                  (ruleTrans (congL pi (ap1 (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1))) input_pkg) (nHb 5 bnd e))
                    (congR pi (ap2 natEqF (ap1 Fst bnd) (natCode 5))
                      (ruleTrans (ax_C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1)) input_pkg)
                        (ruleTrans (congL pi (ap1 (C natEqF bunGidx (constN 1)) input_pkg) (nHb 6 bnd e))
                                   (congR pi (ap2 natEqF (ap1 Fst bnd) (natCode 6)) (nHb 1 bnd e))))))))))))
  -- ap1c / ap2c cell values (single carried fun  bnd = Snd lab).
  ap1cInner_of : (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
    Deriv (eqF (ap1 (C pi fvB unaryCell) input_pkg) (ap2 pi (funValid bnd) (ap1 wfFunRec l)))
  ap1cInner_of bnd e =
    ruleTrans (ax_C pi fvB unaryCell input_pkg)
      (ruleTrans (congL pi (ap1 unaryCell input_pkg) (fvOf bnd e))
                 (congR pi (funValid bnd) recL))
  ap1cCell_of : (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
    Deriv (eqF (ap1 ap1cCell input_pkg) (ap2 pi (isF1 bnd) (ap2 pi (funValid bnd) (ap1 wfFunRec l))))
  ap1cCell_of bnd e =
    ruleTrans (ax_C pi arF1cell (C pi fvB unaryCell) input_pkg)
      (ruleTrans (congL pi (ap1 (C pi fvB unaryCell) input_pkg) (arF1_of bnd e))
                 (congR pi (isF1 bnd) (ap1cInner_of bnd e)))
  ap2cInner_of : (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
    Deriv (eqF (ap1 (C pi fvB wfAdCell) input_pkg) (ap2 pi (funValid bnd) (ap2 pi (ap1 wfFunRec l) (ap1 wfFunRec r))))
  ap2cInner_of bnd e =
    ruleTrans (ax_C pi fvB wfAdCell input_pkg)
      (ruleTrans (congL pi (ap1 wfAdCell input_pkg) (fvOf bnd e))
                 (congR pi (funValid bnd) ad_val'))
    where
      ad_val' : Deriv (eqF (ap1 wfAdCell input_pkg) (ap2 pi (ap1 wfFunRec l) (ap1 wfFunRec r)))
      ad_val' = ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
                  (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                             (congR pi (ap1 wfFunRec l) recR))
  ap2cCell_of : (bnd : Term) -> Deriv (eqF (ap1 Snd lab) bnd) ->
    Deriv (eqF (ap1 ap2cCell input_pkg)
               (ap2 pi (isF2 bnd) (ap2 pi (funValid bnd) (ap2 pi (ap1 wfFunRec l) (ap1 wfFunRec r)))))
  ap2cCell_of bnd e =
    ruleTrans (ax_C pi arF2cell (C pi fvB wfAdCell) input_pkg)
      (ruleTrans (congL pi (ap1 (C pi fvB wfAdCell) input_pkg) (arF2_of bnd e))
                 (congR pi (isF2 bnd) (ap2cInner_of bnd e)))
  ad_val : Deriv (eqF (ap1 wfAdCell input_pkg) (ap2 pi (ap1 wfFunRec l) (ap1 wfFunRec r)))
  ad_val = ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
             (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                        (congR pi (ap1 wfFunRec l) recR))
  -- fv3 cell value, given  Snd lab = bun3 g h1 h2 .
  fv3_of : (g h1 h2 : Term) ->
    Deriv (eqF (ap1 Snd lab) (ap2 Pair g (ap2 Pair h1 h2))) ->
    Deriv (eqF (ap1 fv3 input_pkg)
               (ap2 pi (funValid g) (ap2 pi (funValid h1) (funValid h2))))
  fv3_of g h1 h2 e =
    let bunSnd_eq : Deriv (eqF (ap1 bunSndIdx input_pkg) (ap2 Pair h1 h2))
        bunSnd_eq = ruleTrans (compose1U_eq Snd derBunIdx input_pkg)
                      (ruleTrans (cong1 Snd derBun_eq)
                        (ruleTrans (cong1 Snd e) (axSnd g (ap2 Pair h1 h2))))
        bunG_eq : Deriv (eqF (ap1 bunGidx input_pkg) g)
        bunG_eq = ruleTrans (compose1U_eq Fst derBunIdx input_pkg)
                    (ruleTrans (cong1 Fst derBun_eq)
                      (ruleTrans (cong1 Fst e) (axFst g (ap2 Pair h1 h2))))
        bunH1_eq : Deriv (eqF (ap1 bunH1idx input_pkg) h1)
        bunH1_eq = ruleTrans (compose1U_eq Fst bunSndIdx input_pkg)
                     (ruleTrans (cong1 Fst bunSnd_eq) (axFst h1 h2))
        bunH2_eq : Deriv (eqF (ap1 bunH2idx input_pkg) h2)
        bunH2_eq = ruleTrans (compose1U_eq Snd bunSndIdx input_pkg)
                     (ruleTrans (cong1 Snd bunSnd_eq) (axSnd h1 h2))
        fvG : Deriv (eqF (ap1 (compose1U funValidF bunGidx) input_pkg) (funValid g))
        fvG = ruleTrans (compose1U_eq funValidF bunGidx input_pkg)
                (ruleTrans (cong1 funValidF bunG_eq) (funValidF_eq g))
        fvH1 : Deriv (eqF (ap1 (compose1U funValidF bunH1idx) input_pkg) (funValid h1))
        fvH1 = ruleTrans (compose1U_eq funValidF bunH1idx input_pkg)
                 (ruleTrans (cong1 funValidF bunH1_eq) (funValidF_eq h1))
        fvH2 : Deriv (eqF (ap1 (compose1U funValidF bunH2idx) input_pkg) (funValid h2))
        fvH2 = ruleTrans (compose1U_eq funValidF bunH2idx input_pkg)
                 (ruleTrans (cong1 funValidF bunH2_eq) (funValidF_eq h2))
        innerCell : Fun1
        innerCell = C pi (compose1U funValidF bunH1idx) (compose1U funValidF bunH2idx)
        inner_val : Deriv (eqF (ap1 innerCell input_pkg)
                               (ap2 pi (funValid h1) (funValid h2)))
        inner_val =
          ruleTrans (ax_C pi (compose1U funValidF bunH1idx) (compose1U funValidF bunH2idx) input_pkg)
            (ruleTrans (congL pi (ap1 (compose1U funValidF bunH2idx) input_pkg) fvH1)
                       (congR pi (funValid h1) fvH2))
    in ruleTrans (ax_C pi (compose1U funValidF bunGidx) innerCell input_pkg)
         (ruleTrans (congL pi (ap1 innerCell input_pkg) fvG)
                    (congR pi (funValid g) inner_val))
  -- redex unary / binary cell values.
  rcUnary_of : (g h1 h2 : Term) ->
    Deriv (eqF (ap1 Snd lab) (ap2 Pair g (ap2 Pair h1 h2))) ->
    Deriv (eqF (ap1 rcUnaryCell input_pkg)
               (ap2 pi (ap2 pi (funValid g) (ap2 pi (funValid h1) (funValid h2)))
                       (ap1 wfFunRec l)))
  rcUnary_of g h1 h2 e =
    ruleTrans (ax_C pi fv3 unaryCell input_pkg)
      (ruleTrans (congL pi (ap1 unaryCell input_pkg) (fv3_of g h1 h2 e))
                 (congR pi (ap2 pi (funValid g) (ap2 pi (funValid h1) (funValid h2))) recL))
  rcBin_of : (g h1 h2 : Term) ->
    Deriv (eqF (ap1 Snd lab) (ap2 Pair g (ap2 Pair h1 h2))) ->
    Deriv (eqF (ap1 rcBinCell input_pkg)
               (ap2 pi (ap1 wfFun (cRec g h1 h2))
                       (ap2 pi (ap1 wfFunRec l) (ap1 wfFunRec r))))
  rcBin_of g h1 h2 e =
    let recRForm_eq : Deriv (eqF (ap1 recRForm input_pkg) (cRec g h1 h2))
        recRForm_eq = ruleTrans (ax_C Pair (constN 8) derBunIdx input_pkg)
                        (ruleTrans (congL Pair (ap1 derBunIdx input_pkg) (constN_eq 8 input_pkg))
                                   (congR Pair (natCode 8) (ruleTrans derBun_eq e)))
        recRwf_eq : Deriv (eqF (ap1 recRwf input_pkg) (ap1 wfFun (cRec g h1 h2)))
        recRwf_eq = ruleTrans (compose1U_eq wfFun recRForm input_pkg) (cong1 wfFun recRForm_eq)
    in ruleTrans (ax_C pi recRwf wfAdCell input_pkg)
         (ruleTrans (congL pi (ap1 wfAdCell input_pkg) recRwf_eq)
                    (congR pi (ap1 wfFun (cRec g h1 h2)) ad_val))
  -- FIX(C): derC validates wfFun (cComp g h1 h2) = Pair 6 bundle (unary child).
  rcCompC_of : (g h1 h2 : Term) ->
    Deriv (eqF (ap1 Snd lab) (ap2 Pair g (ap2 Pair h1 h2))) ->
    Deriv (eqF (ap1 rcCompC input_pkg) (ap2 pi (ap1 wfFun (cComp g h1 h2)) (ap1 wfFunRec l)))
  rcCompC_of g h1 h2 e =
    let recCForm_eq : Deriv (eqF (ap1 recCForm input_pkg) (cComp g h1 h2))
        recCForm_eq = ruleTrans (ax_C Pair (constN 6) derBunIdx input_pkg)
                        (ruleTrans (congL Pair (ap1 derBunIdx input_pkg) (constN_eq 6 input_pkg))
                                   (congR Pair (natCode 6) (ruleTrans derBun_eq e)))
        recCwf_eq : Deriv (eqF (ap1 recCwf input_pkg) (ap1 wfFun (cComp g h1 h2)))
        recCwf_eq = ruleTrans (compose1U_eq wfFun recCForm input_pkg) (cong1 wfFun recCForm_eq)
    in ruleTrans (ax_C pi recCwf unaryCell input_pkg)
         (ruleTrans (congL pi (ap1 unaryCell input_pkg) recCwf_eq)
                    (congR pi (ap1 wfFun (cComp g h1 h2)) recL))
  -- FIX(C): derRb validates wfFun (cRec g h1 h2) = Pair 8 bundle (unary child).
  rcCompRb_of : (g h1 h2 : Term) ->
    Deriv (eqF (ap1 Snd lab) (ap2 Pair g (ap2 Pair h1 h2))) ->
    Deriv (eqF (ap1 rcCompRb input_pkg) (ap2 pi (ap1 wfFun (cRec g h1 h2)) (ap1 wfFunRec l)))
  rcCompRb_of g h1 h2 e =
    let recRForm_eq : Deriv (eqF (ap1 recRForm input_pkg) (cRec g h1 h2))
        recRForm_eq = ruleTrans (ax_C Pair (constN 8) derBunIdx input_pkg)
                        (ruleTrans (congL Pair (ap1 derBunIdx input_pkg) (constN_eq 8 input_pkg))
                                   (congR Pair (natCode 8) (ruleTrans derBun_eq e)))
        recRwf_eq : Deriv (eqF (ap1 recRwf input_pkg) (ap1 wfFun (cRec g h1 h2)))
        recRwf_eq = ruleTrans (compose1U_eq wfFun recRForm input_pkg) (cong1 wfFun recRForm_eq)
    in ruleTrans (ax_C pi recRwf unaryCell input_pkg)
         (ruleTrans (congL pi (ap1 unaryCell input_pkg) recRwf_eq)
                    (congR pi (ap1 wfFun (cRec g h1 h2)) recL))

------------------------------------------------------------------------
-- SECTION 4.  Unary congruence / redex equations.

wfFunRec_ap1c : (f d : Term) ->
  Deriv (eqF (ap1 wfFunRec (ap1c f d)) (ap2 pi (isF1 f) (ap2 pi (funValid f) (ap1 wfFunRec d))))
wfFunRec_ap1c f d =
  let open Node (ap2 Pair dgAp1c f) d filler
      tg = tag_eq (natCode 1) (axFst dgAp1c f)
      fires = fork_true_to_fst ap1cCell ff_l2 (testTag 1) input_pkg (idxTest_fire derTagIdx 1 input_pkg tg)
  in ruleTrans to_cellNode (ruleTrans fires (ap1cCell_of f (axSnd dgAp1c f)))

wfFunRec_rO : (d : Term) -> Deriv (eqF (ap1 wfFunRec (derO d)) (ap1 wfFunRec d))
wfFunRec_rO d =
  let open Node (ap2 Pair dgRo O) d filler
      tg = tag_eq (natCode 3) (axFst dgRo O)
      fires =
        ruleTrans (fork_false_to_snd ap1cCell ff_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 3 1 input_pkg (wn 3 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell ff_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 3 2 input_pkg (wn 3 2 (\ ())) tg))
                     (fork_true_to_fst unaryCell ff_l4 (testTag 3) input_pkg (idxTest_fire derTagIdx 3 input_pkg tg)))
  in ruleTrans to_cellNode (ruleTrans fires recL)

wfFunRec_rU : (d : Term) -> Deriv (eqF (ap1 wfFunRec (derU d)) (ap1 wfFunRec d))
wfFunRec_rU d =
  let open Node (ap2 Pair dgRu O) d filler
      tg = tag_eq (natCode 4) (axFst dgRu O)
      fires =
        ruleTrans (fork_false_to_snd ap1cCell ff_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 4 1 input_pkg (wn 4 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell ff_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 4 2 input_pkg (wn 4 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell ff_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 4 3 input_pkg (wn 4 3 (\ ())) tg))
                       (fork_true_to_fst unaryCell ff_l5 (testTag 4) input_pkg (idxTest_fire derTagIdx 4 input_pkg tg))))
  in ruleTrans to_cellNode (ruleTrans fires recL)

wfFunRec_rC : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 wfFunRec (derC g h1 h2 d))
             (ap2 pi (ap1 wfFun (cComp g h1 h2)) (ap1 wfFunRec d)))
wfFunRec_rC g h1 h2 d =
  let open Node (ap2 Pair dgRC (bun3 g h1 h2)) d filler
      tg = tag_eq (natCode 6) (axFst dgRC (bun3 g h1 h2))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell ff_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 6 1 input_pkg (wn 6 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell ff_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 6 2 input_pkg (wn 6 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell ff_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 6 3 input_pkg (wn 6 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell ff_l5 (testTag 4) input_pkg (idxTest_skip derTagIdx 6 4 input_pkg (wn 6 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell ff_l6 (testTag 5) input_pkg (idxTest_skip derTagIdx 6 5 input_pkg (wn 6 5 (\ ())) tg))
                           (fork_true_to_fst rcCompC ff_l7 (testTag 6) input_pkg (idxTest_fire derTagIdx 6 input_pkg tg))))))
  in ruleTrans to_cellNode (ruleTrans fires (rcCompC_of g h1 h2 (axSnd dgRC (bun3 g h1 h2))))

wfFunRec_rRb : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 wfFunRec (derRb g h1 h2 d))
             (ap2 pi (ap1 wfFun (cRec g h1 h2)) (ap1 wfFunRec d)))
wfFunRec_rRb g h1 h2 d =
  let open Node (ap2 Pair dgRb (bun3 g h1 h2)) d filler
      tg = tag_eq (natCode 7) (axFst dgRb (bun3 g h1 h2))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell ff_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 7 1 input_pkg (wn 7 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell ff_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 7 2 input_pkg (wn 7 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell ff_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 7 3 input_pkg (wn 7 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell ff_l5 (testTag 4) input_pkg (idxTest_skip derTagIdx 7 4 input_pkg (wn 7 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell ff_l6 (testTag 5) input_pkg (idxTest_skip derTagIdx 7 5 input_pkg (wn 7 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd rcCompC ff_l7 (testTag 6) input_pkg (idxTest_skip derTagIdx 7 6 input_pkg (wn 7 6 (\ ())) tg))
                             (fork_true_to_fst rcCompRb ff_l8 (testTag 7) input_pkg (idxTest_fire derTagIdx 7 input_pkg tg)))))))
  in ruleTrans to_cellNode (ruleTrans fires (rcCompRb_of g h1 h2 (axSnd dgRb (bun3 g h1 h2))))

------------------------------------------------------------------------
-- SECTION 5.  Binary congruence / redex equations.

wfFunRec_ap2c : (g d1 d2 : Term) ->
  Deriv (eqF (ap1 wfFunRec (ap2c g d1 d2))
             (ap2 pi (isF2 g) (ap2 pi (funValid g) (ap2 pi (ap1 wfFunRec d1) (ap1 wfFunRec d2)))))
wfFunRec_ap2c g d1 d2 =
  let open Node (ap2 Pair dgAp2c g) d1 d2
      tg = tag_eq (natCode 2) (axFst dgAp2c g)
      fires =
        ruleTrans (fork_false_to_snd ap1cCell ff_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 2 1 input_pkg w21 tg))
                  (fork_true_to_fst ap2cCell ff_l3 (testTag 2) input_pkg (idxTest_fire derTagIdx 2 input_pkg tg))
  in ruleTrans to_cellNode (ruleTrans fires (ap2cCell_of g (axSnd dgAp2c g)))

wfFunRec_rV : (d1 d2 : Term) ->
  Deriv (eqF (ap1 wfFunRec (derV d1 d2)) (ap2 pi (ap1 wfFunRec d1) (ap1 wfFunRec d2)))
wfFunRec_rV d1 d2 =
  let open Node (ap2 Pair dgRv O) d1 d2
      tg = tag_eq (natCode 5) (axFst dgRv O)
      fires =
        ruleTrans (fork_false_to_snd ap1cCell ff_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 5 1 input_pkg (wn 5 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell ff_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 5 2 input_pkg (wn 5 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell ff_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 5 3 input_pkg (wn 5 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell ff_l5 (testTag 4) input_pkg (idxTest_skip derTagIdx 5 4 input_pkg (wn 5 4 (\ ())) tg))
                         (fork_true_to_fst wfAdCell ff_l6 (testTag 5) input_pkg (idxTest_fire derTagIdx 5 input_pkg tg)))))
  in ruleTrans to_cellNode (ruleTrans fires ad_val)

wfFunRec_rRs : (g h1 h2 d1 d2 : Term) ->
  Deriv (eqF (ap1 wfFunRec (derRs g h1 h2 d1 d2))
             (ap2 pi (ap1 wfFun (cRec g h1 h2))
                     (ap2 pi (ap1 wfFunRec d1) (ap1 wfFunRec d2))))
wfFunRec_rRs g h1 h2 d1 d2 =
  let open Node (ap2 Pair dgRs (bun3 g h1 h2)) d1 d2
      tg = tag_eq (natCode 8) (axFst dgRs (bun3 g h1 h2))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell ff_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 8 1 input_pkg (wn 8 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell ff_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 8 2 input_pkg (wn 8 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell ff_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 8 3 input_pkg (wn 8 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell ff_l5 (testTag 4) input_pkg (idxTest_skip derTagIdx 8 4 input_pkg (wn 8 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell ff_l6 (testTag 5) input_pkg (idxTest_skip derTagIdx 8 5 input_pkg (wn 8 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd rcCompC ff_l7 (testTag 6) input_pkg (idxTest_skip derTagIdx 8 6 input_pkg (wn 8 6 (\ ())) tg))
                    (ruleTrans (fork_false_to_snd rcCompRb ff_l8 (testTag 7) input_pkg (idxTest_skip derTagIdx 8 7 input_pkg (wn 8 7 (\ ())) tg))
                               (fork_true_to_fst rcBinCell Z (testTag 8) input_pkg (idxTest_fire derTagIdx 8 input_pkg tg))))))))
  in ruleTrans to_cellNode (ruleTrans fires (rcBin_of g h1 h2 (axSnd dgRs (bun3 g h1 h2))))
