{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrDev -- the OBJECT COMPLETE DEVELOPMENT  devF : Fun1  over coded TERMS of
-- the FULL closed-term p.r. calculus (T4.PrCodeObj), generalising T4.DerDev
-- from the toy {ze#,su#,ad#}.  Takahashi's complete development internalised,
-- contracting ALL current redexes of the 6 rules simultaneously:
--
--   devF (tmO)                = tmO                                     (base)
--   devF (tmAp1 s t)          = tmAp1 s (devF t)                        (s-cong)
--   devF (tmAp1 o t)          = tmO                                     (o)
--   devF (tmAp1 u t)          = devF t                                  (u)
--   devF (tmAp1 (C g h1 h2) t)= tmAp2 g (tmAp1 h1 (devF t))(tmAp1 h2 (devF t))   (C)
--   devF (tmAp2 v a b)        = devF b                                  (v)
--   devF (tmAp2 (R g h1 h2) a tmO)        = tmAp1 g (devF a)            (Rb)
--   devF (tmAp2 (R g h1 h2) a (tmAp1 s n))=
--        tmAp2 h1 (tmAp2 h2 (devF a)(devF n))(tmAp2 (R g h1 h2)(devF a)(devF n)) (Rs)
--
-- Fun-codes (s,o,u,C,v,R sub-codes) are INERT (contain no ap nodes => normal);
-- devF copies them verbatim, recursing only into the TERM arguments.  devF is
-- a  binRec Z ap1Cell ap2Cell : ap1Cell (tag 1 = tmAp1) sub-dispatches on the
-- head fun's tag (o/u/s/C), ap2Cell (tag 2 = tmAp2) on the head fun (v/R) and,
-- for R, on the second argument (tmO / s-headed / else).
--
-- The grandchild  devF n  in the Rs case is recovered from  devF b  (=
-- tmAp1 s (devF n)) by the s-congruence, exactly as the toy's ar(devF a)=devF x.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrDev where

open import T4.Base

open import T4.BinTree using ( binRec )
open import T4.ParsObj using ( foldOf ; stepOf ; test1 ; module NP )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt ; fold_at_O )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.ParEnds  using ( pi_O_O )
open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )

open import T4.PrCodeObj
  using ( tmO ; tmAp1 ; tmAp2 ; cSuc ; cZero ; cId ; cComp ; cProj ; cRec
        ; tgO ; tgAp1 ; tgAp2 ; tgSuc ; tgZero ; tgId ; tgComp ; tgProj ; tgRec )

open import BRA3.Church       using ( pi )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  Index Fun1s (read components out of a fold node package).
-- get_rc input = payload.  tmAp1 payload = Pair f t ; tmAp2 payload = Pair g (Pair a b).

apFun : Fun1                         -- f (tmAp1) or g (tmAp2)  = Fst payload
apFun = compose1U Fst get_rc

apArg1 : Fun1                        -- t (tmAp1 arg)  = Snd payload
apArg1 = compose1U Snd get_rc

headF : Fun1                         -- head tag of the fun  = Fst (Fst payload)
headF = compose1U Fst apFun

fBun : Fun1                          -- Snd of the fun  (= Pair g (Pair h1 h2) for C/R)
fBun = compose1U Snd apFun

bG0 : Fun1                           -- C/R first component  g0 = Fst fBun
bG0 = compose1U Fst fBun
bH1 : Fun1                           -- second component  h1 = Fst (Snd fBun)
bH1 = compose1U Fst (compose1U Snd fBun)
bH2 : Fun1                           -- third component  h2 = Snd (Snd fBun)
bH2 = compose1U Snd (compose1U Snd fBun)

-- tmAp2 inner bundle  Pair a b  = Snd payload.
apA : Fun1                           -- a = Fst (Snd payload)
apA = compose1U Fst (compose1U Snd get_rc)
apB : Fun1                           -- b = Snd (Snd payload)
apB = compose1U Snd (compose1U Snd get_rc)
headB : Fun1                         -- head tag of b  = Fst b
headB = compose1U Fst apB
bSnd : Fun1                          -- Snd b (= Pair s-code n  for b = tmAp1 s n)
bSnd = compose1U Snd apB
headBFun : Fun1                      -- head tag of b's fun  = Fst (Fst (Snd b))
headBFun = compose1U Fst (compose1U Fst bSnd)

-- recursive (developed) values.
devT : Fun1                          -- devF t
devT = lookupAt apArg1
devA : Fun1                          -- devF a
devA = lookupAt apA
devB : Fun1                          -- devF b
devB = lookupAt apB
devN : Fun1                          -- devF n  (from devB = tmAp1 s (devF n))
devN = compose1U Snd (compose1U Snd devB)

------------------------------------------------------------------------
-- SECTION 2.  Constructor / builder Fun1s and their value lemmas.

tmOF : Fun1                          -- constant tmO
tmOF = C pi Z Z

cSucF : Fun1                         -- constant cSuc
cSucF = C pi (constN 3) Z

mkAp1 : Fun1 -> Fun1 -> Fun1         -- tmAp1 (F .) (A .)
mkAp1 F A = C pi (constN 1) (C pi F A)

mkAp2 : Fun1 -> Fun1 -> Fun1 -> Fun1 -- tmAp2 (G .) (A .) (B .)
mkAp2 G A B = C pi (constN 2) (C pi G (C pi A B))

mkRec : Fun1 -> Fun1 -> Fun1 -> Fun1 -- cRec (G0 .) (H1 .) (H2 .)
mkRec G0 H1 H2 = C pi (constN 8) (C pi G0 (C pi H1 H2))

tmOF_val : (input : Term) -> Deriv (eqF (ap1 tmOF input) tmO)
tmOF_val input =
  ruleTrans (ax_C pi Z Z input)
    (ruleTrans (congL pi (ap1 Z input) (axZ input)) (congR pi O (axZ input)))

cSucF_val : (input : Term) -> Deriv (eqF (ap1 cSucF input) cSuc)
cSucF_val input =
  ruleTrans (ax_C pi (constN 3) Z input)
    (ruleTrans (congL pi (ap1 Z input) (constN_eq 3 input)) (congR pi (natCode 3) (axZ input)))

mkAp1_val : (F A : Fun1) (input vf va : Term) ->
  Deriv (eqF (ap1 F input) vf) -> Deriv (eqF (ap1 A input) va) ->
  Deriv (eqF (ap1 (mkAp1 F A) input) (tmAp1 vf va))
mkAp1_val F A input vf va eF eA =
  let inner : Deriv (eqF (ap1 (C pi F A) input) (ap2 Pair vf va))
      inner = ruleTrans (ax_C pi F A input)
                (ruleTrans (congL pi (ap1 A input) eF) (congR pi vf eA))
  in ruleTrans (ax_C pi (constN 1) (C pi F A) input)
       (ruleTrans (congL pi (ap1 (C pi F A) input) (constN_eq 1 input))
                  (congR pi (natCode 1) inner))

mkAp2_val : (G A B : Fun1) (input vg va vb : Term) ->
  Deriv (eqF (ap1 G input) vg) -> Deriv (eqF (ap1 A input) va) -> Deriv (eqF (ap1 B input) vb) ->
  Deriv (eqF (ap1 (mkAp2 G A B) input) (tmAp2 vg va vb))
mkAp2_val G A B input vg va vb eG eA eB =
  let inAB : Deriv (eqF (ap1 (C pi A B) input) (ap2 Pair va vb))
      inAB = ruleTrans (ax_C pi A B input)
               (ruleTrans (congL pi (ap1 B input) eA) (congR pi va eB))
      inner : Deriv (eqF (ap1 (C pi G (C pi A B)) input) (ap2 Pair vg (ap2 Pair va vb)))
      inner = ruleTrans (ax_C pi G (C pi A B) input)
                (ruleTrans (congL pi (ap1 (C pi A B) input) eG) (congR pi vg inAB))
  in ruleTrans (ax_C pi (constN 2) (C pi G (C pi A B)) input)
       (ruleTrans (congL pi (ap1 (C pi G (C pi A B)) input) (constN_eq 2 input))
                  (congR pi (natCode 2) inner))

mkRec_val : (G0 H1 H2 : Fun1) (input vg vh1 vh2 : Term) ->
  Deriv (eqF (ap1 G0 input) vg) -> Deriv (eqF (ap1 H1 input) vh1) -> Deriv (eqF (ap1 H2 input) vh2) ->
  Deriv (eqF (ap1 (mkRec G0 H1 H2) input) (cRec vg vh1 vh2))
mkRec_val G0 H1 H2 input vg vh1 vh2 eG eH1 eH2 =
  let inH : Deriv (eqF (ap1 (C pi H1 H2) input) (ap2 Pair vh1 vh2))
      inH = ruleTrans (ax_C pi H1 H2 input)
              (ruleTrans (congL pi (ap1 H2 input) eH1) (congR pi vh1 eH2))
      inner : Deriv (eqF (ap1 (C pi G0 (C pi H1 H2)) input) (ap2 Pair vg (ap2 Pair vh1 vh2)))
      inner = ruleTrans (ax_C pi G0 (C pi H1 H2) input)
                (ruleTrans (congL pi (ap1 (C pi H1 H2) input) eG) (congR pi vg inH))
  in ruleTrans (ax_C pi (constN 8) (C pi G0 (C pi H1 H2)) input)
       (ruleTrans (congL pi (ap1 (C pi G0 (C pi H1 H2)) input) (constN_eq 8 input))
                  (congR pi (natCode 8) inner))

------------------------------------------------------------------------
-- SECTION 3.  The cells and  devF .

br_o : Fun1
br_o = tmOF
br_u : Fun1
br_u = devT
br_s : Fun1
br_s = mkAp1 cSucF devT
br_C : Fun1
br_C = mkAp2 bG0 (mkAp1 bH1 devT) (mkAp1 bH2 devT)
br_ap1cong : Fun1
br_ap1cong = mkAp1 apFun devT

testF : Nat -> Fun1
testF k = C natEqF headF (constN k)

ap1_lvl3 : Fun1                       -- head=C(6) -> br_C ; else br_ap1cong
ap1_lvl3 = C condFork (C pi br_C br_ap1cong) (testF 6)
ap1_lvl2 : Fun1                       -- head=s(3) -> br_s ; else lvl3
ap1_lvl2 = C condFork (C pi br_s ap1_lvl3) (testF 3)
ap1_lvl1 : Fun1                       -- head=u(5) -> br_u ; else lvl2
ap1_lvl1 = C condFork (C pi br_u ap1_lvl2) (testF 5)
ap1Cell : Fun1                        -- head=o(4) -> br_o ; else lvl1
ap1Cell = C condFork (C pi br_o ap1_lvl1) (testF 4)

br_v : Fun1
br_v = devB
br_Rb : Fun1
br_Rb = mkAp1 bG0 devA
br_Rs : Fun1
br_Rs = mkAp2 bH1 (mkAp2 bH2 devA devN) (mkAp2 (mkRec bG0 bH1 bH2) devA devN)
br_Rcong : Fun1
br_Rcong = mkAp2 (mkRec bG0 bH1 bH2) devA devB

testB : Nat -> Fun1
testB k = C natEqF headB (constN k)
testBF : Nat -> Fun1
testBF k = C natEqF headBFun (constN k)

R_lvl2 : Fun1                         -- b head-fun = s(3) -> br_Rs ; else br_Rcong
R_lvl2 = C condFork (C pi br_Rs br_Rcong) (testBF 3)
R_disp : Fun1                         -- b head = tmO(0) -> br_Rb ; else R_lvl2
R_disp = C condFork (C pi br_Rb R_lvl2) (testB 0)

br_ap2cong : Fun1
br_ap2cong = mkAp2 apFun devA devB

testG : Nat -> Fun1
testG k = C natEqF headF (constN k)   -- head of the ap2 fun g (= headF, same Fst-of-payload)

ap2_lvl1 : Fun1                       -- head=R(8) -> R_disp ; else ap2cong
ap2_lvl1 = C condFork (C pi R_disp br_ap2cong) (testG 8)
ap2Cell : Fun1                        -- head=v(7) -> br_v ; else lvl1
ap2Cell = C condFork (C pi br_v ap2_lvl1) (testG 7)

devF : Fun1
devF = binRec Z ap1Cell ap2Cell

------------------------------------------------------------------------
-- SECTION 4.  Generic test fire / skip (parametric in the index Fun1).

idxTest_fire : (idx : Fun1) (k : Nat) (input : Term) ->
  Deriv (eqF (ap1 idx input) (natCode k)) ->
  Deriv (eqF (ap1 (C natEqF idx (constN k)) input) (ap1 s O))
idxTest_fire idx k input eq =
  ruleTrans (ax_C natEqF idx (constN k) input)
    (ruleTrans (congL natEqF (ap1 (constN k) input) eq)
      (ruleTrans (congR natEqF (natCode k) (constN_eq k input)) (natEq_eq k)))

idxTest_skip : (idx : Fun1) (m k : Nat) (input : Term) -> NatNeqWitness m k ->
  Deriv (eqF (ap1 idx input) (natCode m)) ->
  Deriv (eqF (ap1 (C natEqF idx (constN k)) input) O)
idxTest_skip idx m k input w eq =
  ruleTrans (ax_C natEqF idx (constN k) input)
    (ruleTrans (congL natEqF (ap1 (constN k) input) eq)
      (ruleTrans (congR natEqF (natCode m) (constN_eq k input)) (natEqF_at_neq m k w)))

-- neq witnesses used below.
w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())
w54 : NatNeqWitness 5 4
w54 = decideNatNeq 5 4 (\ ())
w34 : NatNeqWitness 3 4
w34 = decideNatNeq 3 4 (\ ())
w35 : NatNeqWitness 3 5
w35 = decideNatNeq 3 5 (\ ())
w64 : NatNeqWitness 6 4
w64 = decideNatNeq 6 4 (\ ())
w65 : NatNeqWitness 6 5
w65 = decideNatNeq 6 5 (\ ())
w63 : NatNeqWitness 6 3
w63 = decideNatNeq 6 3 (\ ())
w87 : NatNeqWitness 8 7
w87 = decideNatNeq 8 7 (\ ())
w70 : NatNeqWitness 7 0   -- v: dummy (unused)
w70 = decideNatNeq 7 0 (\ ())

------------------------------------------------------------------------
-- SECTION 5.  Base:  devF (tmO) = tmO   (tmO = pi O O = O, the fold base).

devF_O : Deriv (eqF (ap1 devF O) O)
devF_O = ruleTrans (fold_at_O Z (Post (stepOf ap1Cell ap2Cell) pi)) (axZ O)

devF_tmO : Deriv (eqF (ap1 devF tmO) tmO)
devF_tmO = ruleTrans (cong1 devF pi_O_O) (ruleTrans devF_O (ruleSym pi_O_O))

------------------------------------------------------------------------
-- SECTION 6.  ap1 equations.  Node  tmAp1 f t = pi (s O) (Pair f t)
-- (A = O , payload = Pair f t).  The leaf cell ap1Cell fires (tag 1).

-- shared plumbing for an ap1 node with fun f and arg t.
module Ap1 (f t : Term) where
  open NP Z ap1Cell ap2Cell O (ap2 Pair f t) public
  t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
  t1_fire = ruleTrans test1_val (natEq_eq 1)
  -- apFun input = f.
  apFun_eq : Deriv (eqF (ap1 apFun input_pkg) f)
  apFun_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
               (ruleTrans (cong1 Fst np_rc) (axFst f t))
  -- apArg1 input = t , and devT input = devF t.
  apArg1_eq : Deriv (eqF (ap1 apArg1 input_pkg) t)
  apArg1_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                (ruleTrans (cong1 Snd np_rc) (axSnd f t))
  recT : Deriv (eqF (ap1 devT input_pkg) (ap1 devF t))
  recT = np_lookup_gen apArg1 t apArg1_eq
           (leq_trans t (ap2 Pair f t) P_outer (leq_pi_right f t) leq_b_P)
  -- cell fired = ap1Cell input_pkg.
  to_ap1Cell : Deriv (eqF (ap1 devF (tmAp1 f t)) (ap1 ap1Cell input_pkg))
  to_ap1Cell = collapse_fst t1_fire

-- head of f = Fst f.  (used to fire the right cascade level.)
headF_at : (f t : Term) -> let open Ap1 f t in
           (hf : Term) -> Deriv (eqF (ap1 Fst f) hf) ->
           Deriv (eqF (ap1 headF input_pkg) hf)
headF_at f t hf eq =
  let open Ap1 f t
  in ruleTrans (compose1U_eq Fst apFun input_pkg)
       (ruleTrans (cong1 Fst apFun_eq) eq)

-- s-congruence:  devF (tmAp1 s t) = tmAp1 s (devF t)   (f = cSuc).
devF_ap1_s : (t : Term) -> Deriv (eqF (ap1 devF (tmAp1 cSuc t)) (tmAp1 cSuc (ap1 devF t)))
devF_ap1_s t =
  let open Ap1 cSuc t
      hF : Deriv (eqF (ap1 headF input_pkg) (natCode 3))
      hF = headF_at cSuc t (natCode 3) (axFst tgSuc O)
      -- cascade: skip o(4), skip u(5), fire s(3).
      fires : Deriv (eqF (ap1 ap1Cell input_pkg) (ap1 br_s input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_o ap1_lvl1 (testF 4) input_pkg
                     (idxTest_skip headF 3 4 input_pkg w34 hF))
          (ruleTrans (fork_false_to_snd br_u ap1_lvl2 (testF 5) input_pkg
                       (idxTest_skip headF 3 5 input_pkg w35 hF))
                     (fork_true_to_fst br_s ap1_lvl3 (testF 3) input_pkg
                       (idxTest_fire headF 3 input_pkg hF)))
      val : Deriv (eqF (ap1 br_s input_pkg) (tmAp1 cSuc (ap1 devF t)))
      val = mkAp1_val cSucF devT input_pkg cSuc (ap1 devF t) (cSucF_val input_pkg) recT
  in ruleTrans to_ap1Cell (ruleTrans fires val)

-- o-redex:  devF (tmAp1 o t) = tmO   (f = cZero).
devF_o : (t : Term) -> Deriv (eqF (ap1 devF (tmAp1 cZero t)) tmO)
devF_o t =
  let open Ap1 cZero t
      hF : Deriv (eqF (ap1 headF input_pkg) (natCode 4))
      hF = headF_at cZero t (natCode 4) (axFst tgZero O)
      fires : Deriv (eqF (ap1 ap1Cell input_pkg) (ap1 br_o input_pkg))
      fires = fork_true_to_fst br_o ap1_lvl1 (testF 4) input_pkg
                (idxTest_fire headF 4 input_pkg hF)
  in ruleTrans to_ap1Cell (ruleTrans fires (tmOF_val input_pkg))

-- u-redex:  devF (tmAp1 u t) = devF t   (f = cId).
devF_u : (t : Term) -> Deriv (eqF (ap1 devF (tmAp1 cId t)) (ap1 devF t))
devF_u t =
  let open Ap1 cId t
      hF : Deriv (eqF (ap1 headF input_pkg) (natCode 5))
      hF = headF_at cId t (natCode 5) (axFst tgId O)
      fires : Deriv (eqF (ap1 ap1Cell input_pkg) (ap1 br_u input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_o ap1_lvl1 (testF 4) input_pkg
                     (idxTest_skip headF 5 4 input_pkg w54 hF))
                  (fork_true_to_fst br_u ap1_lvl2 (testF 5) input_pkg
                     (idxTest_fire headF 5 input_pkg hF))
  in ruleTrans to_ap1Cell (ruleTrans fires recT)

-- C-redex:  devF (tmAp1 (C g h1 h2) t) = tmAp2 g (tmAp1 h1 (devF t))(tmAp1 h2 (devF t)).
devF_C : (g h1 h2 t : Term) ->
  Deriv (eqF (ap1 devF (tmAp1 (cComp g h1 h2) t))
             (tmAp2 g (tmAp1 h1 (ap1 devF t)) (tmAp1 h2 (ap1 devF t))))
devF_C g h1 h2 t =
  let open Ap1 (cComp g h1 h2) t
      hF : Deriv (eqF (ap1 headF input_pkg) (natCode 6))
      hF = headF_at (cComp g h1 h2) t (natCode 6) (axFst tgComp (ap2 Pair g (ap2 Pair h1 h2)))
      -- fBun input = Snd f = Pair g (Pair h1 h2) ; project g, h1, h2.
      fBun_eq : Deriv (eqF (ap1 fBun input_pkg) (ap2 Pair g (ap2 Pair h1 h2)))
      fBun_eq = ruleTrans (compose1U_eq Snd apFun input_pkg)
                  (ruleTrans (cong1 Snd apFun_eq) (axSnd tgComp (ap2 Pair g (ap2 Pair h1 h2))))
      bG0_eq : Deriv (eqF (ap1 bG0 input_pkg) g)
      bG0_eq = ruleTrans (compose1U_eq Fst fBun input_pkg)
                 (ruleTrans (cong1 Fst fBun_eq) (axFst g (ap2 Pair h1 h2)))
      fInner_eq : Deriv (eqF (ap1 (compose1U Snd fBun) input_pkg) (ap2 Pair h1 h2))
      fInner_eq = ruleTrans (compose1U_eq Snd fBun input_pkg)
                    (ruleTrans (cong1 Snd fBun_eq) (axSnd g (ap2 Pair h1 h2)))
      bH1_eq : Deriv (eqF (ap1 bH1 input_pkg) h1)
      bH1_eq = ruleTrans (compose1U_eq Fst (compose1U Snd fBun) input_pkg)
                 (ruleTrans (cong1 Fst fInner_eq) (axFst h1 h2))
      bH2_eq : Deriv (eqF (ap1 bH2 input_pkg) h2)
      bH2_eq = ruleTrans (compose1U_eq Snd (compose1U Snd fBun) input_pkg)
                 (ruleTrans (cong1 Snd fInner_eq) (axSnd h1 h2))
      fires : Deriv (eqF (ap1 ap1Cell input_pkg) (ap1 br_C input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_o ap1_lvl1 (testF 4) input_pkg
                     (idxTest_skip headF 6 4 input_pkg w64 hF))
          (ruleTrans (fork_false_to_snd br_u ap1_lvl2 (testF 5) input_pkg
                       (idxTest_skip headF 6 5 input_pkg w65 hF))
            (ruleTrans (fork_false_to_snd br_s ap1_lvl3 (testF 3) input_pkg
                         (idxTest_skip headF 6 3 input_pkg w63 hF))
                       (fork_true_to_fst br_C br_ap1cong (testF 6) input_pkg
                         (idxTest_fire headF 6 input_pkg hF))))
      armH1 : Deriv (eqF (ap1 (mkAp1 bH1 devT) input_pkg) (tmAp1 h1 (ap1 devF t)))
      armH1 = mkAp1_val bH1 devT input_pkg h1 (ap1 devF t) bH1_eq recT
      armH2 : Deriv (eqF (ap1 (mkAp1 bH2 devT) input_pkg) (tmAp1 h2 (ap1 devF t)))
      armH2 = mkAp1_val bH2 devT input_pkg h2 (ap1 devF t) bH2_eq recT
      val : Deriv (eqF (ap1 br_C input_pkg)
                       (tmAp2 g (tmAp1 h1 (ap1 devF t)) (tmAp1 h2 (ap1 devF t))))
      val = mkAp2_val bG0 (mkAp1 bH1 devT) (mkAp1 bH2 devT) input_pkg
              g (tmAp1 h1 (ap1 devF t)) (tmAp1 h2 (ap1 devF t)) bG0_eq armH1 armH2
  in ruleTrans to_ap1Cell (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 7.  ap2 equations.  Node  tmAp2 g a b = pi (s (s O)) (Pair g (Pair a b))
-- (A = natCode 1 , payload = Pair g (Pair a b)).  The node cell ap2Cell fires.

module Ap2 (g a b : Term) where
  open NP Z ap1Cell ap2Cell (natCode 1) (ap2 Pair g (ap2 Pair a b)) public
  t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
  t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
  apFun_eq : Deriv (eqF (ap1 apFun input_pkg) g)
  apFun_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
               (ruleTrans (cong1 Fst np_rc) (axFst g (ap2 Pair a b)))
  apBundle_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) input_pkg) (ap2 Pair a b))
  apBundle_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                  (ruleTrans (cong1 Snd np_rc) (axSnd g (ap2 Pair a b)))
  apA_eq : Deriv (eqF (ap1 apA input_pkg) a)
  apA_eq = ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) input_pkg)
             (ruleTrans (cong1 Fst apBundle_eq) (axFst a b))
  apB_eq : Deriv (eqF (ap1 apB input_pkg) b)
  apB_eq = ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) input_pkg)
             (ruleTrans (cong1 Snd apBundle_eq) (axSnd a b))
  recA : Deriv (eqF (ap1 devA input_pkg) (ap1 devF a))
  recA = np_lookup_gen apA a apA_eq
           (leq_trans a (ap2 Pair a b) P_outer (leq_pi_left a b)
             (leq_trans (ap2 Pair a b) (ap2 Pair g (ap2 Pair a b)) P_outer
               (leq_pi_right g (ap2 Pair a b)) leq_b_P))
  recB : Deriv (eqF (ap1 devB input_pkg) (ap1 devF b))
  recB = np_lookup_gen apB b apB_eq
           (leq_trans b (ap2 Pair a b) P_outer (leq_pi_right a b)
             (leq_trans (ap2 Pair a b) (ap2 Pair g (ap2 Pair a b)) P_outer
               (leq_pi_right g (ap2 Pair a b)) leq_b_P))
  headG_eq : (hg : Term) -> Deriv (eqF (ap1 Fst g) hg) ->
             Deriv (eqF (ap1 headF input_pkg) hg)
  headG_eq hg eq = ruleTrans (compose1U_eq Fst apFun input_pkg)
                     (ruleTrans (cong1 Fst apFun_eq) eq)
  to_ap2Cell : Deriv (eqF (ap1 devF (tmAp2 g a b)) (ap1 ap2Cell input_pkg))
  to_ap2Cell = collapse_snd t1_O

-- v-redex:  devF (tmAp2 v a b) = devF b   (g = cProj).
devF_v : (a b : Term) -> Deriv (eqF (ap1 devF (tmAp2 cProj a b)) (ap1 devF b))
devF_v a b =
  let open Ap2 cProj a b
      hG : Deriv (eqF (ap1 headF input_pkg) (natCode 7))
      hG = headG_eq (natCode 7) (axFst tgProj O)
      fires : Deriv (eqF (ap1 ap2Cell input_pkg) (ap1 br_v input_pkg))
      fires = fork_true_to_fst br_v ap2_lvl1 (testG 7) input_pkg
                (idxTest_fire headF 7 input_pkg hG)
  in ruleTrans to_ap2Cell (ruleTrans fires recB)

-- shared: under g = cRec g0 h1 h2, project g0/h1/h2 and fire to R_disp.
module Rec (g0 h1 h2 a b : Term) where
  open Ap2 (cRec g0 h1 h2) a b public
  hG : Deriv (eqF (ap1 headF input_pkg) (natCode 8))
  hG = headG_eq (natCode 8) (axFst tgRec (ap2 Pair g0 (ap2 Pair h1 h2)))
  gBun_eq : Deriv (eqF (ap1 fBun input_pkg) (ap2 Pair g0 (ap2 Pair h1 h2)))
  gBun_eq = ruleTrans (compose1U_eq Snd apFun input_pkg)
              (ruleTrans (cong1 Snd apFun_eq) (axSnd tgRec (ap2 Pair g0 (ap2 Pair h1 h2))))
  bG0_eq : Deriv (eqF (ap1 bG0 input_pkg) g0)
  bG0_eq = ruleTrans (compose1U_eq Fst fBun input_pkg)
             (ruleTrans (cong1 Fst gBun_eq) (axFst g0 (ap2 Pair h1 h2)))
  gInner_eq : Deriv (eqF (ap1 (compose1U Snd fBun) input_pkg) (ap2 Pair h1 h2))
  gInner_eq = ruleTrans (compose1U_eq Snd fBun input_pkg)
                (ruleTrans (cong1 Snd gBun_eq) (axSnd g0 (ap2 Pair h1 h2)))
  bH1_eq : Deriv (eqF (ap1 bH1 input_pkg) h1)
  bH1_eq = ruleTrans (compose1U_eq Fst (compose1U Snd fBun) input_pkg)
             (ruleTrans (cong1 Fst gInner_eq) (axFst h1 h2))
  bH2_eq : Deriv (eqF (ap1 bH2 input_pkg) h2)
  bH2_eq = ruleTrans (compose1U_eq Snd (compose1U Snd fBun) input_pkg)
             (ruleTrans (cong1 Snd gInner_eq) (axSnd h1 h2))
  to_R_disp : Deriv (eqF (ap1 ap2Cell input_pkg) (ap1 R_disp input_pkg))
  to_R_disp =
    ruleTrans (fork_false_to_snd br_v ap2_lvl1 (testG 7) input_pkg
                 (idxTest_skip headF 8 7 input_pkg w87 hG))
              (fork_true_to_fst R_disp br_ap2cong (testG 8) input_pkg
                 (idxTest_fire headF 8 input_pkg hG))

-- R-base redex:  devF (tmAp2 (R g0 h1 h2) a tmO) = tmAp1 g0 (devF a).
devF_Rb : (g0 h1 h2 a : Term) ->
  Deriv (eqF (ap1 devF (tmAp2 (cRec g0 h1 h2) a tmO)) (tmAp1 g0 (ap1 devF a)))
devF_Rb g0 h1 h2 a =
  let open Rec g0 h1 h2 a tmO
      -- headB input = Fst b = Fst tmO = natCode 0.
      hB : Deriv (eqF (ap1 headB input_pkg) (natCode 0))
      hB = ruleTrans (compose1U_eq Fst apB input_pkg)
             (ruleTrans (cong1 Fst apB_eq) (axFst tgO O))
      fires : Deriv (eqF (ap1 R_disp input_pkg) (ap1 br_Rb input_pkg))
      fires = fork_true_to_fst br_Rb R_lvl2 (testB 0) input_pkg
                (idxTest_fire headB 0 input_pkg hB)
      val : Deriv (eqF (ap1 br_Rb input_pkg) (tmAp1 g0 (ap1 devF a)))
      val = mkAp1_val bG0 devA input_pkg g0 (ap1 devF a) bG0_eq recA
  in ruleTrans to_ap2Cell (ruleTrans to_R_disp (ruleTrans fires val))

-- R-step redex:  devF (tmAp2 (R g0 h1 h2) a (tmAp1 s n)) =
--   tmAp2 h1 (tmAp2 h2 (devF a)(devF n))(tmAp2 (R g0 h1 h2)(devF a)(devF n)).
devF_Rs : (g0 h1 h2 a n : Term) ->
  Deriv (eqF (ap1 devF (tmAp2 (cRec g0 h1 h2) a (tmAp1 cSuc n)))
             (tmAp2 h1 (tmAp2 h2 (ap1 devF a) (ap1 devF n))
                       (tmAp2 (cRec g0 h1 h2) (ap1 devF a) (ap1 devF n))))
devF_Rs g0 h1 h2 a n =
  let open Rec g0 h1 h2 a (tmAp1 cSuc n)
      -- headB = Fst (tmAp1 cSuc n) = natCode 1 (skip 0) ; headBFun = Fst cSuc = natCode 3 (fire).
      hB : Deriv (eqF (ap1 headB input_pkg) (natCode 1))
      hB = ruleTrans (compose1U_eq Fst apB input_pkg)
             (ruleTrans (cong1 Fst apB_eq) (axFst tgAp1 (ap2 Pair cSuc n)))
      bSnd_eq : Deriv (eqF (ap1 bSnd input_pkg) (ap2 Pair cSuc n))
      bSnd_eq = ruleTrans (compose1U_eq Snd apB input_pkg)
                  (ruleTrans (cong1 Snd apB_eq) (axSnd tgAp1 (ap2 Pair cSuc n)))
      bFun_eq : Deriv (eqF (ap1 (compose1U Fst bSnd) input_pkg) cSuc)
      bFun_eq = ruleTrans (compose1U_eq Fst bSnd input_pkg)
                  (ruleTrans (cong1 Fst bSnd_eq) (axFst cSuc n))
      hBF : Deriv (eqF (ap1 headBFun input_pkg) (natCode 3))
      hBF = ruleTrans (compose1U_eq Fst (compose1U Fst bSnd) input_pkg)
              (ruleTrans (cong1 Fst bFun_eq) (axFst tgSuc O))
      w10 : NatNeqWitness 1 0
      w10 = decideNatNeq 1 0 (\ ())
      fires : Deriv (eqF (ap1 R_disp input_pkg) (ap1 br_Rs input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_Rb R_lvl2 (testB 0) input_pkg
                     (idxTest_skip headB 1 0 input_pkg w10 hB))
                  (fork_true_to_fst br_Rs br_Rcong (testBF 3) input_pkg
                     (idxTest_fire headBFun 3 input_pkg hBF))
      -- devN input = devF n , from devB input = devF (tmAp1 cSuc n) = tmAp1 cSuc (devF n).
      recB' : Deriv (eqF (ap1 devB input_pkg) (tmAp1 cSuc (ap1 devF n)))
      recB' = ruleTrans recB (devF_ap1_s n)
      devN_eq : Deriv (eqF (ap1 devN input_pkg) (ap1 devF n))
      devN_eq = ruleTrans (compose1U_eq Snd (compose1U Snd devB) input_pkg)
                  (ruleTrans (cong1 Snd (ruleTrans (compose1U_eq Snd devB input_pkg)
                                          (cong1 Snd recB')))
                    (ruleTrans (cong1 Snd (axSnd tgAp1 (ap2 Pair cSuc (ap1 devF n))))
                               (axSnd cSuc (ap1 devF n))))
      arm2 : Deriv (eqF (ap1 (mkAp2 bH2 devA devN) input_pkg)
                        (tmAp2 h2 (ap1 devF a) (ap1 devF n)))
      arm2 = mkAp2_val bH2 devA devN input_pkg h2 (ap1 devF a) (ap1 devF n) bH2_eq recA devN_eq
      recFun : Deriv (eqF (ap1 (mkRec bG0 bH1 bH2) input_pkg) (cRec g0 h1 h2))
      recFun = mkRec_val bG0 bH1 bH2 input_pkg g0 h1 h2 bG0_eq bH1_eq bH2_eq
      arm3 : Deriv (eqF (ap1 (mkAp2 (mkRec bG0 bH1 bH2) devA devN) input_pkg)
                        (tmAp2 (cRec g0 h1 h2) (ap1 devF a) (ap1 devF n)))
      arm3 = mkAp2_val (mkRec bG0 bH1 bH2) devA devN input_pkg
               (cRec g0 h1 h2) (ap1 devF a) (ap1 devF n) recFun recA devN_eq
      val : Deriv (eqF (ap1 br_Rs input_pkg)
                       (tmAp2 h1 (tmAp2 h2 (ap1 devF a) (ap1 devF n))
                                 (tmAp2 (cRec g0 h1 h2) (ap1 devF a) (ap1 devF n))))
      val = mkAp2_val bH1 (mkAp2 bH2 devA devN) (mkAp2 (mkRec bG0 bH1 bH2) devA devN) input_pkg
              h1 (tmAp2 h2 (ap1 devF a) (ap1 devF n))
              (tmAp2 (cRec g0 h1 h2) (ap1 devF a) (ap1 devF n)) bH1_eq arm2 arm3
  in ruleTrans to_ap2Cell (ruleTrans to_R_disp (ruleTrans fires val))
