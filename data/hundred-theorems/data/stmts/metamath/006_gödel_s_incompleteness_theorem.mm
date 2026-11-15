$(
  Statement-only formalization of Hundred Theorems artifact 006, "G&ouml;del's
  Incompleteness Theorem": a weakly consistent theory extending the concrete
  nine-axiom arithmetic theory NN, with representable axiom membership, has a
  closed formula independent of the theory. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Arithmetic terms and formulas are concrete tagged finite trees.  The least
  constructor-closed sets below give their syntax.  All subsequent operations
  are defined constructor by constructor.
$)

$c HT006Var HT006Zero HT006Succ HT006Add HT006Mul $.
$c HT006Eq HT006Lt HT006Imp HT006Neg HT006All $.
$c HT006Or HT006And HT006Iff HT006Ex HT006Terms HT006Formulas $.

ht006-var-syn $a class ( HT006Var A ) $.
ht006-zero-syn $a class HT006Zero $.
ht006-succ-syn $a class ( HT006Succ A ) $.
ht006-add-syn $a class ( HT006Add A B ) $.
ht006-mul-syn $a class ( HT006Mul A B ) $.
ht006-eq-syn $a class ( HT006Eq A B ) $.
ht006-lt-syn $a class ( HT006Lt A B ) $.
ht006-imp-syn $a class ( HT006Imp A B ) $.
ht006-neg-syn $a class ( HT006Neg A ) $.
ht006-all-syn $a class ( HT006All A B ) $.
ht006-or-syn $a class ( HT006Or A B ) $.
ht006-and-syn $a class ( HT006And A B ) $.
ht006-iff-syn $a class ( HT006Iff A B ) $.
ht006-ex-syn $a class ( HT006Ex A B ) $.
ht006-terms-syn $a class HT006Terms $.
ht006-formulas-syn $a class HT006Formulas $.

ht006-var-def $a |- ( HT006Var A ) = <. 0 , A >. $.
ht006-zero-def $a |- HT006Zero = <. 1 , 0 >. $.
ht006-succ-def $a |- ( HT006Succ A ) = <. 2 , A >. $.
ht006-add-def $a |- ( HT006Add A B ) = <. 3 , <. A , B >. >. $.
ht006-mul-def $a |- ( HT006Mul A B ) = <. 4 , <. A , B >. >. $.
ht006-eq-def $a |- ( HT006Eq A B ) = <. 5 , <. A , B >. >. $.
ht006-lt-def $a |- ( HT006Lt A B ) = <. 6 , <. A , B >. >. $.
ht006-imp-def $a |- ( HT006Imp A B ) = <. 7 , <. A , B >. >. $.
ht006-neg-def $a |- ( HT006Neg A ) = <. 8 , A >. $.
ht006-all-def $a |- ( HT006All A B ) = <. 9 , <. A , B >. >. $.
ht006-or-def $a
  |- ( HT006Or A B ) = ( HT006Imp ( HT006Neg A ) B ) $.
ht006-and-def $a
  |- ( HT006And A B ) = ( HT006Neg ( HT006Imp A ( HT006Neg B ) ) ) $.
ht006-iff-def $a
  |- ( HT006Iff A B ) =
     ( HT006And ( HT006Imp A B ) ( HT006Imp B A ) ) $.
ht006-ex-def $a
  |- ( HT006Ex A B ) = ( HT006Neg ( HT006All A ( HT006Neg B ) ) ) $.

ht006-terms-def $a |- HT006Terms =
  |^| { x |
    (
      ( A. n e. NN0 ( HT006Var n ) e. x /\ HT006Zero e. x )
      /\
      (
        ( A. s e. x ( HT006Succ s ) e. x
          /\ A. s e. x A. u e. x ( HT006Add s u ) e. x )
        /\
        A. s e. x A. u e. x ( HT006Mul s u ) e. x
      )
    )
  } $.

ht006-formulas-def $a |- HT006Formulas =
  |^| { x |
    (
      A. s e. HT006Terms A. u e. HT006Terms
        ( ( HT006Eq s u ) e. x /\ ( HT006Lt s u ) e. x )
      /\
      (
        ( A. a e. x A. b e. x ( HT006Imp a b ) e. x
          /\ A. a e. x ( HT006Neg a ) e. x )
        /\
        A. n e. NN0 A. a e. x ( HT006All n a ) e. x
      )
    )
  } $.

$c HT006FVTerm HT006AVTerm HT006FVFormula HT006AVFormula $.
$c HT006RenameTerm HT006RenameBound HT006SubstTerm HT006Fresh $.
$c HT006SubstFormula $.

ht006-fvt-syn $a class ( HT006FVTerm A ) $.
ht006-avt-syn $a class ( HT006AVTerm A ) $.
ht006-fvf-syn $a class ( HT006FVFormula A ) $.
ht006-avf-syn $a class ( HT006AVFormula A ) $.
ht006-rt-syn $a class ( HT006RenameTerm A B C ) $.
ht006-rb-syn $a class ( HT006RenameBound A B C ) $.
ht006-st-syn $a class ( HT006SubstTerm A B C ) $.
ht006-fresh-syn $a class ( HT006Fresh A B C D ) $.
ht006-sf-syn $a class ( HT006SubstFormula A B C ) $.

$(
  Constructor equations are guarded by their intended domains. Without these
  guards, substitution of proper classes can collapse distinct tagged
  constructors in NBG class semantics and force incompatible values for one
  recursive operation.
$)

ht006-fvt-var $a |- (
  A e. NN0
  ->
  ( HT006FVTerm ( HT006Var A ) ) = { A }
) $.
ht006-fvt-zero $a |- ( HT006FVTerm HT006Zero ) = (/) $.
ht006-fvt-succ $a |- (
  A e. HT006Terms
  ->
  ( HT006FVTerm ( HT006Succ A ) ) = ( HT006FVTerm A )
) $.
ht006-fvt-add $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006FVTerm ( HT006Add A B ) ) =
    ( ( HT006FVTerm A ) u. ( HT006FVTerm B ) )
) $.
ht006-fvt-mul $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006FVTerm ( HT006Mul A B ) ) =
    ( ( HT006FVTerm A ) u. ( HT006FVTerm B ) )
) $.
ht006-avt-var $a |- (
  A e. NN0
  ->
  ( HT006AVTerm ( HT006Var A ) ) = { A }
) $.
ht006-avt-zero $a |- ( HT006AVTerm HT006Zero ) = (/) $.
ht006-avt-succ $a |- (
  A e. HT006Terms
  ->
  ( HT006AVTerm ( HT006Succ A ) ) = ( HT006AVTerm A )
) $.
ht006-avt-add $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006AVTerm ( HT006Add A B ) ) =
    ( ( HT006AVTerm A ) u. ( HT006AVTerm B ) )
) $.
ht006-avt-mul $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006AVTerm ( HT006Mul A B ) ) =
    ( ( HT006AVTerm A ) u. ( HT006AVTerm B ) )
) $.

ht006-fvf-eq $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006FVFormula ( HT006Eq A B ) ) =
    ( ( HT006FVTerm A ) u. ( HT006FVTerm B ) )
) $.
ht006-fvf-lt $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006FVFormula ( HT006Lt A B ) ) =
    ( ( HT006FVTerm A ) u. ( HT006FVTerm B ) )
) $.
ht006-fvf-imp $a |- (
  ( A e. HT006Formulas /\ B e. HT006Formulas )
  ->
  ( HT006FVFormula ( HT006Imp A B ) ) =
    ( ( HT006FVFormula A ) u. ( HT006FVFormula B ) )
) $.
ht006-fvf-neg $a |- (
  A e. HT006Formulas
  ->
  ( HT006FVFormula ( HT006Neg A ) ) = ( HT006FVFormula A )
) $.
ht006-fvf-all $a |- (
  ( A e. NN0 /\ B e. HT006Formulas )
  ->
  ( HT006FVFormula ( HT006All A B ) ) =
    ( ( HT006FVFormula B ) \ { A } )
) $.
ht006-avf-eq $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006AVFormula ( HT006Eq A B ) ) =
    ( ( HT006AVTerm A ) u. ( HT006AVTerm B ) )
) $.
ht006-avf-lt $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006AVFormula ( HT006Lt A B ) ) =
    ( ( HT006AVTerm A ) u. ( HT006AVTerm B ) )
) $.
ht006-avf-imp $a |- (
  ( A e. HT006Formulas /\ B e. HT006Formulas )
  ->
  ( HT006AVFormula ( HT006Imp A B ) ) =
    ( ( HT006AVFormula A ) u. ( HT006AVFormula B ) )
) $.
ht006-avf-neg $a |- (
  A e. HT006Formulas
  ->
  ( HT006AVFormula ( HT006Neg A ) ) = ( HT006AVFormula A )
) $.
ht006-avf-all $a |- (
  ( A e. NN0 /\ B e. HT006Formulas )
  ->
  ( HT006AVFormula ( HT006All A B ) ) =
    ( { A } u. ( HT006AVFormula B ) )
) $.

ht006-rt-var $a |- (
  ( ( A e. NN0 /\ B e. NN0 ) /\ C e. NN0 )
  ->
  ( HT006RenameTerm ( HT006Var A ) B C ) =
    if ( A = B , ( HT006Var C ) , ( HT006Var A ) )
) $.
ht006-rt-zero $a |- (
  ( B e. NN0 /\ C e. NN0 )
  ->
  ( HT006RenameTerm HT006Zero B C ) = HT006Zero
) $.
ht006-rt-succ $a |- (
  ( ( A e. HT006Terms /\ B e. NN0 ) /\ C e. NN0 )
  ->
  ( HT006RenameTerm ( HT006Succ A ) B C ) =
    ( HT006Succ ( HT006RenameTerm A B C ) )
) $.
ht006-rt-add $a |- (
  (
    ( A e. HT006Terms /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. NN0 )
  )
  ->
  ( HT006RenameTerm ( HT006Add A B ) C D ) =
    ( HT006Add ( HT006RenameTerm A C D )
      ( HT006RenameTerm B C D ) )
) $.
ht006-rt-mul $a |- (
  (
    ( A e. HT006Terms /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. NN0 )
  )
  ->
  ( HT006RenameTerm ( HT006Mul A B ) C D ) =
    ( HT006Mul ( HT006RenameTerm A C D )
      ( HT006RenameTerm B C D ) )
) $.

ht006-rb-eq $a |- (
  (
    ( A e. HT006Terms /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. NN0 )
  )
  ->
  ( HT006RenameBound ( HT006Eq A B ) C D ) =
    ( HT006Eq ( HT006RenameTerm A C D )
      ( HT006RenameTerm B C D ) )
) $.
ht006-rb-lt $a |- (
  (
    ( A e. HT006Terms /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. NN0 )
  )
  ->
  ( HT006RenameBound ( HT006Lt A B ) C D ) =
    ( HT006Lt ( HT006RenameTerm A C D )
      ( HT006RenameTerm B C D ) )
) $.
ht006-rb-imp $a |- (
  (
    ( A e. HT006Formulas /\ B e. HT006Formulas )
    /\
    ( C e. NN0 /\ D e. NN0 )
  )
  ->
  ( HT006RenameBound ( HT006Imp A B ) C D ) =
    ( HT006Imp ( HT006RenameBound A C D )
      ( HT006RenameBound B C D ) )
) $.
ht006-rb-neg $a |- (
  ( ( A e. HT006Formulas /\ C e. NN0 ) /\ D e. NN0 )
  ->
  ( HT006RenameBound ( HT006Neg A ) C D ) =
    ( HT006Neg ( HT006RenameBound A C D ) )
) $.
ht006-rb-all $a |- (
  (
    ( A e. NN0 /\ B e. HT006Formulas )
    /\
    ( C e. NN0 /\ D e. NN0 )
  )
  ->
  ( HT006RenameBound ( HT006All A B ) C D ) =
    if ( A = C , ( HT006All A B ) ,
         ( HT006All A ( HT006RenameBound B C D ) ) )
) $.

ht006-st-var $a |- (
  ( ( A e. NN0 /\ B e. NN0 ) /\ C e. HT006Terms )
  ->
  ( HT006SubstTerm ( HT006Var A ) B C ) =
    if ( A = B , C , ( HT006Var A ) )
) $.
ht006-st-zero $a |- (
  ( B e. NN0 /\ C e. HT006Terms )
  ->
  ( HT006SubstTerm HT006Zero B C ) = HT006Zero
) $.
ht006-st-succ $a |- (
  ( ( A e. HT006Terms /\ B e. NN0 ) /\ C e. HT006Terms )
  ->
  ( HT006SubstTerm ( HT006Succ A ) B C ) =
    ( HT006Succ ( HT006SubstTerm A B C ) )
) $.
ht006-st-add $a |- (
  (
    ( A e. HT006Terms /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. HT006Terms )
  )
  ->
  ( HT006SubstTerm ( HT006Add A B ) C D ) =
    ( HT006Add ( HT006SubstTerm A C D )
      ( HT006SubstTerm B C D ) )
) $.
ht006-st-mul $a |- (
  (
    ( A e. HT006Terms /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. HT006Terms )
  )
  ->
  ( HT006SubstTerm ( HT006Mul A B ) C D ) =
    ( HT006Mul ( HT006SubstTerm A C D )
      ( HT006SubstTerm B C D ) )
) $.

ht006-fresh-def $a |- (
  (
    ( A e. HT006Formulas /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. NN0 )
  )
  ->
  ( HT006Fresh A B C D ) =
    suc U. ( ( HT006AVFormula A )
      u. ( ( HT006AVTerm B ) u. { C , D } ) )
) $.
ht006-sf-eq $a |- (
  (
    ( A e. HT006Terms /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. HT006Terms )
  )
  ->
  ( HT006SubstFormula ( HT006Eq A B ) C D ) =
    ( HT006Eq ( HT006SubstTerm A C D )
      ( HT006SubstTerm B C D ) )
) $.
ht006-sf-lt $a |- (
  (
    ( A e. HT006Terms /\ B e. HT006Terms )
    /\
    ( C e. NN0 /\ D e. HT006Terms )
  )
  ->
  ( HT006SubstFormula ( HT006Lt A B ) C D ) =
    ( HT006Lt ( HT006SubstTerm A C D )
      ( HT006SubstTerm B C D ) )
) $.
ht006-sf-imp $a |- (
  (
    ( A e. HT006Formulas /\ B e. HT006Formulas )
    /\
    ( C e. NN0 /\ D e. HT006Terms )
  )
  ->
  ( HT006SubstFormula ( HT006Imp A B ) C D ) =
    ( HT006Imp ( HT006SubstFormula A C D )
      ( HT006SubstFormula B C D ) )
) $.
ht006-sf-neg $a |- (
  (
    ( A e. HT006Formulas /\ C e. NN0 )
    /\
    D e. HT006Terms
  )
  ->
  ( HT006SubstFormula ( HT006Neg A ) C D ) =
    ( HT006Neg ( HT006SubstFormula A C D ) )
) $.
ht006-sf-all $a |- (
  (
    ( A e. NN0 /\ B e. HT006Formulas )
    /\
    ( C e. NN0 /\ D e. HT006Terms )
  )
  ->
  ( HT006SubstFormula ( HT006All A B ) C D ) =
    if (
      A = C ,
      ( HT006All A B ) ,
      if (
        A e. ( HT006FVTerm D ) ,
        ( HT006All
          ( HT006Fresh B D C A )
          ( HT006SubstFormula
            ( HT006RenameBound B A ( HT006Fresh B D C A ) ) C D ) ) ,
        ( HT006All A ( HT006SubstFormula B C D ) )
      )
    )
) $.

$(
  The following are the source pairing, numeral, G&ouml;del-code, and
  reflection equations.
$)

$c HT006Numeral HT006PairCode HT006CodeTerm HT006CodeFormula HT006Reflect $.
ht006-num-syn $a class ( HT006Numeral A ) $.
ht006-pair-syn $a class ( HT006PairCode A B ) $.
ht006-ct-syn $a class ( HT006CodeTerm A ) $.
ht006-cf-syn $a class ( HT006CodeFormula A ) $.
ht006-reflect-syn $a class ( HT006Reflect A ) $.

ht006-num-zero $a |- ( HT006Numeral 0 ) = HT006Zero $.
ht006-num-succ $a |- ( A e. NN0 ->
  ( HT006Numeral ( A + 1 ) ) = ( HT006Succ ( HT006Numeral A ) ) ) $.
ht006-pair-def $a |- ( HT006PairCode A B ) =
  ( ( 2 ^ A ) x. ( ( 2 x. B ) + 1 ) ) $.
ht006-ct-var $a |- (
  A e. NN0
  ->
  ( HT006CodeTerm ( HT006Var A ) ) = ( 5 x. A )
) $.
ht006-ct-zero $a |- ( HT006CodeTerm HT006Zero ) = 1 $.
ht006-ct-succ $a |- (
  A e. HT006Terms
  ->
  ( HT006CodeTerm ( HT006Succ A ) ) =
    ( ( 5 x. ( HT006CodeTerm A ) ) + 2 )
) $.
ht006-ct-add $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006CodeTerm ( HT006Add A B ) ) =
    ( ( 5 x.
        ( HT006PairCode ( HT006CodeTerm A ) ( HT006CodeTerm B ) ) )
      + 3 )
) $.
ht006-ct-mul $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006CodeTerm ( HT006Mul A B ) ) =
    ( ( 5 x.
        ( HT006PairCode ( HT006CodeTerm A ) ( HT006CodeTerm B ) ) )
      + 4 )
) $.
ht006-cf-eq $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006CodeFormula ( HT006Eq A B ) ) =
    ( 5 x.
      ( HT006PairCode ( HT006CodeTerm A ) ( HT006CodeTerm B ) ) )
) $.
ht006-cf-lt $a |- (
  ( A e. HT006Terms /\ B e. HT006Terms )
  ->
  ( HT006CodeFormula ( HT006Lt A B ) ) =
    ( ( 5 x.
        ( HT006PairCode ( HT006CodeTerm A ) ( HT006CodeTerm B ) ) )
      + 1 )
) $.
ht006-cf-imp $a |- (
  ( A e. HT006Formulas /\ B e. HT006Formulas )
  ->
  ( HT006CodeFormula ( HT006Imp A B ) ) =
    ( ( 5 x.
        ( HT006PairCode ( HT006CodeFormula A )
          ( HT006CodeFormula B ) ) )
      + 2 )
) $.
ht006-cf-neg $a |- (
  A e. HT006Formulas
  ->
  ( HT006CodeFormula ( HT006Neg A ) ) =
    ( ( 5 x. ( HT006CodeFormula A ) ) + 3 )
) $.
ht006-cf-all $a |- (
  ( A e. NN0 /\ B e. HT006Formulas )
  ->
  ( HT006CodeFormula ( HT006All A B ) ) =
    ( ( 5 x. ( HT006PairCode A ( HT006CodeFormula B ) ) ) + 4 )
) $.
ht006-reflect-def $a |- (
  A e. HT006Formulas
  ->
  ( HT006Reflect A ) = ( HT006Numeral ( HT006CodeFormula A ) )
) $.

$c HT006NN1 HT006NN2 HT006NN3 HT006NN4 HT006NN5 $.
$c HT006NN6 HT006NN7 HT006NN8 HT006NN9 HT006NN $.
ht006-nn1-syn $a class HT006NN1 $.
ht006-nn2-syn $a class HT006NN2 $.
ht006-nn3-syn $a class HT006NN3 $.
ht006-nn4-syn $a class HT006NN4 $.
ht006-nn5-syn $a class HT006NN5 $.
ht006-nn6-syn $a class HT006NN6 $.
ht006-nn7-syn $a class HT006NN7 $.
ht006-nn8-syn $a class HT006NN8 $.
ht006-nn9-syn $a class HT006NN9 $.
ht006-nn-syn $a class HT006NN $.

ht006-nn1-def $a |- HT006NN1 =
  ( HT006All 0 ( HT006Neg
    ( HT006Eq ( HT006Succ ( HT006Var 0 ) ) HT006Zero ) ) ) $.
ht006-nn2-def $a |- HT006NN2 =
  ( HT006All 1 ( HT006All 0
    ( HT006Imp
      ( HT006Eq ( HT006Succ ( HT006Var 0 ) )
                  ( HT006Succ ( HT006Var 1 ) ) )
      ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) ) ) ) ) $.
ht006-nn3-def $a |- HT006NN3 =
  ( HT006All 0
    ( HT006Eq ( HT006Add ( HT006Var 0 ) HT006Zero ) ( HT006Var 0 ) ) ) $.
ht006-nn4-def $a |- HT006NN4 =
  ( HT006All 1 ( HT006All 0
    ( HT006Eq
      ( HT006Add ( HT006Var 0 ) ( HT006Succ ( HT006Var 1 ) ) )
      ( HT006Succ ( HT006Add ( HT006Var 0 ) ( HT006Var 1 ) ) ) ) ) ) $.
ht006-nn5-def $a |- HT006NN5 =
  ( HT006All 0
    ( HT006Eq ( HT006Mul ( HT006Var 0 ) HT006Zero ) HT006Zero ) ) $.
ht006-nn6-def $a |- HT006NN6 =
  ( HT006All 1 ( HT006All 0
    ( HT006Eq
      ( HT006Mul ( HT006Var 0 ) ( HT006Succ ( HT006Var 1 ) ) )
      ( HT006Add ( HT006Mul ( HT006Var 0 ) ( HT006Var 1 ) )
                  ( HT006Var 0 ) ) ) ) ) $.
ht006-nn7-def $a |- HT006NN7 =
  ( HT006All 0 ( HT006Neg ( HT006Lt ( HT006Var 0 ) HT006Zero ) ) ) $.
ht006-nn8-def $a |- HT006NN8 =
  ( HT006All 1 ( HT006All 0
    ( HT006Imp
      ( HT006Lt ( HT006Var 0 ) ( HT006Succ ( HT006Var 1 ) ) )
      ( HT006Or ( HT006Lt ( HT006Var 0 ) ( HT006Var 1 ) )
                 ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) ) ) ) ) ) $.
ht006-nn9-def $a |- HT006NN9 =
  ( HT006All 1 ( HT006All 0
    ( HT006Or
      ( HT006Lt ( HT006Var 0 ) ( HT006Var 1 ) )
      ( HT006Or ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) )
                 ( HT006Lt ( HT006Var 1 ) ( HT006Var 0 ) ) ) ) ) ) $.
ht006-nn-def $a |- HT006NN =
  { HT006NN1 , HT006NN2 , HT006NN3 , HT006NN4 , HT006NN5 ,
    HT006NN6 , HT006NN7 , HT006NN8 , HT006NN9 } $.

$(
  Derivability uses finite sets of assumptions, the set quotient of the
  source lists: append becomes union and free variables become indexed union.
  HT006Deriv is the least relation closed under exactly the displayed source
  Hilbert rules.
$)

$c HT006LessCong HT006SuccCong HT006AddCong HT006MulCong $.
$c HT006DerivationClosed HT006Deriv HT006Provable $.
ht006-lc-syn $a class HT006LessCong $.
ht006-sc-syn $a class HT006SuccCong $.
ht006-ac-syn $a class HT006AddCong $.
ht006-mc-syn $a class HT006MulCong $.
ht006-dc-syn $a wff ( HT006DerivationClosed A ) $.
ht006-deriv-syn $a class HT006Deriv $.
ht006-prov-syn $a wff ( HT006Provable A B ) $.

ht006-lc-def $a |- HT006LessCong =
  ( HT006Imp ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) )
    ( HT006Imp ( HT006Eq ( HT006Var 2 ) ( HT006Var 3 ) )
      ( HT006Iff ( HT006Lt ( HT006Var 0 ) ( HT006Var 2 ) )
                  ( HT006Lt ( HT006Var 1 ) ( HT006Var 3 ) ) ) ) ) $.
ht006-sc-def $a |- HT006SuccCong =
  ( HT006Imp ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) )
    ( HT006Eq ( HT006Succ ( HT006Var 0 ) )
                ( HT006Succ ( HT006Var 1 ) ) ) ) $.
ht006-ac-def $a |- HT006AddCong =
  ( HT006Imp ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) )
    ( HT006Imp ( HT006Eq ( HT006Var 2 ) ( HT006Var 3 ) )
      ( HT006Eq ( HT006Add ( HT006Var 0 ) ( HT006Var 2 ) )
                  ( HT006Add ( HT006Var 1 ) ( HT006Var 3 ) ) ) ) ) $.
ht006-mc-def $a |- HT006MulCong =
  ( HT006Imp ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) )
    ( HT006Imp ( HT006Eq ( HT006Var 2 ) ( HT006Var 3 ) )
      ( HT006Eq ( HT006Mul ( HT006Var 0 ) ( HT006Var 2 ) )
                  ( HT006Mul ( HT006Var 1 ) ( HT006Var 3 ) ) ) ) ) $.

ht006-dc-def $a |- (
  HT006DerivationClosed A
  <->
  (
    (
      A. a e. HT006Formulas <. { a } , a >. e. A
      /\
      A. h A. k A. a e. HT006Formulas A. b e. HT006Formulas
        (
          (
            ( ( h e. Fin /\ h C_ HT006Formulas )
              /\ ( k e. Fin /\ k C_ HT006Formulas ) )
            /\
            ( <. h , ( HT006Imp a b ) >. e. A /\ <. k , a >. e. A )
          )
          -> <. ( h u. k ) , b >. e. A
        )
    )
    /\
    (
      (
        A. h A. n e. NN0 A. a e. HT006Formulas
          (
            ( ( ( h e. Fin /\ h C_ HT006Formulas )
                /\ <. h , a >. e. A )
              /\ -. n e. U_ b e. h ( HT006FVFormula b ) )
            -> <. h , ( HT006All n a ) >. e. A
          )
        /\
        A. a e. HT006Formulas A. b e. HT006Formulas
          <. (/) , ( HT006Imp a ( HT006Imp b a ) ) >. e. A
      )
      /\
      (
        (
          A. a e. HT006Formulas A. b e. HT006Formulas
          A. c e. HT006Formulas
            <. (/) ,
              ( HT006Imp ( HT006Imp a ( HT006Imp b c ) )
                ( HT006Imp ( HT006Imp a b ) ( HT006Imp a c ) ) ) >. e. A
          /\
          A. a e. HT006Formulas A. b e. HT006Formulas
            <. (/) ,
              ( HT006Imp ( HT006Imp ( HT006Neg a ) ( HT006Neg b ) )
                           ( HT006Imp b a ) ) >. e. A
        )
        /\
        (
          A. n e. NN0 A. a e. HT006Formulas A. s e. HT006Terms
            <. (/) ,
              ( HT006Imp ( HT006All n a )
                           ( HT006SubstFormula a n s ) ) >. e. A
          /\
          A. n e. NN0 A. a e. HT006Formulas
            ( -. n e. ( HT006FVFormula a )
              -> <. (/) , ( HT006Imp a ( HT006All n a ) ) >. e. A )
        )
      )
    )
    /\
    (
      (
        A. n e. NN0 A. a e. HT006Formulas A. b e. HT006Formulas
          <. (/) ,
            ( HT006Imp ( HT006All n ( HT006Imp a b ) )
              ( HT006Imp ( HT006All n a ) ( HT006All n b ) ) ) >. e. A
        /\
        <. (/) , ( HT006Eq ( HT006Var 0 ) ( HT006Var 0 ) ) >. e. A
      )
      /\
      (
        (
          <. (/) ,
            ( HT006Imp ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) )
                         ( HT006Eq ( HT006Var 1 ) ( HT006Var 0 ) ) ) >. e. A
          /\
          <. (/) ,
            ( HT006Imp ( HT006Eq ( HT006Var 0 ) ( HT006Var 1 ) )
              ( HT006Imp ( HT006Eq ( HT006Var 1 ) ( HT006Var 2 ) )
                           ( HT006Eq ( HT006Var 0 ) ( HT006Var 2 ) ) ) )
          >. e. A
        )
        /\
        (
          <. (/) , HT006LessCong >. e. A
          /\
          ( <. (/) , ( HT006Eq HT006Zero HT006Zero ) >. e. A
            /\
            ( <. (/) , HT006SuccCong >. e. A
              /\
              ( <. (/) , HT006AddCong >. e. A
                /\ <. (/) , HT006MulCong >. e. A ) ) )
        )
      )
    )
  )
) $.

ht006-deriv-def $a |- HT006Deriv =
  |^| { q | ( HT006DerivationClosed q ) } $.
ht006-prov-def $a |- (
  HT006Provable A B
  <->
  E. h
    ( ( h e. Fin /\ h C_ HT006Formulas )
      /\ ( <. h , B >. e. HT006Deriv /\ h C_ A ) )
) $.

$c HT006WeaklyConsistent HT006Independent HT006Closed $.
ht006-wc-syn $a wff ( HT006WeaklyConsistent A ) $.
ht006-ind-syn $a wff ( HT006Independent A B ) $.
ht006-closed-syn $a wff ( HT006Closed A ) $.

ht006-wc-def $a |- (
  HT006WeaklyConsistent A
  <->
  A. a e. HT006Formulas A. n e. NN0
    (
      A. k e. ( HT006FVFormula a ) n = k
      ->
      (
        ( HT006Provable A ( HT006Ex n ( HT006Neg a ) ) )
        ->
        E. k e. NN0
          -. ( HT006Provable
                A ( HT006SubstFormula a n ( HT006Numeral k ) ) )
      )
    )
) $.
ht006-ind-def $a |- (
  HT006Independent A B
  <->
  ( -. ( HT006Provable A B )
    /\ -. ( HT006Provable A ( HT006Neg B ) ) )
) $.
ht006-closed-def $a |- (
  HT006Closed A <-> ( HT006FVFormula A ) = (/)
) $.

$(
  In the final scope t is the arbitrary source system T, r is repT, and v is
  v0.  The existential independent closed formula remains internal.
$)

${
  ht006-system-type $e |- t C_ HT006Formulas $.
  ht006-representer-type $e |- r e. HT006Formulas $.
  ht006-variable-type $e |- v e. NN0 $.
  ht006-extends-nn $e |- HT006NN C_ t $.
  ht006-representer-fv $e
    |- A. n e. ( HT006FVFormula r ) n = v $.
  ht006-rep-positive $e |- (
    A. a e. HT006Formulas
      ( a e. t ->
        ( HT006Provable t
          ( HT006SubstFormula r v ( HT006Reflect a ) ) ) )
  ) $.
  ht006-rep-negative $e |- (
    A. a e. HT006Formulas
      ( -. a e. t ->
        ( HT006Provable t
          ( HT006Neg
            ( HT006SubstFormula r v ( HT006Reflect a ) ) ) ) )
  ) $.
  hundred-theorems-006-goedel-first-incompleteness $a |- (
    ( HT006WeaklyConsistent t )
    ->
    E. a e. HT006Formulas
      ( ( HT006Independent t a ) /\ ( HT006Closed a ) )
  ) $.
$}
