$(
  Statement-only formalization of Thousand Theorems corpus artifact Q180345
  (thousand-theorems__metamath__Q180345), "Rational root theorem": over an
  arbitrary unique factorization domain, a root in its fraction field has
  reduced numerator dividing the constant coefficient and reduced denominator
  dividing the leading coefficient. This file contains no proof.

  The canonical fraction field Frac ` R represents the arbitrary fraction
  field in the source statement up to its canonical R-algebra isomorphism.
  Q180345Reduced selects coprime numerator-denominator representatives; all
  such representatives differ by a unit, so the two divisibility conclusions
  are equivalent to those for the source's normalized numerator and
  denominator.
$)

$[ lib/set.mm $]

$c Q180345Root Q180345Reduced Q180345Leading $.

q180345-root-syntax $a wff ( Q180345Root R P X ) $.
q180345-reduced-syntax $a wff ( Q180345Reduced R X A B ) $.
q180345-leading-syntax $a class ( Q180345Leading R P ) $.

${
  $d P Q R X k $.
  q180345-root-definition $a |- ( ( Q180345Root R P X ) <->
      E. Q e. ( Base ` ( Poly1 ` ( Frac ` R ) ) )
        ( ( A. k e. NN0
              ( ( coe1 ` Q ) ` k ) =
                [ <. ( ( coe1 ` P ) ` k ) , ( 1r ` R ) >. ]
                  ( R ~RL ( RLReg ` R ) ) )
          /\
          ( ( ( eval1 ` ( Frac ` R ) ) ` Q ) ` X ) =
            ( 0g ` ( Frac ` R ) ) ) ) ) $.
$}

${
  $d A B D R X $.
  q180345-reduced-definition $a |- ( ( Q180345Reduced R X A B ) <->
      ( ( A e. ( Base ` R ) /\ B e. ( RLReg ` R ) )
        /\
        ( X = [ <. A , B >. ] ( R ~RL ( RLReg ` R ) )
          /\
          A. D e. ( Base ` R )
            ( ( D ( ||r ` R ) A /\ D ( ||r ` R ) B ) ->
              D e. ( Unit ` R ) ) ) ) ) $.
$}

${
  $d P R $.
  q180345-leading-definition $a |- ( ( Q180345Leading R P ) =
      if ( P = ( 0g ` ( Poly1 ` R ) ) ,
           ( 0g ` R ) ,
           ( ( coe1 ` P ) ` ( ( deg1 ` R ) ` P ) ) ) ) $.
$}

${
  $d A B P R X $.
  thousand-theorems-q180345-num-dvd-of-is-root $a |-
      A. R e. UFD
        A. P e. ( Base ` ( Poly1 ` R ) )
          A. X e. ( Base ` ( Frac ` R ) )
            ( ( Q180345Root R P X ) ->
              A. A e. ( Base ` R )
                A. B e. ( RLReg ` R )
                  ( ( Q180345Reduced R X A B ) ->
                    A ( ||r ` R ) ( ( coe1 ` P ) ` 0 ) ) ) $.
$}

${
  $d A B P R X $.
  thousand-theorems-q180345-den-dvd-of-is-root $a |-
      A. R e. UFD
        A. P e. ( Base ` ( Poly1 ` R ) )
          A. X e. ( Base ` ( Frac ` R ) )
            ( ( Q180345Root R P X ) ->
              A. A e. ( Base ` R )
                A. B e. ( RLReg ` R )
                  ( ( Q180345Reduced R X A B ) ->
                    B ( ||r ` R ) ( Q180345Leading R P ) ) ) $.
$}
