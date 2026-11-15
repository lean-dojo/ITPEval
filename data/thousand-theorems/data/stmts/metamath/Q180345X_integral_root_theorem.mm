$(
  Statement-only formalization of Thousand Theorems corpus artifact Q180345X
  (thousand-theorems__metamath__Q180345X), "Integral root theorem": over an
  arbitrary unique factorization domain, every root in its fraction field of
  a monic polynomial over the domain is the image of an element of the
  domain. This file contains no proof.

  The canonical fraction field Frac ` R represents the arbitrary fraction
  field in the source statement up to its canonical R-algebra isomorphism.
  SetMM's Monic1p ` R is the class of monic univariate polynomials over R.
  The conclusion writes the root as the fraction class of <A, 1>, which is
  exactly membership in the image of the base domain.
$)

$[ lib/set.mm $]

$c Q180345XRoot $.

q180345x-root-syntax $a wff ( Q180345XRoot R P X ) $.

${
  $d P Q R X k $.
  q180345x-root-definition $a |- ( ( Q180345XRoot R P X ) <->
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
  $d A P R X $.
  thousand-theorems-q180345x-is-integer-of-is-root-of-monic $a |-
      A. R e. UFD
        A. P e. ( Base ` ( Poly1 ` R ) )
          A. X e. ( Base ` ( Frac ` R ) )
            ( ( P e. ( Monic1p ` R )
                /\ ( Q180345XRoot R P X ) ) ->
              E. A e. ( Base ` R )
                X = [ <. A , ( 1r ` R ) >. ]
                      ( R ~RL ( RLReg ` R ) ) ) $.
$}
