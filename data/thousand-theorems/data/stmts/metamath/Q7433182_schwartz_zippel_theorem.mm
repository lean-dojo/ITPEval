$(
  Statement-only formalization of Thousand Theorems corpus artifact Q7433182
  (thousand-theorems__metamath__Q7433182), "Schwartz-Zippel theorem": for a
  nonzero multivariate polynomial over an arbitrary integral domain, the
  normalized number of zeros on a dependent product of finite subsets is
  bounded by the support supremum of the sums of coordinate degrees divided
  by the corresponding subset cardinalities. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite ordinal n represents Lean's Fin n.  A family S maps each
  coordinate to a finite subset of Base(R), and the restricted class in the
  numerator is exactly its dependent product filtered by polynomial
  evaluation at zero.  SetMM polynomials are coefficient functions on
  finitely supported NN0-valued exponent vectors, so P supp (0g ` R) is
  Lean's polynomial support and s ` i is the exponent of coordinate i.

  All cardinalities, exponents, sums, products, and quotient values in the
  displayed inequality are nonnegative rationals.  Q7433182ZDiv explicitly
  returns zero when its denominator is zero and otherwise uses ordinary
  rational division, exactly matching Lean's nonnegative-rational division.
  Because P is nonzero, its support is finite and nonempty, making the ordered
  supremum over QQ exactly Lean's finite supremum.  The declaration below is
  an unproved $a statement; this database contains no $p proof declaration.
$)

$c Q7433182ZDiv $.

q7433182-zero-totalized-quotient-syntax $a
  class ( Q7433182ZDiv A B )
$.

${
  $d A B $.

  q7433182-zero-totalized-quotient-definition $a |-
    ( Q7433182ZDiv A B ) =
      if ( B = 0 , 0 , ( A / B ) )
  $.
$}

${
  $d P R S i n s x $.

  thousand-theorems-q7433182-schwartz-zippel-sup-sum $a |-
    A. R e. IDomn
      A. n e. NN0
        A. P e. ( Base ` ( n mPoly R ) )
          ( P =/= ( 0g ` ( n mPoly R ) )
            ->
            A. S e. ( n --> ( ~P ( Base ` R ) i^i Fin ) )
              (
                ( Q7433182ZDiv
                  ( # `
                    { x e. ( ( Base ` R ) ^m n ) |
                      ( ( A. i e. n ( x ` i ) e. ( S ` i ) )
                        /\
                        ( ( ( n eval R ) ` P ) ` x ) =
                          ( 0g ` R ) ) } )
                  ( prod_ i e. n ( # ` ( S ` i ) ) )
                )
                <_
                sup (
                  ran
                    ( s e. ( P supp ( 0g ` R ) ) |->
                      ( sum_ i e. n
                        ( Q7433182ZDiv
                          ( s ` i )
                          ( # ` ( S ` i ) ) ) ) ) ,
                  QQ ,
                  <
                )
              ) )
  $.
$}
