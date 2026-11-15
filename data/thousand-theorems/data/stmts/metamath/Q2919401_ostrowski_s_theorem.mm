$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2919401
  (thousand-theorems__metamath__Q2919401), "Ostrowski's theorem":
  every nontrivial real-valued absolute value on the rational numbers is
  order-equivalent either to the usual absolute value or to the p-adic
  absolute value for a unique prime p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q2919401Nontrivial states that an absolute value differs from one at some
  nonzero rational. Q2919401Equivalent is the source notion of equivalence:
  the two absolute values induce the same ordering of all pairs of rationals.
  Q2919401Padic is the canonical p-adic absolute value, using the integer
  p-adic valuation pCnt. Every declaration below is an unproved $a statement
  encoding; this database contains no $p proof.
$)

$c Q2919401Nontrivial Q2919401Equivalent Q2919401Padic $.

q2919401-nontrivial-syntax
  $a wff ( Q2919401Nontrivial f ) $.
q2919401-equivalent-syntax
  $a wff ( Q2919401Equivalent f g ) $.
q2919401-padic-syntax
  $a class ( Q2919401Padic p ) $.

${
  $d f x $.

  q2919401-nontrivial-definition $a |- (
    Q2919401Nontrivial f
  ) <->
  E. x e. QQ
    (
      x =/= 0
      /\
      ( f ` x ) =/= 1
    )
  $.
$}

${
  $d f g x y $.

  q2919401-equivalent-definition $a |- (
    Q2919401Equivalent f g
  ) <->
  A. x e. QQ
    A. y e. QQ
      (
        ( ( f ` x ) <_ ( f ` y ) )
        <->
        ( ( g ` x ) <_ ( g ` y ) )
      )
  $.
$}

${
  $d p x $.

  q2919401-padic-definition $a |- (
    Q2919401Padic p
  ) = (
    x e. QQ |->
      if (
        x = 0 ,
        0 ,
        ( p ^ -u ( p pCnt x ) )
      )
  ) $.
$}

${
  $d f p $.

  thousand-theorems-q2919401-ostrowski-s-theorem $a |-
    A. f e. ( AbsVal ` ( CCfld |`s QQ ) )
      (
        ( Q2919401Nontrivial f )
        ->
        (
          ( Q2919401Equivalent f ( abs |` QQ ) )
          \/
          E! p e. Prime
            ( Q2919401Equivalent f ( Q2919401Padic p ) )
        )
      )
  $.
$}
