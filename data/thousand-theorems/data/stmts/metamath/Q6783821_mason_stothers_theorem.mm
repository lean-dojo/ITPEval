$(
  Statement-only formalization of Thousand Theorems corpus artifact Q6783821
  (thousand-theorems__metamath__Q6783821), catalog title "Mason-Stothers
  theorem": over an arbitrary field, three nonzero univariate polynomials
  that sum to zero, with the first two coprime, satisfy all three
  Mason-Stothers radical-degree bounds unless all three formal derivatives
  vanish. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q6783821Radical sends zero to one and otherwise is the product of the
  distinct monic irreducible divisors. This is the normalized polynomial
  radical used by the source. Q6783821Coprime is the polynomial-ring Bezout
  identity. On the nonzero polynomials occurring in the theorem, set.mm's
  deg1 agrees with the source's natural degree. All declarations below are
  unproved $a statement encodings; this root statement file contains no $p
  proof.
$)

$c Q6783821Factors Q6783821Radical Q6783821Coprime $.

q6783821-factors-syntax $a class ( Q6783821Factors F P ) $.
q6783821-radical-syntax $a class ( Q6783821Radical F P ) $.
q6783821-coprime-syntax $a wff ( Q6783821Coprime F A B ) $.

${
  $d F P q $.
  q6783821-factors-definition $a
    |- ( Q6783821Factors F P ) =
       { q e. ( Irred ` ( Poly1 ` F ) ) |
         ( ( ( coe1 ` q ) ` ( ( deg1 ` F ) ` q ) ) = ( 1r ` F )
           /\
           q ( ||r ` ( Poly1 ` F ) ) P ) } $.
$}

${
  $d F P q $.
  q6783821-radical-definition $a
    |- ( Q6783821Radical F P ) =
       if ( P = ( 0g ` ( Poly1 ` F ) ) ,
         ( 1r ` ( Poly1 ` F ) ) ,
         ( ( mulGrp ` ( Poly1 ` F ) ) gsum
           ( q e. ( Q6783821Factors F P ) |-> q ) ) ) $.
$}

${
  $d A B F U V $.
  q6783821-coprime-definition $a
    |- ( Q6783821Coprime F A B ) <->
       E. U e. ( Base ` ( Poly1 ` F ) )
       E. V e. ( Base ` ( Poly1 ` F ) )
       ( ( U ( .r ` ( Poly1 ` F ) ) A )
           ( +g ` ( Poly1 ` F ) )
           ( V ( .r ` ( Poly1 ` F ) ) B ) ) =
         ( 1r ` ( Poly1 ` F ) ) $.
$}

${
  $d A B C F $.
  q6783821-mason-stothers-theorem $a
    |- A. F e. Field
       A. A e. ( Base ` ( Poly1 ` F ) )
       A. B e. ( Base ` ( Poly1 ` F ) )
       A. C e. ( Base ` ( Poly1 ` F ) )
       ( ( A =/= ( 0g ` ( Poly1 ` F ) )
           /\
           ( B =/= ( 0g ` ( Poly1 ` F ) )
             /\
             ( C =/= ( 0g ` ( Poly1 ` F ) )
               /\
               ( ( Q6783821Coprime F A B )
                 /\
                 ( ( A ( +g ` ( Poly1 ` F ) ) B )
                     ( +g ` ( Poly1 ` F ) ) C ) =
                   ( 0g ` ( Poly1 ` F ) ) ) ) ) )
         ->
         ( ( ( ( ( deg1 ` F ) ` A ) + 1 ) <_
               ( ( deg1 ` F ) `
                 ( Q6783821Radical F
                   ( ( A ( .r ` ( Poly1 ` F ) ) B )
                     ( .r ` ( Poly1 ` F ) ) C ) ) )
               /\
               ( ( ( ( deg1 ` F ) ` B ) + 1 ) <_
                   ( ( deg1 ` F ) `
                     ( Q6783821Radical F
                       ( ( A ( .r ` ( Poly1 ` F ) ) B )
                         ( .r ` ( Poly1 ` F ) ) C ) ) )
                 /\
                 ( ( ( deg1 ` F ) ` C ) + 1 ) <_
                   ( ( deg1 ` F ) `
                     ( Q6783821Radical F
                       ( ( A ( .r ` ( Poly1 ` F ) ) B )
                         ( .r ` ( Poly1 ` F ) ) C ) ) ) ) )
             \/
             ( ( ( ( ( 1o mPSDer F ) ` (/) ) ` A ) =
                   ( 0g ` ( Poly1 ` F ) )
                 /\
                 ( ( ( ( 1o mPSDer F ) ` (/) ) ` B ) =
                     ( 0g ` ( Poly1 ` F ) )
                   /\
                   ( ( ( 1o mPSDer F ) ` (/) ) ` C ) =
                     ( 0g ` ( Poly1 ` F ) ) ) ) ) ) ) $.
$}
