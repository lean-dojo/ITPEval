$(
  Statement-only formalization of Thousand Theorems corpus artifact Q5638886
  (thousand-theorems__metamath__Q5638886), "Hahn embedding theorem": every
  linearly ordered abelian group admits an injective order-preserving additive
  homomorphism into the lexicographically ordered group of real Hahn series
  indexed by its finite Archimedean classes, with each element's class equal
  to the least support index of its image. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  G e. Abel and G e. oGrp retain the arbitrary bundled linearly ordered
  abelian group of the Lean statement. Q5638886Abs and Q5638886NatMul use
  G's actual inverse and addition operations. Q5638886Dominates G a b says
  that |b| is bounded above by a natural multiple of |a|. The symmetric
  closure Q5638886ArchEq is Archimedean equivalence, and
  Q5638886ArchClass G a is the actual equivalence-class subset of Base ` G.

  Q5638886FiniteClasses G is exactly the set of Archimedean classes having a
  nonzero representative. Q5638886ClassLe uses the standard reverse-growth
  order: [a] <= [b] when |b| is bounded by a natural multiple of |a|.

  Q5638886Hahn G is the full set of real-valued functions on those classes
  whose support is well-ordered by the strict class order. This is the
  linearly ordered version of Hahn series' partially well-ordered support.
  Q5638886LexLe is the lexicographic order obtained at the least differing
  index. Q5638886Embedding requires an actual injective function preserving
  G-addition and this order.

  Q5638886TopClass expresses the source equality with HahnSeries.orderTop
  through its defining cases: zero maps to the zero series, while a nonzero
  element's Archimedean class is the least support index of its image. Thus
  the finite-class subtype and WithTop order isomorphism are represented
  without changing their mathematical content.

  Every declaration before the final one is syntax or a bidirectional
  definition. The final $a declaration is the single unproved corpus
  statement. There is no $p proof statement in this file.
$)

$c Q5638886Abs Q5638886NatMul Q5638886Dominates Q5638886ArchEq
   Q5638886ArchClass Q5638886FiniteClasses Q5638886ClassLe
   Q5638886ClassLtRel Q5638886Support Q5638886Hahn Q5638886Zero
   Q5638886Add Q5638886LexLe Q5638886Embedding Q5638886TopClass $.

q5638886-abs-syntax
  $a class ( Q5638886Abs G a ) $.
q5638886-nat-mul-syntax
  $a class ( Q5638886NatMul G n a ) $.
q5638886-dominates-syntax
  $a wff ( Q5638886Dominates G a b ) $.
q5638886-arch-eq-syntax
  $a wff ( Q5638886ArchEq G a b ) $.
q5638886-arch-class-syntax
  $a class ( Q5638886ArchClass G a ) $.
q5638886-finite-classes-syntax
  $a class ( Q5638886FiniteClasses G ) $.
q5638886-class-le-syntax
  $a wff ( Q5638886ClassLe G C D ) $.
q5638886-class-lt-rel-syntax
  $a class ( Q5638886ClassLtRel G ) $.
q5638886-support-syntax
  $a class ( Q5638886Support G s ) $.
q5638886-hahn-syntax
  $a class ( Q5638886Hahn G ) $.
q5638886-zero-syntax
  $a class ( Q5638886Zero G ) $.
q5638886-add-syntax
  $a class ( Q5638886Add G s t ) $.
q5638886-lex-le-syntax
  $a wff ( Q5638886LexLe G s t ) $.
q5638886-embedding-syntax
  $a wff ( Q5638886Embedding G f ) $.
q5638886-top-class-syntax
  $a wff ( Q5638886TopClass G a s ) $.

${
  $d G a $.

  q5638886-abs-definition $a |- (
    Q5638886Abs G a
  ) = if (
    a ( le ` G ) ( 0g ` G ) ,
    ( ( -g ` G ) ` a ) ,
    a
  ) $.
$}

${
  $d G a k n $.

  q5638886-nat-mul-definition $a |- (
    Q5638886NatMul G n a
  ) = (
    G gsum ( k e. ( 1 ... n ) |-> a )
  ) $.
$}

${
  $d G a b n $.

  q5638886-dominates-definition $a |- (
    ( Q5638886Dominates G a b )
    <->
    E. n e. NN0
      (
        ( Q5638886Abs G b )
        ( le ` G )
        ( Q5638886NatMul G n ( Q5638886Abs G a ) )
      )
  ) $.
$}

${
  $d G a b $.

  q5638886-arch-eq-definition $a |- (
    ( Q5638886ArchEq G a b )
    <->
    (
      ( Q5638886Dominates G a b )
      /\
      ( Q5638886Dominates G b a )
    )
  ) $.
$}

${
  $d G a b $.

  q5638886-arch-class-definition $a |- (
    Q5638886ArchClass G a
  ) = {
    b e. ( Base ` G ) |
      ( Q5638886ArchEq G a b )
  } $.
$}

${
  $d G a c $.

  q5638886-finite-classes-definition $a |- (
    Q5638886FiniteClasses G
  ) = {
    c e. ~P ( Base ` G ) |
      E. a e. ( Base ` G )
        (
          a =/= ( 0g ` G )
          /\
          c = ( Q5638886ArchClass G a )
        )
  } $.
$}

${
  $d C D G a b $.

  q5638886-class-le-definition $a |- (
    ( Q5638886ClassLe G C D )
    <->
    E. a e. C E. b e. D
      ( Q5638886Dominates G a b )
  ) $.
$}

${
  $d G c d p $.

  q5638886-class-lt-rel-definition $a |- (
    Q5638886ClassLtRel G
  ) = {
    p e.
      (
        ( Q5638886FiniteClasses G )
        X.
        ( Q5638886FiniteClasses G )
      ) |
      E. c e. ( Q5638886FiniteClasses G )
        E. d e. ( Q5638886FiniteClasses G )
          (
            p = <. c , d >.
            /\
            (
              ( Q5638886ClassLe G c d )
              /\
              c =/= d
            )
          )
  } $.
$}

${
  $d G c s $.

  q5638886-support-definition $a |- (
    Q5638886Support G s
  ) = {
    c e. ( Q5638886FiniteClasses G ) |
      ( s ` c ) =/= 0
  } $.
$}

${
  $d G s $.

  q5638886-hahn-definition $a |- (
    Q5638886Hahn G
  ) = {
    s e. ( RR ^m ( Q5638886FiniteClasses G ) ) |
      ( Q5638886ClassLtRel G ) We ( Q5638886Support G s )
  } $.
$}

${
  $d G c $.

  q5638886-zero-definition $a |- (
    Q5638886Zero G
  ) = (
    c e. ( Q5638886FiniteClasses G ) |-> 0
  ) $.
$}

${
  $d G c s t $.

  q5638886-add-definition $a |- (
    Q5638886Add G s t
  ) = (
    c e. ( Q5638886FiniteClasses G ) |->
      ( ( s ` c ) + ( t ` c ) )
  ) $.
$}

${
  $d G c d s t $.

  q5638886-lex-le-definition $a |- (
    ( Q5638886LexLe G s t )
    <->
    (
      s = t
      \/
      E. c e. ( Q5638886FiniteClasses G )
        (
          ( s ` c ) < ( t ` c )
          /\
          A. d e. ( Q5638886FiniteClasses G )
            (
              d ( Q5638886ClassLtRel G ) c
              ->
              ( s ` d ) = ( t ` d )
            )
        )
    )
  ) $.
$}

${
  $d G a b f $.

  q5638886-embedding-definition $a |- (
    ( Q5638886Embedding G f )
    <->
    (
      f
        : ( Base ` G )
        -1-1->
        ( Q5638886Hahn G )
      /\
      (
        A. a e. ( Base ` G ) A. b e. ( Base ` G )
          (
            f ` ( a ( +g ` G ) b )
          )
          =
          (
            Q5638886Add G ( f ` a ) ( f ` b )
          )
        /\
        A. a e. ( Base ` G ) A. b e. ( Base ` G )
          (
            a ( le ` G ) b
            ->
            ( Q5638886LexLe G ( f ` a ) ( f ` b ) )
          )
      )
    )
  ) $.
$}

${
  $d G a c s $.

  q5638886-top-class-definition $a |- (
    ( Q5638886TopClass G a s )
    <->
    (
      (
        a = ( 0g ` G )
        /\
        s = ( Q5638886Zero G )
      )
      \/
      (
        a =/= ( 0g ` G )
        /\
        (
          ( Q5638886ArchClass G a )
            e. ( Q5638886Support G s )
          /\
          A. c e. ( Q5638886Support G s )
            (
              Q5638886ClassLe
                G
                ( Q5638886ArchClass G a )
                c
            )
        )
      )
    )
  ) $.
$}

${
  $d a f g $.

  thousand-theorems-q5638886-hahn-embedding $a |-
    A. g
      (
        (
          g e. Abel
          /\
          g e. oGrp
        )
        ->
        E. f
          (
            ( Q5638886Embedding g f )
            /\
            A. a e. ( Base ` g )
              ( Q5638886TopClass g a ( f ` a ) )
          )
      )
  $.
$}
