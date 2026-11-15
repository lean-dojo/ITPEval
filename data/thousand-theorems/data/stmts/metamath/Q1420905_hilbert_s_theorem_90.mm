$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1420905
  (thousand-theorems__metamath__Q1420905), "Hilbert's theorem 90": in a
  finite-dimensional cyclic Galois field extension, every element of norm one
  is y divided by its image under a chosen generator, for some nonzero unit y.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  k and l are arbitrary fields and f e. ( k RingHom l ) is the algebra map.
  Q1420905ExtensionModule is l as a k-vector space, and
  Q1420905FiniteDimensional says that it has a finite basis.

  Q1420905Automorphisms is the set of all bijective ring endomorphisms of L
  that fix F pointwise. Restricting the symmetric group of Base ` L to this
  set gives the full K-algebra automorphism group. In a finite-dimensional
  field extension, finiteness of this group and equality of its cardinality
  with the dimension is equivalent to the source IsGalois K L hypothesis.

  Under that Galois hypothesis, Algebra.norm K x = 1 is equivalent, by the
  Galois product formula and injectivity of F, to the product of all conjugates
  s(x) being 1 in L. Q1420905Norm is this product. Q1420905Generates states
  exactly that every automorphism is an integral power of g. The witness stays
  existentially quantified in the conclusion and lies in Unit ` L.

  All auxiliary $a declarations below are syntax or transparent definitions.
  The final $a declaration is the unproved corpus statement; there is no $p
  proof statement in this file.
$)

$c Q1420905ExtensionModule Q1420905FiniteDimensional
   Q1420905Automorphisms Q1420905GaloisGroup Q1420905IsGalois
   Q1420905Generates Q1420905Norm $.

q1420905-extension-module-syntax $a class
  ( Q1420905ExtensionModule K L F ) $.
q1420905-finite-dimensional-syntax $a wff
  ( Q1420905FiniteDimensional K L F ) $.
q1420905-automorphisms-syntax $a class
  ( Q1420905Automorphisms K L F ) $.
q1420905-galois-group-syntax $a class
  ( Q1420905GaloisGroup K L F ) $.
q1420905-is-galois-syntax $a wff
  ( Q1420905IsGalois K L F ) $.
q1420905-generates-syntax $a wff
  ( Q1420905Generates K L F g ) $.
q1420905-norm-syntax $a class
  ( Q1420905Norm K L F x ) $.

${
  $d F K L a x $.

  q1420905-extension-module-definition $a |- (
    Q1420905ExtensionModule K L F
  ) = (
    {
      <. ( Base ` ndx ) , ( Base ` L ) >. ,
      <. ( +g ` ndx ) , ( +g ` L ) >. ,
      <. ( Scalar ` ndx ) , K >.
    }
    u.
    {
      <.
        ( .s ` ndx ) ,
        (
          a e. ( Base ` K ) ,
          x e. ( Base ` L )
          |->
          ( ( F ` a ) ( .r ` L ) x )
        )
      >.
    }
  ) $.
$}

${
  $d F K L b $.

  q1420905-finite-dimensional-definition $a |- (
    Q1420905FiniteDimensional K L F
  ) <->
  (
    E. b e. ( LBasis ` ( Q1420905ExtensionModule K L F ) )
      b e. Fin
  ) $.
$}

${
  $d F K L s $.

  q1420905-automorphisms-definition $a |- (
    Q1420905Automorphisms K L F
  ) = {
    s e. ( L RingHom L ) |
    (
      s : ( Base ` L ) -1-1-onto-> ( Base ` L )
      /\
      ( s o. F ) = F
    )
  } $.
$}

${
  q1420905-galois-group-definition $a |- (
    Q1420905GaloisGroup K L F
  ) = (
    ( SymGrp ` ( Base ` L ) )
    |`s
    ( Q1420905Automorphisms K L F )
  ) $.
$}

${
  $d F K L b $.

  q1420905-is-galois-definition $a |- (
    Q1420905IsGalois K L F
  ) <->
  (
    ( Q1420905Automorphisms K L F ) e. Fin
    /\
    A. b e. ( LBasis ` ( Q1420905ExtensionModule K L F ) )
      (
        b e. Fin
        ->
        ( # ` ( Q1420905Automorphisms K L F ) ) = ( # ` b )
      )
  ) $.
$}

${
  $d F K L g n $.

  q1420905-generates-definition $a |- (
    Q1420905Generates K L F g
  ) <->
  (
    g e. ( Base ` ( Q1420905GaloisGroup K L F ) )
    /\
    ran
      (
        n e. ZZ
        |->
        (
          n
          ( .g ` ( Q1420905GaloisGroup K L F ) )
          g
        )
      )
      =
      ( Base ` ( Q1420905GaloisGroup K L F ) )
  ) $.
$}

${
  $d F K L s x $.

  q1420905-norm-definition $a |- (
    Q1420905Norm K L F x
  ) = (
    ( mulGrp ` L )
    gsum
    (
      s e. ( Q1420905Automorphisms K L F )
      |->
      ( s ` x )
    )
  ) $.
$}

${
  $d f g k l x y $.

  thousand-theorems-q1420905-hilbert-s-theorem-90 $a |- (
    A. k e. Field
      A. l e. Field
        A. f e. ( k RingHom l )
          (
            (
              ( Q1420905FiniteDimensional k l f )
              /\
              ( Q1420905IsGalois k l f )
              /\
              ( Q1420905GaloisGroup k l f ) e. CycGrp
            )
            ->
            A. g e. ( Base ` ( Q1420905GaloisGroup k l f ) )
              (
                ( Q1420905Generates k l f g )
                ->
                A. x e. ( Base ` l )
                  (
                    ( Q1420905Norm k l f x ) = ( 1r ` l )
                    ->
                    E. y e. ( Unit ` l )
                      (
                        y
                        ( /r ` l )
                        ( g ` y )
                      )
                      =
                      x
                  )
              )
          )
  ) $.
$}
