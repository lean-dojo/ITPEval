$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1660147
  (thousand-theorems__metamath__Q1660147), "Mazur&ndash;Ulam theorem": every
  isometric equivalence between arbitrary real normed affine spaces is an
  affine isometry equivalence with the same underlying isometry. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  E and F range over SetMM normed vector spaces over RRfld. The arbitrary
  point carriers P and Q, together with A,D and B,C, respectively, present
  normed additive torsors: A and B are vector additions on points, while D
  and C are point differences. Their induced distances are the norms of point
  differences.

  Q1660147IsometryEquiv states that f and g are mutually inverse maps and that
  f preserves every induced distance. Q1660147LinearIsometryEquiv states that
  L and M are mutually inverse real-linear maps and that L preserves norms.
  The conclusion keeps L and M internally existentially quantified and adds
  the affine compatibility equation for the original map f. This is exactly
  the data of a real affine isometry equivalence whose underlying isometry
  equivalence is f (and hence has inverse g), matching the source equality
  `toRealAffineIsometryEquiv.toIsometryEquiv = f`.

  Every declaration before the final one is syntax or a faithful
  bidirectional definition. The final $a declaration is the single unproved
  corpus statement, and this database contains no $p proof statement.
$)

$c Q1660147NormedAddTorsor Q1660147IsometryEquiv
   Q1660147LinearIsometryEquiv Q1660147AffineCompatible $.

q1660147-normed-add-torsor-syntax
  $a wff ( Q1660147NormedAddTorsor E P A D ) $.
q1660147-isometry-equiv-syntax
  $a wff ( Q1660147IsometryEquiv E P D F Q C f g ) $.
q1660147-linear-isometry-equiv-syntax
  $a wff ( Q1660147LinearIsometryEquiv E F L M ) $.
q1660147-affine-compatible-syntax
  $a wff ( Q1660147AffineCompatible E P A F Q B f L ) $.

${
  $d A D E P p q u v $.

  q1660147-normed-add-torsor-definition $a |- (
    ( Q1660147NormedAddTorsor E P A D )
    <->
    (
      P =/= (/)
      /\
      A : ( ( Base ` E ) X. P ) --> P
      /\
      D : ( P X. P ) --> ( Base ` E )
      /\
      A. p e. P
        ( A ` <. ( 0g ` E ) , p >. ) = p
      /\
      A. u e. ( Base ` E )
        A. v e. ( Base ` E )
          A. p e. P
            (
              A
              `
              <. ( u ( +g ` E ) v ) , p >.
            )
            =
            (
              A
              `
              <. u , ( A ` <. v , p >. ) >.
            )
      /\
      A. p e. P
        A. q e. P
          (
            A
            `
            <. ( D ` <. p , q >. ) , q >.
          )
          =
          p
      /\
      A. v e. ( Base ` E )
        A. p e. P
          (
            D
            `
            <. ( A ` <. v , p >. ) , p >.
          )
          =
          v
    )
  ) $.
$}

${
  $d C D E F P Q f g p q r $.

  q1660147-isometry-equiv-definition $a |- (
    ( Q1660147IsometryEquiv E P D F Q C f g )
    <->
    (
      f : P -1-1-onto-> Q
      /\
      g : Q -1-1-onto-> P
      /\
      A. p e. P ( g ` ( f ` p ) ) = p
      /\
      A. r e. Q ( f ` ( g ` r ) ) = r
      /\
      A. p e. P
        A. q e. P
          (
            ( norm ` F )
            `
            (
              C
              `
              <. ( f ` p ) , ( f ` q ) >.
            )
          )
          =
          (
            ( norm ` E )
            `
            ( D ` <. p , q >. )
          )
    )
  ) $.
$}

${
  $d E F L M x y $.

  q1660147-linear-isometry-equiv-definition $a |- (
    ( Q1660147LinearIsometryEquiv E F L M )
    <->
    (
      L e. ( E LMHom F )
      /\
      M e. ( F LMHom E )
      /\
      A. x e. ( Base ` E )
        ( M ` ( L ` x ) ) = x
      /\
      A. y e. ( Base ` F )
        ( L ` ( M ` y ) ) = y
      /\
      A. x e. ( Base ` E )
        (
          ( norm ` F )
          `
          ( L ` x )
        )
        =
        ( ( norm ` E ) ` x )
    )
  ) $.
$}

${
  $d A B E F L P Q f p v $.

  q1660147-affine-compatible-definition $a |- (
    ( Q1660147AffineCompatible E P A F Q B f L )
    <->
    A. v e. ( Base ` E )
      A. p e. P
        (
          f
          `
          ( A ` <. v , p >. )
        )
        =
        (
          B
          `
          <. ( L ` v ) , ( f ` p ) >.
        )
  ) $.
$}

${
  $d A B C D E F L M P Q f g e h $.

  thousand-theorems-q1660147-mazur-ulam-theorem $a |-
    A. E e. { e e. NrmVec | ( Scalar ` e ) = RRfld }
      A. F e. { h e. NrmVec | ( Scalar ` h ) = RRfld }
        A. P A. Q A. A A. D A. B A. C A. f A. g
          (
            (
              ( Q1660147NormedAddTorsor E P A D )
              /\
              ( Q1660147NormedAddTorsor F Q B C )
              /\
              ( Q1660147IsometryEquiv E P D F Q C f g )
            )
            ->
            E. L E. M
              (
                ( Q1660147LinearIsometryEquiv E F L M )
                /\
                ( Q1660147AffineCompatible E P A F Q B f L )
              )
          )
  $.
$}
