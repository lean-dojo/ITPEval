$(
  Statement-only formalization of Thousand Theorems corpus artifact Q510197
  (thousand-theorems__metamath__Q510197), "Tutte theorem": a finite simple
  graph has a perfect matching if and only if deleting any vertex subset
  leaves at most that many connected components of odd cardinality. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Finite Lean vertex types are represented by arbitrary finite sets V.
  Q510197SimpleGraph says that G is an irreflexive symmetric relation on V.
  Q510197PerfectMatching says that M is a simple subgraph of G in which every
  vertex has exactly one M-neighbor, exactly matching a spanning perfect
  matching.

  Q510197Deleted is the edge relation induced on V \ U. Q510197Component is
  the set of vertices equal to, or reachable by a nonempty finite G-path from,
  a root after deleting U. Q510197OddComponents collects these component sets
  extensionally, so roots in the same component do not create duplicates.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful bidirectional definitions.
  This file introduces no $p proof statement.
$)

$c Q510197SimpleGraph Q510197PerfectMatching Q510197Deleted
   Q510197Component Q510197OddComponents $.

q510197-simple-graph-syntax $a
  wff ( Q510197SimpleGraph V G ) $.
q510197-perfect-matching-syntax $a
  wff ( Q510197PerfectMatching V G M ) $.
q510197-deleted-syntax $a
  class ( Q510197Deleted V G U ) $.
q510197-component-syntax $a
  class ( Q510197Component V G U x ) $.
q510197-odd-components-syntax $a
  class ( Q510197OddComponents V G U ) $.

${
  $d G V u v $.

  q510197-simple-graph-definition $a |- (
    ( Q510197SimpleGraph V G )
    <->
    (
      G C_ ( V X. V )
      /\
      (
        A. u e. V -. <. u , u >. e. G
        /\
        A. u e. V A. v e. V
          ( <. u , v >. e. G <-> <. v , u >. e. G )
      )
    )
  ) $.
$}

${
  $d G M V u v $.

  q510197-perfect-matching-definition $a |- (
    ( Q510197PerfectMatching V G M )
    <->
    (
      M C_ G
      /\
      (
        ( Q510197SimpleGraph V M )
        /\
        A. u e. V E! v e. V <. u , v >. e. M
      )
    )
  ) $.
$}

${
  $d G U V $.

  q510197-deleted-definition $a |- (
    ( Q510197Deleted V G U )
    =
    (
      G
      i^i
      ( ( V \ U ) X. ( V \ U ) )
    )
  ) $.
$}

${
  $d G U V x y $.

  q510197-component-definition $a |- (
    ( Q510197Component V G U x )
    =
    { y e. ( V \ U ) |
      x
        (
          ( t+ ` ( Q510197Deleted V G U ) )
          u.
          _I
        )
        y
    }
  ) $.
$}

${
  $d C G U V x $.

  q510197-odd-components-definition $a |- (
    ( Q510197OddComponents V G U )
    =
    { C e. ~P ( V \ U ) |
      E. x e. ( V \ U )
        (
          C = ( Q510197Component V G U x )
          /\
          ( # ` C ) e. Odd
        )
    }
  ) $.
$}

${
  $d G M U V $.

  thousand-theorems-q510197-tutte $a |- (
    A. V A. G
      (
        (
          V e. Fin
          /\
          ( Q510197SimpleGraph V G )
        )
        ->
        (
          E. M ( Q510197PerfectMatching V G M )
          <->
          A. U e. ~P V
            -.
            ( # ` U )
            <
            ( # ` ( Q510197OddComponents V G U ) )
        )
      )
  ) $.
$}
