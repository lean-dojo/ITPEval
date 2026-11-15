$(
  Statement-only formalization of Thousand Theorems corpus artifact Q791663
  (thousand-theorems__metamath__Q791663), "Beatty's theorem": conjugate
  real Beatty sequences complement one another, and for an irrational
  parameter their positive-index sequences partition the positive integers.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q791663Beatty r is the set of all floor(k r) for integer k.
  Q791663BeattyPrime r is the set of all ceiling(k r) - 1 for integer k.
  Q791663BeattyPos r restricts the first construction to positive integer k.

  For real r and s, the displayed condition
    1 < r /\ 1 / r + 1 / s = 1
  is equivalent to Lean's r.HolderConjugate s.  Irrationality of the real r
  is written r e/ QQ.  Complement in the first assertion is relative to ZZ,
  matching the source set complement on the integer type, and /_\ is SetMM's
  symmetric difference.

  The last two $a declarations are the unproved corpus statements
  compl_beattySeq and Irrational.beattySeq_symmDiff_beattySeq_pos.  All
  preceding $a declarations are syntax or explicit definitions, and this
  database contains no $p proof statement.
$)

$c Q791663Beatty Q791663BeattyPrime Q791663BeattyPos $.

q791663-beatty-syntax $a class ( Q791663Beatty r ) $.
q791663-beatty-prime-syntax $a class ( Q791663BeattyPrime r ) $.
q791663-beatty-pos-syntax $a class ( Q791663BeattyPos r ) $.

${
  $d k n r $.

  q791663-beatty-definition $a |- ( Q791663Beatty r ) =
    { n e. ZZ | E. k e. ZZ n = ( |_ ` ( k x. r ) ) } $.
$}

${
  $d k n r $.

  q791663-beatty-prime-definition $a |- ( Q791663BeattyPrime r ) =
    { n e. ZZ |
      E. k e. ZZ n = ( ( |^ ` ( k x. r ) ) - 1 ) } $.
$}

${
  $d k n r $.

  q791663-beatty-pos-definition $a |- ( Q791663BeattyPos r ) =
    { n e. ZZ |
      E. k e. ZZ
        ( 0 < k /\ n = ( |_ ` ( k x. r ) ) ) } $.
$}

${
  $d r s $.

  thousand-theorems-q791663-compl-beatty-seq $a |- A. r e. RR
    A. s e. RR
      (
        (
          1 < r
          /\
          ( ( 1 / r ) + ( 1 / s ) ) = 1
        )
        ->
        ( ZZ \ ( Q791663Beatty r ) ) = ( Q791663BeattyPrime s )
      ) $.
$}

${
  $d r s $.

  thousand-theorems-q791663-beatty-seq-symmetric-difference-pos $a
    |- A. r e. RR
      A. s e. RR
        (
          (
            (
              1 < r
              /\
              ( ( 1 / r ) + ( 1 / s ) ) = 1
            )
            /\
            r e/ QQ
          )
          ->
          (
            ( ( Q791663BeattyPos r ) /_\ ( Q791663BeattyPos s ) )
            =
            NN
          )
        ) $.
$}
