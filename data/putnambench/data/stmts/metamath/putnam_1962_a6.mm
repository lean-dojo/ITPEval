$(
  Statement-only formalization of PutnamBench artifact putnam_1962_a6:
  a rational set closed under addition and multiplication, and choosing
  exactly one of each nonzero rational and its negative, is the set of
  positive rationals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The subset hypothesis represents the source type S : Set Q. The three
  pairwise exclusions, together with exhaustiveness, state that exactly one
  of r in S, -r in S, and r = 0 holds for every rational r. The final
  declaration is an unproved $a statement; this database has no $p statements.
$)

${
  $d a b r S $.

  putnambench-putnam-1962-a6 $a |- A. S
    (
      (
        S C_ QQ
        /\
        (
          A. a e. S A. b e. S ( a + b ) e. S
          /\
          (
            A. a e. S A. b e. S ( a x. b ) e. S
            /\
            A. r e. QQ
              (
                (
                  (
                    ( r e. S \/ ( -u r ) e. S )
                    \/
                    r = 0
                  )
                  /\
                  -. ( r e. S /\ ( -u r ) e. S )
                )
                /\
                (
                  -. ( r e. S /\ r = 0 )
                  /\
                  -. ( ( -u r ) e. S /\ r = 0 )
                )
              )
          )
        )
      )
      ->
      S = { r e. QQ | 0 < r }
    )
  $.
$}
