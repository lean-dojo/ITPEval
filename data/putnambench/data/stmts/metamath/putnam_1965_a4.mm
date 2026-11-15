$(
  Statement-only formalization of PutnamBench artifact putnam_1965_a4:
  a finite bipartite dance relation in which every girl has a partner but no
  boy dances with every girl contains two crossed related and unrelated
  pairs. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  G and B are arbitrary finite nonempty sets, and D is an arbitrary relation
  from G to B. Membership of <. g , b >. in D represents that g dances with
  b. The hypothesis and conclusion preserve the source quantifier scopes.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d B D G b c g h $.

  putnambench-putnam-1965-a4 $a |- A. G e. Fin
    A. B e. Fin
      A. D e. ~P ( G X. B )
        (
          (
            (
              G =/= (/)
              /\
              B =/= (/)
            )
            /\
            (
              (
                -. E. b e. B A. g e. G <. g , b >. e. D
              )
              /\
              A. g e. G E. b e. B <. g , b >. e. D
            )
          )
          ->
          E. g e. G E. h e. G E. b e. B E. c e. B
            (
              <. g , b >. e. D
              /\
              (
                <. h , c >. e. D
                /\
                (
                  -. <. h , b >. e. D
                  /\
                  -. <. g , c >. e. D
                )
              )
            )
        )
  $.
$}
