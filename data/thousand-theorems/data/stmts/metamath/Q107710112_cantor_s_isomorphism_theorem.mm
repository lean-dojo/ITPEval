$(
  Statement-only formalization of Thousand Theorems corpus artifact Q107710112
  (thousand-theorems__metamath__Q107710112), "Cantor's isomorphism theorem":
  any two countable, dense, nonempty linear orders without endpoints are order
  isomorphic. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary Lean types are represented by set carriers a and b, with
  strict total-order relations r and s. Countability is expressed by injections
  into omega. Density and the absence of minimum and maximum elements are
  stated explicitly over each carrier.

  SetMM's predicate f Isom r , s ( a , b ) says that f is a bijection from a
  onto b and preserves and reflects the two relations. The witness f remains
  existentially quantified in the conclusion. The final declaration is the
  single unproved corpus $a statement, and this file has no $p statement.
$)

${
  $d a b f r s x y z $.

  thousand-theorems-q107710112-cantor-isomorphism $a |- (
    A. a A. b A. r A. s
      (
        (
          (
            a ~<_ _om
            /\
            b ~<_ _om
          )
          /\
          (
            (
              a =/= ( / )
              /\
              r Or a
            )
            /\
            (
              (
                A. x e. a A. y e. a
                  (
                    x r y
                    ->
                    E. z e. a
                      (
                        x r z
                        /\
                        z r y
                      )
                  )
                /\
                A. x e. a E. y e. a y r x
              )
              /\
              A. x e. a E. y e. a x r y
            )
          )
          /\
          (
            (
              b =/= ( / )
              /\
              s Or b
            )
            /\
            (
              (
                A. x e. b A. y e. b
                  (
                    x s y
                    ->
                    E. z e. b
                      (
                        x s z
                        /\
                        z s y
                      )
                  )
                /\
                A. x e. b E. y e. b y s x
              )
              /\
              A. x e. b E. y e. b x s y
            )
          )
        )
        ->
        E. f f Isom r , s ( a , b )
      )
  ) $.
$}
