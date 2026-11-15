(* ========================================================================= *)
(* The Cayley-Hamilton theorem (for real matrices).                          *)
(* ========================================================================= *)

needs "Multivariate/complexes.ml";;
needs "Multivariate/msum.ml";;

(* ------------------------------------------------------------------------- *)
(* Powers of a square matrix (mpow).                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("mpow",(24,"left"));;

let mpow = define
  `(!A:real^N^N. A mpow 0 = (mat 1 :real^N^N)) /\
   (!A:real^N^N n. A mpow (SUC n) = A ** A mpow n)`;;

let MPOW_ADD = `!A:real^N^N m n. A mpow (m + n) = A mpow m ** A mpow n`;;

let MPOW_1 = `!A:real^N^N. A mpow 1 = A`;;

let MPOW_SUC = `!A:real^N^N n. A mpow (SUC n) = A mpow n ** A`;;

(* ------------------------------------------------------------------------- *)
(* The main lemma underlying the proof.                                      *)
(* ------------------------------------------------------------------------- *)

let MATRIC_POLYFUN_EQ_0 = `!n A:num->real^N^M.
        (!x. msum(0..n) (\i. x pow i %% A i) = mat 0) <=>
        (!i. i IN 0..n ==> A i = mat 0)`;;

let MATRIC_POLY_LEMMA = `!(A:real^N^N) B (C:real^N^N) n.
        (!x. msum (0..n) (\i. (x pow i) %% B i) ** (A - x %% mat 1) = C)
        ==> C = mat 0`;;

(* ------------------------------------------------------------------------- *)
(* Show that cofactor and determinant are n-1 and n degree polynomials.      *)
(* ------------------------------------------------------------------------- *)

let POLYFUN_N_CONST = `!c n. ?b. !x. c = sum(0..n) (\i. b i * x pow i)`;;

let POLYFUN_N_ADD = `!f g. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i)) /\
         (?c. !x. g(x) = sum(0..n) (\i. c i * x pow i))
         ==> ?d. !x. f(x) + g(x) = sum(0..n) (\i. d i * x pow i)`;;

let POLYFUN_N_CMUL = `!f c. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. c * f(x) = sum(0..n) (\i. b i * x pow i)`;;

let POLYFUN_N_SUM = `!f s. FINITE s /\
         (!a. a IN s ==> ?b. !x. f x a = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. sum s (f x) = sum(0..n) (\i. b i * x pow i)`;;

let POLYFUN_N_PRODUCT = `!f s n. FINITE s /\
           (!a:A. a IN s ==> ?c d. !x. f x a = c + d * x) /\ CARD(s) <= n
           ==> ?b. !x. product s (f x) = sum(0..n) (\i. b i * x pow i)`;;

let COFACTOR_ENTRY_AS_POLYFUN = `!A:real^N^N x i j.
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N)
        ==> ?c. !x. cofactor(A - x %% mat 1)$i$j =
                    sum(0..dimindex(:N)-1) (\i. c(i) * x pow i)`;;

let DETERMINANT_AS_POLYFUN = `!A:real^N^N.
        ?c. !x. det(A - x %% mat 1) =
                sum(0..dimindex(:N)) (\i. c(i) * x pow i)`;;

(* ------------------------------------------------------------------------- *)
(* Hence define characteristic polynomial coefficients.                      *)
(* ------------------------------------------------------------------------- *)

let char_poly = new_specification ["char_poly"]
  (REWRITE_RULE[SKOLEM_THM] DETERMINANT_AS_POLYFUN);;

(* ------------------------------------------------------------------------- *)
(* Now the Cayley-Hamilton proof.                                            *)
(* ------------------------------------------------------------------------- *)

let COFACTOR_AS_MATRIC_POLYNOMIAL = `!A:real^N^N. ?C.
      !x. cofactor(A - x %% mat 1) =
          msum(0..dimindex(:N)-1) (\i. x pow i %% C i)`;;

let MATRIC_POWER_DIFFERENCE = `!A:real^N^N x n.
        A mpow (SUC n) - x pow (SUC n) %% mat 1 =
        msum (0..n) (\i. x pow i %% A mpow (n - i)) ** (A - x %% mat 1)`;;

let MATRIC_CHARPOLY_DIFFERENCE = `!A:real^N^N. ?B.
      !x. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) -
          sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1 =
          msum(0..(dimindex(:N)-1)) (\i. x pow i %% B i) ** (A - x %% mat 1)`;;

let CAYLEY_HAMILTON = `!A:real^N^N. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) = mat 0`;;
