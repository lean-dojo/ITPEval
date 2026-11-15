(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a3:
  the universal assertion that every assignment of subsets of six courses to
  twenty students has five students and two courses uniformly chosen or
  uniformly omitted, stated as equivalent to false. This file contains no
  proof.
*)

let statement =
  `let students20 = {s:num | s < 20} in
   let courses6 = {c:num | c < 6} in
   let putnam_1996_a3_solution = F in
   ((!choices:num->num->bool.
       (!s:num. s IN students20 ==> choices s SUBSET courses6)
       ==> ?students courses.
             students SUBSET students20 /\
             students HAS_SIZE 5 /\
             courses SUBSET courses6 /\
             courses HAS_SIZE 2 /\
             ((!s:num.
                  s IN students ==> courses SUBSET choices s) \/
              (!s:num.
                  s IN students
                  ==> courses SUBSET (courses6 DIFF choices s))))
    <=> putnam_1996_a3_solution)`;;
