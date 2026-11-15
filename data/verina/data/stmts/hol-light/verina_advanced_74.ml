(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_74,
  catalog title "solution": an executable natural-number computation sums the
  squares of the numbers of distinct elements in every nonempty contiguous
  subarray, together with its bounded-input precondition and correctness
  contract. This file contains no proof.
*)

let solution_precond = new_definition
  `solution_precond (nums:num list) <=>
     1 <= LENGTH nums /\
     LENGTH nums <= 100 /\
     ALL (\x:num. 1 <= x /\ x <= 100) nums`;;

let solution_range =
  new_recursive_definition num_RECURSION
    `(solution_range 0 = []) /\
     (!n:num.
        solution_range (SUC n) =
        APPEND (solution_range n) (CONS n []))`;;

let solution_drop =
  new_recursive_definition num_RECURSION
    `(!nums:num list.
        solution_drop 0 nums = nums) /\
     (!n:num. !nums:num list.
        solution_drop (SUC n) nums =
        if nums = [] then []
        else solution_drop n (TL nums))`;;

let solution_take =
  new_recursive_definition num_RECURSION
    `(!nums:num list.
        solution_take 0 nums = []) /\
     (!n:num. !nums:num list.
        solution_take (SUC n) nums =
        if nums = [] then []
        else CONS (HD nums) (solution_take n (TL nums)))`;;

let solution_subarray = new_definition
  `solution_subarray
      (nums:num list) (i:num) (j:num) =
     solution_take (j - i + 1) (solution_drop i nums)`;;

let solution_hashSetFold =
  new_recursive_definition list_RECURSION
    `(!seen:num list.
        solution_hashSetFold ([]:num list) seen = seen) /\
     (!x:num. !xs:num list. !seen:num list.
        solution_hashSetFold (CONS x xs) seen =
        solution_hashSetFold xs
          (if MEM x seen then seen
           else APPEND seen (CONS x [])))`;;

let solution_distinctCount = new_definition
  `solution_distinctCount (l:num list) =
     LENGTH (solution_hashSetFold l [])`;;

let solution_innerFold =
  new_recursive_definition list_RECURSION
    `(!nums:num list. !i:num. !acc:num.
        solution_innerFold nums i ([]:num list) acc = acc) /\
     (!d:num. !ds:num list. !nums:num list. !i:num. !acc:num.
        solution_innerFold nums i (CONS d ds) acc =
        let j = i + d in
        let subarr = solution_subarray nums i j in
        let cnt = solution_distinctCount subarr in
        solution_innerFold nums i ds (acc + cnt * cnt))`;;

let solution_outerFold =
  new_recursive_definition list_RECURSION
    `(!nums:num list. !acc:num.
        solution_outerFold nums ([]:num list) acc = acc) /\
     (!i:num. !is:num list. !nums:num list. !acc:num.
        solution_outerFold nums (CONS i is) acc =
        let innerSum =
          solution_innerFold nums i
            (solution_range (LENGTH nums - i)) 0 in
        solution_outerFold nums is (acc + innerSum))`;;

let solution = new_definition
  `solution (nums:num list) =
     let n = LENGTH nums in
     solution_outerFold nums (solution_range n) 0`;;

let solution_seenFold =
  new_recursive_definition list_RECURSION
    `(!seen:num list.
        solution_seenFold ([]:num list) seen = seen) /\
     (!x:num. !xs:num list. !seen:num list.
        solution_seenFold (CONS x xs) seen =
        solution_seenFold xs
          (if MEM x seen then seen else CONS x seen))`;;

let solution_expectedDistinctCount = new_definition
  `solution_expectedDistinctCount (l:num list) =
     LENGTH (solution_seenFold l [])`;;

let solution_expectedInnerFold =
  new_recursive_definition list_RECURSION
    `(!nums:num list. !i:num. !acc:num.
        solution_expectedInnerFold
          nums i ([]:num list) acc = acc) /\
     (!d:num. !ds:num list. !nums:num list. !i:num. !acc:num.
        solution_expectedInnerFold nums i (CONS d ds) acc =
        let j = i + d in
        let subarr = solution_subarray nums i j in
        let count = solution_expectedDistinctCount subarr in
        solution_expectedInnerFold
          nums i ds (acc + count * count))`;;

let solution_expectedOuterFold =
  new_recursive_definition list_RECURSION
    `(!nums:num list. !acc:num.
        solution_expectedOuterFold
          nums ([]:num list) acc = acc) /\
     (!i:num. !is:num list. !nums:num list. !acc:num.
        solution_expectedOuterFold nums (CONS i is) acc =
        let innerSum =
          solution_expectedInnerFold nums i
            (solution_range (LENGTH nums - i)) 0 in
        solution_expectedOuterFold nums is (acc + innerSum))`;;

let solution_expectedSum = new_definition
  `solution_expectedSum (nums:num list) =
     let n = LENGTH nums in
     solution_expectedOuterFold nums (solution_range n) 0`;;

let solution_postcond = new_definition
  `solution_postcond
      (nums:num list) (result:num) <=>
     solution_precond nums
     ==> result >= 0 /\
         result = solution_expectedSum nums`;;

let solution_spec_satisfied =
  `!nums:num list.
     solution_postcond nums (solution nums)`;;
