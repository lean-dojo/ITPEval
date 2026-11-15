(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_57,
  catalog title "nextGreaterElement": an executable monotone-stack scan finds
  for each selected distinct integer the first greater integer to its right
  in a containing distinct list, or -1 when none exists. This file contains
  no proof.
*)

theory verina_advanced_57
  imports Main
begin

definition nextGreaterElement_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "nextGreaterElement_precond nums1 nums2 \<longleftrightarrow>
    distinct nums1 \<and>
    distinct nums2 \<and>
    list_all (\<lambda>x. x \<in> set nums2) nums1"

fun nge_processStack ::
    "int \<Rightarrow> int list \<Rightarrow> (int \<times> int) list
      \<Rightarrow> int list \<times> (int \<times> int) list" where
  "nge_processStack current [] m = ([], m)"
| "nge_processStack current (topValue # rest) m =
    (if current > topValue
     then nge_processStack current rest ((topValue, current) # m)
     else (topValue # rest, m))"

fun nge_mapLoop ::
    "int list \<Rightarrow> int list \<Rightarrow> (int \<times> int) list
      \<Rightarrow> (int \<times> int) list" where
  "nge_mapLoop [] stack m =
    foldl (\<lambda>acc value. (value, -1) # acc) m stack"
| "nge_mapLoop (current # remaining) stack m =
    (case nge_processStack current stack m of
       (newStack, newMap) \<Rightarrow>
         nge_mapLoop remaining (current # newStack) newMap)"

fun nge_findInMap ::
    "int \<Rightarrow> (int \<times> int) list \<Rightarrow> int" where
  "nge_findInMap value [] = -1"
| "nge_findInMap value ((number, nextGreater) # remaining) =
    (if number = value
     then nextGreater
     else nge_findInMap value remaining)"

fun nge_resultLoop ::
    "int list \<Rightarrow> (int \<times> int) list \<Rightarrow> int list
      \<Rightarrow> int list" where
  "nge_resultLoop [] m result = rev result"
| "nge_resultLoop (value # remaining) m result =
    nge_resultLoop remaining m (nge_findInMap value m # result)"

definition nextGreaterElement ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "nextGreaterElement nums1 nums2 =
    nge_resultLoop nums1 (nge_mapLoop nums2 [] []) []"

fun nge_findIndexFrom ::
    "int \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat option" where
  "nge_findIndexFrom value index [] = None"
| "nge_findIndexFrom value index (x # xs) =
    (if x = value
     then Some index
     else nge_findIndexFrom value (Suc index) xs)"

definition nge_findIndex ::
    "int \<Rightarrow> int list \<Rightarrow> nat option" where
  "nge_findIndex value xs = nge_findIndexFrom value 0 xs"

fun nge_findGreaterOffset ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat
      \<Rightarrow> nat option" where
  "nge_findGreaterOffset nums value position 0 = None"
| "nge_findGreaterOffset nums value position (Suc remaining) =
    (if nums ! position > value
     then Some 0
     else
       (case nge_findGreaterOffset nums value (Suc position) remaining of
          None \<Rightarrow> None
        | Some offset \<Rightarrow> Some (Suc offset)))"

definition nextGreaterElement_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "nextGreaterElement_postcond nums1 nums2 result \<longleftrightarrow>
    length result = length nums1 \<and>
    list_all
      (\<lambda>i.
        let value = nums1 ! i;
            resultValue = result ! i
        in case nge_findIndex value nums2 of
             None \<Rightarrow> False
           | Some index \<Rightarrow>
               (case nge_findGreaterOffset
                       nums2 value (Suc index)
                       (length nums2 - index - 1) of
                  None \<Rightarrow> resultValue = -1
                | Some offset \<Rightarrow>
                    resultValue = nums2 ! (index + offset + 1)))
      [0..<length nums1] \<and>
    list_all (\<lambda>value. value = -1 \<or> value \<in> set nums2) result"

theorem nextGreaterElement_spec_satisfied:
  assumes "nextGreaterElement_precond nums1 nums2"
  shows
    "nextGreaterElement_postcond
      nums1 nums2 (nextGreaterElement nums1 nums2)"
  sorry

end
