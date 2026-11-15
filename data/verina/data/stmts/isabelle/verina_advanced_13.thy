(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_13,
  catalog title "hasChordIntersection": an executable program normalizes and
  sorts chords, then scans them for an endpoint interleaving that represents
  an intersection, together with its precondition and correctness contract.
  This file contains no proof.
*)

theory verina_advanced_13
  imports Main
begin

fun chordEndpoint :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "chordEndpoint [] i = 0"
| "chordEndpoint (x # xs) 0 = x"
| "chordEndpoint (x # xs) (Suc i) = chordEndpoint xs i"

definition hasChordIntersection_precond ::
    "nat \<Rightarrow> nat list list \<Rightarrow> bool" where
  "hasChordIntersection_precond N chords \<longleftrightarrow>
    N \<ge> 2 \<and>
    length chords = N \<and>
    list_all
      (\<lambda>chord.
        length chord = 2 \<and>
        chordEndpoint chord 0 \<ge> 1 \<and>
        chordEndpoint chord 0 \<le> 2 * N \<and>
        chordEndpoint chord 1 \<ge> 1 \<and>
        chordEndpoint chord 1 \<le> 2 * N)
      chords \<and>
    distinct (concat chords)"

definition normalizeChord :: "nat list \<Rightarrow> nat list" where
  "normalizeChord chord =
    (let a = chordEndpoint chord 0;
         b = chordEndpoint chord 1
     in if a > b then [b, a] else [a, b])"

fun checkIntersection ::
    "nat list list \<Rightarrow> nat list list \<Rightarrow> bool" where
  "checkIntersection stack [] = False"
| "checkIntersection stack (chord # rest) =
    (let a = chordEndpoint chord 0;
         b = chordEndpoint chord 1;
         newStack =
           dropWhile (\<lambda>c. chordEndpoint c 1 < a) stack
     in case newStack of
          [] \<Rightarrow> checkIntersection (chord # newStack) rest
        | headChord # tail \<Rightarrow>
            (if chordEndpoint headChord 1 > a \<and>
                chordEndpoint headChord 1 < b
             then True
             else checkIntersection (chord # newStack) rest))"

fun insertChord ::
    "nat list \<Rightarrow> nat list list \<Rightarrow> nat list list" where
  "insertChord x [] = [x]"
| "insertChord x (y # ys) =
    (if chordEndpoint x 0 < chordEndpoint y 0
     then x # y # ys
     else y # insertChord x ys)"

fun sortChords :: "nat list list \<Rightarrow> nat list list" where
  "sortChords [] = []"
| "sortChords (x # xs) = insertChord x (sortChords xs)"

definition hasChordIntersection ::
    "nat \<Rightarrow> nat list list \<Rightarrow> bool" where
  "hasChordIntersection N chords =
    checkIntersection [] (sortChords (map normalizeChord chords))"

definition hasIntersection ::
    "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "hasIntersection chord1 chord2 \<longleftrightarrow>
    (let a1 = chordEndpoint chord1 0;
         b1 = chordEndpoint chord1 1;
         a2 = chordEndpoint chord2 0;
         b2 = chordEndpoint chord2 1
     in (a1 < a2 \<and> a2 < b1 \<and> b1 < b2) \<or>
        (a2 < a1 \<and> a1 < b2 \<and> b2 < b1))"

fun checkAllPairs :: "nat list list \<Rightarrow> bool" where
  "checkAllPairs [] = False"
| "checkAllPairs (x # xs) =
    (if list_ex (hasIntersection x) xs
     then True
     else checkAllPairs xs)"

fun pairwiseNoIntersection :: "nat list list \<Rightarrow> bool" where
  "pairwiseNoIntersection [] = True"
| "pairwiseNoIntersection (x # xs) =
    (list_all (\<lambda>y. \<not> hasIntersection x y) xs \<and>
     pairwiseNoIntersection xs)"

definition hasChordIntersection_postcond ::
    "nat \<Rightarrow> nat list list \<Rightarrow> bool \<Rightarrow> bool" where
  "hasChordIntersection_postcond N chords result \<longleftrightarrow>
    (let sortedChords = map normalizeChord chords
     in (pairwiseNoIntersection sortedChords \<longrightarrow> \<not> result) \<and>
        (list_ex
           (\<lambda>x. list_ex (\<lambda>y. hasIntersection x y) sortedChords)
           sortedChords
         \<longrightarrow> result))"

theorem hasChordIntersection_spec_satisfied:
  assumes "hasChordIntersection_precond N chords"
  shows
    "hasChordIntersection_postcond
      N chords (hasChordIntersection N chords)"
  sorry

end
