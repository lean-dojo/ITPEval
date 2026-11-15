(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_8,
  catalog title "canCompleteCircuit": an executable greedy program returns the
  least gas-station index from which every prefix of a circular trip maintains
  nonnegative fuel, or -1 when no such index exists. This file contains no
  proof.
*)

theory verina_advanced_8
  imports Main
begin

definition canCompleteCircuit_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "canCompleteCircuit_precond gas cost \<longleftrightarrow>
    length gas > 0 \<and> length gas = length cost"

fun canCompleteCircuit_loop ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "canCompleteCircuit_loop [] [] idx tank start = int start"
| "canCompleteCircuit_loop [] (ci # cs) idx tank start = -1"
| "canCompleteCircuit_loop (gi # gs) [] idx tank start = -1"
| "canCompleteCircuit_loop (gi # gs) (ci # cs) idx tank start =
    (let tank' = tank + gi - ci
     in if tank' < 0
        then canCompleteCircuit_loop gs cs (idx + 1) 0 (idx + 1)
        else canCompleteCircuit_loop gs cs (idx + 1) tank' start)"

fun canCompleteCircuit_walk ::
    "(int \<times> int) list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "canCompleteCircuit_walk [] i tank start = int start"
| "canCompleteCircuit_walk ((g, c) # rest) i tank start =
    (let newTank = tank + g - c
     in if newTank < 0
        then canCompleteCircuit_walk rest (i + 1) 0 (i + 1)
        else canCompleteCircuit_walk rest (i + 1) newTank start)"

definition canCompleteCircuit :: "int list \<Rightarrow> int list \<Rightarrow> int" where
  "canCompleteCircuit gas cost =
    (let totalGas = foldl (+) 0 gas;
         totalCost = foldl (+) 0 cost
     in if totalGas < totalCost
        then -1
        else canCompleteCircuit_walk (zip gas cost) 0 0 0)"

fun canCompleteCircuit_nthDefault ::
    "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "canCompleteCircuit_nthDefault d [] n = d"
| "canCompleteCircuit_nthDefault d (x # xs) 0 = x"
| "canCompleteCircuit_nthDefault d (x # xs) (Suc n) =
    canCompleteCircuit_nthDefault d xs n"

definition canCompleteCircuit_valid ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> bool" where
  "canCompleteCircuit_valid gas cost start \<longleftrightarrow>
    list_all
      (\<lambda>i.
        0 \<le>
          foldl
            (\<lambda>t j.
              let jdx = (start + j) mod length gas
              in t +
                 canCompleteCircuit_nthDefault 0 gas jdx -
                 canCompleteCircuit_nthDefault 0 cost jdx)
            0 [0..<i + 1])
      [0..<length gas]"

definition canCompleteCircuit_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> bool" where
  "canCompleteCircuit_postcond gas cost result \<longleftrightarrow>
    result \<ge> -1 \<and>
    (result = -1 \<longrightarrow>
      list_all
        (\<lambda>start. \<not> canCompleteCircuit_valid gas cost start)
        [0..<length gas]) \<and>
    (result \<ge> 0 \<longrightarrow>
      result < int (length gas) \<and>
      canCompleteCircuit_valid gas cost (nat result) \<and>
      list_all
        (\<lambda>start. \<not> canCompleteCircuit_valid gas cost start)
        [0..<nat result])"

theorem canCompleteCircuit_spec_satisfied:
  assumes "canCompleteCircuit_precond gas cost"
  shows
    "canCompleteCircuit_postcond gas cost
      (canCompleteCircuit gas cost)"
  sorry

end
