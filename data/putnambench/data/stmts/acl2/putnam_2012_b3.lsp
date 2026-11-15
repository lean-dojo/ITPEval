;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_b3:
;; every round-robin tournament on 2n teams admits an injective choice of one
;; winning team from each of its 2n-1 days. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; MATCHUPS and WINS are tame ACL2 function objects of two arguments. On the
;; finite day and team domains, every source function has an extensionally
;; equal tame function-object representation, and every accepted object below
;; restricts to a source function. The recursive checks enumerate exactly the
;; Fin-indexed domains from the Lean statement.

(defun putnam-2012-b3-matchup (matchups day team)
  (apply$ matchups (list day team)))

(defun putnam-2012-b3-win (wins day team)
  (apply$ wins (list day team)))

(defun putnam-2012-b3-booleanp (value)
  (or (equal value t)
      (equal value nil)))

(defun putnam-2012-b3-games-for-teams-p
    (matchups day team-count remaining-teams)
  (declare (xargs :measure (nfix remaining-teams)))
  (if (zp remaining-teams)
      t
    (let* ((team (- remaining-teams 1))
           (opponent
            (putnam-2012-b3-matchup matchups day team)))
      (and
       (natp opponent)
       (< opponent team-count)
       (not (equal opponent team))
       (equal
        (putnam-2012-b3-matchup matchups day opponent)
        team)
       (putnam-2012-b3-games-for-teams-p
        matchups day team-count team)))))

(defun putnam-2012-b3-games-for-days-p
    (matchups team-count remaining-days)
  (declare (xargs :measure (nfix remaining-days)))
  (if (zp remaining-days)
      t
    (and
     (putnam-2012-b3-games-for-teams-p
      matchups
      (- remaining-days 1)
      team-count
      team-count)
     (putnam-2012-b3-games-for-days-p
      matchups team-count (- remaining-days 1)))))

(defun putnam-2012-b3-opponent-day-exists-p
    (matchups team1 team2 remaining-days)
  (declare (xargs :measure (nfix remaining-days)))
  (if (zp remaining-days)
      nil
    (or
     (equal
      (putnam-2012-b3-matchup
       matchups (- remaining-days 1) team1)
      team2)
     (putnam-2012-b3-opponent-day-exists-p
      matchups team1 team2 (- remaining-days 1)))))

(defun putnam-2012-b3-all-opponents-for-team-p
    (matchups team1 day-count remaining-teams)
  (declare (xargs :measure (nfix remaining-teams)))
  (if (zp remaining-teams)
      t
    (let ((team2 (- remaining-teams 1)))
      (and
       (implies
        (not (equal team1 team2))
        (putnam-2012-b3-opponent-day-exists-p
         matchups team1 team2 day-count))
       (putnam-2012-b3-all-opponents-for-team-p
        matchups team1 day-count team2)))))

(defun putnam-2012-b3-all-opponents-p
    (matchups day-count team-count remaining-teams)
  (declare (xargs :measure (nfix remaining-teams)))
  (if (zp remaining-teams)
      t
    (let ((team1 (- remaining-teams 1)))
      (and
       (putnam-2012-b3-all-opponents-for-team-p
        matchups team1 day-count team-count)
       (putnam-2012-b3-all-opponents-p
        matchups day-count team-count team1)))))

(defun putnam-2012-b3-wins-for-teams-p
    (matchups wins day remaining-teams)
  (declare (xargs :measure (nfix remaining-teams)))
  (if (zp remaining-teams)
      t
    (let* ((team (- remaining-teams 1))
           (opponent
            (putnam-2012-b3-matchup matchups day team))
           (team-wins
            (putnam-2012-b3-win wins day team))
           (opponent-wins
            (putnam-2012-b3-win wins day opponent)))
      (and
       (putnam-2012-b3-booleanp team-wins)
       (putnam-2012-b3-booleanp opponent-wins)
       (equal team-wins (not opponent-wins))
       (putnam-2012-b3-wins-for-teams-p
        matchups wins day team)))))

(defun putnam-2012-b3-wins-for-days-p
    (matchups wins team-count remaining-days)
  (declare (xargs :measure (nfix remaining-days)))
  (if (zp remaining-days)
      t
    (and
     (putnam-2012-b3-wins-for-teams-p
      matchups
      wins
      (- remaining-days 1)
      team-count)
     (putnam-2012-b3-wins-for-days-p
      matchups wins team-count (- remaining-days 1)))))

;; This finite branching search is exactly the source existential quantifier
;; over choices. For each day it tries every team, and USED enforces
;; injectivity. The fuel is larger than the maximum recursion depth along any
;; branch, so it does not remove any possible choice function.
(defun putnam-2012-b3-winning-choice-search-p
    (fuel day day-count team-count candidate wins used)
  (declare (xargs :measure (nfix fuel)))
  (cond
   ((<= day-count day) t)
   ((or (zp fuel)
        (<= team-count candidate))
    nil)
   (t
    (or
     (and
      (equal
       (putnam-2012-b3-win wins day candidate)
       t)
      (not (member-equal candidate used))
      (putnam-2012-b3-winning-choice-search-p
       (- fuel 1)
       (+ day 1)
       day-count
       team-count
       0
       wins
       (cons candidate used)))
     (putnam-2012-b3-winning-choice-search-p
      (- fuel 1)
      day
      day-count
      team-count
      (+ candidate 1)
      wins
      used)))))

(defun putnam-2012-b3-winning-choice-exists-p
    (day-count team-count wins)
  (putnam-2012-b3-winning-choice-search-p
   (+ 1 (* day-count (+ team-count 1)))
   0
   day-count
   team-count
   0
   wins
   nil))

;; The source solution is True, so its biconditional is the universally closed
;; implication represented by this predicate-valued definition.
(defun putnambench-putnam-2012-b3-statement (n matchups wins)
  (let ((team-count (* 2 n))
        (day-count (- (* 2 n) 1)))
    (implies
     (and
      (natp n)
      (<= 1 n)
      (tamep-functionp matchups)
      (tamep-functionp wins)
      (putnam-2012-b3-games-for-days-p
       matchups team-count day-count)
      (putnam-2012-b3-all-opponents-p
       matchups day-count team-count team-count)
      (putnam-2012-b3-wins-for-days-p
       matchups wins team-count day-count))
     (putnam-2012-b3-winning-choice-exists-p
      day-count team-count wins))))

(value-triple :itpeval-statement-checked)
:q
