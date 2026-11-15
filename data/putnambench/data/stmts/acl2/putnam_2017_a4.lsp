;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_a4:
;; a class of 2N students using every integer quiz score from 0 through 10
;; and averaging 7.4 admits two N-student groups each averaging 7.4. This
;; file contains no proof.

(in-package "ACL2")

;; The list order labels the students, so a length-2N list with entries in
;; 0,...,10 is bijective with the source function Fin(2N) -> Fin(11).
;; Selecting list positions below therefore represents an arbitrary subset of
;; students even when several students have equal scores.
(defun putnam-2017-a4-score-list-p (scores)
  (if (consp scores)
      (and
       (natp (car scores))
       (<= (car scores) 10)
       (putnam-2017-a4-score-list-p (cdr scores)))
    (equal scores nil)))

(defun putnam-2017-a4-score-sum (scores)
  (if (consp scores)
      (+ (car scores)
         (putnam-2017-a4-score-sum (cdr scores)))
    0))

(defun putnam-2017-a4-every-score-occurs-p (scores)
  (and
   (member-equal 0 scores)
   (member-equal 1 scores)
   (member-equal 2 scores)
   (member-equal 3 scores)
   (member-equal 4 scores)
   (member-equal 5 scores)
   (member-equal 6 scores)
   (member-equal 7 scores)
   (member-equal 8 scores)
   (member-equal 9 scores)
   (member-equal 10 scores)))

;; This exhaustive two-way recursion is the internal existential quantifier
;; over subsets of the labeled students. At the end, SELECTED-COUNT=N and the
;; two sum equalities say that both groups have average 37/5. Since every
;; position is placed in exactly one accumulator, the groups are complements.
(defun putnam-2017-a4-partition-search-p
    (scores n selected-count selected-sum unselected-sum)
  (if (consp scores)
      (or
       (putnam-2017-a4-partition-search-p
        (cdr scores)
        n
        (+ selected-count 1)
        (+ selected-sum (car scores))
        unselected-sum)
       (putnam-2017-a4-partition-search-p
        (cdr scores)
        n
        selected-count
        selected-sum
        (+ unselected-sum (car scores))))
    (and
     (equal selected-count n)
     (equal (* 5 selected-sum) (* 37 n))
     (equal (* 5 unselected-sum) (* 37 n)))))

(defun putnambench-putnam-2017-a4-statement (n scores)
  (implies
   (and
    (natp n)
    (putnam-2017-a4-score-list-p scores)
    (equal (len scores) (* 2 n))
    (putnam-2017-a4-every-score-occurs-p scores)
    ;; sum/(2N)=37/5 is equivalent to 5*sum=74*N; the occurrence
    ;; hypothesis makes N positive, so no zero-denominator case is introduced.
    (equal
     (* 5 (putnam-2017-a4-score-sum scores))
     (* 74 n)))
   (putnam-2017-a4-partition-search-p
    scores n 0 0 0)))

(value-triple :itpeval-statement-checked)
:q
