;; Statement-only formalization of VERINA corpus artifact verina_basic_80,
;; catalog title "only_once": a deterministic scan of an integer array returns
;; true exactly when the given key occurs once, with its precondition,
;; postcondition, and correctness proposition. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-80-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-80-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int and Int binder domains
;; remain explicit in the final correctness proposition.

(defun verina-basic-80-only-once-precond (a key)
  (declare (ignore a key))
  t)

(defun verina-basic-80-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This suffix recursion performs the source loop's remaining iterations. It
;; increments the natural occurrence counter exactly when the current value
;; equals KEY and returns whether the final counter is one.

(defun verina-basic-80-only-once-loop-from
    (remaining key key-count)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-80-only-once-loop-from
       (cdr remaining)
       key
       (if (equal (car remaining) key)
           (+ key-count 1)
         key-count))
    (equal key-count 1)))

;; For natural I and KEY-COUNT, NTHCDR selects exactly the suffix beginning at
;; source array index I. If I is at or beyond the array size the suffix is
;; empty, matching the source loop's terminal branch.

(defun verina-basic-80-only-once-loop
    (a key i key-count)
  (verina-basic-80-only-once-loop-from
   (nthcdr i a)
   key
   key-count))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. These initial arguments preserve the complete executable
;; source implementation.

(defun verina-basic-80-only-once (a key)
  (verina-basic-80-only-once-loop a key 0 0))

;; This recursion is extensionally the source Array.foldl count_occurrences
;; helper, with the same left-to-right equality test and natural accumulator.

(defun verina-basic-80-count-occurrences (a key)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (+
       (if (equal (car a) key) 1 0)
       (verina-basic-80-count-occurrences
        (cdr a)
        key))
    0))

;; This is the complete source postcondition. Boolean values are represented
;; by T and NIL, so the two implications say respectively that a count of one
;; forces true and every other count forces false.

(defun verina-basic-80-only-once-postcond
    (a key result)
  (and
   (verina-basic-80-int-array-p a)
   (integerp key)
   (verina-basic-80-bool-p result)
   (implies
    (equal
     (verina-basic-80-count-occurrences a key)
     1)
    result)
   (implies
    (not
     (equal
      (verina-basic-80-count-occurrences a key)
      1))
    (not result))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int and Int domains, assumes exactly the source
;; True precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-80-only-once-spec-satisfied-statement
    ()
  (forall (a key)
    (implies
     (and
      (verina-basic-80-int-array-p a)
      (integerp key)
      (verina-basic-80-only-once-precond a key))
     (verina-basic-80-only-once-postcond
      a
      key
      (verina-basic-80-only-once a key)))))

(value-triple :itpeval-statement-checked)
:q
