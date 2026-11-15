;; Statement-only formalization of VERINA corpus artifact verina_basic_55,
;; catalog title "Compare": deterministic integer equality comparison returns
;; true exactly when the two inputs are equal and false otherwise. This file
;; contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int input domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-55-compare-precond (a b)
  (declare (ignore a b))
  t)

;; This recognizes exactly the two values of Lean Bool.

(defun verina-basic-55-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. This conditional is the exact source Compare computation.

(defun verina-basic-55-compare (a b)
  (if (equal a b)
      t
    nil))

;; This is the complete source postcondition. Typed Int and Bool binder domains
;; are explicit, and the proof-valued precondition argument is unused and
;; erased.

(defun verina-basic-55-compare-postcond
    (a b result)
  (and
   (integerp a)
   (integerp b)
   (verina-basic-55-bool-p result)
   (implies
    (equal a b)
    (equal result t))
   (implies
    (not (equal a b))
    (equal result nil))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over all integer inputs, assumes exactly the source True precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-55-compare-spec-satisfied-statement
    ()
  (forall (a b)
    (implies
     (and
      (integerp a)
      (integerp b)
      (verina-basic-55-compare-precond a b))
     (verina-basic-55-compare-postcond
      a
      b
      (verina-basic-55-compare a b)))))

(value-triple :itpeval-statement-checked)
:q
