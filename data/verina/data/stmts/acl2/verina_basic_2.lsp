;; Statement-only formalization of VERINA corpus artifact verina_basic_2,
;; catalog title "findSmallest": a deterministic natural-number-array program
;; returns none exactly for empty input and otherwise returns its smallest
;; element. This file contains no proof.

(in-package "ACL2")

;; A finite Array Nat is represented bijectively by a proper ACL2 list of
;; natural numbers. The source program observes the array only through toList.

(defun verina-basic-2-nat-array-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (natp (car s))
       (verina-basic-2-nat-array-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The Array Nat domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-2-find-smallest-precond (s)
  (declare (ignore s))
  t)

;; Option Nat is represented by the atom :none or the tagged dotted pair
;; (:some . value), preserving none distinctly from every natural value.

(defun verina-basic-2-option-nat-p (result)
  (or
   (equal result :none)
   (and
    (consp result)
    (equal (car result) :some)
    (natp (cdr result)))))

;; On a nonempty natural list this recursion computes its minimum. It is the
;; value component of the source List.min? computation.

(defun verina-basic-2-minimum-nonempty (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp (cdr s))
      (let ((tail-minimum
             (verina-basic-2-minimum-nonempty (cdr s))))
        (if (<= (car s) tail-minimum)
            (car s)
          tail-minimum))
    (car s)))

;; The proof-valued True precondition argument has no computational effect and
;; is erased. This is exactly s.toList.min?: empty input gives none, while a
;; nonempty input gives its recursively computed minimum.

(defun verina-basic-2-find-smallest (s)
  (if (consp s)
      (cons
       :some
       (verina-basic-2-minimum-nonempty s))
    :none))

;; This recursion is the bounded universal quantifier over list membership in
;; the source postcondition.

(defun verina-basic-2-every-element-at-least-p (minimum s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (<= minimum (car s))
       (verina-basic-2-every-element-at-least-p
        minimum
        (cdr s)))
    t))

(defun verina-basic-2-find-smallest-postcond (s result)
  (and
   (verina-basic-2-nat-array-p s)
   (verina-basic-2-option-nat-p result)
   (if (equal result :none)
       (equal s nil)
     (let ((minimum (cdr result)))
       (and
        (member-equal minimum s)
        (verina-basic-2-every-element-at-least-p
         minimum
         s))))))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Array Nat input and True precondition, and applies the full
;; postcondition to the exact executable result.

(defun-sk verina-basic-2-find-smallest-spec-satisfied-statement ()
  (forall (s)
    (implies
     (and
      (verina-basic-2-nat-array-p s)
      (verina-basic-2-find-smallest-precond s))
     (verina-basic-2-find-smallest-postcond
      s
      (verina-basic-2-find-smallest s)))))

(value-triple :itpeval-statement-checked)
:q
