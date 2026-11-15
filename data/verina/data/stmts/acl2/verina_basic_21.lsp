;; Statement-only formalization of VERINA corpus artifact verina_basic_21,
;; catalog title "isSublist": a deterministic integer-list program returns
;; true exactly when the first list is a contiguous sublist of the second.
;; This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented exactly by proper ACL2 lists of
;; integers.

(defun verina-basic-21-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-basic-21-integer-listp (cdr xs)))
    (equal xs nil)))

(defun verina-basic-21-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; The source precondition is True. The List Int binder domains remain
;; explicit in the final correctness proposition.

(defun verina-basic-21-is-sublist-precond (sub main)
  (declare (ignore sub main))
  t)

;; These are exact total representations of List.drop and List.take on the
;; natural indices used by the source program and postcondition.

(defun verina-basic-21-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      xs
    (if (consp xs)
        (verina-basic-21-drop
         (- count 1)
         (cdr xs))
      nil)))

(defun verina-basic-21-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp xs)
        (cons
         (car xs)
         (verina-basic-21-take
          (- count 1)
          (cdr xs)))
      nil)))

;; At source index i, SUFFIX is exactly main.drop i. Thus the first branch is
;; i + subLen > mainLen, the equality branch compares sub with
;; (main.drop i).take subLen, and recurring on CDR advances to i + 1.

(defun verina-basic-21-is-sublist-check
    (sub suffix sub-length)
  (declare (xargs :measure (acl2-count suffix)))
  (if (> sub-length (len suffix))
      nil
    (if (equal
         sub
         (verina-basic-21-take
          sub-length
          suffix))
        t
      (if (consp suffix)
          (verina-basic-21-is-sublist-check
           sub
           (cdr suffix)
           sub-length)
        nil))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The outer length test and complete local-helper search are
;; otherwise the exact source implementation.

(defun verina-basic-21-is-sublist (sub main)
  (let ((sub-length (len sub))
        (main-length (len main)))
    (if (> sub-length main-length)
        nil
      (verina-basic-21-is-sublist-check
       sub
       main
       sub-length))))

;; This preserves the source postcondition's internal existential Nat index
;; and its exact bounded drop/take equality.

(defun-sk verina-basic-21-contiguous-sublist-p (sub main)
  (exists (i)
    (and
     (natp i)
     (<= (+ i (len sub))
         (len main))
     (equal
      sub
      (verina-basic-21-take
       (len sub)
       (verina-basic-21-drop i main))))))

(defun verina-basic-21-is-sublist-postcond
    (sub main result)
  (and
   (verina-basic-21-integer-listp sub)
   (verina-basic-21-integer-listp main)
   (verina-basic-21-bool-p result)
   (iff
    (verina-basic-21-contiguous-sublist-p sub main)
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; arbitrary List Int inputs and the True precondition, and applies the full
;; biconditional postcondition to the exact executable result.

(defun-sk verina-basic-21-is-sublist-spec-satisfied-statement ()
  (forall (sub main)
    (implies
     (and
      (verina-basic-21-integer-listp sub)
      (verina-basic-21-integer-listp main)
      (verina-basic-21-is-sublist-precond sub main))
     (verina-basic-21-is-sublist-postcond
      sub
      main
      (verina-basic-21-is-sublist sub main)))))

(value-triple :itpeval-statement-checked)
:q
