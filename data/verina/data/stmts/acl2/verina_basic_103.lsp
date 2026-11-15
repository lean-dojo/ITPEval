;; Statement-only formalization of VERINA corpus artifact verina_basic_103,
;; catalog title "UpdateElements": a deterministic integer-array program
;; increments index 4 by 3, sets index 7 to 516, and preserves every other
;; entry. This file contains no proof.

(in-package "ACL2")

;; A Lean Array Int is represented exactly by its finite sequence of entries:
;; a proper ACL2 list whose elements are integers.

(defun verina-basic-103-integer-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-103-integer-array-p (cdr a)))
    (equal a nil)))

(defun verina-basic-103-update-elements-precond (a)
  (<= 8 (len a)))

;; Array.get! returns the in-bounds entry and the inhabited integer default
;; zero otherwise.

(defun verina-basic-103-nth-default-zero (index a)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; This total list update agrees with Array.set! on the represented array:
;; it replaces an in-bounds entry and leaves the array unchanged otherwise.

(defun verina-basic-103-set-at (index value a)
  (declare (xargs :measure (nfix index)))
  (if (consp a)
      (if (zp index)
          (cons value (cdr a))
        (cons
         (car a)
         (verina-basic-103-set-at
          (- index 1)
          value
          (cdr a))))
    nil))

;; The proof-valued precondition argument has no computational effect and is
;; erased. The two LET bindings preserve the source's sequential updates.

(defun verina-basic-103-update-elements (a)
  (let* ((a1
          (verina-basic-103-set-at
           4
           (+ (verina-basic-103-nth-default-zero 4 a) 3)
           a))
         (a2
          (verina-basic-103-set-at
           7
           516
           a1)))
    a2))

;; This preserves the source postcondition's universal Nat index binder.

(defun-sk verina-basic-103-other-indices-unchanged-p
    (a result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a))
      (not (equal i 4))
      (not (equal i 7)))
     (equal
      (verina-basic-103-nth-default-zero i result)
      (verina-basic-103-nth-default-zero i a)))))

(defun verina-basic-103-update-elements-postcond
    (a result)
  (and
   (verina-basic-103-integer-array-p a)
   (verina-basic-103-integer-array-p result)
   (equal (len result) (len a))
   (equal
    (verina-basic-103-nth-default-zero 4 result)
    (+ (verina-basic-103-nth-default-zero 4 a) 3))
   (equal
    (verina-basic-103-nth-default-zero 7 result)
    516)
   (verina-basic-103-other-indices-unchanged-p
    a
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Array Int input and size precondition, and applies the full
;; postcondition to the exact executable result.

(defun-sk
    verina-basic-103-update-elements-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-103-integer-array-p a)
      (verina-basic-103-update-elements-precond a))
     (verina-basic-103-update-elements-postcond
      a
      (verina-basic-103-update-elements a)))))

(value-triple :itpeval-statement-checked)
:q
