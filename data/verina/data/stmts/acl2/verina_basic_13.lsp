;; Statement-only formalization of VERINA corpus artifact verina_basic_13,
;; catalog title "cubeElements": a deterministic integer-array program maps
;; every entry to its cube, preserving array length and the complete pointwise
;; correctness contract. This file contains no proof.

(in-package "ACL2")

;; A Lean Array Int is represented exactly by its finite sequence of entries:
;; a proper ACL2 list whose elements are integers.

(defun verina-basic-13-integer-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-13-integer-array-p
        (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness statement.

(defun verina-basic-13-cube-elements-precond (a)
  (declare (ignore a))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. Structural recursion on the represented array is exactly Array.map
;; with the source function x * x * x, including its left association.

(defun verina-basic-13-cube-elements (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (let ((x (car a)))
        (cons
         (* (* x x) x)
         (verina-basic-13-cube-elements
          (cdr a))))
    nil))

;; Array.get! returns the in-bounds entry and the inhabited integer default
;; zero otherwise.

(defun verina-basic-13-nth-default-zero (index a)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; This predicate preserves the source postcondition's universal Nat index
;; binder and its default-zero reads at each in-bounds array index.

(defun-sk verina-basic-13-cubes-at-every-index-p
    (a result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a)))
     (let ((x
            (verina-basic-13-nth-default-zero
             i
             a)))
       (equal
        (verina-basic-13-nth-default-zero
         i
         result)
        (* (* x x) x))))))

(defun verina-basic-13-cube-elements-postcond
    (a result)
  (and
   (verina-basic-13-integer-array-p a)
   (verina-basic-13-integer-array-p result)
   (equal (len result) (len a))
   (verina-basic-13-cubes-at-every-index-p
    a
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Array Int input and True precondition, and applies the
;; complete postcondition to the exact executable result.

(defun-sk
    verina-basic-13-cube-elements-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-13-integer-array-p a)
      (verina-basic-13-cube-elements-precond a))
     (verina-basic-13-cube-elements-postcond
      a
      (verina-basic-13-cube-elements a)))))

(value-triple :itpeval-statement-checked)
:q
