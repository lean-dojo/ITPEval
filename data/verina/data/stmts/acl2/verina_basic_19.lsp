;; Statement-only formalization of VERINA corpus artifact verina_basic_19,
;; catalog title "isSorted": a deterministic integer-array program returns
;; true exactly when every adjacent pair is in nondecreasing order. This file
;; contains no proof.

(in-package "ACL2")

;; ACL2 proper lists of integers represent exactly the finite Array Int inputs.

(defun verina-basic-19-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-19-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness statement.

(defun verina-basic-19-is-sorted-precond (a)
  (declare (ignore a))
  t)

;; The proof-valued True precondition argument is computationally irrelevant.
;; This recursion returns true for arrays of length at most one and otherwise
;; performs the same adjacent comparisons as mapIdx followed by all id.

(defun verina-basic-19-is-sorted (a)
  (declare (xargs :measure (acl2-count a)))
  (if (or
       (endp a)
       (endp (cdr a)))
      t
    (and
     (<= (car a) (cadr a))
     (verina-basic-19-is-sorted (cdr a)))))

(defun verina-basic-19-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; NFIX of an integer difference is Lean's truncated Nat subtraction.

(defun verina-basic-19-nat-sub (left right)
  (if (and
       (natp left)
       (natp right))
      (nfix (- left right))
    0))

;; This preserves the source postcondition's universal Nat index binder and
;; the bound i < a.size - 1.

(defun-sk verina-basic-19-every-adjacent-pair-nondecreasing-p (a)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i
         (verina-basic-19-nat-sub
          (len a)
          1)))
     (<= (nth i a)
         (nth (+ i 1) a)))))

(defun verina-basic-19-is-sorted-postcond (a result)
  (and
   (verina-basic-19-int-array-p a)
   (verina-basic-19-bool-p result)
   (iff
    (verina-basic-19-every-adjacent-pair-nondecreasing-p a)
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Array Int input and True precondition, and applies the
;; complete biconditional postcondition to the exact executable result.

(defun-sk verina-basic-19-is-sorted-spec-satisfied-statement ()
  (forall (a)
    (implies
     (and
      (verina-basic-19-int-array-p a)
      (verina-basic-19-is-sorted-precond a))
     (verina-basic-19-is-sorted-postcond
      a
      (verina-basic-19-is-sorted a)))))

(value-triple :itpeval-statement-checked)
:q
