;; Statement-only formalization of VERINA corpus artifact verina_basic_10,
;; "isGreater": a deterministic integer-array program returns true exactly
;; when its integer input exceeds every array element. This file contains no proof.

(in-package "ACL2")

;; ACL2 true lists of integers represent exactly the finite Array Int inputs.

(defun verina-basic-10-int-array-p (a)
  (if (consp a)
      (and (integerp (car a))
           (verina-basic-10-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition a.size > 0 is nonemptiness of the finite list.

(defun verina-basic-10-is-greater-precond (n a)
  (declare (ignore n))
  (< 0 (len a)))

;; This is the exact Array.all computation, traversing the array in order and
;; returning an ACL2 Boolean.

(defun verina-basic-10-is-greater (n a)
  (if (consp a)
      (and (< (car a) n)
           (verina-basic-10-is-greater n (cdr a)))
    t))

(defun verina-basic-10-bool-p (result)
  (or (equal result t)
      (equal result nil)))

;; This preserves the source postcondition's universal Nat index binder:
;; every in-bounds array entry is strictly smaller than n.

(defun-sk verina-basic-10-every-index-smaller-p (n a)
  (forall (i)
    (implies
     (and (natp i)
          (< i (len a)))
     (< (nth i a) n))))

(defun verina-basic-10-is-greater-postcond (n a result)
  (and
   (verina-basic-10-bool-p result)
   (iff
    (verina-basic-10-every-index-smaller-p n a)
    result)))

;; This predicate is the unproved final correctness proposition. It keeps both
;; source domains and the nonempty-array precondition explicit, and applies
;; the complete postcondition to the exact executable result.

(defun-sk verina-basic-10-is-greater-spec-satisfied-statement ()
  (forall (n a)
    (implies
     (and
      (integerp n)
      (verina-basic-10-int-array-p a)
      (verina-basic-10-is-greater-precond n a))
     (verina-basic-10-is-greater-postcond
      n a (verina-basic-10-is-greater n a)))))

(value-triple :itpeval-statement-checked)
:q
