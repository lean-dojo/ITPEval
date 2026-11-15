;; Statement-only formalization of VERINA corpus artifact verina_basic_9,
;; catalog title "hasCommonElement": a deterministic scan of two nonempty
;; integer arrays returns true exactly when they share an element. This file
;; contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-9-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-9-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition requires both arrays to have positive size.

(defun verina-basic-9-has-common-element-precond (a b)
  (and
   (< 0 (len a))
   (< 0 (len b))))

;; This inner scan is exactly b.any (fun y => x = y), returning an ACL2
;; Boolean after testing the entries of b in source order.

(defun verina-basic-9-occurs-in-p (x b)
  (declare (xargs :measure (acl2-count b)))
  (if (consp b)
      (if (equal x (car b))
          t
        (verina-basic-9-occurs-in-p x (cdr b)))
    nil))

;; The outer recursion is exactly a.any (fun x => b.any (fun y => x = y)).
;; The proof-valued precondition argument is computationally irrelevant and
;; is erased.

(defun verina-basic-9-has-common-element (a b)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (if (verina-basic-9-occurs-in-p (car a) b)
          t
        (verina-basic-9-has-common-element (cdr a) b))
    nil))

(defun verina-basic-9-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This preserves the source postcondition's existential Nat indices and
;; strict bounds. Under those bounds, NTH is exactly each source getElem!
;; access.

(defun-sk verina-basic-9-common-indices-p (a b)
  (exists (i j)
    (and
     (natp i)
     (natp j)
     (< i (len a))
     (< j (len b))
     (equal
      (nth i a)
      (nth j b)))))

;; The proof-valued precondition argument in the Lean definition is unused and
;; erased. IFF against the Boolean result preserves the source coercion of
;; Bool to Prop.

(defun verina-basic-9-has-common-element-postcond
    (a b result)
  (and
   (verina-basic-9-int-array-p a)
   (verina-basic-9-int-array-p b)
   (verina-basic-9-bool-p result)
   (iff
    (verina-basic-9-common-indices-p a b)
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int domains, assumes exactly the source nonempty
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk
    verina-basic-9-has-common-element-spec-satisfied-statement
    ()
  (forall (a b)
    (implies
     (and
      (verina-basic-9-int-array-p a)
      (verina-basic-9-int-array-p b)
      (verina-basic-9-has-common-element-precond a b))
     (verina-basic-9-has-common-element-postcond
      a
      b
      (verina-basic-9-has-common-element a b)))))

(value-triple :itpeval-statement-checked)
:q
