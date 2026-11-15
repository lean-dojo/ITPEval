;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2019_ghc_sort_Top_orderqtvc: ordering a monotonic integer
;; list by retaining a strictly increasing list or reversing a non-increasing
;; list, yielding a nondecreasing permutation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite ACL2 integer lists represent Why3 lists of mathematical
;; integers without bounding their lengths or element values.

(defun ghc-order-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (ghc-order-integer-list-p (cdr xs)))
    (equal xs nil)))

;; These recursive predicates are exactly the source inductive relations:
;; strict increase, nondecrease, and nonincrease on adjacent list elements.

(defun ghc-order-strict-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (< (car xs) (cadr xs))
       (ghc-order-strict-increasing-p
        (cdr xs)))
    t))

(defun ghc-order-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (<= (car xs) (cadr xs))
       (ghc-order-nondecreasing-p
        (cdr xs)))
    t))

(defun ghc-order-nonincreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (<= (cadr xs) (car xs))
       (ghc-order-nonincreasing-p
        (cdr xs)))
    t))

;; Finite-list permutation is encoded by removing one matching occurrence at
;; a time. On proper lists this is equivalent to Why3 permut and List.Perm.

(defun ghc-order-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (ghc-order-remove-first
        value
        (cdr xs))))))

(defun ghc-order-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (ghc-order-permutation-p
      (cdr left)
      (ghc-order-remove-first
       (car left)
       right)))))

;; This preserves the source match exactly. Its first verification-condition
;; conjunct is True in each of the empty, singleton, and longer-list cases.

(defun ghc-order-pattern-obligation-p (xs)
  (if (endp xs)
      t
    (if (endp (cdr xs))
        t
      t)))

(defun ghc-order-result-premise-p (input result)
  (if (endp input)
      (equal result input)
    (if (endp (cdr input))
        (equal result input)
      (if (< (car input) (cadr input))
          (equal result input)
        (equal result (reverse input))))))

;; RESULT remains universally quantified over all integer lists inside the
;; statement, with the source implication from the order computation to both
;; postconditions.

(defun-sk ghc-order-all-results-correct-p (input)
  (forall (result)
    (implies
     (ghc-order-integer-list-p result)
     (implies
      (ghc-order-result-premise-p
       input result)
      (and
       (ghc-order-nondecreasing-p result)
       (ghc-order-permutation-p
        input result))))))

;; This closed predicate is the complete unproved order verification
;; condition, including the full integer-list domain and monotonicity
;; assumption.

(defun-sk
    ntp4vc-pearl-verifythis-2019-ghc-sort-top-orderqtvc-statement
    ()
  (forall (input)
    (implies
     (ghc-order-integer-list-p input)
     (implies
      (or
       (ghc-order-strict-increasing-p input)
       (ghc-order-nonincreasing-p input))
      (and
       (ghc-order-pattern-obligation-p input)
       (ghc-order-all-results-correct-p
        input))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
