;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_list_OCamlMergesort_mergesortqtvc: the mergesort
;; verification condition over lists from an arbitrary inhabited carrier with
;; a total preorder, preserving sortedness and permutation. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type, total preorder, and polymorphic prefix operation at the
;; element type used by this verification condition. The carrier is neither
;; bounded nor enumerated, and every source law is explicit below.

(defstub msl-element-p (value) t)
(defstub msl-default-element () t)
(defstub msl-le (left right) t)
(defstub msl-prefix1 (n xs) t)

(defun msl-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (msl-element-p (car xs))
       (msl-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk msl-le-reflexive-p ()
  (forall (x)
    (implies
     (msl-element-p x)
     (msl-le x x))))

(defun-sk msl-le-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (msl-element-p x)
      (msl-element-p y)
      (msl-element-p z)
      (msl-le x y)
      (msl-le y z))
     (msl-le x z))))

(defun-sk msl-le-total-p ()
  (forall (x y)
    (implies
     (and
      (msl-element-p x)
      (msl-element-p y))
     (or
      (msl-le x y)
      (msl-le y x)))))

;; This recursion is definitionally equivalent to the source inductive
;; SORTED relation: nil and singleton lists are sorted, while a list with at
;; least two elements is sorted exactly when its first pair is ordered and its
;; tail is sorted.

(defun msl-sorted-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (msl-element-p (car xs))
       (if (consp (cdr xs))
           (and
            (msl-le (car xs) (cadr xs))
            (msl-sorted-p (cdr xs)))
         (equal (cdr xs) nil)))
    (equal xs nil)))

;; ALL-AFTER-P is the finite-list rendering of
;; forall y in XS, LE X Y.

(defun msl-all-after-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (msl-le x (car xs))
       (msl-all-after-p x (cdr xs)))
    (equal xs nil)))

;; CROSS-ORDERED-P is the finite-list rendering of
;; forall x in LEFT, forall y in RIGHT, LE x y.

(defun msl-cross-ordered-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (msl-all-after-p (car left) right)
       (msl-cross-ordered-p (cdr left) right))
    (equal left nil)))

;; These are the two source axioms characterizing sorted cons and sorted
;; append. Their typed quantifier domains remain explicit.

(defun-sk msl-sorted-cons-law-p ()
  (forall (xs x)
    (implies
     (and
      (msl-list-p xs)
      (msl-element-p x))
     (iff
      (and
       (msl-all-after-p x xs)
       (msl-sorted-p xs))
      (msl-sorted-p (cons x xs))))))

(defun-sk msl-sorted-append-law-p ()
  (forall (left right)
    (implies
     (and
      (msl-list-p left)
      (msl-list-p right))
     (iff
      (and
       (msl-sorted-p left)
       (msl-sorted-p right)
       (msl-cross-ordered-p left right))
      (msl-sorted-p (append left right))))))

;; The prefix operation is intentionally abstract, as in the source. Its
;; result typing and both defining equations are assumptions corresponding to
;; its source type and prefix_def1/prefix_def2 laws.

(defun-sk msl-prefix-typed-p ()
  (forall (n xs)
    (implies
     (and
      (integerp n)
      (msl-list-p xs))
     (msl-list-p (msl-prefix1 n xs)))))

(defun-sk msl-prefix-zero-law-p ()
  (forall (xs)
    (implies
     (msl-list-p xs)
     (equal (msl-prefix1 0 xs) nil))))

(defun-sk msl-prefix-cons-law-p ()
  (forall (n x xs)
    (implies
     (and
      (integerp n)
      (< 0 n)
      (msl-element-p x)
      (msl-list-p xs))
     (equal
      (msl-prefix1 n (cons x xs))
      (cons x (msl-prefix1 (- n 1) xs))))))

(defun msl-source-context-p ()
  (and
   (msl-element-p (msl-default-element))
   (msl-le-reflexive-p)
   (msl-le-transitive-p)
   (msl-le-total-p)
   (msl-sorted-cons-law-p)
   (msl-sorted-append-law-p)
   (msl-prefix-typed-p)
   (msl-prefix-zero-law-p)
   (msl-prefix-cons-law-p)))

;; This deletion-based relation is exactly multiset permutation for finite
;; lists, including multiplicities.

(defun msl-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (msl-remove-first value (cdr xs))))
    nil))

(defun msl-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (msl-permutation-p
        (cdr left)
        (msl-remove-first (car left) right)))
    (and
     (equal left nil)
     (equal right nil))))

;; RESULT remains universally quantified over the complete source List elt
;; domain. The conditional premise and sorted-permutation conclusion retain
;; their original scope.

(defun-sk msl-all-results-p (l n)
  (forall (result)
    (implies
     (msl-list-p result)
     (implies
      (if (< n 2)
          (equal result l)
        (and
         (msl-sorted-p result)
         (msl-permutation-p
          result
          (msl-prefix1 n l))))
      (and
       (msl-sorted-p result)
       (msl-permutation-p result l))))))

(defun msl-mergesort-vc-p (l)
  (let ((n (len l)))
    (and
     (implies
      (not (< n 2))
      (and
       (<= 2 n)
       (<= n (len l))))
     (msl-all-results-p l n))))

(defun-sk
  ntp4vc-pearl-mergesort-list-ocamlmergesort-mergesortqtvc-statement
  ()
  (forall (l)
    (implies
     (and
      (msl-source-context-p)
      (msl-list-p l))
     (msl-mergesort-vc-p l))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
