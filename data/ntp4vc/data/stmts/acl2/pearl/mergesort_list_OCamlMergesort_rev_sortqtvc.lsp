;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_list_OCamlMergesort_rev_sortqtvc: the recursive reverse-sort
;; verification condition over list prefixes, sortedness, and permutation for
;; an arbitrary inhabited carrier with a total preorder. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the arbitrary inhabited source
;; element type, its total preorder, and the abstract prefix operation.

(defstub mrs-element-p (value) t)
(defstub mrs-default-element () t)
(defstub mrs-le (left right) t)
(defstub mrs-prefix1 (n xs) t)

(defun mrs-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (mrs-element-p (car xs))
       (mrs-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk mrs-le-reflexive-p ()
  (forall (x)
    (implies
     (mrs-element-p x)
     (mrs-le x x))))

(defun-sk mrs-le-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (mrs-element-p x)
      (mrs-element-p y)
      (mrs-element-p z)
      (mrs-le x y)
      (mrs-le y z))
     (mrs-le x z))))

(defun-sk mrs-le-total-p ()
  (forall (x y)
    (implies
     (and
      (mrs-element-p x)
      (mrs-element-p y))
     (or
      (mrs-le x y)
      (mrs-le y x)))))

;; This recursion is definitionally equivalent to the source inductive
;; SORTED relation.

(defun mrs-sorted-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (mrs-element-p (car xs))
       (if (consp (cdr xs))
           (and
            (mrs-le (car xs) (cadr xs))
            (mrs-sorted-p (cdr xs)))
         (equal (cdr xs) nil)))
    (equal xs nil)))

(defun mrs-all-after-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (mrs-le x (car xs))
       (mrs-all-after-p x (cdr xs)))
    (equal xs nil)))

(defun mrs-cross-ordered-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (mrs-all-after-p (car left) right)
       (mrs-cross-ordered-p (cdr left) right))
    (equal left nil)))

(defun-sk mrs-sorted-cons-law-p ()
  (forall (xs x)
    (implies
     (and
      (mrs-list-p xs)
      (mrs-element-p x))
     (iff
      (and
       (mrs-all-after-p x xs)
       (mrs-sorted-p xs))
      (mrs-sorted-p (cons x xs))))))

(defun-sk mrs-sorted-append-law-p ()
  (forall (left right)
    (implies
     (and
      (mrs-list-p left)
      (mrs-list-p right))
     (iff
      (and
       (mrs-sorted-p left)
       (mrs-sorted-p right)
       (mrs-cross-ordered-p left right))
      (mrs-sorted-p (append left right))))))

(defun-sk mrs-prefix-typed-p ()
  (forall (n xs)
    (implies
     (and
      (integerp n)
      (mrs-list-p xs))
     (mrs-list-p (mrs-prefix1 n xs)))))

(defun-sk mrs-prefix-zero-law-p ()
  (forall (xs)
    (implies
     (mrs-list-p xs)
     (equal (mrs-prefix1 0 xs) nil))))

(defun-sk mrs-prefix-cons-law-p ()
  (forall (n x xs)
    (implies
     (and
      (integerp n)
      (< 0 n)
      (mrs-element-p x)
      (mrs-list-p xs))
     (equal
      (mrs-prefix1 n (cons x xs))
      (cons x (mrs-prefix1 (- n 1) xs))))))

(defun mrs-source-context-p ()
  (and
   (mrs-element-p (mrs-default-element))
   (mrs-le-reflexive-p)
   (mrs-le-transitive-p)
   (mrs-le-total-p)
   (mrs-sorted-cons-law-p)
   (mrs-sorted-append-law-p)
   (mrs-prefix-typed-p)
   (mrs-prefix-zero-law-p)
   (mrs-prefix-cons-law-p)))

;; This deletion-based relation is exactly multiset permutation for finite
;; lists, including multiplicities.

(defun mrs-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (mrs-remove-first value (cdr xs))))
    nil))

(defun mrs-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (mrs-permutation-p
        (cdr left)
        (mrs-remove-first (car left) right)))
    (and
     (equal left nil)
     (equal right nil))))

;; These nested universal predicates preserve the recursive-call side
;; conditions and their original quantifier scopes.

(defun-sk mrs-all-s2-side-conditions-p (n l2 n2 s1)
  (forall (s2)
    (implies
     (mrs-list-p s2)
     (implies
      (and
       (mrs-sorted-p s2)
       (mrs-permutation-p s2 (mrs-prefix1 n2 l2)))
      (and
       (and
        (mrs-sorted-p (reverse nil))
        (mrs-sorted-p s1)
        (mrs-sorted-p s2))
       (mrs-cross-ordered-p nil s1)
       (mrs-cross-ordered-p nil s2))))))

(defun-sk mrs-all-s1-side-conditions-p (n l l2 n1 n2)
  (forall (s1)
    (implies
     (mrs-list-p s1)
     (implies
      (and
       (mrs-sorted-p s1)
       (mrs-permutation-p s1 (mrs-prefix1 n1 l)))
      (and
       (and
        (<= 0 n)
        (< n2 n))
       (<= 2 n2)
       (<= n2 (len l2))
       (mrs-all-s2-side-conditions-p n l2 n2 s1))))))

(defun-sk mrs-all-l2-side-conditions-p (n l n1 n2)
  (forall (l2)
    (implies
     (mrs-list-p l2)
     (implies
      (equal l (append (mrs-prefix1 n1 l) l2))
      (and
       (and
        (<= 0 n)
        (< n1 n))
       (<= 2 n1)
       (<= n1 (len l))
       (mrs-all-s1-side-conditions-p n l l2 n1 n2))))))

(defun mrs-recursive-side-conditions-p (n l)
  (let*
      ((n1 (floor n 2))
       (n2 (- n n1)))
    (and
     (and
      (<= 0 n1)
      (<= n1 (len l)))
     (mrs-all-l2-side-conditions-p n l n1 n2))))

(defun mrs-control-side-conditions-p (n l)
  (if (equal n 2)
      (and
       (consp l)
       (consp (cdr l)))
    (if (equal n 3)
        (and
         (consp l)
         (consp (cdr l))
         (consp (cddr l)))
      (and
       (not (equal 2 0))
       (mrs-recursive-side-conditions-p n l)))))

;; The recursive branch keeps l2, s1, and s2 existentially quantified inside
;; the computation premise, as in the source verification condition.

(defun-sk mrs-recursive-result-premise-p (n l result)
  (exists (l2 s1 s2)
    (and
     (mrs-list-p l2)
     (mrs-list-p s1)
     (mrs-list-p s2)
     (equal
      l
      (append
       (mrs-prefix1 (floor n 2) l)
       l2))
     (mrs-sorted-p s1)
     (mrs-permutation-p
      s1
      (mrs-prefix1 (floor n 2) l))
     (mrs-sorted-p s2)
     (mrs-permutation-p
      s2
      (mrs-prefix1
       (- n (floor n 2))
       l2))
     (mrs-sorted-p (reverse result))
     (mrs-permutation-p
      result
      (append (append nil s1) s2)))))

(defun mrs-two-element-result-p (l result)
  (if (and
       (consp l)
       (consp (cdr l)))
      (let*
          ((x1 (car l))
           (x2 (cadr l)))
        (if (not (mrs-le x1 x2))
            (equal result (list x1 x2))
          (equal result (list x2 x1))))
    nil))

(defun mrs-three-element-result-p (l result)
  (if (and
       (consp l)
       (consp (cdr l))
       (consp (cddr l)))
      (let*
          ((x1 (car l))
           (x2 (cadr l))
           (x3 (caddr l)))
        (if (not (mrs-le x1 x2))
            (if (not (mrs-le x2 x3))
                (equal result (list x1 x2 x3))
              (if (not (mrs-le x1 x3))
                  (equal result (list x1 x3 x2))
                (equal result (list x3 x1 x2))))
          (if (not (mrs-le x1 x3))
              (equal result (list x2 x1 x3))
            (if (not (mrs-le x2 x3))
                (equal result (list x2 x3 x1))
              (equal result (list x3 x2 x1))))))
    nil))

(defun mrs-result-premise-p (n l result)
  (if (equal n 2)
      (mrs-two-element-result-p l result)
    (if (equal n 3)
        (mrs-three-element-result-p l result)
      (mrs-recursive-result-premise-p n l result))))

(defun-sk mrs-all-results-p (n l)
  (forall (result)
    (implies
     (mrs-list-p result)
     (implies
      (mrs-result-premise-p n l result)
      (and
       (mrs-sorted-p (reverse result))
       (mrs-permutation-p result (mrs-prefix1 n l)))))))

(defun
  ntp4vc-pearl-mergesort-list-ocamlmergesort-rev-sortqtvc-statement
  (n l)
  (implies
   (and
    (mrs-source-context-p)
    (integerp n)
    (mrs-list-p l)
    (<= 2 n)
    (<= n (len l)))
   (and
    (mrs-control-side-conditions-p n l)
    (mrs-all-results-p n l))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
