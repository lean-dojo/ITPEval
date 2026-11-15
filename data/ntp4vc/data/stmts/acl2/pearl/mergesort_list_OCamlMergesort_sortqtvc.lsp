;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_list_OCamlMergesort_sortqtvc: the recursive sort
;; verification condition over list prefixes, sortedness, and permutation for
;; an arbitrary inhabited carrier with a total preorder. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the arbitrary inhabited source
;; element type, its total preorder, and the abstract prefix operation.

(defstub mss-element-p (value) t)
(defstub mss-default-element () t)
(defstub mss-le (left right) t)
(defstub mss-prefix1 (n xs) t)

(defun mss-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (mss-element-p (car xs))
       (mss-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk mss-le-reflexive-p ()
  (forall (x)
    (implies
     (mss-element-p x)
     (mss-le x x))))

(defun-sk mss-le-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (mss-element-p x)
      (mss-element-p y)
      (mss-element-p z)
      (mss-le x y)
      (mss-le y z))
     (mss-le x z))))

(defun-sk mss-le-total-p ()
  (forall (x y)
    (implies
     (and
      (mss-element-p x)
      (mss-element-p y))
     (or
      (mss-le x y)
      (mss-le y x)))))

;; This recursion is definitionally equivalent to the source inductive
;; SORTED relation.

(defun mss-sorted-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (mss-element-p (car xs))
       (if (consp (cdr xs))
           (and
            (mss-le (car xs) (cadr xs))
            (mss-sorted-p (cdr xs)))
         (equal (cdr xs) nil)))
    (equal xs nil)))

(defun mss-all-after-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (mss-le x (car xs))
       (mss-all-after-p x (cdr xs)))
    (equal xs nil)))

(defun mss-cross-ordered-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (mss-all-after-p (car left) right)
       (mss-cross-ordered-p (cdr left) right))
    (equal left nil)))

;; This is the merge precondition
;; forall x in LEFT, forall y in RIGHT, LE y x.

(defun mss-all-before-p (right x)
  (declare (xargs :measure (acl2-count right)))
  (if (consp right)
      (and
       (mss-le (car right) x)
       (mss-all-before-p (cdr right) x))
    (equal right nil)))

(defun mss-reverse-cross-ordered-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (mss-all-before-p right (car left))
       (mss-reverse-cross-ordered-p (cdr left) right))
    (equal left nil)))

(defun-sk mss-sorted-cons-law-p ()
  (forall (xs x)
    (implies
     (and
      (mss-list-p xs)
      (mss-element-p x))
     (iff
      (and
       (mss-all-after-p x xs)
       (mss-sorted-p xs))
      (mss-sorted-p (cons x xs))))))

(defun-sk mss-sorted-append-law-p ()
  (forall (left right)
    (implies
     (and
      (mss-list-p left)
      (mss-list-p right))
     (iff
      (and
       (mss-sorted-p left)
       (mss-sorted-p right)
       (mss-cross-ordered-p left right))
      (mss-sorted-p (append left right))))))

(defun-sk mss-prefix-typed-p ()
  (forall (n xs)
    (implies
     (and
      (integerp n)
      (mss-list-p xs))
     (mss-list-p (mss-prefix1 n xs)))))

(defun-sk mss-prefix-zero-law-p ()
  (forall (xs)
    (implies
     (mss-list-p xs)
     (equal (mss-prefix1 0 xs) nil))))

(defun-sk mss-prefix-cons-law-p ()
  (forall (n x xs)
    (implies
     (and
      (integerp n)
      (< 0 n)
      (mss-element-p x)
      (mss-list-p xs))
     (equal
      (mss-prefix1 n (cons x xs))
      (cons x (mss-prefix1 (- n 1) xs))))))

(defun mss-source-context-p ()
  (and
   (mss-element-p (mss-default-element))
   (mss-le-reflexive-p)
   (mss-le-transitive-p)
   (mss-le-total-p)
   (mss-sorted-cons-law-p)
   (mss-sorted-append-law-p)
   (mss-prefix-typed-p)
   (mss-prefix-zero-law-p)
   (mss-prefix-cons-law-p)))

;; This deletion-based relation is exactly multiset permutation for finite
;; lists, including multiplicities.

(defun mss-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (mss-remove-first value (cdr xs))))
    nil))

(defun mss-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (mss-permutation-p
        (cdr left)
        (mss-remove-first (car left) right)))
    (and
     (equal left nil)
     (equal right nil))))

;; These nested universal predicates preserve the recursive-call side
;; conditions and their original quantifier scopes.

(defun-sk mss-all-s2-side-conditions-p (l2 n2 s1)
  (forall (s2)
    (implies
     (mss-list-p s2)
     (implies
      (and
       (mss-sorted-p (reverse s2))
       (mss-permutation-p s2 (mss-prefix1 n2 l2)))
      (and
       (and
        (mss-sorted-p nil)
        (mss-sorted-p (reverse s1))
        (mss-sorted-p (reverse s2)))
       (mss-reverse-cross-ordered-p nil s1)
       (mss-reverse-cross-ordered-p nil s2))))))

(defun-sk mss-all-s1-side-conditions-p (n l l2 n1 n2)
  (forall (s1)
    (implies
     (mss-list-p s1)
     (implies
      (and
       (mss-sorted-p (reverse s1))
       (mss-permutation-p s1 (mss-prefix1 n1 l)))
      (and
       (and
        (<= 0 n)
        (< n2 n))
       (<= 2 n2)
       (<= n2 (len l2))
       (mss-all-s2-side-conditions-p l2 n2 s1))))))

(defun-sk mss-all-l2-side-conditions-p (n l n1 n2)
  (forall (l2)
    (implies
     (mss-list-p l2)
     (implies
      (equal l (append (mss-prefix1 n1 l) l2))
      (and
       (and
        (<= 0 n)
        (< n1 n))
       (<= 2 n1)
       (<= n1 (len l))
       (mss-all-s1-side-conditions-p n l l2 n1 n2))))))

(defun mss-recursive-side-conditions-p (n l)
  (let*
      ((n1 (floor n 2))
       (n2 (- n n1)))
    (and
     (and
      (<= 0 n1)
      (<= n1 (len l)))
     (mss-all-l2-side-conditions-p n l n1 n2))))

(defun mss-control-side-conditions-p (n l)
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
       (mss-recursive-side-conditions-p n l)))))

;; The recursive branch keeps l2, s1, and s2 existentially quantified inside
;; the computation premise, as in the source verification condition.

(defun-sk mss-recursive-result-premise-p (n l result)
  (exists (l2 s1 s2)
    (and
     (mss-list-p l2)
     (mss-list-p s1)
     (mss-list-p s2)
     (equal
      l
      (append
       (mss-prefix1 (floor n 2) l)
       l2))
     (mss-sorted-p (reverse s1))
     (mss-permutation-p
      s1
      (mss-prefix1 (floor n 2) l))
     (mss-sorted-p (reverse s2))
     (mss-permutation-p
      s2
      (mss-prefix1
       (- n (floor n 2))
       l2))
     (mss-sorted-p result)
     (mss-permutation-p
      result
      (append (append nil s1) s2)))))

(defun mss-two-element-result-p (l result)
  (if (and
       (consp l)
       (consp (cdr l)))
      (let*
          ((x1 (car l))
           (x2 (cadr l)))
        (if (mss-le x1 x2)
            (equal result (list x1 x2))
          (equal result (list x2 x1))))
    nil))

(defun mss-three-element-result-p (l result)
  (if (and
       (consp l)
       (consp (cdr l))
       (consp (cddr l)))
      (let*
          ((x1 (car l))
           (x2 (cadr l))
           (x3 (caddr l)))
        (if (mss-le x1 x2)
            (if (mss-le x2 x3)
                (equal result (list x1 x2 x3))
              (if (mss-le x1 x3)
                  (equal result (list x1 x3 x2))
                (equal result (list x3 x1 x2))))
          (if (mss-le x1 x3)
              (equal result (list x2 x1 x3))
            (if (mss-le x2 x3)
                (equal result (list x2 x3 x1))
              (equal result (list x3 x2 x1))))))
    nil))

(defun mss-result-premise-p (n l result)
  (if (equal n 2)
      (mss-two-element-result-p l result)
    (if (equal n 3)
        (mss-three-element-result-p l result)
      (mss-recursive-result-premise-p n l result))))

(defun-sk mss-all-results-p (n l)
  (forall (result)
    (implies
     (mss-list-p result)
     (implies
      (mss-result-premise-p n l result)
      (and
       (mss-sorted-p result)
       (mss-permutation-p result (mss-prefix1 n l)))))))

(defun
  ntp4vc-pearl-mergesort-list-ocamlmergesort-sortqtvc-statement
  (n l)
  (implies
   (and
    (mss-source-context-p)
    (integerp n)
    (mss-list-p l)
    (<= 2 n)
    (<= n (len l)))
   (and
    (mss-control-side-conditions-p n l)
    (mss-all-results-p n l))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
