;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_a6:
;; a uniformly logarithmic-length sequence in every nontrivial finite group
;; has ordered subsequence products covering the group. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A finite group is represented by a duplicate-free carrier list, an identity
;; element, and finite multiplication and inverse tables. This is
;; bidirectionally equivalent to the source's arbitrary finite groups: every
;; such group has a table presentation, and every code satisfying GROUP-P
;; defines a finite group on its listed carrier.
;;
;; For n > 1, INTEGER-LENGTH(n-1) is ceiling(log_2 n). Existence of a uniform
;; positive real c with length <= c*ln(n) is equivalent to existence of a
;; uniform positive natural C with length <= C*ceiling(log_2 n), since these
;; two positive logarithmic quantities bound one another by absolute constant
;; factors on integers n >= 2.
;;
;; Nested DEFUN-SK predicates preserve the source quantifier order:
;; there exists C such that every nontrivial finite group code has an
;; internally existentially quantified sequence witness.

(defun putnam-2008-a6-table-has-key-p (key table)
  (if (assoc-equal key table) t nil))

(defun putnam-2008-a6-table-value (key table)
  (cdr (assoc-equal key table)))

(defun putnam-2008-a6-mul (left right mul-table)
  (putnam-2008-a6-table-value (list left right) mul-table))

(defun putnam-2008-a6-inv (element inv-table)
  (putnam-2008-a6-table-value (list element) inv-table))

(defun putnam-2008-a6-mul-row-closed-p
    (left elements carrier mul-table)
  (if (atom elements)
      t
    (and
     (putnam-2008-a6-table-has-key-p
      (list left (car elements))
      mul-table)
     (member-equal
      (putnam-2008-a6-mul left (car elements) mul-table)
      carrier)
     (putnam-2008-a6-mul-row-closed-p
      left (cdr elements) carrier mul-table))))

(defun putnam-2008-a6-mul-closed-p
    (elements carrier mul-table)
  (if (atom elements)
      t
    (and
     (putnam-2008-a6-mul-row-closed-p
      (car elements) carrier carrier mul-table)
     (putnam-2008-a6-mul-closed-p
      (cdr elements) carrier mul-table))))

(defun putnam-2008-a6-inv-closed-p
    (elements carrier inv-table)
  (if (atom elements)
      t
    (and
     (putnam-2008-a6-table-has-key-p
      (list (car elements))
      inv-table)
     (member-equal
      (putnam-2008-a6-inv (car elements) inv-table)
      carrier)
     (putnam-2008-a6-inv-closed-p
      (cdr elements) carrier inv-table))))

(defun putnam-2008-a6-assoc-third-p
    (left middle elements mul-table)
  (if (atom elements)
      t
    (and
     (equal
      (putnam-2008-a6-mul
       left
       (putnam-2008-a6-mul
        middle (car elements) mul-table)
       mul-table)
      (putnam-2008-a6-mul
       (putnam-2008-a6-mul left middle mul-table)
       (car elements)
       mul-table))
     (putnam-2008-a6-assoc-third-p
      left middle (cdr elements) mul-table))))

(defun putnam-2008-a6-assoc-second-p
    (left elements carrier mul-table)
  (if (atom elements)
      t
    (and
     (putnam-2008-a6-assoc-third-p
      left (car elements) carrier mul-table)
     (putnam-2008-a6-assoc-second-p
      left (cdr elements) carrier mul-table))))

(defun putnam-2008-a6-assoc-p
    (elements carrier mul-table)
  (if (atom elements)
      t
    (and
     (putnam-2008-a6-assoc-second-p
      (car elements) carrier carrier mul-table)
     (putnam-2008-a6-assoc-p
      (cdr elements) carrier mul-table))))

(defun putnam-2008-a6-identity-laws-p
    (elements one mul-table)
  (if (atom elements)
      t
    (and
     (equal
      (putnam-2008-a6-mul
       (car elements) one mul-table)
      (car elements))
     (equal
      (putnam-2008-a6-mul
       one (car elements) mul-table)
      (car elements))
     (putnam-2008-a6-identity-laws-p
      (cdr elements) one mul-table))))

(defun putnam-2008-a6-inverse-laws-p
    (elements one mul-table inv-table)
  (if (atom elements)
      t
    (and
     (equal
      (putnam-2008-a6-mul
       (putnam-2008-a6-inv (car elements) inv-table)
       (car elements)
       mul-table)
      one)
     (equal
      (putnam-2008-a6-mul
       (car elements)
       (putnam-2008-a6-inv (car elements) inv-table)
       mul-table)
      one)
     (putnam-2008-a6-inverse-laws-p
      (cdr elements) one mul-table inv-table))))

(defun putnam-2008-a6-group-p
    (carrier one mul-table inv-table)
  (and
   (true-listp carrier)
   (consp carrier)
   (no-duplicatesp-equal carrier)
   (member-equal one carrier)
   (alistp mul-table)
   (alistp inv-table)
   (putnam-2008-a6-mul-closed-p
    carrier carrier mul-table)
   (putnam-2008-a6-inv-closed-p
    carrier carrier inv-table)
   (putnam-2008-a6-assoc-p
    carrier carrier mul-table)
   (putnam-2008-a6-identity-laws-p
    carrier one mul-table)
   (putnam-2008-a6-inverse-laws-p
    carrier one mul-table inv-table)))

(defun putnam-2008-a6-nontrivial-group-code-p (group-code)
  (and
   (true-listp group-code)
   (equal (len group-code) 4)
   (let ((carrier (nth 0 group-code))
         (one (nth 1 group-code))
         (mul-table (nth 2 group-code))
         (inv-table (nth 3 group-code)))
     (and
      (< 1 (len carrier))
      (putnam-2008-a6-group-p
       carrier one mul-table inv-table)))))

(defun putnam-2008-a6-all-in-carrier-p
    (sequence carrier)
  (if (atom sequence)
      (equal sequence nil)
    (and
     (member-equal (car sequence) carrier)
     (putnam-2008-a6-all-in-carrier-p
      (cdr sequence) carrier))))

(defun putnam-2008-a6-left-multiply-products
    (left products mul-table)
  (if (atom products)
      nil
    (cons
     (putnam-2008-a6-mul
      left (car products) mul-table)
     (putnam-2008-a6-left-multiply-products
      left (cdr products) mul-table))))

;; These are exactly the products of all order-preserving subsequences. The
;; empty subsequence contributes ONE; at a cons, a subsequence either omits
;; the head or prepends it to a subsequence of the tail.
(defun putnam-2008-a6-subsequence-products
    (sequence one mul-table)
  (if (atom sequence)
      (list one)
    (let ((tail-products
           (putnam-2008-a6-subsequence-products
            (cdr sequence) one mul-table)))
      (append
       tail-products
       (putnam-2008-a6-left-multiply-products
        (car sequence) tail-products mul-table)))))

(defun putnam-2008-a6-carrier-covered-p
    (elements products)
  (if (atom elements)
      t
    (and
     (member-equal (car elements) products)
     (putnam-2008-a6-carrier-covered-p
      (cdr elements) products))))

(defun putnam-2008-a6-sequence-witness-p
    (constant group-code sequence)
  (let ((carrier (nth 0 group-code))
        (one (nth 1 group-code))
        (mul-table (nth 2 group-code)))
    (and
     (true-listp sequence)
     (putnam-2008-a6-all-in-carrier-p
      sequence carrier)
     (<=
      (len sequence)
      (*
       constant
       (integer-length (- (len carrier) 1))))
     (putnam-2008-a6-carrier-covered-p
      carrier
      (putnam-2008-a6-subsequence-products
       sequence one mul-table)))))

(defun-sk putnam-2008-a6-sequence-exists-p
    (constant group-code)
  (exists (sequence)
    (putnam-2008-a6-sequence-witness-p
     constant group-code sequence)))

(defun-sk putnam-2008-a6-all-groups-p (constant)
  (forall (group-code)
    (implies
     (putnam-2008-a6-nontrivial-group-code-p group-code)
     (putnam-2008-a6-sequence-exists-p
      constant group-code))))

(defun-sk putnambench-putnam-2008-a6-statement ()
  (exists (constant)
    (and
     (natp constant)
     (< 0 constant)
     (putnam-2008-a6-all-groups-p constant))))

(value-triple :itpeval-statement-checked)
:q
