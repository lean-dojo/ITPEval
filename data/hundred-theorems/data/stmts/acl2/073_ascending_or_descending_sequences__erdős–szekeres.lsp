;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__073, "Ascending or Descending Sequences
;; (Erdős–Szekeres)": every finite linearly ordered sequence with more than
;; m*n terms has a nondecreasing subsequence longer than m or a strictly
;; decreasing subsequence longer than n. This file contains no proof.

(in-package "ACL2")

;; LEXORDER is ACL2's total order on all ACL2 objects. Every finite sequence
;; in an arbitrary linear order has an order-preserving rank encoding into
;; this order, while every ACL2 list under LEXORDER is itself a finite
;; linearly ordered sequence. Thus this representation preserves exactly the
;; finite order patterns used by the theorem, without restricting values to
;; rationals or exposing a subsequence witness as an external parameter.

(defun ht073-prepend-to-each (value sequences)
  (if (consp sequences)
      (cons (cons value (car sequences))
            (ht073-prepend-to-each value (cdr sequences)))
    nil))

(defun ht073-subsequences (sequence)
  (if (consp sequence)
      (let ((tail-subsequences
             (ht073-subsequences (cdr sequence))))
        (append
         tail-subsequences
         (ht073-prepend-to-each
          (car sequence)
          tail-subsequences)))
    (list nil)))

(defun ht073-nondecreasing-p (sequence)
  (if (and (consp sequence)
           (consp (cdr sequence)))
      (and (lexorder (car sequence)
                     (cadr sequence))
           (ht073-nondecreasing-p (cdr sequence)))
    t))

(defun ht073-strictly-decreasing-p (sequence)
  (if (and (consp sequence)
           (consp (cdr sequence)))
      (and (lexorder (cadr sequence)
                     (car sequence))
           (not (equal (car sequence)
                       (cadr sequence)))
           (ht073-strictly-decreasing-p (cdr sequence)))
    t))

(defun ht073-has-long-nondecreasing-p (sequences bound)
  (if (consp sequences)
      (or (and (< bound (len (car sequences)))
               (ht073-nondecreasing-p (car sequences)))
          (ht073-has-long-nondecreasing-p
           (cdr sequences)
           bound))
    nil))

(defun ht073-has-long-strictly-decreasing-p (sequences bound)
  (if (consp sequences)
      (or (and (< bound (len (car sequences)))
               (ht073-strictly-decreasing-p (car sequences)))
          (ht073-has-long-strictly-decreasing-p
           (cdr sequences)
           bound))
    nil))

(defun hundred-theorems-073-ascending-or-descending-sequences-statement
    (sequence m n)
  (implies
   (and (true-listp sequence)
        (natp m)
        (natp n)
        (< (* m n) (len sequence)))
   (let ((subsequences (ht073-subsequences sequence)))
     (or
      (ht073-has-long-nondecreasing-p subsequences m)
      (ht073-has-long-strictly-decreasing-p subsequences n)))))

(value-triple :itpeval-statement-checked)
:q
