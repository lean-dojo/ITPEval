;; Statement-only formalization of thousand-theorems artifact
;; thousand-theorems__acl2__Q976607, "Erdős–Szekeres theorem": an injective
;; map from a finite linearly ordered domain with more than r*s elements has
;; a strictly increasing subset longer than r or a strictly decreasing subset
;; longer than s. This file contains no proof.

(in-package "ACL2")

;; Enumerating the finite domain in increasing order turns the injective map
;; into a duplicate-free list. LEXORDER is ACL2's total order on all ACL2
;; objects; an order-preserving rank encoding realizes every finite order
;; pattern in the map's range. Subsequence lists therefore correspond exactly
;; to the source theorem's finite subsets, listed in domain order.

(defun q976607-prepend-to-each (value sequences)
  (if (consp sequences)
      (cons (cons value (car sequences))
            (q976607-prepend-to-each value (cdr sequences)))
    nil))

(defun q976607-subsequences (sequence)
  (if (consp sequence)
      (let ((tail-subsequences
             (q976607-subsequences (cdr sequence))))
        (append
         tail-subsequences
         (q976607-prepend-to-each
          (car sequence)
          tail-subsequences)))
    (list nil)))

(defun q976607-strictly-increasing-p (sequence)
  (if (and (consp sequence)
           (consp (cdr sequence)))
      (and (lexorder (car sequence)
                     (cadr sequence))
           (not (equal (car sequence)
                       (cadr sequence)))
           (q976607-strictly-increasing-p (cdr sequence)))
    t))

(defun q976607-strictly-decreasing-p (sequence)
  (if (and (consp sequence)
           (consp (cdr sequence)))
      (and (lexorder (cadr sequence)
                     (car sequence))
           (not (equal (car sequence)
                       (cadr sequence)))
           (q976607-strictly-decreasing-p (cdr sequence)))
    t))

(defun q976607-has-long-increasing-p (sequences bound)
  (if (consp sequences)
      (or (and (< bound (len (car sequences)))
               (q976607-strictly-increasing-p (car sequences)))
          (q976607-has-long-increasing-p
           (cdr sequences)
           bound))
    nil))

(defun q976607-has-long-decreasing-p (sequences bound)
  (if (consp sequences)
      (or (and (< bound (len (car sequences)))
               (q976607-strictly-decreasing-p (car sequences)))
          (q976607-has-long-decreasing-p
           (cdr sequences)
           bound))
    nil))

(defun thousand-theorems-q976607-erdos-szekeres-statement
    (sequence r s)
  (implies
   (and (true-listp sequence)
        (no-duplicatesp-equal sequence)
        (natp r)
        (natp s)
        (< (* r s) (len sequence)))
   (let ((subsequences (q976607-subsequences sequence)))
     (or
      (q976607-has-long-increasing-p subsequences r)
      (q976607-has-long-decreasing-p subsequences s)))))

(value-triple :itpeval-statement-checked)
:q
