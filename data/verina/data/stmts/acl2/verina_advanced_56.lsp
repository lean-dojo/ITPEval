;; Statement-only formalization of VERINA artifact verina_advanced_56,
;; "moveZeroes": moving every zero in an integer list to the end while
;; preserving the relative order of the nonzero elements. This file contains
;; no proof.

(in-package "ACL2")

;; ACL2 is untyped, so this predicate represents the Lean domain List Int.
(defun verina-advanced-56-int-listp (xs)
  (if (consp xs)
      (and (integerp (car xs))
           (verina-advanced-56-int-listp (cdr xs)))
    (equal xs nil)))

;; The Lean precondition is True on its typed input domain.
(defun verina-advanced-56-movezeroes-precond (xs)
  (verina-advanced-56-int-listp xs))

(defun verina-advanced-56-filter-nonzero (xs)
  (if (consp xs)
      (if (equal (car xs) 0)
          (verina-advanced-56-filter-nonzero (cdr xs))
        (cons (car xs)
              (verina-advanced-56-filter-nonzero (cdr xs))))
    nil))

(defun verina-advanced-56-filter-zero (xs)
  (if (consp xs)
      (if (equal (car xs) 0)
          (cons (car xs)
                (verina-advanced-56-filter-zero (cdr xs)))
        (verina-advanced-56-filter-zero (cdr xs)))
    nil))

;; Exact executable translation of filter-nonzero(xs) ++ filter-zero(xs).
(defun verina-advanced-56-movezeroes (xs)
  (append (verina-advanced-56-filter-nonzero xs)
          (verina-advanced-56-filter-zero xs)))

(defun verina-advanced-56-count-val (val xs)
  (if (consp xs)
      (if (equal (car xs) val)
          (+ 1 (verina-advanced-56-count-val val (cdr xs)))
        (verina-advanced-56-count-val val (cdr xs)))
    0))

(defun verina-advanced-56-is-subsequence (xs ys)
  (cond ((atom xs) t)
        ((atom ys) nil)
        ((equal (car xs) (car ys))
         (verina-advanced-56-is-subsequence (cdr xs) (cdr ys)))
        (t
         (verina-advanced-56-is-subsequence xs (cdr ys)))))

(defun verina-advanced-56-drop-while-nonzero (xs)
  (if (and (consp xs)
           (not (equal (car xs) 0)))
      (verina-advanced-56-drop-while-nonzero (cdr xs))
    xs))

(defun verina-advanced-56-all-zero-p (xs)
  (if (consp xs)
      (and (equal (car xs) 0)
           (verina-advanced-56-all-zero-p (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-56-movezeroes-postcond (xs result)
  (and (verina-advanced-56-int-listp xs)
       (verina-advanced-56-int-listp result)
       (verina-advanced-56-is-subsequence
        (verina-advanced-56-filter-nonzero xs)
        result)
       (verina-advanced-56-all-zero-p
        (verina-advanced-56-drop-while-nonzero result))
       (equal (verina-advanced-56-count-val 0 xs)
              (verina-advanced-56-count-val 0 result))
       (equal (len xs) (len result))))

(defun verina-advanced-56-movezeroes-spec-satisfied-statement (xs)
  (implies
   (verina-advanced-56-movezeroes-precond xs)
   (verina-advanced-56-movezeroes-postcond
    xs
    (verina-advanced-56-movezeroes xs))))

(value-triple :itpeval-statement-checked)
:q
