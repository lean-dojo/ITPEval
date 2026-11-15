;; Statement-only formalization of VERINA corpus artifact verina_advanced_11,
;; "findMajorityElement": a deterministic list scan returns the first integer
;; occurring strictly more than half the list length, or -1 if none exists,
;; together with its majority-element correctness contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-11-integer-listp (lst)
  (if (consp lst)
      (and (integerp (car lst))
           (verina-advanced-11-integer-listp (cdr lst)))
    (equal lst nil)))

(defun verina-advanced-11-find-majority-element-precond (lst)
  (declare (ignore lst))
  t)

(defun verina-advanced-11-list-length (lst)
  (if (consp lst)
      (+ 1 (verina-advanced-11-list-length (cdr lst)))
    0))

(defun verina-advanced-11-count-occurrences (n lst)
  (if (consp lst)
      (+ (if (equal (car lst) n) 1 0)
         (verina-advanced-11-count-occurrences n (cdr lst)))
    0))

(defun verina-advanced-11-find-majority-scan
    (remaining whole threshold)
  (if (consp remaining)
      (if (< threshold
             (verina-advanced-11-count-occurrences
              (car remaining) whole))
          (car remaining)
        (verina-advanced-11-find-majority-scan
         (cdr remaining) whole threshold))
    -1))

(defun verina-advanced-11-find-majority-element (lst)
  (verina-advanced-11-find-majority-scan
   lst
   lst
   (floor (verina-advanced-11-list-length lst) 2)))

(defun verina-advanced-11-all-counts-at-most-p
    (remaining whole threshold)
  (if (consp remaining)
      (and
       (<= (verina-advanced-11-count-occurrences
            (car remaining) whole)
           threshold)
       (verina-advanced-11-all-counts-at-most-p
        (cdr remaining) whole threshold))
    (equal remaining nil)))

(defun verina-advanced-11-all-counts-at-most-or-result-p
    (remaining whole threshold result)
  (if (consp remaining)
      (and
       (or
        (<= (verina-advanced-11-count-occurrences
             (car remaining) whole)
            threshold)
        (equal (car remaining) result))
       (verina-advanced-11-all-counts-at-most-or-result-p
        (cdr remaining) whole threshold result))
    (equal remaining nil)))

(defun verina-advanced-11-majority-p (lst result threshold)
  (and
   (< threshold
      (verina-advanced-11-count-occurrences result lst))
   (verina-advanced-11-all-counts-at-most-or-result-p
    lst lst threshold result)))

(defun verina-advanced-11-find-majority-element-postcond
    (lst result)
  (let ((threshold
         (floor (verina-advanced-11-list-length lst) 2)))
    (and
     (integerp result)
     (implies
      (equal result -1)
      (or
       (verina-advanced-11-all-counts-at-most-p
        lst lst threshold)
       (verina-advanced-11-majority-p
        lst result threshold)))
     (implies
      (not (equal result -1))
      (verina-advanced-11-majority-p
       lst result threshold)))))

(defun verina-advanced-11-find-majority-element-spec-satisfied-statement
    (lst)
  (implies
   (and
    (verina-advanced-11-integer-listp lst)
    (verina-advanced-11-find-majority-element-precond lst))
   (verina-advanced-11-find-majority-element-postcond
    lst
    (verina-advanced-11-find-majority-element lst))))

(value-triple :itpeval-statement-checked)
:q
