;; Statement-only formalization of VERINA corpus artifact verina_advanced_1,
;; "FindSingleNumber": a deterministic scan of an integer list returns its
;; unique element of multiplicity one when every other element has
;; multiplicity two. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-1-integer-listp (xs)
  (if (consp xs)
      (and (integerp (car xs))
           (verina-advanced-1-integer-listp (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-1-filterlist (x nums)
  (if (consp nums)
      (if (equal (car nums) x)
          (cons (car nums)
                (verina-advanced-1-filterlist x (cdr nums)))
        (verina-advanced-1-filterlist x (cdr nums)))
    nil))

(defun verina-advanced-1-list-length (xs)
  (if (consp xs)
      (+ 1 (verina-advanced-1-list-length (cdr xs)))
    0))

(defun verina-advanced-1-nums-counts (remaining nums)
  (if (consp remaining)
      (cons
       (verina-advanced-1-list-length
        (verina-advanced-1-filterlist (car remaining) nums))
       (verina-advanced-1-nums-counts (cdr remaining) nums))
    nil))

(defun verina-advanced-1-all-counts-one-or-two-p (counts)
  (if (consp counts)
      (and (or (equal (car counts) 1)
               (equal (car counts) 2))
           (verina-advanced-1-all-counts-one-or-two-p (cdr counts)))
    (equal counts nil)))

(defun verina-advanced-1-count-equal (x xs)
  (if (consp xs)
      (+ (if (equal (car xs) x) 1 0)
         (verina-advanced-1-count-equal x (cdr xs)))
    0))

(defun verina-advanced-1-find-single-number-precond (nums)
  (and
   (verina-advanced-1-integer-listp nums)
   (let ((nums-counts
          (verina-advanced-1-nums-counts nums nums)))
     (and
      (verina-advanced-1-all-counts-one-or-two-p nums-counts)
      (equal (verina-advanced-1-count-equal 1 nums-counts)
             1)))))

(defun verina-advanced-1-find-unique (remaining nums)
  (if (consp remaining)
      (let* ((x (car remaining))
             (filtered
              (verina-advanced-1-filterlist x nums))
             (count
              (verina-advanced-1-list-length filtered)))
        (if (equal count 1)
            x
          (verina-advanced-1-find-unique (cdr remaining) nums)))
    0))

(defun verina-advanced-1-find-single-number (nums)
  (verina-advanced-1-find-unique nums nums))

(defun verina-advanced-1-every-member-is-result-or-twice-p
    (remaining nums result)
  (if (consp remaining)
      (and
       (or
        (equal (car remaining) result)
        (equal
         (verina-advanced-1-list-length
          (verina-advanced-1-filterlist (car remaining) nums))
         2))
       (verina-advanced-1-every-member-is-result-or-twice-p
        (cdr remaining) nums result))
    (equal remaining nil)))

(defun verina-advanced-1-find-single-number-postcond (nums result)
  (and
   (verina-advanced-1-integer-listp nums)
   (integerp result)
   (< 0 (verina-advanced-1-list-length nums))
   (equal
    (verina-advanced-1-list-length
     (verina-advanced-1-filterlist result nums))
    1)
   (verina-advanced-1-every-member-is-result-or-twice-p
    nums nums result)))

(defun verina-advanced-1-find-single-number-spec-satisfied-statement (nums)
  (implies
   (verina-advanced-1-find-single-number-precond nums)
   (verina-advanced-1-find-single-number-postcond
    nums
    (verina-advanced-1-find-single-number nums))))

(value-triple :itpeval-statement-checked)
:q
