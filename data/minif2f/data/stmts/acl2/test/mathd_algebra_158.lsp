;; Statement-only formalization of miniF2F artifact mathd_algebra_158: an even
;; natural number whose first-eight-odd-number sum exceeds the sum of five
;; terms a + 2*k by 4 must equal 8. This file contains no proof.
;;
;; Equality to the positive integer 4 makes the integer subtraction below
;; equivalent to the truncated natural subtraction used in some source
;; representations.

(in-package "ACL2")

(defun mathd-algebra-158-odd-sum-below (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (let ((k (- n 1)))
      (+ (mathd-algebra-158-odd-sum-below k)
         (+ (* 2 k) 1)))))

(defun mathd-algebra-158-progression-sum-below (a n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (let ((k (- n 1)))
      (+ (mathd-algebra-158-progression-sum-below a k)
         (+ a (* 2 k))))))

(defun mathd-algebra-158-statement (a)
  (implies
   (and (natp a)
        (equal (mod a 2) 0)
        (equal
         (- (mathd-algebra-158-odd-sum-below 8)
            (mathd-algebra-158-progression-sum-below a 5))
         4))
   (equal a 8)))

(value-triple :itpeval-statement-checked)
:q
