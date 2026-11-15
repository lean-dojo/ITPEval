;; Statement-only formalization of miniF2F artifact aime_1984_p7: every
;; natural-number function satisfying f(n) = n - 3 for n >= 1000 and
;; f(n) = f(f(n + 5)) for n < 1000 has f(84) = 997. This file contains no
;; proof.

(in-package "ACL2")

;; The table supplies the values below 1000; the other branch is fixed by the
;; first hypothesis.
(defun aime-1984-p7-value (function-table n)
  (if (natp n)
      (if (<= 1000 n)
          (- n 3)
        (let ((entry (assoc-equal n function-table)))
          (if (consp entry)
              (cdr entry)
            0)))
    0))

(defun aime-1984-p7-low-table-p (function-table count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let* ((n (- count 1))
           (entry (assoc-equal n function-table)))
      (and (consp entry)
           (natp (cdr entry))
           (aime-1984-p7-low-table-p function-table n)))))

(defun aime-1984-p7-recurrence-p (function-table count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((n (- count 1)))
      (and (equal
            (aime-1984-p7-value function-table n)
            (aime-1984-p7-value
             function-table
             (aime-1984-p7-value function-table (+ n 5))))
           (aime-1984-p7-recurrence-p function-table n)))))

(defun aime-1984-p7-statement (function-table)
  (implies
   (and (alistp function-table)
        (aime-1984-p7-low-table-p function-table 1000)
        (aime-1984-p7-recurrence-p function-table 1000))
   (equal (aime-1984-p7-value function-table 84)
          997)))

(value-triple :itpeval-statement-checked)
:q
