;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_405: a natural Fibonacci sequence evaluated at indices
;; congruent to 5, 10, and 15 modulo 16 has the stated sum modulo 7.
;; This file contains no proof.
;;
;; The initial values and recurrence uniquely determine the source function
;; on the naturals. Every satisfying source function therefore agrees with
;; the recursive sequence below, and conversely this sequence is
;; natural-valued and satisfies all the source hypotheses. Thus eliminating
;; the function parameter is bidirectionally equivalent to the universally
;; quantified source implication and does not replace it by a finite table.

(in-package "ACL2")

(defun mathd-numbertheory-405-sequence (n)
  (declare (xargs :measure (nfix n)))
  (if (not (natp n))
      0
    (cond ((equal n 0) 0)
          ((equal n 1) 1)
          (t
           (+ (mathd-numbertheory-405-sequence (- n 2))
              (mathd-numbertheory-405-sequence (- n 1)))))))

(defun mathd-numbertheory-405-statement (a b c)
  (implies
   (and (natp a)
        (natp b)
        (natp c)
        (equal (mod a 16) 5)
        (equal (mod b 16) 10)
        (equal (mod c 16) 15))
   (equal
    (mod (+ (mathd-numbertheory-405-sequence a)
            (mathd-numbertheory-405-sequence b)
            (mathd-numbertheory-405-sequence c))
         7)
    5)))

(value-triple :itpeval-statement-checked)
:q
