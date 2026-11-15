;; Statement-only formalization of Logipedia corpus artifact
;; cong.let_clause_1034, catalog title "cong.let_clause_1034": for natural
;; numbers n, m, p, x2515, and x2516 with p positive, x2515 is its remainder
;; modulo x2516 plus x2516 times its natural quotient by x2516. This file
;; contains no proof.

(in-package "ACL2")

;; The source natural-number library totalizes division by zero with
;; mod(x, 0) = x and div(x, 0) = x + 1.

(defun logipedia-cong-let-clause-1034-mod (x y)
  (if (equal y 0)
      x
    (mod x y)))

(defun logipedia-cong-let-clause-1034-div (x y)
  (if (equal y 0)
      (+ x 1)
    (floor x y)))

(defun logipedia-cong-let-clause-1034-statement
    (n m p x2515 x2516)
  (implies
   (and (natp n)
        (natp m)
        (natp p)
        (< 0 p)
        (natp x2515)
        (natp x2516))
   (equal
    x2515
    (+ (logipedia-cong-let-clause-1034-mod
        x2515 x2516)
       (* x2516
          (logipedia-cong-let-clause-1034-div
           x2515 x2516))))))

(value-triple :itpeval-statement-checked)
:q
