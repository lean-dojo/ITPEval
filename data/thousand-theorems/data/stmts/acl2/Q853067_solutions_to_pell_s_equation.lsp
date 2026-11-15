;; Statement-only formalization of thousand-theorems corpus artifact Q853067,
;; "Solutions to Pell's equation": for every natural a greater than one,
;; every natural solution of x^2 - (a^2 - 1)*y^2 = 1 is a pair in the
;; recursively generated Pell sequence beginning with (1,0).
;; This file contains no proof.

(in-package "ACL2")

;; Lean's subtraction on natural numbers is truncated at zero.
(defun q853067-nat-sub (left right)
  (if (and (natp left)
           (natp right))
      (if (< left right)
          0
        (- left right))
    0))

(defun q853067-pell-pair (a n)
  (declare (xargs :measure (nfix n)))
  (if (and (natp a)
           (natp n))
      (if (zp n)
          (cons 1 0)
        (let* ((previous
                (q853067-pell-pair a (- n 1)))
               (previous-x (car previous))
               (previous-y (cdr previous))
               (d (q853067-nat-sub (* a a) 1)))
          (cons
           (+ (* previous-x a)
              (* d previous-y))
           (+ previous-x
              (* previous-y a)))))
    (cons 0 0)))

(defun-sk q853067-pell-index-exists-p (a x y)
  (exists (n)
    (and
     (natp n)
     (let ((pair (q853067-pell-pair a n)))
       (and
        (equal x (car pair))
        (equal y (cdr pair)))))))

(defun thousand-theorems-q853067-solutions-to-pell-s-equation-statement
    (a x y)
  (implies
   (and
    (natp a)
    (natp x)
    (natp y)
    (< 1 a)
    (equal
     (q853067-nat-sub
      (* x x)
      (* (q853067-nat-sub (* a a) 1)
         (* y y)))
     1))
   (q853067-pell-index-exists-p a x y)))

(value-triple :itpeval-statement-checked)
:q
