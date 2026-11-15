;; Statement-only formalization of miniF2F corpus artifact imo_1981_p6:
;; the recursively characterized natural-number function f satisfies its
;; level-four power recurrence, and f(4, 1981) equals the corresponding
;; power-tower value g(1983) minus 3. This file contains no proof.

(in-package "ACL2")

;; The source recurrences uniquely determine f and g on the naturals, so these
;; total recursive definitions are equivalent to quantifying over functions
;; that satisfy those recurrences.
(defun imo-1981-p6-f (x y)
  (declare
   (xargs
    :measure (make-ord 1 (+ 1 (nfix x)) (nfix y))
    :well-founded-relation o<))
  (if (and (natp x) (natp y))
      (if (zp x)
          (+ y 1)
        (if (zp y)
            (imo-1981-p6-f (- x 1) 1)
          (imo-1981-p6-f
           (- x 1)
           (imo-1981-p6-f x (- y 1)))))
    0))

(defun imo-1981-p6-g (n)
  (declare (xargs :measure (nfix n)))
  (if (natp n)
      (if (zp n)
          2
        (expt 2 (imo-1981-p6-g (- n 1))))
    0))

(defun imo-1981-p6-nat-sub (a b)
  (if (and (natp a) (natp b))
      (nfix (- a b))
    0))

(defun imo-1981-p6-statement (y)
  (implies
   (natp y)
   (and
    (equal
     (imo-1981-p6-f 4 (+ y 1))
     (imo-1981-p6-nat-sub
      (expt 2 (+ (imo-1981-p6-f 4 y) 3))
      3))
    (equal
     (imo-1981-p6-f 4 1981)
     (imo-1981-p6-nat-sub (imo-1981-p6-g 1983) 3)))))

(value-triple :itpeval-statement-checked)
:q
