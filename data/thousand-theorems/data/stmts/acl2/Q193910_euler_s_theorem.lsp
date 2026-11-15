;; Statement-only formalization of thousand-theorems corpus artifact Q193910,
;; "Euler's theorem": for natural numbers x and n, coprimality implies that x
;; raised to Euler's totient of n is congruent to 1 modulo n. This file
;; contains no proof.

(in-package "ACL2")

(defun q193910-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (q193910-gcd a (- b a)))
            (t
             (q193910-gcd (- a b) b)))
    0))

(defun q193910-totient-count (k n)
  (declare (xargs :measure (nfix k)))
  (if (and (natp k) (natp n))
      (if (equal k 0)
          0
        (+ (if (equal (q193910-gcd (- k 1) n) 1)
               1
             0)
           (q193910-totient-count (- k 1) n)))
    0))

(defun q193910-totient (n)
  (if (natp n)
      (q193910-totient-count n n)
    0))

(defun q193910-congruent-p (x y n)
  (and (integerp x)
       (integerp y)
       (natp n)
       (if (equal n 0)
           (equal x y)
         (equal (mod x n) (mod y n)))))

(defun thousand-theorems-q193910-euler-s-theorem-statement (x n)
  (implies (and (natp x)
                (natp n)
                (equal (q193910-gcd x n) 1))
           (q193910-congruent-p
            (expt x (q193910-totient n))
            1
            n)))

(value-triple :itpeval-statement-checked)
:q
