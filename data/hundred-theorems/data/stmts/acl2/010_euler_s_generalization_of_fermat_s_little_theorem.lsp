;; Statement-only formalization of Hundred Theorems artifact 010, "Euler's
;; Generalization of Fermat's Little Theorem": for coprime natural numbers a
;; and n, a raised to Euler's totient of n is congruent to 1 modulo n. This
;; file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-010-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (hundred-theorems-010-gcd a (- b a)))
            (t
             (hundred-theorems-010-gcd (- a b) b)))
    0))

(defun hundred-theorems-010-totient-count (k n)
  (declare (xargs :measure (nfix k)))
  (if (and (natp k) (natp n))
      (if (equal k 0)
          0
        (+ (if (equal (hundred-theorems-010-gcd (- k 1) n) 1)
               1
             0)
           (hundred-theorems-010-totient-count (- k 1) n)))
    0))

(defun hundred-theorems-010-totient (n)
  (if (natp n)
      (hundred-theorems-010-totient-count n n)
    0))

(defun hundred-theorems-010-congruent-p (x y n)
  (and (integerp x)
       (integerp y)
       (natp n)
       (if (equal n 0)
           (equal x y)
         (equal (mod x n) (mod y n)))))

(defun hundred-theorems-010-euler-statement (a n)
  (implies (and (natp a)
                (natp n)
                (equal (hundred-theorems-010-gcd a n) 1))
           (hundred-theorems-010-congruent-p
            (expt a (hundred-theorems-010-totient n))
            1
            n)))

(value-triple :itpeval-statement-checked)
:q
